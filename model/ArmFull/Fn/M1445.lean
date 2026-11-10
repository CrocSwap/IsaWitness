import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M1049
import ArmFull.Fn.M1144
import ArmFull.Fn.M1145
import ArmFull.Fn.M1285
import ArmFull.Fn.M1286
import ArmFull.Fn.M1287
import ArmFull.Fn.M1288

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
def __DecodeT32__seg7 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__546 ← (( do
    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111110011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
               __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
               __opcode 11 8)) == (0x0#4 : (BitVec 4))))) : Bool) : Bool)
    then
      (do
        let w__545 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__545 <b 3453) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__546 : Bool)
  then
    (do
      writeReg SEE 3453
      let D := (BitVec.slice __opcode 22 1)
      let Rn := (BitVec.slice __opcode 16 4)
      let Vd := (BitVec.slice __opcode 12 4)
      let size := (BitVec.slice __opcode 10 2)
      let index_align := (BitVec.slice __opcode 4 4)
      let Rm := (BitVec.slice __opcode 0 4)
      (decode_aarch32_instrs_VLD1_1_T1enc_A_txt D Rn Vd size index_align Rm)
      (pure false))
  else
    (do
      let w__548 ← (( do
        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111110011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                   __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                   __opcode 11 8)) == (0x4#4 : (BitVec 4))))) : Bool) : Bool)
        then
          (do
            let w__547 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__547 <b 3454) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__548 : Bool)
      then
        (do
          writeReg SEE 3454
          let D := (BitVec.slice __opcode 22 1)
          let Rn := (BitVec.slice __opcode 16 4)
          let Vd := (BitVec.slice __opcode 12 4)
          let size := (BitVec.slice __opcode 10 2)
          let index_align := (BitVec.slice __opcode 4 4)
          let Rm := (BitVec.slice __opcode 0 4)
          (decode_aarch32_instrs_VLD1_1_T2enc_A_txt D Rn Vd size index_align Rm)
          (pure false))
      else
        (do
          let w__550 ← (( do
            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111110011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                       __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                       __opcode 11 8)) == (0x8#4 : (BitVec 4))))) : Bool) : Bool)
            then
              (do
                let w__549 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__549 <b 3455) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__550 : Bool)
          then
            (do
              writeReg SEE 3455
              let D := (BitVec.slice __opcode 22 1)
              let Rn := (BitVec.slice __opcode 16 4)
              let Vd := (BitVec.slice __opcode 12 4)
              let size := (BitVec.slice __opcode 10 2)
              let index_align := (BitVec.slice __opcode 4 4)
              let Rm := (BitVec.slice __opcode 0 4)
              (decode_aarch32_instrs_VLD1_1_T3enc_A_txt D Rn Vd size index_align Rm)
              (pure false))
          else
            (do
              let w__552 ← (( do
                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111110011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                           __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                           __opcode 11 8)) == (0xC#4 : (BitVec 4))))) : Bool) : Bool)
                then
                  (do
                    let w__551 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__551 <b 3457) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__552 : Bool)
              then
                (do
                  writeReg SEE 3457
                  let D := (BitVec.slice __opcode 22 1)
                  let Rn := (BitVec.slice __opcode 16 4)
                  let Vd := (BitVec.slice __opcode 12 4)
                  let size := (BitVec.slice __opcode 6 2)
                  let T := (BitVec.slice __opcode 5 1)
                  let a := (BitVec.slice __opcode 4 1)
                  let Rm := (BitVec.slice __opcode 0 4)
                  (decode_aarch32_instrs_VLD1_a_T1enc_A_txt D Rn Vd size T a Rm)
                  (pure false))
              else
                (do
                  let w__554 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111110010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                               __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                               __opcode 11 8)) == (0x7#4 : (BitVec 4))))) : Bool) : Bool)
                    then
                      (do
                        let w__553 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__553 <b 3462) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__554 : Bool)
                  then
                    (do
                      writeReg SEE 3462
                      let D := (BitVec.slice __opcode 22 1)
                      let Rn := (BitVec.slice __opcode 16 4)
                      let Vd := (BitVec.slice __opcode 12 4)
                      let itype := (BitVec.slice __opcode 8 4)
                      let size := (BitVec.slice __opcode 6 2)
                      let align := (BitVec.slice __opcode 4 2)
                      let Rm := (BitVec.slice __opcode 0 4)
                      (decode_aarch32_instrs_VLD1_m_T1enc_A_txt D Rn Vd itype size align Rm)
                      (pure false))
                  else
                    (do
                      let w__556 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31
                                 23)) == (0b111110010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                   __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                   __opcode 11 8)) == (0xA#4 : (BitVec 4))))) : Bool) : Bool)
                        then
                          (do
                            let w__555 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__555 <b 3463) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__556 : Bool)
                      then
                        (do
                          writeReg SEE 3463
                          let D := (BitVec.slice __opcode 22 1)
                          let Rn := (BitVec.slice __opcode 16 4)
                          let Vd := (BitVec.slice __opcode 12 4)
                          let itype := (BitVec.slice __opcode 8 4)
                          let size := (BitVec.slice __opcode 6 2)
                          let align := (BitVec.slice __opcode 4 2)
                          let Rm := (BitVec.slice __opcode 0 4)
                          (decode_aarch32_instrs_VLD1_m_T2enc_A_txt D Rn Vd itype size align Rm)
                          (pure false))
                      else
                        (do
                          let w__558 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode
                                     31 23)) == (0b111110010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                       __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                       __opcode 11 8)) == (0x6#4 : (BitVec 4))))) : Bool) : Bool)
                            then
                              (do
                                let w__557 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__557 <b 3464) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__558 : Bool)
                          then
                            (do
                              writeReg SEE 3464
                              let D := (BitVec.slice __opcode 22 1)
                              let Rn := (BitVec.slice __opcode 16 4)
                              let Vd := (BitVec.slice __opcode 12 4)
                              let itype := (BitVec.slice __opcode 8 4)
                              let size := (BitVec.slice __opcode 6 2)
                              let align := (BitVec.slice __opcode 4 2)
                              let Rm := (BitVec.slice __opcode 0 4)
                              (decode_aarch32_instrs_VLD1_m_T3enc_A_txt D Rn Vd itype size align Rm)
                              (pure false))
                          else
                            (do
                              let w__560 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                         __opcode 31 23)) == (0b111110010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                           __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                           __opcode 11 8)) == (0x2#4 : (BitVec 4))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__559 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__559 <b 3465) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__560 : Bool)
                              then
                                (do
                                  writeReg SEE 3465
                                  let D := (BitVec.slice __opcode 22 1)
                                  let Rn := (BitVec.slice __opcode 16 4)
                                  let Vd := (BitVec.slice __opcode 12 4)
                                  let itype := (BitVec.slice __opcode 8 4)
                                  let size := (BitVec.slice __opcode 6 2)
                                  let align := (BitVec.slice __opcode 4 2)
                                  let Rm := (BitVec.slice __opcode 0 4)
                                  (decode_aarch32_instrs_VLD1_m_T4enc_A_txt D Rn Vd itype size align
                                    Rm)
                                  (pure false))
                              else
                                (do
                                  let w__562 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                             __opcode 31 23)) == (0b111110011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                               __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                               __opcode 11 8)) == (0x1#4 : (BitVec 4))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__561 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__561 <b 3469) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__562 : Bool)
                                  then
                                    (do
                                      writeReg SEE 3469
                                      let D := (BitVec.slice __opcode 22 1)
                                      let Rn := (BitVec.slice __opcode 16 4)
                                      let Vd := (BitVec.slice __opcode 12 4)
                                      let size := (BitVec.slice __opcode 10 2)
                                      let index_align := (BitVec.slice __opcode 4 4)
                                      let Rm := (BitVec.slice __opcode 0 4)
                                      (decode_aarch32_instrs_VLD2_1_T1enc_A_txt D Rn Vd size
                                        index_align Rm)
                                      (pure false))
                                  else
                                    (do
                                      let w__564 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                 __opcode 31 23)) == (0b111110011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                   __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                   __opcode 11 8)) == (0x5#4 : (BitVec 4))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__563 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__563 <b 3470) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__564 : Bool)
                                      then
                                        (do
                                          writeReg SEE 3470
                                          let D := (BitVec.slice __opcode 22 1)
                                          let Rn := (BitVec.slice __opcode 16 4)
                                          let Vd := (BitVec.slice __opcode 12 4)
                                          let size := (BitVec.slice __opcode 10 2)
                                          let index_align := (BitVec.slice __opcode 4 4)
                                          let Rm := (BitVec.slice __opcode 0 4)
                                          (decode_aarch32_instrs_VLD2_1_T2enc_A_txt D Rn Vd size
                                            index_align Rm)
                                          (pure false))
                                      else
                                        (do
                                          let w__566 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                     __opcode 31 23)) == (0b111110011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                       __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                       __opcode 11 8)) == (0x9#4 : (BitVec 4))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__565 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__565 <b 3471) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__566 : Bool)
                                          then
                                            (do
                                              writeReg SEE 3471
                                              let D := (BitVec.slice __opcode 22 1)
                                              let Rn := (BitVec.slice __opcode 16 4)
                                              let Vd := (BitVec.slice __opcode 12 4)
                                              let size := (BitVec.slice __opcode 10 2)
                                              let index_align := (BitVec.slice __opcode 4 4)
                                              let Rm := (BitVec.slice __opcode 0 4)
                                              (decode_aarch32_instrs_VLD2_1_T3enc_A_txt D Rn Vd size
                                                index_align Rm)
                                              (pure false))
                                          else
                                            (do
                                              let w__568 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                         __opcode 31 23)) == (0b111110011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                           __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                           __opcode 11 8)) == (0xD#4 : (BitVec 4))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__567 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__567 <b 3473) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__568 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 3473
                                                  let D := (BitVec.slice __opcode 22 1)
                                                  let Rn := (BitVec.slice __opcode 16 4)
                                                  let Vd := (BitVec.slice __opcode 12 4)
                                                  let size := (BitVec.slice __opcode 6 2)
                                                  let T := (BitVec.slice __opcode 5 1)
                                                  let a := (BitVec.slice __opcode 4 1)
                                                  let Rm := (BitVec.slice __opcode 0 4)
                                                  (decode_aarch32_instrs_VLD2_a_T1enc_A_txt D Rn Vd
                                                    size T a Rm)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__570 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                             __opcode 31 23)) == (0b111110010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                               __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                               __opcode 11 9)) == (0b100#3 : (BitVec 3))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__569 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__569 <b 3476) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__570 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 3476
                                                      let D := (BitVec.slice __opcode 22 1)
                                                      let Rn := (BitVec.slice __opcode 16 4)
                                                      let Vd := (BitVec.slice __opcode 12 4)
                                                      let itype := (BitVec.slice __opcode 8 4)
                                                      let size := (BitVec.slice __opcode 6 2)
                                                      let align := (BitVec.slice __opcode 4 2)
                                                      let Rm := (BitVec.slice __opcode 0 4)
                                                      (decode_aarch32_instrs_VLD2_m_T1enc_A_txt D Rn
                                                        Vd itype size align Rm)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__572 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                 __opcode 31 23)) == (0b111110010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                   __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                   __opcode 11 8)) == (0x3#4 : (BitVec 4))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__571 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__571 <b 3477) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__572 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 3477
                                                          let D := (BitVec.slice __opcode 22 1)
                                                          let Rn := (BitVec.slice __opcode 16 4)
                                                          let Vd := (BitVec.slice __opcode 12 4)
                                                          let itype := (BitVec.slice __opcode 8 4)
                                                          let size := (BitVec.slice __opcode 6 2)
                                                          let align := (BitVec.slice __opcode 4 2)
                                                          let Rm := (BitVec.slice __opcode 0 4)
                                                          (decode_aarch32_instrs_VLD2_m_T2enc_A_txt
                                                            D Rn Vd itype size align Rm)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__574 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                     __opcode 31 23)) == (0b111110011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                       __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                       __opcode 11 8)) == (0x2#4 : (BitVec 4))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__573 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__573 <b 3481) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__574 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 3481
                                                              let D := (BitVec.slice __opcode 22 1)
                                                              let Rn := (BitVec.slice __opcode 16 4)
                                                              let Vd := (BitVec.slice __opcode 12 4)
                                                              let size :=
                                                                (BitVec.slice __opcode 10 2)
                                                              let index_align :=
                                                                (BitVec.slice __opcode 4 4)
                                                              let Rm := (BitVec.slice __opcode 0 4)
                                                              (decode_aarch32_instrs_VLD3_1_T1enc_A_txt
                                                                D Rn Vd size index_align Rm)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__576 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                         __opcode 31 23)) == (0b111110011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                           __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                           __opcode 11 8)) == (0x6#4 : (BitVec 4))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__575 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__575 <b 3482) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__576 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 3482
                                                                  let D :=
                                                                    (BitVec.slice __opcode 22 1)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 16 4)
                                                                  let Vd :=
                                                                    (BitVec.slice __opcode 12 4)
                                                                  let size :=
                                                                    (BitVec.slice __opcode 10 2)
                                                                  let index_align :=
                                                                    (BitVec.slice __opcode 4 4)
                                                                  let Rm :=
                                                                    (BitVec.slice __opcode 0 4)
                                                                  (decode_aarch32_instrs_VLD3_1_T2enc_A_txt
                                                                    D Rn Vd size index_align Rm)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__578 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                             __opcode 31 23)) == (0b111110011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                               __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                               __opcode 11 8)) == (0xA#4 : (BitVec 4))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__577 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__577 <b 3483) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__578 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 3483
                                                                      let D :=
                                                                        (BitVec.slice __opcode 22 1)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 16 4)
                                                                      let Vd :=
                                                                        (BitVec.slice __opcode 12 4)
                                                                      let size :=
                                                                        (BitVec.slice __opcode 10 2)
                                                                      let index_align :=
                                                                        (BitVec.slice __opcode 4 4)
                                                                      let Rm :=
                                                                        (BitVec.slice __opcode 0 4)
                                                                      (decode_aarch32_instrs_VLD3_1_T3enc_A_txt
                                                                        D Rn Vd size index_align Rm)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__580 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 23)) == (0b111110011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                   __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                   __opcode 11 8)) == (0xE#4 : (BitVec 4))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__579 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__579 <b 3485) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__580 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 3485
                                                                          let D :=
                                                                            (BitVec.slice __opcode
                                                                              22 1)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode
                                                                              16 4)
                                                                          let Vd :=
                                                                            (BitVec.slice __opcode
                                                                              12 4)
                                                                          let size :=
                                                                            (BitVec.slice __opcode 6
                                                                              2)
                                                                          let T :=
                                                                            (BitVec.slice __opcode 5
                                                                              1)
                                                                          let a :=
                                                                            (BitVec.slice __opcode 4
                                                                              1)
                                                                          let Rm :=
                                                                            (BitVec.slice __opcode 0
                                                                              4)
                                                                          (decode_aarch32_instrs_VLD3_a_T1enc_A_txt
                                                                            D Rn Vd size T a Rm)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__582 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 23)) == (0b111110010#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                     __opcode 21 20)) == (0b10#2 : (BitVec 2)))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__581 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__581 <b 3487) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__582 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 3487
                                                                              let D :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 1)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 4)
                                                                              let Vd :=
                                                                                (BitVec.slice
                                                                                  __opcode 12 4)
                                                                              let itype :=
                                                                                (BitVec.slice
                                                                                  __opcode 8 4)
                                                                              let size :=
                                                                                (BitVec.slice
                                                                                  __opcode 6 2)
                                                                              let align :=
                                                                                (BitVec.slice
                                                                                  __opcode 4 2)
                                                                              let Rm :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 4)
                                                                              (decode_aarch32_instrs_VLD3_m_T1enc_A_txt
                                                                                D Rn Vd itype size
                                                                                align Rm)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__584 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         23)) == (0b111110011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           11 8)) == (0x3#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__583 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__583 <b 3491) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__584 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 3491
                                                                                  let D :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 1)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 4)
                                                                                  let Vd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 12 4)
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 10 2)
                                                                                  let index_align :=
                                                                                    (BitVec.slice
                                                                                      __opcode 4 4)
                                                                                  let Rm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 4)
                                                                                  (decode_aarch32_instrs_VLD4_1_T1enc_A_txt
                                                                                    D Rn Vd size
                                                                                    index_align Rm)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__586 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 23)) == (0b111110011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               11 8)) == (0x7#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__585 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__585 <b 3492) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__586 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 3492
                                                                                      let D :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 1)
                                                                                      let Rn :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 4)
                                                                                      let Vd :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          12 4)
                                                                                      let size :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          10 2)
                                                                                      let index_align :=
                                                                                        (BitVec.slice
                                                                                          __opcode 4
                                                                                          4)
                                                                                      let Rm :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          4)
                                                                                      (decode_aarch32_instrs_VLD4_1_T2enc_A_txt
                                                                                        D Rn Vd size
                                                                                        index_align
                                                                                        Rm)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__588 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 23)) == (0b111110011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   21
                                                                                                   20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   11
                                                                                                   8)) == (0xB#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__587 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__587 <b 3493) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__588 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 3493
                                                                                          let D :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 1)
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 4)
                                                                                          let Vd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              12 4)
                                                                                          let size :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              10 2)
                                                                                          let index_align :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              4 4)
                                                                                          let Rm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 4)
                                                                                          (decode_aarch32_instrs_VLD4_1_T3enc_A_txt
                                                                                            D Rn Vd
                                                                                            size
                                                                                            index_align
                                                                                            Rm)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__590 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     23)) == (0b111110011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       21
                                                                                                       20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       11
                                                                                                       8)) == (0xF#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__589 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__589 <b 3495) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__590 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 3495
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
                                                                                                  6
                                                                                                  2)
                                                                                              let T :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  5
                                                                                                  1)
                                                                                              let a :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  4
                                                                                                  1)
                                                                                              let Rm :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  4)
                                                                                              (decode_aarch32_instrs_VLD4_a_T1enc_A_txt
                                                                                                D Rn
                                                                                                Vd
                                                                                                size
                                                                                                T a
                                                                                                Rm)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__592 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         23)) == (0b111110010#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         21
                                                                                                         20)) == (0b10#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__591 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__591 <b 3497) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__592 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 3497
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
                                                                                                  let itype :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      8
                                                                                                      4)
                                                                                                  let size :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      6
                                                                                                      2)
                                                                                                  let align :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      4
                                                                                                      2)
                                                                                                  let Rm :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      4)
                                                                                                  (decode_aarch32_instrs_VLD4_m_T1enc_A_txt
                                                                                                    D
                                                                                                    Rn
                                                                                                    Vd
                                                                                                    itype
                                                                                                    size
                                                                                                    align
                                                                                                    Rm)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__594 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             25)) == (0b1110110#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               20
                                                                                                               20)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               11
                                                                                                               8)) == (0xB#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__593 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__593 <b 3500) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__594 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 3500
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
                                                                                                      (decode_aarch32_instrs_VLDM_T1enc_A_txt
                                                                                                        P
                                                                                                        U
                                                                                                        D
                                                                                                        W
                                                                                                        Rn
                                                                                                        Vd
                                                                                                        imm8)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__596 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 25)) == (0b1110110#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   20
                                                                                                                   20)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   11
                                                                                                                   8)) == (0xA#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__595 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__595 <b 3501) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__596 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 3501
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
                                                                                                          (decode_aarch32_instrs_VLDM_T2enc_A_txt
                                                                                                            P
                                                                                                            U
                                                                                                            D
                                                                                                            W
                                                                                                            Rn
                                                                                                            Vd
                                                                                                            imm8)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__598 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     24)) == (0xED#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       21
                                                                                                                       20)) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       11
                                                                                                                       10)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__597 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__597 <b 3503) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__598 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 3503
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
                                                                                                              (decode_aarch32_instrs_VLDR_T1enc_A_txt
                                                                                                                U
                                                                                                                D
                                                                                                                Rn
                                                                                                                Vd
                                                                                                                size
                                                                                                                imm8)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__600 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         23)) == (0b111011110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           11
                                                                                                                           8)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           4
                                                                                                                           4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__599 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__599 <b 3505) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__600 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 3505
                                                                                                                  let D :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      22
                                                                                                                      1)
                                                                                                                  let op :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      21
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
                                                                                                                  (decode_aarch32_instrs_VMAX_f_T1enc_A_txt
                                                                                                                    D
                                                                                                                    op
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
                                                                                                                  let w__602 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               27
                                                                                                                               23)) == (0b11110#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               11
                                                                                                                               8)) == (0x6#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__601 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__601 <b 3507) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__602 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 3507
                                                                                                                      let U :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          28
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
                                                                                                                      let op :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          4
                                                                                                                          1)
                                                                                                                      let Vm :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          4)
                                                                                                                      (decode_aarch32_instrs_VMAX_i_T1enc_A_txt
                                                                                                                        U
                                                                                                                        D
                                                                                                                        size
                                                                                                                        Vn
                                                                                                                        Vd
                                                                                                                        N
                                                                                                                        Q
                                                                                                                        M
                                                                                                                        op
                                                                                                                        Vm)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__604 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 23)) == (0b111011110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   11
                                                                                                                                   8)) == (0xD#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   4
                                                                                                                                   4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__603 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__603 <b 3510) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__604 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 3510
                                                                                                                          let D :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              22
                                                                                                                              1)
                                                                                                                          let op :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              21
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
                                                                                                                          (decode_aarch32_instrs_VMLA_f_T1enc_A_txt
                                                                                                                            D
                                                                                                                            op
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
                                                                                                                          let w__606 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     23)) == (0b111011100#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
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
                                                                                                                                let w__605 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__605 <b 3511) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__606 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 3511
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
                                                                                                                              (decode_aarch32_instrs_VMLA_f_T2enc_A_txt
                                                                                                                                D
                                                                                                                                Vn
                                                                                                                                Vd
                                                                                                                                size
                                                                                                                                N
                                                                                                                                op
                                                                                                                                M
                                                                                                                                Vm)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__608 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           27
                                                                                                                                           23)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             11
                                                                                                                                             8)) == (0x9#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             4
                                                                                                                                             4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__607 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__607 <b 3514) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__608 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 3514
                                                                                                                                  let op :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      28
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
                                                                                                                                  (decode_aarch32_instrs_VMLA_i_T1enc_A_txt
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
                                                                                                                                (do
                                                                                                                                  let w__610 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               27
                                                                                                                                               23)) == (0b11111#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 11
                                                                                                                                                 10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   8
                                                                                                                                                   8)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     6
                                                                                                                                                     6)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     4
                                                                                                                                                     4)) == (0#1 : (BitVec 1)))))))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__609 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__609 <b 3515) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__610 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 3515
                                                                                                                                      let U :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          28
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
                                                                                                                                      let op :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          9
                                                                                                                                          1)
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
                                                                                                                                      (decode_aarch32_instrs_VMLA_i_T2enc_A_txt
                                                                                                                                        U
                                                                                                                                        D
                                                                                                                                        size
                                                                                                                                        Vn
                                                                                                                                        Vd
                                                                                                                                        op
                                                                                                                                        N
                                                                                                                                        M
                                                                                                                                        Vm)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__612 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   27
                                                                                                                                                   23)) == (0b11111#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
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
                                                                                                                                            let w__611 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__611 <b 3518) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__612 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 3518
                                                                                                                                          let Q :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              28
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
                                                                                                                                          let op :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              10
                                                                                                                                              1)
                                                                                                                                          let F :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              8
                                                                                                                                              1)
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
                                                                                                                                          (decode_aarch32_instrs_VMLA_s_T1enc_A_txt
                                                                                                                                            Q
                                                                                                                                            D
                                                                                                                                            size
                                                                                                                                            Vn
                                                                                                                                            Vd
                                                                                                                                            op
                                                                                                                                            F
                                                                                                                                            N
                                                                                                                                            M
                                                                                                                                            Vm)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (pure true))))))))))))))))))))))))))))))))))


end ArmFull.Functions
