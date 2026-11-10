import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M1294
import ArmFull.Fn.M1295
import ArmFull.Fn.M1296
import ArmFull.Fn.M1297

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
def __DecodeA64_LoadStore__seg1 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__73 ← (( do
    if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb __opcode 31 10)) == (0b1101100100011111000011#22 : (BitVec 22))) : Bool) : Bool)
    then
      (do
        let w__72 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__72 <b 475) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__73 : Bool)
  then
    (do
      writeReg SEE 475
      let Rt := (BitVec.slice __opcode 0 5)
      let Rn := (BitVec.slice __opcode 5 5)
      let opc := (BitVec.slice __opcode 12 3)
      (decode_gcsstr_aarch64_instrs_memory_gcs_general_register Rt Rn opc)
      (pure false))
  else
    (do
      let w__75 ← (( do
        if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb __opcode 31 10)) == (0b1101100100011111000111#22 : (BitVec 22))) : Bool) : Bool)
        then
          (do
            let w__74 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__74 <b 476) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__75 : Bool)
      then
        (do
          writeReg SEE 476
          let Rt := (BitVec.slice __opcode 0 5)
          let Rn := (BitVec.slice __opcode 5 5)
          let opc := (BitVec.slice __opcode 12 3)
          (decode_gcssttr_aarch64_instrs_memory_gcs_general_register Rt Rn opc)
          (pure false))
      else
        (do
          let w__77 ← (( do
            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb
                       __opcode 29 16)) == (0b00110101000000#14 : (BitVec 14))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       __opcode 13 13)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
            then
              (do
                let w__76 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__76 <b 484) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__77 : Bool)
          then
            (do
              writeReg SEE 484
              let Rt := (BitVec.slice __opcode 0 5)
              let Rn := (BitVec.slice __opcode 5 5)
              let size := (BitVec.slice __opcode 10 2)
              let S := (BitVec.slice __opcode 12 1)
              let opcode := (BitVec.slice __opcode 13 3)
              let o2 := (BitVec.slice __opcode 16 1)
              let R := (BitVec.slice __opcode 21 1)
              let L := (BitVec.slice __opcode 22 1)
              let Q := (BitVec.slice __opcode 30 1)
              (decode_ld1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb Rt Rn size S opcode
                o2 R L Q)
              (pure false))
          else
            (do
              let w__79 ← (( do
                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                           __opcode 29 21)) == (0b001101110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           __opcode 13 13)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                then
                  (do
                    let w__78 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__78 <b 485) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__79 : Bool)
              then
                (do
                  writeReg SEE 485
                  let Rt := (BitVec.slice __opcode 0 5)
                  let Rn := (BitVec.slice __opcode 5 5)
                  let size := (BitVec.slice __opcode 10 2)
                  let S := (BitVec.slice __opcode 12 1)
                  let opcode := (BitVec.slice __opcode 13 3)
                  let Rm := (BitVec.slice __opcode 16 5)
                  let R := (BitVec.slice __opcode 21 1)
                  let L := (BitVec.slice __opcode 22 1)
                  let Q := (BitVec.slice __opcode 30 1)
                  (decode_ld1_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc Rt Rn size S
                    opcode Rm R L Q)
                  (pure false))
              else
                (do
                  let w__81 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb
                             __opcode 29 12)) == (0b001101010000001100#18 : (BitVec 18)))) : Bool) : Bool)
                    then
                      (do
                        let w__80 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__80 <b 486) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__81 : Bool)
                  then
                    (do
                      writeReg SEE 486
                      let Rt := (BitVec.slice __opcode 0 5)
                      let Rn := (BitVec.slice __opcode 5 5)
                      let size := (BitVec.slice __opcode 10 2)
                      let S := (BitVec.slice __opcode 12 1)
                      let opcode := (BitVec.slice __opcode 13 3)
                      let o2 := (BitVec.slice __opcode 16 1)
                      let R := (BitVec.slice __opcode 21 1)
                      let L := (BitVec.slice __opcode 22 1)
                      let Q := (BitVec.slice __opcode 30 1)
                      (decode_ld1r_advsimd_aarch64_instrs_memory_vector_single_no_wb Rt Rn size S
                        opcode o2 R L Q)
                      (pure false))
                  else
                    (do
                      let w__83 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31
                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                   __opcode 29 21)) == (0b001101110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                   __opcode 15 12)) == (0xC#4 : (BitVec 4))))) : Bool) : Bool)
                        then
                          (do
                            let w__82 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__82 <b 487) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__83 : Bool)
                      then
                        (do
                          writeReg SEE 487
                          let Rt := (BitVec.slice __opcode 0 5)
                          let Rn := (BitVec.slice __opcode 5 5)
                          let size := (BitVec.slice __opcode 10 2)
                          let S := (BitVec.slice __opcode 12 1)
                          let opcode := (BitVec.slice __opcode 13 3)
                          let Rm := (BitVec.slice __opcode 16 5)
                          let R := (BitVec.slice __opcode 21 1)
                          let L := (BitVec.slice __opcode 22 1)
                          let Q := (BitVec.slice __opcode 30 1)
                          (decode_ld1r_advsimd_aarch64_instrs_memory_vector_single_post_inc Rt Rn
                            size S opcode Rm R L Q)
                          (pure false))
                      else
                        (do
                          let w__85 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode
                                     31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb
                                       __opcode 29 16)) == (0b00110101100000#14 : (BitVec 14))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                       __opcode 13 13)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                            then
                              (do
                                let w__84 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__84 <b 488) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__85 : Bool)
                          then
                            (do
                              writeReg SEE 488
                              let Rt := (BitVec.slice __opcode 0 5)
                              let Rn := (BitVec.slice __opcode 5 5)
                              let size := (BitVec.slice __opcode 10 2)
                              let S := (BitVec.slice __opcode 12 1)
                              let opcode := (BitVec.slice __opcode 13 3)
                              let o2 := (BitVec.slice __opcode 16 1)
                              let R := (BitVec.slice __opcode 21 1)
                              let L := (BitVec.slice __opcode 22 1)
                              let Q := (BitVec.slice __opcode 30 1)
                              (decode_ld2_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb Rt
                                Rn size S opcode o2 R L Q)
                              (pure false))
                          else
                            (do
                              let w__87 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                         __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                           __opcode 29 21)) == (0b001101111#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                           __opcode 13 13)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__86 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__86 <b 489) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__87 : Bool)
                              then
                                (do
                                  writeReg SEE 489
                                  let Rt := (BitVec.slice __opcode 0 5)
                                  let Rn := (BitVec.slice __opcode 5 5)
                                  let size := (BitVec.slice __opcode 10 2)
                                  let S := (BitVec.slice __opcode 12 1)
                                  let opcode := (BitVec.slice __opcode 13 3)
                                  let Rm := (BitVec.slice __opcode 16 5)
                                  let R := (BitVec.slice __opcode 21 1)
                                  let L := (BitVec.slice __opcode 22 1)
                                  let Q := (BitVec.slice __opcode 30 1)
                                  (decode_ld2_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc
                                    Rt Rn size S opcode Rm R L Q)
                                  (pure false))
                              else
                                (do
                                  let w__89 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             __opcode 31 31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb
                                             __opcode 29 12)) == (0b001101011000001100#18 : (BitVec 18)))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__88 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__88 <b 490) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__89 : Bool)
                                  then
                                    (do
                                      writeReg SEE 490
                                      let Rt := (BitVec.slice __opcode 0 5)
                                      let Rn := (BitVec.slice __opcode 5 5)
                                      let size := (BitVec.slice __opcode 10 2)
                                      let S := (BitVec.slice __opcode 12 1)
                                      let opcode := (BitVec.slice __opcode 13 3)
                                      let o2 := (BitVec.slice __opcode 16 1)
                                      let R := (BitVec.slice __opcode 21 1)
                                      let L := (BitVec.slice __opcode 22 1)
                                      let Q := (BitVec.slice __opcode 30 1)
                                      (decode_ld2r_advsimd_aarch64_instrs_memory_vector_single_no_wb
                                        Rt Rn size S opcode o2 R L Q)
                                      (pure false))
                                  else
                                    (do
                                      let w__91 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                   __opcode 29 21)) == (0b001101111#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                   __opcode 15 12)) == (0xC#4 : (BitVec 4))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__90 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__90 <b 491) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__91 : Bool)
                                      then
                                        (do
                                          writeReg SEE 491
                                          let Rt := (BitVec.slice __opcode 0 5)
                                          let Rn := (BitVec.slice __opcode 5 5)
                                          let size := (BitVec.slice __opcode 10 2)
                                          let S := (BitVec.slice __opcode 12 1)
                                          let opcode := (BitVec.slice __opcode 13 3)
                                          let Rm := (BitVec.slice __opcode 16 5)
                                          let R := (BitVec.slice __opcode 21 1)
                                          let L := (BitVec.slice __opcode 22 1)
                                          let Q := (BitVec.slice __opcode 30 1)
                                          (decode_ld2r_advsimd_aarch64_instrs_memory_vector_single_post_inc
                                            Rt Rn size S opcode Rm R L Q)
                                          (pure false))
                                      else
                                        (do
                                          let w__93 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                     __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb
                                                       __opcode 29 16)) == (0b00110101000000#14 : (BitVec 14))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 13 13)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__92 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__92 <b 492) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__93 : Bool)
                                          then
                                            (do
                                              writeReg SEE 492
                                              let Rt := (BitVec.slice __opcode 0 5)
                                              let Rn := (BitVec.slice __opcode 5 5)
                                              let size := (BitVec.slice __opcode 10 2)
                                              let S := (BitVec.slice __opcode 12 1)
                                              let opcode := (BitVec.slice __opcode 13 3)
                                              let o2 := (BitVec.slice __opcode 16 1)
                                              let R := (BitVec.slice __opcode 21 1)
                                              let L := (BitVec.slice __opcode 22 1)
                                              let Q := (BitVec.slice __opcode 30 1)
                                              (decode_ld3_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb
                                                Rt Rn size S opcode o2 R L Q)
                                              (pure false))
                                          else
                                            (do
                                              let w__95 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                         __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                           __opcode 29 21)) == (0b001101110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 13 13)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__94 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__94 <b 493) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__95 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 493
                                                  let Rt := (BitVec.slice __opcode 0 5)
                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                  let size := (BitVec.slice __opcode 10 2)
                                                  let S := (BitVec.slice __opcode 12 1)
                                                  let opcode := (BitVec.slice __opcode 13 3)
                                                  let Rm := (BitVec.slice __opcode 16 5)
                                                  let R := (BitVec.slice __opcode 21 1)
                                                  let L := (BitVec.slice __opcode 22 1)
                                                  let Q := (BitVec.slice __opcode 30 1)
                                                  (decode_ld3_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc
                                                    Rt Rn size S opcode Rm R L Q)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__97 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                             __opcode 31 31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb
                                                             __opcode 29 12)) == (0b001101010000001110#18 : (BitVec 18)))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__96 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__96 <b 494) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__97 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 494
                                                      let Rt := (BitVec.slice __opcode 0 5)
                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                      let size := (BitVec.slice __opcode 10 2)
                                                      let S := (BitVec.slice __opcode 12 1)
                                                      let opcode := (BitVec.slice __opcode 13 3)
                                                      let o2 := (BitVec.slice __opcode 16 1)
                                                      let R := (BitVec.slice __opcode 21 1)
                                                      let L := (BitVec.slice __opcode 22 1)
                                                      let Q := (BitVec.slice __opcode 30 1)
                                                      (decode_ld3r_advsimd_aarch64_instrs_memory_vector_single_no_wb
                                                        Rt Rn size S opcode o2 R L Q)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__99 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                 __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                   __opcode 29 21)) == (0b001101110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                   __opcode 15 12)) == (0xE#4 : (BitVec 4))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__98 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__98 <b 495) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__99 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 495
                                                          let Rt := (BitVec.slice __opcode 0 5)
                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                          let size := (BitVec.slice __opcode 10 2)
                                                          let S := (BitVec.slice __opcode 12 1)
                                                          let opcode := (BitVec.slice __opcode 13 3)
                                                          let Rm := (BitVec.slice __opcode 16 5)
                                                          let R := (BitVec.slice __opcode 21 1)
                                                          let L := (BitVec.slice __opcode 22 1)
                                                          let Q := (BitVec.slice __opcode 30 1)
                                                          (decode_ld3r_advsimd_aarch64_instrs_memory_vector_single_post_inc
                                                            Rt Rn size S opcode Rm R L Q)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__101 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                     __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb
                                                                       __opcode 29 16)) == (0b00110101100000#14 : (BitVec 14))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 13 13)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__100 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__100 <b 496) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__101 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 496
                                                              let Rt := (BitVec.slice __opcode 0 5)
                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                              let size :=
                                                                (BitVec.slice __opcode 10 2)
                                                              let S := (BitVec.slice __opcode 12 1)
                                                              let opcode :=
                                                                (BitVec.slice __opcode 13 3)
                                                              let o2 := (BitVec.slice __opcode 16 1)
                                                              let R := (BitVec.slice __opcode 21 1)
                                                              let L := (BitVec.slice __opcode 22 1)
                                                              let Q := (BitVec.slice __opcode 30 1)
                                                              (decode_ld4_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb
                                                                Rt Rn size S opcode o2 R L Q)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__103 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                         __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                           __opcode 29 21)) == (0b001101111#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 13 13)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__102 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__102 <b 497) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__103 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 497
                                                                  let Rt :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let size :=
                                                                    (BitVec.slice __opcode 10 2)
                                                                  let S :=
                                                                    (BitVec.slice __opcode 12 1)
                                                                  let opcode :=
                                                                    (BitVec.slice __opcode 13 3)
                                                                  let Rm :=
                                                                    (BitVec.slice __opcode 16 5)
                                                                  let R :=
                                                                    (BitVec.slice __opcode 21 1)
                                                                  let L :=
                                                                    (BitVec.slice __opcode 22 1)
                                                                  let Q :=
                                                                    (BitVec.slice __opcode 30 1)
                                                                  (decode_ld4_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc
                                                                    Rt Rn size S opcode Rm R L Q)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__105 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                             __opcode 31 31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb
                                                                             __opcode 29 12)) == (0b001101011000001110#18 : (BitVec 18)))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__104 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__104 <b 498) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__105 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 498
                                                                      let Rt :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let size :=
                                                                        (BitVec.slice __opcode 10 2)
                                                                      let S :=
                                                                        (BitVec.slice __opcode 12 1)
                                                                      let opcode :=
                                                                        (BitVec.slice __opcode 13 3)
                                                                      let o2 :=
                                                                        (BitVec.slice __opcode 16 1)
                                                                      let R :=
                                                                        (BitVec.slice __opcode 21 1)
                                                                      let L :=
                                                                        (BitVec.slice __opcode 22 1)
                                                                      let Q :=
                                                                        (BitVec.slice __opcode 30 1)
                                                                      (decode_ld4r_advsimd_aarch64_instrs_memory_vector_single_no_wb
                                                                        Rt Rn size S opcode o2 R L Q)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__107 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                   __opcode 29 21)) == (0b001101111#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                   __opcode 15 12)) == (0xE#4 : (BitVec 4))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__106 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__106 <b 499) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__107 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 499
                                                                          let Rt :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let size :=
                                                                            (BitVec.slice __opcode
                                                                              10 2)
                                                                          let S :=
                                                                            (BitVec.slice __opcode
                                                                              12 1)
                                                                          let opcode :=
                                                                            (BitVec.slice __opcode
                                                                              13 3)
                                                                          let Rm :=
                                                                            (BitVec.slice __opcode
                                                                              16 5)
                                                                          let R :=
                                                                            (BitVec.slice __opcode
                                                                              21 1)
                                                                          let L :=
                                                                            (BitVec.slice __opcode
                                                                              22 1)
                                                                          let Q :=
                                                                            (BitVec.slice __opcode
                                                                              30 1)
                                                                          (decode_ld4r_advsimd_aarch64_instrs_memory_vector_single_post_inc
                                                                            Rt Rn size S opcode Rm R
                                                                            L Q)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__109 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb
                                                                                       __opcode 29
                                                                                       16)) == (0b00110100000000#14 : (BitVec 14))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 13
                                                                                       13)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__108 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__108 <b 500) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__109 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 500
                                                                              let Rt :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let size :=
                                                                                (BitVec.slice
                                                                                  __opcode 10 2)
                                                                              let S :=
                                                                                (BitVec.slice
                                                                                  __opcode 12 1)
                                                                              let opcode :=
                                                                                (BitVec.slice
                                                                                  __opcode 13 3)
                                                                              let o2 :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 1)
                                                                              let R :=
                                                                                (BitVec.slice
                                                                                  __opcode 21 1)
                                                                              let L :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 1)
                                                                              let Q :=
                                                                                (BitVec.slice
                                                                                  __opcode 30 1)
                                                                              (decode_st1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb
                                                                                Rt Rn size S opcode
                                                                                o2 R L Q)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__111 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           29 21)) == (0b001101100#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           13 13)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__110 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__110 <b 501) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__111 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 501
                                                                                  let Rt :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 10 2)
                                                                                  let S :=
                                                                                    (BitVec.slice
                                                                                      __opcode 12 1)
                                                                                  let opcode :=
                                                                                    (BitVec.slice
                                                                                      __opcode 13 3)
                                                                                  let Rm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 5)
                                                                                  let R :=
                                                                                    (BitVec.slice
                                                                                      __opcode 21 1)
                                                                                  let L :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 1)
                                                                                  let Q :=
                                                                                    (BitVec.slice
                                                                                      __opcode 30 1)
                                                                                  (decode_st1_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc
                                                                                    Rt Rn size S
                                                                                    opcode Rm R L Q)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__113 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               29 16)) == (0b00110100100000#14 : (BitVec 14))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               13 13)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__112 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__112 <b 502) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__113 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 502
                                                                                      let Rt :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          5)
                                                                                      let Rn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let size :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          10 2)
                                                                                      let S :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          12 1)
                                                                                      let opcode :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          13 3)
                                                                                      let o2 :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 1)
                                                                                      let R :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          21 1)
                                                                                      let L :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 1)
                                                                                      let Q :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          30 1)
                                                                                      (decode_st2_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb
                                                                                        Rt Rn size S
                                                                                        opcode o2 R
                                                                                        L Q)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__115 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   29
                                                                                                   21)) == (0b001101101#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   13
                                                                                                   13)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__114 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__114 <b 503) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__115 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 503
                                                                                          let Rt :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 5)
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let size :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              10 2)
                                                                                          let S :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              12 1)
                                                                                          let opcode :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              13 3)
                                                                                          let Rm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 5)
                                                                                          let R :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              21 1)
                                                                                          let L :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 1)
                                                                                          let Q :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              30 1)
                                                                                          (decode_st2_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc
                                                                                            Rt Rn
                                                                                            size S
                                                                                            opcode
                                                                                            Rm R L Q)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__117 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       29
                                                                                                       16)) == (0b00110100000000#14 : (BitVec 14))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       13
                                                                                                       13)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__116 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__116 <b 504) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__117 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 504
                                                                                              let Rt :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  5)
                                                                                              let Rn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  5
                                                                                                  5)
                                                                                              let size :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  10
                                                                                                  2)
                                                                                              let S :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  12
                                                                                                  1)
                                                                                              let opcode :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  13
                                                                                                  3)
                                                                                              let o2 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  1)
                                                                                              let R :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  21
                                                                                                  1)
                                                                                              let L :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  22
                                                                                                  1)
                                                                                              let Q :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  30
                                                                                                  1)
                                                                                              (decode_st3_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb
                                                                                                Rt
                                                                                                Rn
                                                                                                size
                                                                                                S
                                                                                                opcode
                                                                                                o2 R
                                                                                                L Q)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__119 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           29
                                                                                                           21)) == (0b001101100#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           13
                                                                                                           13)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__118 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__118 <b 505) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__119 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 505
                                                                                                  let Rt :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      5)
                                                                                                  let Rn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      5
                                                                                                      5)
                                                                                                  let size :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      10
                                                                                                      2)
                                                                                                  let S :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      12
                                                                                                      1)
                                                                                                  let opcode :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      13
                                                                                                      3)
                                                                                                  let Rm :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      5)
                                                                                                  let R :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      21
                                                                                                      1)
                                                                                                  let L :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      22
                                                                                                      1)
                                                                                                  let Q :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      30
                                                                                                      1)
                                                                                                  (decode_st3_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc
                                                                                                    Rt
                                                                                                    Rn
                                                                                                    size
                                                                                                    S
                                                                                                    opcode
                                                                                                    Rm
                                                                                                    R
                                                                                                    L
                                                                                                    Q)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__121 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               29
                                                                                                               16)) == (0b00110100100000#14 : (BitVec 14))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               13
                                                                                                               13)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__120 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__120 <b 506) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__121 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 506
                                                                                                      let Rt :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          5)
                                                                                                      let Rn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          5
                                                                                                          5)
                                                                                                      let size :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          10
                                                                                                          2)
                                                                                                      let S :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          12
                                                                                                          1)
                                                                                                      let opcode :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          13
                                                                                                          3)
                                                                                                      let o2 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          1)
                                                                                                      let R :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          21
                                                                                                          1)
                                                                                                      let L :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          22
                                                                                                          1)
                                                                                                      let Q :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          30
                                                                                                          1)
                                                                                                      (decode_st4_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb
                                                                                                        Rt
                                                                                                        Rn
                                                                                                        size
                                                                                                        S
                                                                                                        opcode
                                                                                                        o2
                                                                                                        R
                                                                                                        L
                                                                                                        Q)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__123 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   29
                                                                                                                   21)) == (0b001101101#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   13
                                                                                                                   13)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__122 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__122 <b 507) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__123 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 507
                                                                                                          let Rt :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              5)
                                                                                                          let Rn :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              5
                                                                                                              5)
                                                                                                          let size :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              10
                                                                                                              2)
                                                                                                          let S :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              12
                                                                                                              1)
                                                                                                          let opcode :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              13
                                                                                                              3)
                                                                                                          let Rm :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              5)
                                                                                                          let R :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              21
                                                                                                              1)
                                                                                                          let L :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              22
                                                                                                              1)
                                                                                                          let Q :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              30
                                                                                                              1)
                                                                                                          (decode_st4_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc
                                                                                                            Rt
                                                                                                            Rn
                                                                                                            size
                                                                                                            S
                                                                                                            opcode
                                                                                                            Rm
                                                                                                            R
                                                                                                            L
                                                                                                            Q)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__125 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       29
                                                                                                                       16)) == (0b00110001000000#14 : (BitVec 14))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       13
                                                                                                                       13)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__124 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__124 <b 508) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__125 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 508
                                                                                                              let Rt :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  5)
                                                                                                              let Rn :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  5
                                                                                                                  5)
                                                                                                              let size :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  10
                                                                                                                  2)
                                                                                                              let opcode :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  12
                                                                                                                  4)
                                                                                                              let L :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  22
                                                                                                                  1)
                                                                                                              let Q :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  30
                                                                                                                  1)
                                                                                                              (decode_ld1_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb
                                                                                                                Rt
                                                                                                                Rn
                                                                                                                size
                                                                                                                opcode
                                                                                                                L
                                                                                                                Q)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__127 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           29
                                                                                                                           21)) == (0b001100110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           13
                                                                                                                           13)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__126 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__126 <b 509) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__127 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 509
                                                                                                                  let Rt :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      5)
                                                                                                                  let Rn :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      5
                                                                                                                      5)
                                                                                                                  let size :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      10
                                                                                                                      2)
                                                                                                                  let opcode :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      12
                                                                                                                      4)
                                                                                                                  let Rm :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      5)
                                                                                                                  let L :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      22
                                                                                                                      1)
                                                                                                                  let Q :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      30
                                                                                                                      1)
                                                                                                                  (decode_ld1_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc
                                                                                                                    Rt
                                                                                                                    Rn
                                                                                                                    size
                                                                                                                    opcode
                                                                                                                    Rm
                                                                                                                    L
                                                                                                                    Q)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__129 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             29
                                                                                                                             12)) == (0b001100010000001000#18 : (BitVec 18)))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__128 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__128 <b 510) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__129 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 510
                                                                                                                      let Rt :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          5)
                                                                                                                      let Rn :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          5
                                                                                                                          5)
                                                                                                                      let size :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          10
                                                                                                                          2)
                                                                                                                      let opcode :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          12
                                                                                                                          4)
                                                                                                                      let L :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          22
                                                                                                                          1)
                                                                                                                      let Q :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          30
                                                                                                                          1)
                                                                                                                      (decode_ld2_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb
                                                                                                                        Rt
                                                                                                                        Rn
                                                                                                                        size
                                                                                                                        opcode
                                                                                                                        L
                                                                                                                        Q)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__131 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   29
                                                                                                                                   21)) == (0b001100110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   15
                                                                                                                                   12)) == (0x8#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__130 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__130 <b 511) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__131 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 511
                                                                                                                          let Rt :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              5)
                                                                                                                          let Rn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              5
                                                                                                                              5)
                                                                                                                          let size :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              10
                                                                                                                              2)
                                                                                                                          let opcode :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              12
                                                                                                                              4)
                                                                                                                          let Rm :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              5)
                                                                                                                          let L :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              22
                                                                                                                              1)
                                                                                                                          let Q :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              30
                                                                                                                              1)
                                                                                                                          (decode_ld2_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc
                                                                                                                            Rt
                                                                                                                            Rn
                                                                                                                            size
                                                                                                                            opcode
                                                                                                                            Rm
                                                                                                                            L
                                                                                                                            Q)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__133 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     29
                                                                                                                                     12)) == (0b001100010000000100#18 : (BitVec 18)))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__132 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__132 <b 512) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__133 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 512
                                                                                                                              let Rt :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  5)
                                                                                                                              let Rn :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  5
                                                                                                                                  5)
                                                                                                                              let size :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  10
                                                                                                                                  2)
                                                                                                                              let opcode :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  12
                                                                                                                                  4)
                                                                                                                              let L :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  22
                                                                                                                                  1)
                                                                                                                              let Q :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  30
                                                                                                                                  1)
                                                                                                                              (decode_ld3_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb
                                                                                                                                Rt
                                                                                                                                Rn
                                                                                                                                size
                                                                                                                                opcode
                                                                                                                                L
                                                                                                                                Q)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__135 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           29
                                                                                                                                           21)) == (0b001100110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           15
                                                                                                                                           12)) == (0x4#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__134 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__134 <b 513) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__135 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 513
                                                                                                                                  let Rt :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      5)
                                                                                                                                  let Rn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      5
                                                                                                                                      5)
                                                                                                                                  let size :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      10
                                                                                                                                      2)
                                                                                                                                  let opcode :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      12
                                                                                                                                      4)
                                                                                                                                  let Rm :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      5)
                                                                                                                                  let L :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      22
                                                                                                                                      1)
                                                                                                                                  let Q :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      30
                                                                                                                                      1)
                                                                                                                                  (decode_ld3_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc
                                                                                                                                    Rt
                                                                                                                                    Rn
                                                                                                                                    size
                                                                                                                                    opcode
                                                                                                                                    Rm
                                                                                                                                    L
                                                                                                                                    Q)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (pure true))))))))))))))))))))))))))))))))


end ArmFull.Functions
