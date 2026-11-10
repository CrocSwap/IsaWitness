import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M1105
import ArmFull.Fn.M1106
import ArmFull.Fn.M1151
import ArmFull.Fn.M1152

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
def __DecodeA64_DataProcFPSIMD__seg7 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__545 ← (( do
    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x1E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
               __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
               __opcode 15 10)) == (0b000010#6 : (BitVec 6))))) : Bool) : Bool)
    then
      (do
        let w__544 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__544 <b 410) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__545 : Bool)
  then
    (do
      writeReg SEE 410
      let Rd := (BitVec.slice __opcode 0 5)
      let Rn := (BitVec.slice __opcode 5 5)
      let op := (BitVec.slice __opcode 15 1)
      let Rm := (BitVec.slice __opcode 16 5)
      let ftype := (BitVec.slice __opcode 22 2)
      (decode_fmul_float_aarch64_instrs_float_arithmetic_mul_product Rd Rn op Rm ftype)
      (pure false))
  else
    (do
      let w__547 ← (( do
        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x1E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                   __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                   __opcode 15 10)) == (0b100010#6 : (BitVec 6))))) : Bool) : Bool)
        then
          (do
            let w__546 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__546 <b 411) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__547 : Bool)
      then
        (do
          writeReg SEE 411
          let Rd := (BitVec.slice __opcode 0 5)
          let Rn := (BitVec.slice __opcode 5 5)
          let op := (BitVec.slice __opcode 15 1)
          let Rm := (BitVec.slice __opcode 16 5)
          let ftype := (BitVec.slice __opcode 22 2)
          (decode_fnmul_float_aarch64_instrs_float_arithmetic_mul_product Rd Rn op Rm ftype)
          (pure false))
      else
        (do
          let w__549 ← (( do
            if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb __opcode 31 22)) == (0b0101111100#10 : (BitVec 10))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                       __opcode 15 12)) == (0x9#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       __opcode 10 10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
            then
              (do
                let w__548 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__548 <b 412) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__549 : Bool)
          then
            (do
              writeReg SEE 412
              let Rd := (BitVec.slice __opcode 0 5)
              let Rn := (BitVec.slice __opcode 5 5)
              let H := (BitVec.slice __opcode 11 1)
              let Rm := (BitVec.slice __opcode 16 4)
              let M := (BitVec.slice __opcode 20 1)
              let L := (BitVec.slice __opcode 21 1)
              let U := (BitVec.slice __opcode 29 1)
              (decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd
                Rd Rn H Rm M L U)
              (pure false))
          else
            (do
              let w__551 ← (( do
                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b010111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                           __opcode 15 12)) == (0x9#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           __opcode 10 10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                then
                  (do
                    let w__550 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__550 <b 413) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__551 : Bool)
              then
                (do
                  writeReg SEE 413
                  let Rd := (BitVec.slice __opcode 0 5)
                  let Rn := (BitVec.slice __opcode 5 5)
                  let H := (BitVec.slice __opcode 11 1)
                  let Rm := (BitVec.slice __opcode 16 4)
                  let M := (BitVec.slice __opcode 20 1)
                  let L := (BitVec.slice __opcode 21 1)
                  let sz := (BitVec.slice __opcode 22 1)
                  let U := (BitVec.slice __opcode 29 1)
                  (decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_sisd
                    Rd Rn H Rm M L sz U)
                  (pure false))
              else
                (do
                  let w__553 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                               __opcode 29 22)) == (0x3C#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                 __opcode 15 12)) == (0x9#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                 __opcode 10 10)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                    then
                      (do
                        let w__552 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__552 <b 414) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__553 : Bool)
                  then
                    (do
                      writeReg SEE 414
                      let Rd := (BitVec.slice __opcode 0 5)
                      let Rn := (BitVec.slice __opcode 5 5)
                      let H := (BitVec.slice __opcode 11 1)
                      let Rm := (BitVec.slice __opcode 16 4)
                      let M := (BitVec.slice __opcode 20 1)
                      let L := (BitVec.slice __opcode 21 1)
                      let U := (BitVec.slice __opcode 29 1)
                      let Q := (BitVec.slice __opcode 30 1)
                      (decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_simd
                        Rd Rn H Rm M L U Q)
                      (pure false))
                  else
                    (do
                      let w__555 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31
                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                   __opcode 29 23)) == (0b0011111#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                     __opcode 15 12)) == (0x9#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                     __opcode 10 10)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                        then
                          (do
                            let w__554 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__554 <b 415) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__555 : Bool)
                      then
                        (do
                          writeReg SEE 415
                          let Rd := (BitVec.slice __opcode 0 5)
                          let Rn := (BitVec.slice __opcode 5 5)
                          let H := (BitVec.slice __opcode 11 1)
                          let Rm := (BitVec.slice __opcode 16 4)
                          let M := (BitVec.slice __opcode 20 1)
                          let L := (BitVec.slice __opcode 21 1)
                          let sz := (BitVec.slice __opcode 22 1)
                          let U := (BitVec.slice __opcode 29 1)
                          let Q := (BitVec.slice __opcode 30 1)
                          (decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_simd
                            Rd Rn H Rm M L sz U Q)
                          (pure false))
                      else
                        (do
                          let w__557 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb __opcode
                                     31 22)) == (0b0111111100#10 : (BitVec 10))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                       __opcode 15 12)) == (0x9#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                       __opcode 10 10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                            then
                              (do
                                let w__556 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__556 <b 416) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__557 : Bool)
                          then
                            (do
                              writeReg SEE 416
                              let Rd := (BitVec.slice __opcode 0 5)
                              let Rn := (BitVec.slice __opcode 5 5)
                              let H := (BitVec.slice __opcode 11 1)
                              let Rm := (BitVec.slice __opcode 16 4)
                              let M := (BitVec.slice __opcode 20 1)
                              let L := (BitVec.slice __opcode 21 1)
                              let U := (BitVec.slice __opcode 29 1)
                              (decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd
                                Rd Rn H Rm M L U)
                              (pure false))
                          else
                            (do
                              let w__559 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                         __opcode 31 23)) == (0b011111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                           __opcode 15 12)) == (0x9#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                           __opcode 10 10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__558 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__558 <b 417) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__559 : Bool)
                              then
                                (do
                                  writeReg SEE 417
                                  let Rd := (BitVec.slice __opcode 0 5)
                                  let Rn := (BitVec.slice __opcode 5 5)
                                  let H := (BitVec.slice __opcode 11 1)
                                  let Rm := (BitVec.slice __opcode 16 4)
                                  let M := (BitVec.slice __opcode 20 1)
                                  let L := (BitVec.slice __opcode 21 1)
                                  let sz := (BitVec.slice __opcode 22 1)
                                  let U := (BitVec.slice __opcode 29 1)
                                  (decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_sisd
                                    Rd Rn H Rm M L sz U)
                                  (pure false))
                              else
                                (do
                                  let w__561 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                               __opcode 29 22)) == (0xBC#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                 __opcode 15 12)) == (0x9#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 __opcode 10 10)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__560 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__560 <b 418) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__561 : Bool)
                                  then
                                    (do
                                      writeReg SEE 418
                                      let Rd := (BitVec.slice __opcode 0 5)
                                      let Rn := (BitVec.slice __opcode 5 5)
                                      let H := (BitVec.slice __opcode 11 1)
                                      let Rm := (BitVec.slice __opcode 16 4)
                                      let M := (BitVec.slice __opcode 20 1)
                                      let L := (BitVec.slice __opcode 21 1)
                                      let U := (BitVec.slice __opcode 29 1)
                                      let Q := (BitVec.slice __opcode 30 1)
                                      (decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_simd
                                        Rd Rn H Rm M L U Q)
                                      (pure false))
                                  else
                                    (do
                                      let w__563 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                   __opcode 29 23)) == (0b1011111#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                     __opcode 15 12)) == (0x9#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                     __opcode 10 10)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__562 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__562 <b 419) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__563 : Bool)
                                      then
                                        (do
                                          writeReg SEE 419
                                          let Rd := (BitVec.slice __opcode 0 5)
                                          let Rn := (BitVec.slice __opcode 5 5)
                                          let H := (BitVec.slice __opcode 11 1)
                                          let Rm := (BitVec.slice __opcode 16 4)
                                          let M := (BitVec.slice __opcode 20 1)
                                          let L := (BitVec.slice __opcode 21 1)
                                          let sz := (BitVec.slice __opcode 22 1)
                                          let U := (BitVec.slice __opcode 29 1)
                                          let Q := (BitVec.slice __opcode 30 1)
                                          (decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_simd
                                            Rd Rn H Rm M L sz U Q)
                                          (pure false))
                                      else
                                        (do
                                          let w__565 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                     __opcode 31 21)) == (0b01011110010#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                     __opcode 15 10)) == (0b000111#6 : (BitVec 6)))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__564 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__564 <b 420) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__565 : Bool)
                                          then
                                            (do
                                              writeReg SEE 420
                                              let Rd := (BitVec.slice __opcode 0 5)
                                              let Rn := (BitVec.slice __opcode 5 5)
                                              let Rm := (BitVec.slice __opcode 16 5)
                                              (decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_sisd
                                                Rd Rn Rm)
                                              (pure false))
                                          else
                                            (do
                                              let w__567 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                         __opcode 31 23)) == (0b010111100#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                           __opcode 15 10)) == (0b110111#6 : (BitVec 6))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__566 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__566 <b 421) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__567 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 421
                                                  let Rd := (BitVec.slice __opcode 0 5)
                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                  let Rm := (BitVec.slice __opcode 16 5)
                                                  let sz := (BitVec.slice __opcode 22 1)
                                                  (decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_extended_sisd
                                                    Rd Rn Rm sz)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__569 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                             __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                               __opcode 29 21)) == (0b001110010#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                               __opcode 15 10)) == (0b000111#6 : (BitVec 6))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__568 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__568 <b 422) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__569 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 422
                                                      let Rd := (BitVec.slice __opcode 0 5)
                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                      let Rm := (BitVec.slice __opcode 16 5)
                                                      let Q := (BitVec.slice __opcode 30 1)
                                                      (decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_simd
                                                        Rd Rn Rm Q)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__571 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                 __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                   __opcode 29 23)) == (0b0011100#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                     __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                     __opcode 15 10)) == (0b110111#6 : (BitVec 6)))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__570 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__570 <b 423) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__571 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 423
                                                          let Rd := (BitVec.slice __opcode 0 5)
                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                          let Rm := (BitVec.slice __opcode 16 5)
                                                          let sz := (BitVec.slice __opcode 22 1)
                                                          let Q := (BitVec.slice __opcode 30 1)
                                                          (decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_extended_simd
                                                            Rd Rn Rm sz Q)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__573 ← (( do
                                                            if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                   __opcode 31 10)) == (0b0101111011111001110110#22 : (BitVec 22))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__572 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__572 <b 424) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__573 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 424
                                                              let Rd := (BitVec.slice __opcode 0 5)
                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                              (decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_fp16_sisd
                                                                Rd Rn)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__575 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                         __opcode 31 23)) == (0b010111101#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                         __opcode 21 10)) == (0x876#12 : (BitVec 12)))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__574 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__574 <b 425) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__575 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 425
                                                                  let Rd :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let sz :=
                                                                    (BitVec.slice __opcode 22 1)
                                                                  (decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_float_sisd
                                                                    Rd Rn sz)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__577 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                             __opcode 31 31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                                             __opcode 29 10)) == (0x3BE76#20 : (BitVec 20)))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__576 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__576 <b 426) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__577 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 426
                                                                      let Rd :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let Q :=
                                                                        (BitVec.slice __opcode 30 1)
                                                                      (decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_fp16_simd
                                                                        Rd Rn Q)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__579 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                   __opcode 29 23)) == (0b0011101#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                   __opcode 21 10)) == (0x876#12 : (BitVec 12))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__578 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__578 <b 427) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__579 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 427
                                                                          let Rd :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let sz :=
                                                                            (BitVec.slice __opcode
                                                                              22 1)
                                                                          let Q :=
                                                                            (BitVec.slice __opcode
                                                                              30 1)
                                                                          (decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_float_simd
                                                                            Rd Rn sz Q)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__581 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 21)) == (0b01011110010#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                     __opcode 15 10)) == (0b001111#6 : (BitVec 6)))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__580 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__580 <b 428) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__581 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 428
                                                                              let Rd :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let Rm :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 5)
                                                                              (decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_sisd
                                                                                Rd Rn Rm)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__583 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         23)) == (0b010111100#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           15 10)) == (0b111111#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__582 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__582 <b 429) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__583 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 429
                                                                                  let Rd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let Rm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 5)
                                                                                  let sz :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 1)
                                                                                  (decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_sisd
                                                                                    Rd Rn Rm sz)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__585 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               29 21)) == (0b001110010#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               15 10)) == (0b001111#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__584 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__584 <b 430) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__585 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 430
                                                                                      let Rd :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          5)
                                                                                      let Rn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let Rm :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 5)
                                                                                      let Q :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          30 1)
                                                                                      (decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_simd
                                                                                        Rd Rn Rm Q)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__587 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   29
                                                                                                   23)) == (0b0011100#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     21
                                                                                                     21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     15
                                                                                                     10)) == (0b111111#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__586 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__586 <b 431) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__587 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 431
                                                                                          let Rd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 5)
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let Rm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 5)
                                                                                          let sz :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 1)
                                                                                          let Q :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              30 1)
                                                                                          (decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_simd
                                                                                            Rd Rn Rm
                                                                                            sz Q)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__589 ← (( do
                                                                                            if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   31
                                                                                                   10)) == (0b0101111011111001111110#22 : (BitVec 22))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__588 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__588 <b 432) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__589 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 432
                                                                                              let Rd :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  5)
                                                                                              let Rn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  5
                                                                                                  5)
                                                                                              (decode_frecpx_advsimd_aarch64_instrs_vector_arithmetic_unary_special_frecpx_fp16
                                                                                                Rd
                                                                                                Rn)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__591 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         23)) == (0b010111101#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         21
                                                                                                         10)) == (0x87E#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__590 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__590 <b 433) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__591 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 433
                                                                                                  let Rd :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      5)
                                                                                                  let Rn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      5
                                                                                                      5)
                                                                                                  let sz :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      22
                                                                                                      1)
                                                                                                  (decode_frecpx_advsimd_aarch64_instrs_vector_arithmetic_unary_special_frecpx
                                                                                                    Rd
                                                                                                    Rn
                                                                                                    sz)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__593 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               29
                                                                                                               23)) == (0b1011100#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               21
                                                                                                               10)) == (0x87A#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__592 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__592 <b 434) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__593 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 434
                                                                                                      let Rd :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          5)
                                                                                                      let Rn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          5
                                                                                                          5)
                                                                                                      let op :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          12
                                                                                                          1)
                                                                                                      let sz :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          22
                                                                                                          1)
                                                                                                      let U :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          29
                                                                                                          1)
                                                                                                      let Q :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          30
                                                                                                          1)
                                                                                                      (decode_frint32x_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64
                                                                                                        Rd
                                                                                                        Rn
                                                                                                        op
                                                                                                        sz
                                                                                                        U
                                                                                                        Q)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__595 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   29
                                                                                                                   23)) == (0b0011100#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   21
                                                                                                                   10)) == (0x87A#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__594 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__594 <b 435) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__595 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 435
                                                                                                          let Rd :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              5)
                                                                                                          let Rn :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              5
                                                                                                              5)
                                                                                                          let op :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              12
                                                                                                              1)
                                                                                                          let sz :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              22
                                                                                                              1)
                                                                                                          let U :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              29
                                                                                                              1)
                                                                                                          let Q :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              30
                                                                                                              1)
                                                                                                          (decode_frint32z_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64
                                                                                                            Rd
                                                                                                            Rn
                                                                                                            op
                                                                                                            sz
                                                                                                            U
                                                                                                            Q)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__597 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       29
                                                                                                                       23)) == (0b1011100#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       21
                                                                                                                       10)) == (0x87E#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__596 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__596 <b 436) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__597 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 436
                                                                                                              let Rd :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  5)
                                                                                                              let Rn :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  5
                                                                                                                  5)
                                                                                                              let op :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  12
                                                                                                                  1)
                                                                                                              let sz :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  22
                                                                                                                  1)
                                                                                                              let U :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  29
                                                                                                                  1)
                                                                                                              let Q :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  30
                                                                                                                  1)
                                                                                                              (decode_frint64x_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64
                                                                                                                Rd
                                                                                                                Rn
                                                                                                                op
                                                                                                                sz
                                                                                                                U
                                                                                                                Q)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__599 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           29
                                                                                                                           23)) == (0b0011100#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           21
                                                                                                                           10)) == (0x87E#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__598 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__598 <b 437) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__599 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 437
                                                                                                                  let Rd :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      5)
                                                                                                                  let Rn :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      5
                                                                                                                      5)
                                                                                                                  let op :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      12
                                                                                                                      1)
                                                                                                                  let sz :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      22
                                                                                                                      1)
                                                                                                                  let U :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      29
                                                                                                                      1)
                                                                                                                  let Q :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      30
                                                                                                                      1)
                                                                                                                  (decode_frint64z_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64
                                                                                                                    Rd
                                                                                                                    Rn
                                                                                                                    op
                                                                                                                    sz
                                                                                                                    U
                                                                                                                    Q)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__601 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             23)) == (0b000111100#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             21
                                                                                                                             10)) == (0xA30#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__600 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__600 <b 438) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__601 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 438
                                                                                                                      let Rd :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          5)
                                                                                                                      let Rn :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          5
                                                                                                                          5)
                                                                                                                      let op :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          15
                                                                                                                          2)
                                                                                                                      let ftype :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          22
                                                                                                                          2)
                                                                                                                      (decode_frint32x_float_aarch64_instrs_float_arithmetic_round_frint_32_64
                                                                                                                        Rd
                                                                                                                        Rn
                                                                                                                        op
                                                                                                                        ftype)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__603 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 23)) == (0b000111100#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 21
                                                                                                                                 10)) == (0xA10#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__602 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__602 <b 439) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__603 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 439
                                                                                                                          let Rd :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              5)
                                                                                                                          let Rn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              5
                                                                                                                              5)
                                                                                                                          let op :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              15
                                                                                                                              2)
                                                                                                                          let ftype :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              22
                                                                                                                              2)
                                                                                                                          (decode_frint32z_float_aarch64_instrs_float_arithmetic_round_frint_32_64
                                                                                                                            Rd
                                                                                                                            Rn
                                                                                                                            op
                                                                                                                            ftype)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__605 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     23)) == (0b000111100#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     21
                                                                                                                                     10)) == (0xA70#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__604 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__604 <b 440) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__605 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 440
                                                                                                                              let Rd :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  5)
                                                                                                                              let Rn :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  5
                                                                                                                                  5)
                                                                                                                              let op :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  15
                                                                                                                                  2)
                                                                                                                              let ftype :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  22
                                                                                                                                  2)
                                                                                                                              (decode_frint64x_float_aarch64_instrs_float_arithmetic_round_frint_32_64
                                                                                                                                Rd
                                                                                                                                Rn
                                                                                                                                op
                                                                                                                                ftype)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__607 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         23)) == (0b000111100#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         21
                                                                                                                                         10)) == (0xA50#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__606 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__606 <b 441) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__607 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 441
                                                                                                                                  let Rd :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      5)
                                                                                                                                  let Rn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      5
                                                                                                                                      5)
                                                                                                                                  let op :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      15
                                                                                                                                      2)
                                                                                                                                  let ftype :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      22
                                                                                                                                      2)
                                                                                                                                  (decode_frint64z_float_aarch64_instrs_float_arithmetic_round_frint_32_64
                                                                                                                                    Rd
                                                                                                                                    Rn
                                                                                                                                    op
                                                                                                                                    ftype)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__609 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             29
                                                                                                                                             10)) == (0xB9E62#20 : (BitVec 20)))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__608 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__608 <b 442) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__609 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 442
                                                                                                                                      let Rd :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          5)
                                                                                                                                      let Rn :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          5
                                                                                                                                          5)
                                                                                                                                      let o1 :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          12
                                                                                                                                          1)
                                                                                                                                      let o2 :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          23
                                                                                                                                          1)
                                                                                                                                      let U :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          29
                                                                                                                                          1)
                                                                                                                                      let Q :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          30
                                                                                                                                          1)
                                                                                                                                      (decode_frinta_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round
                                                                                                                                        Rd
                                                                                                                                        Rn
                                                                                                                                        o1
                                                                                                                                        o2
                                                                                                                                        U
                                                                                                                                        Q)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__611 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   29
                                                                                                                                                   23)) == (0b1011100#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   21
                                                                                                                                                   10)) == (0x862#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__610 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__610 <b 443) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__611 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 443
                                                                                                                                          let Rd :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              0
                                                                                                                                              5)
                                                                                                                                          let Rn :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              5
                                                                                                                                              5)
                                                                                                                                          let o1 :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              12
                                                                                                                                              1)
                                                                                                                                          let sz :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              22
                                                                                                                                              1)
                                                                                                                                          let o2 :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              23
                                                                                                                                              1)
                                                                                                                                          let U :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              29
                                                                                                                                              1)
                                                                                                                                          let Q :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              30
                                                                                                                                              1)
                                                                                                                                          (decode_frinta_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round
                                                                                                                                            Rd
                                                                                                                                            Rn
                                                                                                                                            o1
                                                                                                                                            sz
                                                                                                                                            o2
                                                                                                                                            U
                                                                                                                                            Q)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__613 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     29
                                                                                                                                                     10)) == (0xBBE66#20 : (BitVec 20)))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__612 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__612 <b 444) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__613 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 444
                                                                                                                                              let Rd :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  0
                                                                                                                                                  5)
                                                                                                                                              let Rn :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  5
                                                                                                                                                  5)
                                                                                                                                              let o1 :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  12
                                                                                                                                                  1)
                                                                                                                                              let o2 :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  23
                                                                                                                                                  1)
                                                                                                                                              let U :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  29
                                                                                                                                                  1)
                                                                                                                                              let Q :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  30
                                                                                                                                                  1)
                                                                                                                                              (decode_frinti_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round
                                                                                                                                                Rd
                                                                                                                                                Rn
                                                                                                                                                o1
                                                                                                                                                o2
                                                                                                                                                U
                                                                                                                                                Q)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__615 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         31
                                                                                                                                                         31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           29
                                                                                                                                                           23)) == (0b1011101#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           21
                                                                                                                                                           10)) == (0x866#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__614 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__614 <b 445) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__615 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 445
                                                                                                                                                  let Rd :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      0
                                                                                                                                                      5)
                                                                                                                                                  let Rn :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      5
                                                                                                                                                      5)
                                                                                                                                                  let o1 :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      12
                                                                                                                                                      1)
                                                                                                                                                  let sz :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      22
                                                                                                                                                      1)
                                                                                                                                                  let o2 :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      23
                                                                                                                                                      1)
                                                                                                                                                  let U :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      29
                                                                                                                                                      1)
                                                                                                                                                  let Q :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      30
                                                                                                                                                      1)
                                                                                                                                                  (decode_frinti_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round
                                                                                                                                                    Rd
                                                                                                                                                    Rn
                                                                                                                                                    o1
                                                                                                                                                    sz
                                                                                                                                                    o2
                                                                                                                                                    U
                                                                                                                                                    Q)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__617 ← (( do
                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             31
                                                                                                                                                             31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             29
                                                                                                                                                             10)) == (0x39E66#20 : (BitVec 20)))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__616 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__616 <b 446) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__617 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 446
                                                                                                                                                      let Rd :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          0
                                                                                                                                                          5)
                                                                                                                                                      let Rn :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          5
                                                                                                                                                          5)
                                                                                                                                                      let o1 :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          12
                                                                                                                                                          1)
                                                                                                                                                      let o2 :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          23
                                                                                                                                                          1)
                                                                                                                                                      let U :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          29
                                                                                                                                                          1)
                                                                                                                                                      let Q :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          30
                                                                                                                                                          1)
                                                                                                                                                      (decode_frintm_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round
                                                                                                                                                        Rd
                                                                                                                                                        Rn
                                                                                                                                                        o1
                                                                                                                                                        o2
                                                                                                                                                        U
                                                                                                                                                        Q)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__619 ← (( do
                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 31
                                                                                                                                                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                                   __opcode
                                                                                                                                                                   29
                                                                                                                                                                   23)) == (0b0011100#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                   __opcode
                                                                                                                                                                   21
                                                                                                                                                                   10)) == (0x866#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__618 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__618 <b 447) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false)
                                                                                                                                                        )
                                                                                                                                                        :
                                                                                                                                                        SailM
                                                                                                                                                        Bool
                                                                                                                                                        )
                                                                                                                                                      if (w__619 : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 447
                                                                                                                                                          let Rd :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              0
                                                                                                                                                              5)
                                                                                                                                                          let Rn :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              5
                                                                                                                                                              5)
                                                                                                                                                          let o1 :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              12
                                                                                                                                                              1)
                                                                                                                                                          let sz :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              22
                                                                                                                                                              1)
                                                                                                                                                          let o2 :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              23
                                                                                                                                                              1)
                                                                                                                                                          let U :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              29
                                                                                                                                                              1)
                                                                                                                                                          let Q :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              30
                                                                                                                                                              1)
                                                                                                                                                          (decode_frintm_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round
                                                                                                                                                            Rd
                                                                                                                                                            Rn
                                                                                                                                                            o1
                                                                                                                                                            sz
                                                                                                                                                            o2
                                                                                                                                                            U
                                                                                                                                                            Q)
                                                                                                                                                          (pure false))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          let w__621 ← (( do
                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     31
                                                                                                                                                                     31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     29
                                                                                                                                                                     10)) == (0x39E62#20 : (BitVec 20)))) : Bool) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let w__620 ← (( do
                                                                                                                                                                  readReg SEE
                                                                                                                                                                  )
                                                                                                                                                                  :
                                                                                                                                                                  SailM
                                                                                                                                                                  Int
                                                                                                                                                                  )
                                                                                                                                                                (pure (((w__620 <b 448) : Bool))))
                                                                                                                                                            else
                                                                                                                                                              (pure false)
                                                                                                                                                            )
                                                                                                                                                            :
                                                                                                                                                            SailM
                                                                                                                                                            Bool
                                                                                                                                                            )
                                                                                                                                                          if (w__621 : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 448
                                                                                                                                                              let Rd :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  0
                                                                                                                                                                  5)
                                                                                                                                                              let Rn :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  5
                                                                                                                                                                  5)
                                                                                                                                                              let o1 :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  12
                                                                                                                                                                  1)
                                                                                                                                                              let o2 :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  23
                                                                                                                                                                  1)
                                                                                                                                                              let U :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  29
                                                                                                                                                                  1)
                                                                                                                                                              let Q :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  30
                                                                                                                                                                  1)
                                                                                                                                                              (decode_frintn_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round
                                                                                                                                                                Rd
                                                                                                                                                                Rn
                                                                                                                                                                o1
                                                                                                                                                                o2
                                                                                                                                                                U
                                                                                                                                                                Q)
                                                                                                                                                              (pure false))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              let w__623 ← (( do
                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         31
                                                                                                                                                                         31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           29
                                                                                                                                                                           23)) == (0b0011100#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           21
                                                                                                                                                                           10)) == (0x862#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    let w__622 ← (( do
                                                                                                                                                                      readReg SEE
                                                                                                                                                                      )
                                                                                                                                                                      :
                                                                                                                                                                      SailM
                                                                                                                                                                      Int
                                                                                                                                                                      )
                                                                                                                                                                    (pure (((w__622 <b 449) : Bool))))
                                                                                                                                                                else
                                                                                                                                                                  (pure false)
                                                                                                                                                                )
                                                                                                                                                                :
                                                                                                                                                                SailM
                                                                                                                                                                Bool
                                                                                                                                                                )
                                                                                                                                                              if (w__623 : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 449
                                                                                                                                                                  let Rd :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      0
                                                                                                                                                                      5)
                                                                                                                                                                  let Rn :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      5
                                                                                                                                                                      5)
                                                                                                                                                                  let o1 :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      12
                                                                                                                                                                      1)
                                                                                                                                                                  let sz :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      22
                                                                                                                                                                      1)
                                                                                                                                                                  let o2 :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      23
                                                                                                                                                                      1)
                                                                                                                                                                  let U :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      29
                                                                                                                                                                      1)
                                                                                                                                                                  let Q :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      30
                                                                                                                                                                      1)
                                                                                                                                                                  (decode_frintn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round
                                                                                                                                                                    Rd
                                                                                                                                                                    Rn
                                                                                                                                                                    o1
                                                                                                                                                                    sz
                                                                                                                                                                    o2
                                                                                                                                                                    U
                                                                                                                                                                    Q)
                                                                                                                                                                  (pure false))
                                                                                                                                                              else
                                                                                                                                                                (pure true))))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
