import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M1103
import ArmFull.Fn.M1104
import ArmFull.Fn.M1149

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
def __DecodeA64_DataProcFPSIMD__seg4 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__319 ← (( do
    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb __opcode 30 24)) == (0b0011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
             __opcode 21 10)) == (0x8C0#12 : (BitVec 12)))) : Bool) : Bool)
    then
      (do
        let w__318 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__318 <b 297) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__319 : Bool)
  then
    (do
      writeReg SEE 297
      let Rd := (BitVec.slice __opcode 0 5)
      let Rn := (BitVec.slice __opcode 5 5)
      let opcode := (BitVec.slice __opcode 16 3)
      let rmode := (BitVec.slice __opcode 19 2)
      let ftype := (BitVec.slice __opcode 22 2)
      let sf := (BitVec.slice __opcode 31 1)
      (decode_ucvtf_float_int_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype sf)
      (pure false))
  else
    (do
      let w__321 ← (( do
        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                   __opcode 29 23)) == (0b0011100#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                   __opcode 21 10)) == (0x85E#12 : (BitVec 12))))) : Bool) : Bool)
        then
          (do
            let w__320 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__320 <b 298) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__321 : Bool)
      then
        (do
          writeReg SEE 298
          let Rd := (BitVec.slice __opcode 0 5)
          let Rn := (BitVec.slice __opcode 5 5)
          let sz := (BitVec.slice __opcode 22 1)
          let Q := (BitVec.slice __opcode 30 1)
          (decode_fcvtl_advsimd_aarch64_instrs_vector_arithmetic_unary_float_widen Rd Rn sz Q)
          (pure false))
      else
        (do
          let w__323 ← (( do
            if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb __opcode 31 10)) == (0b0101111001111001101110#22 : (BitVec 22))) : Bool) : Bool)
            then
              (do
                let w__322 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__322 <b 299) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__323 : Bool)
          then
            (do
              writeReg SEE 299
              let Rd := (BitVec.slice __opcode 0 5)
              let Rn := (BitVec.slice __opcode 5 5)
              let o1 := (BitVec.slice __opcode 12 1)
              let o2 := (BitVec.slice __opcode 23 1)
              let U := (BitVec.slice __opcode 29 1)
              (decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
                Rd Rn o1 o2 U)
              (pure false))
          else
            (do
              let w__325 ← (( do
                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b010111100#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                         __opcode 21 10)) == (0x86E#12 : (BitVec 12)))) : Bool) : Bool)
                then
                  (do
                    let w__324 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__324 <b 300) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__325 : Bool)
              then
                (do
                  writeReg SEE 300
                  let Rd := (BitVec.slice __opcode 0 5)
                  let Rn := (BitVec.slice __opcode 5 5)
                  let o1 := (BitVec.slice __opcode 12 1)
                  let sz := (BitVec.slice __opcode 22 1)
                  let o2 := (BitVec.slice __opcode 23 1)
                  let U := (BitVec.slice __opcode 29 1)
                  (decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd
                    Rd Rn o1 sz o2 U)
                  (pure false))
              else
                (do
                  let w__327 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                             __opcode 29 10)) == (0x39E6E#20 : (BitVec 20)))) : Bool) : Bool)
                    then
                      (do
                        let w__326 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__326 <b 301) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__327 : Bool)
                  then
                    (do
                      writeReg SEE 301
                      let Rd := (BitVec.slice __opcode 0 5)
                      let Rn := (BitVec.slice __opcode 5 5)
                      let o1 := (BitVec.slice __opcode 12 1)
                      let o2 := (BitVec.slice __opcode 23 1)
                      let U := (BitVec.slice __opcode 29 1)
                      let Q := (BitVec.slice __opcode 30 1)
                      (decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd
                        Rd Rn o1 o2 U Q)
                      (pure false))
                  else
                    (do
                      let w__329 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31
                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                   __opcode 29 23)) == (0b0011100#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                   __opcode 21 10)) == (0x86E#12 : (BitVec 12))))) : Bool) : Bool)
                        then
                          (do
                            let w__328 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__328 <b 302) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__329 : Bool)
                      then
                        (do
                          writeReg SEE 302
                          let Rd := (BitVec.slice __opcode 0 5)
                          let Rn := (BitVec.slice __opcode 5 5)
                          let o1 := (BitVec.slice __opcode 12 1)
                          let sz := (BitVec.slice __opcode 22 1)
                          let o2 := (BitVec.slice __opcode 23 1)
                          let U := (BitVec.slice __opcode 29 1)
                          let Q := (BitVec.slice __opcode 30 1)
                          (decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd
                            Rd Rn o1 sz o2 U Q)
                          (pure false))
                      else
                        (do
                          let w__331 ← (( do
                            if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb __opcode
                                   31 10)) == (0b0111111001111001101110#22 : (BitVec 22))) : Bool) : Bool)
                            then
                              (do
                                let w__330 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__330 <b 303) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__331 : Bool)
                          then
                            (do
                              writeReg SEE 303
                              let Rd := (BitVec.slice __opcode 0 5)
                              let Rn := (BitVec.slice __opcode 5 5)
                              let o1 := (BitVec.slice __opcode 12 1)
                              let o2 := (BitVec.slice __opcode 23 1)
                              let U := (BitVec.slice __opcode 29 1)
                              (decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
                                Rd Rn o1 o2 U)
                              (pure false))
                          else
                            (do
                              let w__333 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                         __opcode 31 23)) == (0b011111100#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                         __opcode 21 10)) == (0x86E#12 : (BitVec 12)))) : Bool) : Bool)
                                then
                                  (do
                                    let w__332 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__332 <b 304) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__333 : Bool)
                              then
                                (do
                                  writeReg SEE 304
                                  let Rd := (BitVec.slice __opcode 0 5)
                                  let Rn := (BitVec.slice __opcode 5 5)
                                  let o1 := (BitVec.slice __opcode 12 1)
                                  let sz := (BitVec.slice __opcode 22 1)
                                  let o2 := (BitVec.slice __opcode 23 1)
                                  let U := (BitVec.slice __opcode 29 1)
                                  (decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd
                                    Rd Rn o1 sz o2 U)
                                  (pure false))
                              else
                                (do
                                  let w__335 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             __opcode 31 31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                             __opcode 29 10)) == (0xB9E6E#20 : (BitVec 20)))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__334 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__334 <b 305) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__335 : Bool)
                                  then
                                    (do
                                      writeReg SEE 305
                                      let Rd := (BitVec.slice __opcode 0 5)
                                      let Rn := (BitVec.slice __opcode 5 5)
                                      let o1 := (BitVec.slice __opcode 12 1)
                                      let o2 := (BitVec.slice __opcode 23 1)
                                      let U := (BitVec.slice __opcode 29 1)
                                      let Q := (BitVec.slice __opcode 30 1)
                                      (decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd
                                        Rd Rn o1 o2 U Q)
                                      (pure false))
                                  else
                                    (do
                                      let w__337 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                   __opcode 29 23)) == (0b1011100#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                   __opcode 21 10)) == (0x86E#12 : (BitVec 12))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__336 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__336 <b 306) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__337 : Bool)
                                      then
                                        (do
                                          writeReg SEE 306
                                          let Rd := (BitVec.slice __opcode 0 5)
                                          let Rn := (BitVec.slice __opcode 5 5)
                                          let o1 := (BitVec.slice __opcode 12 1)
                                          let sz := (BitVec.slice __opcode 22 1)
                                          let o2 := (BitVec.slice __opcode 23 1)
                                          let U := (BitVec.slice __opcode 29 1)
                                          let Q := (BitVec.slice __opcode 30 1)
                                          (decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd
                                            Rd Rn o1 sz o2 U Q)
                                          (pure false))
                                      else
                                        (do
                                          let w__339 ← (( do
                                            if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                   __opcode 31 10)) == (0b0101111001111001101010#22 : (BitVec 22))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__338 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__338 <b 307) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__339 : Bool)
                                          then
                                            (do
                                              writeReg SEE 307
                                              let Rd := (BitVec.slice __opcode 0 5)
                                              let Rn := (BitVec.slice __opcode 5 5)
                                              let o1 := (BitVec.slice __opcode 12 1)
                                              let o2 := (BitVec.slice __opcode 23 1)
                                              let U := (BitVec.slice __opcode 29 1)
                                              (decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
                                                Rd Rn o1 o2 U)
                                              (pure false))
                                          else
                                            (do
                                              let w__341 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                         __opcode 31 23)) == (0b010111100#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                         __opcode 21 10)) == (0x86A#12 : (BitVec 12)))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__340 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__340 <b 308) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__341 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 308
                                                  let Rd := (BitVec.slice __opcode 0 5)
                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                  let o1 := (BitVec.slice __opcode 12 1)
                                                  let sz := (BitVec.slice __opcode 22 1)
                                                  let o2 := (BitVec.slice __opcode 23 1)
                                                  let U := (BitVec.slice __opcode 29 1)
                                                  (decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd
                                                    Rd Rn o1 sz o2 U)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__343 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                             __opcode 31 31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                             __opcode 29 10)) == (0x39E6A#20 : (BitVec 20)))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__342 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__342 <b 309) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__343 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 309
                                                      let Rd := (BitVec.slice __opcode 0 5)
                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                      let o1 := (BitVec.slice __opcode 12 1)
                                                      let o2 := (BitVec.slice __opcode 23 1)
                                                      let U := (BitVec.slice __opcode 29 1)
                                                      let Q := (BitVec.slice __opcode 30 1)
                                                      (decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd
                                                        Rd Rn o1 o2 U Q)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__345 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                 __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                   __opcode 29 23)) == (0b0011100#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                   __opcode 21 10)) == (0x86A#12 : (BitVec 12))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__344 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__344 <b 310) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__345 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 310
                                                          let Rd := (BitVec.slice __opcode 0 5)
                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                          let o1 := (BitVec.slice __opcode 12 1)
                                                          let sz := (BitVec.slice __opcode 22 1)
                                                          let o2 := (BitVec.slice __opcode 23 1)
                                                          let U := (BitVec.slice __opcode 29 1)
                                                          let Q := (BitVec.slice __opcode 30 1)
                                                          (decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd
                                                            Rd Rn o1 sz o2 U Q)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__347 ← (( do
                                                            if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                   __opcode 31 10)) == (0b0111111001111001101010#22 : (BitVec 22))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__346 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__346 <b 311) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__347 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 311
                                                              let Rd := (BitVec.slice __opcode 0 5)
                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                              let o1 := (BitVec.slice __opcode 12 1)
                                                              let o2 := (BitVec.slice __opcode 23 1)
                                                              let U := (BitVec.slice __opcode 29 1)
                                                              (decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
                                                                Rd Rn o1 o2 U)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__349 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                         __opcode 31 23)) == (0b011111100#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                         __opcode 21 10)) == (0x86A#12 : (BitVec 12)))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__348 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__348 <b 312) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__349 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 312
                                                                  let Rd :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let o1 :=
                                                                    (BitVec.slice __opcode 12 1)
                                                                  let sz :=
                                                                    (BitVec.slice __opcode 22 1)
                                                                  let o2 :=
                                                                    (BitVec.slice __opcode 23 1)
                                                                  let U :=
                                                                    (BitVec.slice __opcode 29 1)
                                                                  (decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd
                                                                    Rd Rn o1 sz o2 U)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__351 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                             __opcode 31 31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                                             __opcode 29 10)) == (0xB9E6A#20 : (BitVec 20)))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__350 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__350 <b 313) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__351 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 313
                                                                      let Rd :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let o1 :=
                                                                        (BitVec.slice __opcode 12 1)
                                                                      let o2 :=
                                                                        (BitVec.slice __opcode 23 1)
                                                                      let U :=
                                                                        (BitVec.slice __opcode 29 1)
                                                                      let Q :=
                                                                        (BitVec.slice __opcode 30 1)
                                                                      (decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd
                                                                        Rd Rn o1 o2 U Q)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__353 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                   __opcode 29 23)) == (0b1011100#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                   __opcode 21 10)) == (0x86A#12 : (BitVec 12))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__352 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__352 <b 314) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__353 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 314
                                                                          let Rd :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let o1 :=
                                                                            (BitVec.slice __opcode
                                                                              12 1)
                                                                          let sz :=
                                                                            (BitVec.slice __opcode
                                                                              22 1)
                                                                          let o2 :=
                                                                            (BitVec.slice __opcode
                                                                              23 1)
                                                                          let U :=
                                                                            (BitVec.slice __opcode
                                                                              29 1)
                                                                          let Q :=
                                                                            (BitVec.slice __opcode
                                                                              30 1)
                                                                          (decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd
                                                                            Rd Rn o1 sz o2 U Q)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__355 ← (( do
                                                                            if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                                   __opcode 31 10)) == (0b0101111011111001101010#22 : (BitVec 22))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__354 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__354 <b 315) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__355 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 315
                                                                              let Rd :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let o1 :=
                                                                                (BitVec.slice
                                                                                  __opcode 12 1)
                                                                              let o2 :=
                                                                                (BitVec.slice
                                                                                  __opcode 23 1)
                                                                              let U :=
                                                                                (BitVec.slice
                                                                                  __opcode 29 1)
                                                                              (decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
                                                                                Rd Rn o1 o2 U)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__357 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         23)) == (0b010111101#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                         __opcode 21
                                                                                         10)) == (0x86A#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__356 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__356 <b 316) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__357 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 316
                                                                                  let Rd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let o1 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 12 1)
                                                                                  let sz :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 1)
                                                                                  let o2 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 23 1)
                                                                                  let U :=
                                                                                    (BitVec.slice
                                                                                      __opcode 29 1)
                                                                                  (decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd
                                                                                    Rd Rn o1 sz o2 U)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__359 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             29 10)) == (0x3BE6A#20 : (BitVec 20)))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__358 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__358 <b 317) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__359 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 317
                                                                                      let Rd :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          5)
                                                                                      let Rn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let o1 :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          12 1)
                                                                                      let o2 :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          23 1)
                                                                                      let U :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          29 1)
                                                                                      let Q :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          30 1)
                                                                                      (decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd
                                                                                        Rd Rn o1 o2
                                                                                        U Q)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__361 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   29
                                                                                                   23)) == (0b0011101#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   21
                                                                                                   10)) == (0x86A#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__360 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__360 <b 318) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__361 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 318
                                                                                          let Rd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 5)
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let o1 :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              12 1)
                                                                                          let sz :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 1)
                                                                                          let o2 :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              23 1)
                                                                                          let U :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              29 1)
                                                                                          let Q :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              30 1)
                                                                                          (decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd
                                                                                            Rd Rn o1
                                                                                            sz o2 U
                                                                                            Q)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__363 ← (( do
                                                                                            if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   31
                                                                                                   10)) == (0b0111111011111001101010#22 : (BitVec 22))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__362 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__362 <b 319) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__363 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 319
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
                                                                                              (decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
                                                                                                Rd
                                                                                                Rn
                                                                                                o1
                                                                                                o2 U)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__365 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         23)) == (0b011111101#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         21
                                                                                                         10)) == (0x86A#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__364 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__364 <b 320) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__365 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 320
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
                                                                                                  (decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd
                                                                                                    Rd
                                                                                                    Rn
                                                                                                    o1
                                                                                                    sz
                                                                                                    o2
                                                                                                    U)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__367 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             29
                                                                                                             10)) == (0xBBE6A#20 : (BitVec 20)))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__366 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__366 <b 321) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__367 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 321
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
                                                                                                      (decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd
                                                                                                        Rd
                                                                                                        Rn
                                                                                                        o1
                                                                                                        o2
                                                                                                        U
                                                                                                        Q)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__369 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   29
                                                                                                                   23)) == (0b1011101#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   21
                                                                                                                   10)) == (0x86A#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__368 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__368 <b 322) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__369 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 322
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
                                                                                                          (decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd
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
                                                                                                          let w__371 ← (( do
                                                                                                            if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   31
                                                                                                                   10)) == (0b0101111011111001101110#22 : (BitVec 22))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__370 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__370 <b 323) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__371 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 323
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
                                                                                                              (decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
                                                                                                                Rd
                                                                                                                Rn
                                                                                                                o1
                                                                                                                o2
                                                                                                                U)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__373 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         23)) == (0b010111101#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         21
                                                                                                                         10)) == (0x86E#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__372 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__372 <b 324) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__373 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 324
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
                                                                                                                  (decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd
                                                                                                                    Rd
                                                                                                                    Rn
                                                                                                                    o1
                                                                                                                    sz
                                                                                                                    o2
                                                                                                                    U)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__375 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             29
                                                                                                                             10)) == (0x3BE6E#20 : (BitVec 20)))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__374 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__374 <b 325) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__375 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 325
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
                                                                                                                      (decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd
                                                                                                                        Rd
                                                                                                                        Rn
                                                                                                                        o1
                                                                                                                        o2
                                                                                                                        U
                                                                                                                        Q)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__377 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   29
                                                                                                                                   23)) == (0b0011101#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   21
                                                                                                                                   10)) == (0x86E#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__376 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__376 <b 326) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__377 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 326
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
                                                                                                                          (decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd
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
                                                                                                                          let w__379 ← (( do
                                                                                                                            if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   31
                                                                                                                                   10)) == (0b0111111011111001101110#22 : (BitVec 22))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__378 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__378 <b 327) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__379 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 327
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
                                                                                                                              (decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
                                                                                                                                Rd
                                                                                                                                Rn
                                                                                                                                o1
                                                                                                                                o2
                                                                                                                                U)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__381 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         23)) == (0b011111101#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         21
                                                                                                                                         10)) == (0x86E#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__380 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__380 <b 328) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__381 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 328
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
                                                                                                                                  (decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd
                                                                                                                                    Rd
                                                                                                                                    Rn
                                                                                                                                    o1
                                                                                                                                    sz
                                                                                                                                    o2
                                                                                                                                    U)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__383 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             29
                                                                                                                                             10)) == (0xBBE6E#20 : (BitVec 20)))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__382 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__382 <b 329) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__383 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 329
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
                                                                                                                                      (decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd
                                                                                                                                        Rd
                                                                                                                                        Rn
                                                                                                                                        o1
                                                                                                                                        o2
                                                                                                                                        U
                                                                                                                                        Q)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__385 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   29
                                                                                                                                                   23)) == (0b1011101#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   21
                                                                                                                                                   10)) == (0x86E#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__384 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__384 <b 330) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__385 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 330
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
                                                                                                                                          (decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd
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
                                                                                                                                          let w__387 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       29
                                                                                                                                                       23)) == (0b0011100#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       21
                                                                                                                                                       10)) == (0x85A#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__386 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__386 <b 331) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__387 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 331
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
                                                                                                                                              let Q :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  30
                                                                                                                                                  1)
                                                                                                                                              (decode_fcvtn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_narrow
                                                                                                                                                Rd
                                                                                                                                                Rn
                                                                                                                                                sz
                                                                                                                                                Q)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__389 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         31
                                                                                                                                                         23)) == (0b011111100#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         21
                                                                                                                                                         10)) == (0x85A#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__388 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__388 <b 332) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__389 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 332
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
                                                                                                                                                  (decode_fcvtxn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_xtn_sisd
                                                                                                                                                    Rd
                                                                                                                                                    Rn
                                                                                                                                                    sz)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__391 ← (( do
                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             31
                                                                                                                                                             31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                               __opcode
                                                                                                                                                               29
                                                                                                                                                               23)) == (0b1011100#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                               __opcode
                                                                                                                                                               21
                                                                                                                                                               10)) == (0x85A#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__390 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__390 <b 333) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__391 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 333
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
                                                                                                                                                      let Q :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          30
                                                                                                                                                          1)
                                                                                                                                                      (decode_fcvtxn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_xtn_simd
                                                                                                                                                        Rd
                                                                                                                                                        Rn
                                                                                                                                                        sz
                                                                                                                                                        Q)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__393 ← (( do
                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 30
                                                                                                                                                                 24)) == (0b0011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 21
                                                                                                                                                                 16)) == (0b011000#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__392 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__392 <b 334) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false)
                                                                                                                                                        )
                                                                                                                                                        :
                                                                                                                                                        SailM
                                                                                                                                                        Bool
                                                                                                                                                        )
                                                                                                                                                      if (w__393 : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 334
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
                                                                                                                                                          let scale :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              10
                                                                                                                                                              6)
                                                                                                                                                          let opcode :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              16
                                                                                                                                                              3)
                                                                                                                                                          let rmode :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              19
                                                                                                                                                              2)
                                                                                                                                                          let ftype :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              22
                                                                                                                                                              2)
                                                                                                                                                          let sf :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              31
                                                                                                                                                              1)
                                                                                                                                                          (decode_fcvtzs_float_fix_aarch64_instrs_float_convert_fix
                                                                                                                                                            Rd
                                                                                                                                                            Rn
                                                                                                                                                            scale
                                                                                                                                                            opcode
                                                                                                                                                            rmode
                                                                                                                                                            ftype
                                                                                                                                                            sf)
                                                                                                                                                          (pure false))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          let w__395 ← (( do
                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     30
                                                                                                                                                                     24)) == (0b0011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     21
                                                                                                                                                                     16)) == (0b011001#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let w__394 ← (( do
                                                                                                                                                                  readReg SEE
                                                                                                                                                                  )
                                                                                                                                                                  :
                                                                                                                                                                  SailM
                                                                                                                                                                  Int
                                                                                                                                                                  )
                                                                                                                                                                (pure (((w__394 <b 335) : Bool))))
                                                                                                                                                            else
                                                                                                                                                              (pure false)
                                                                                                                                                            )
                                                                                                                                                            :
                                                                                                                                                            SailM
                                                                                                                                                            Bool
                                                                                                                                                            )
                                                                                                                                                          if (w__395 : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 335
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
                                                                                                                                                              let scale :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  10
                                                                                                                                                                  6)
                                                                                                                                                              let opcode :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  16
                                                                                                                                                                  3)
                                                                                                                                                              let rmode :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  19
                                                                                                                                                                  2)
                                                                                                                                                              let ftype :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  22
                                                                                                                                                                  2)
                                                                                                                                                              let sf :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  31
                                                                                                                                                                  1)
                                                                                                                                                              (decode_fcvtzu_float_fix_aarch64_instrs_float_convert_fix
                                                                                                                                                                Rd
                                                                                                                                                                Rn
                                                                                                                                                                scale
                                                                                                                                                                opcode
                                                                                                                                                                rmode
                                                                                                                                                                ftype
                                                                                                                                                                sf)
                                                                                                                                                              (pure false))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              let w__397 ← (( do
                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         30
                                                                                                                                                                         24)) == (0b0011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         21
                                                                                                                                                                         16)) == (0b000010#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    let w__396 ← (( do
                                                                                                                                                                      readReg SEE
                                                                                                                                                                      )
                                                                                                                                                                      :
                                                                                                                                                                      SailM
                                                                                                                                                                      Int
                                                                                                                                                                      )
                                                                                                                                                                    (pure (((w__396 <b 336) : Bool))))
                                                                                                                                                                else
                                                                                                                                                                  (pure false)
                                                                                                                                                                )
                                                                                                                                                                :
                                                                                                                                                                SailM
                                                                                                                                                                Bool
                                                                                                                                                                )
                                                                                                                                                              if (w__397 : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 336
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
                                                                                                                                                                  let scale :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      10
                                                                                                                                                                      6)
                                                                                                                                                                  let opcode :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      16
                                                                                                                                                                      3)
                                                                                                                                                                  let rmode :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      19
                                                                                                                                                                      2)
                                                                                                                                                                  let ftype :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      22
                                                                                                                                                                      2)
                                                                                                                                                                  let sf :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      31
                                                                                                                                                                      1)
                                                                                                                                                                  (decode_scvtf_float_fix_aarch64_instrs_float_convert_fix
                                                                                                                                                                    Rd
                                                                                                                                                                    Rn
                                                                                                                                                                    scale
                                                                                                                                                                    opcode
                                                                                                                                                                    rmode
                                                                                                                                                                    ftype
                                                                                                                                                                    sf)
                                                                                                                                                                  (pure false))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  let w__399 ← (( do
                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                                             __opcode
                                                                                                                                                                             30
                                                                                                                                                                             24)) == (0b0011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                             __opcode
                                                                                                                                                                             21
                                                                                                                                                                             16)) == (0b000011#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                                    then
                                                                                                                                                                      (do
                                                                                                                                                                        let w__398 ← (( do
                                                                                                                                                                          readReg SEE
                                                                                                                                                                          )
                                                                                                                                                                          :
                                                                                                                                                                          SailM
                                                                                                                                                                          Int
                                                                                                                                                                          )
                                                                                                                                                                        (pure (((w__398 <b 337) : Bool))))
                                                                                                                                                                    else
                                                                                                                                                                      (pure false)
                                                                                                                                                                    )
                                                                                                                                                                    :
                                                                                                                                                                    SailM
                                                                                                                                                                    Bool
                                                                                                                                                                    )
                                                                                                                                                                  if (w__399 : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      writeReg SEE 337
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
                                                                                                                                                                      let scale :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          10
                                                                                                                                                                          6)
                                                                                                                                                                      let opcode :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          16
                                                                                                                                                                          3)
                                                                                                                                                                      let rmode :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          19
                                                                                                                                                                          2)
                                                                                                                                                                      let ftype :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          22
                                                                                                                                                                          2)
                                                                                                                                                                      let sf :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          31
                                                                                                                                                                          1)
                                                                                                                                                                      (decode_ucvtf_float_fix_aarch64_instrs_float_convert_fix
                                                                                                                                                                        Rd
                                                                                                                                                                        Rn
                                                                                                                                                                        scale
                                                                                                                                                                        opcode
                                                                                                                                                                        rmode
                                                                                                                                                                        ftype
                                                                                                                                                                        sf)
                                                                                                                                                                      (pure false))
                                                                                                                                                                  else
                                                                                                                                                                    (pure true)))))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
