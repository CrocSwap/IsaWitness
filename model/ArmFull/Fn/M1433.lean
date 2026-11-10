import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0932
import ArmFull.Fn.M1016
import ArmFull.Fn.M1150
import ArmFull.Fn.M1151
import ArmFull.Fn.M1183
import ArmFull.Fn.M1293
import ArmFull.Fn.M1294

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
def __DecodeA64_DataProcFPSIMD__seg6 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__475 ← (( do
    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
             __opcode 29 10)) == (0x3AC32#20 : (BitVec 20)))) : Bool) : Bool)
    then
      (do
        let w__474 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__474 <b 375) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__475 : Bool)
  then
    (do
      writeReg SEE 375
      let Rd := (BitVec.slice __opcode 0 5)
      let Rn := (BitVec.slice __opcode 5 5)
      let o1 := (BitVec.slice __opcode 23 1)
      let Q := (BitVec.slice __opcode 30 1)
      (decode_fminnmv_advsimd_aarch64_instrs_vector_reduce_fp16_maxnm_simd Rd Rn o1 Q)
      (pure false))
  else
    (do
      let w__477 ← (( do
        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                   __opcode 29 23)) == (0b1011101#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                   __opcode 21 10)) == (0xC32#12 : (BitVec 12))))) : Bool) : Bool)
        then
          (do
            let w__476 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__476 <b 376) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__477 : Bool)
      then
        (do
          writeReg SEE 376
          let Rd := (BitVec.slice __opcode 0 5)
          let Rn := (BitVec.slice __opcode 5 5)
          let sz := (BitVec.slice __opcode 22 1)
          let o1 := (BitVec.slice __opcode 23 1)
          let Q := (BitVec.slice __opcode 30 1)
          (decode_fminnmv_advsimd_aarch64_instrs_vector_reduce_fp_maxnm_simd Rd Rn sz o1 Q)
          (pure false))
      else
        (do
          let w__479 ← (( do
            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b010111100#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                     __opcode 21 10)) == (0xC3E#12 : (BitVec 12)))) : Bool) : Bool)
            then
              (do
                let w__478 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__478 <b 377) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__479 : Bool)
          then
            (do
              writeReg SEE 377
              let Rd := (BitVec.slice __opcode 0 5)
              let Rn := (BitVec.slice __opcode 5 5)
              let sz := (BitVec.slice __opcode 22 1)
              let o1 := (BitVec.slice __opcode 23 1)
              (decode_fmaxp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_max_sisd Rd Rn sz o1)
              (pure false))
          else
            (do
              let w__481 ← (( do
                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b011111100#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                         __opcode 21 10)) == (0xC3E#12 : (BitVec 12)))) : Bool) : Bool)
                then
                  (do
                    let w__480 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__480 <b 378) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__481 : Bool)
              then
                (do
                  writeReg SEE 378
                  let Rd := (BitVec.slice __opcode 0 5)
                  let Rn := (BitVec.slice __opcode 5 5)
                  let sz := (BitVec.slice __opcode 22 1)
                  let o1 := (BitVec.slice __opcode 23 1)
                  (decode_fmaxp_advsimd_pair_aarch64_instrs_vector_reduce_fp_max_sisd Rd Rn sz o1)
                  (pure false))
              else
                (do
                  let w__483 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b010111101#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                             __opcode 21 10)) == (0xC3E#12 : (BitVec 12)))) : Bool) : Bool)
                    then
                      (do
                        let w__482 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__482 <b 379) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__483 : Bool)
                  then
                    (do
                      writeReg SEE 379
                      let Rd := (BitVec.slice __opcode 0 5)
                      let Rn := (BitVec.slice __opcode 5 5)
                      let sz := (BitVec.slice __opcode 22 1)
                      let o1 := (BitVec.slice __opcode 23 1)
                      (decode_fminp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_max_sisd Rd Rn sz
                        o1)
                      (pure false))
                  else
                    (do
                      let w__485 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31
                                 23)) == (0b011111101#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                 __opcode 21 10)) == (0xC3E#12 : (BitVec 12)))) : Bool) : Bool)
                        then
                          (do
                            let w__484 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__484 <b 380) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__485 : Bool)
                      then
                        (do
                          writeReg SEE 380
                          let Rd := (BitVec.slice __opcode 0 5)
                          let Rn := (BitVec.slice __opcode 5 5)
                          let sz := (BitVec.slice __opcode 22 1)
                          let o1 := (BitVec.slice __opcode 23 1)
                          (decode_fminp_advsimd_pair_aarch64_instrs_vector_reduce_fp_max_sisd Rd Rn
                            sz o1)
                          (pure false))
                      else
                        (do
                          let w__487 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode
                                     31 31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                     __opcode 29 10)) == (0x38C3E#20 : (BitVec 20)))) : Bool) : Bool)
                            then
                              (do
                                let w__486 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__486 <b 381) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__487 : Bool)
                          then
                            (do
                              writeReg SEE 381
                              let Rd := (BitVec.slice __opcode 0 5)
                              let Rn := (BitVec.slice __opcode 5 5)
                              let o1 := (BitVec.slice __opcode 23 1)
                              let Q := (BitVec.slice __opcode 30 1)
                              (decode_fmaxv_advsimd_aarch64_instrs_vector_reduce_fp16_max_simd Rd Rn
                                o1 Q)
                              (pure false))
                          else
                            (do
                              let w__489 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                         __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                           __opcode 29 23)) == (0b1011100#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                           __opcode 21 10)) == (0xC3E#12 : (BitVec 12))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__488 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__488 <b 382) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__489 : Bool)
                              then
                                (do
                                  writeReg SEE 382
                                  let Rd := (BitVec.slice __opcode 0 5)
                                  let Rn := (BitVec.slice __opcode 5 5)
                                  let sz := (BitVec.slice __opcode 22 1)
                                  let o1 := (BitVec.slice __opcode 23 1)
                                  let Q := (BitVec.slice __opcode 30 1)
                                  (decode_fmaxv_advsimd_aarch64_instrs_vector_reduce_fp_max_simd Rd
                                    Rn sz o1 Q)
                                  (pure false))
                              else
                                (do
                                  let w__491 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             __opcode 31 31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                             __opcode 29 10)) == (0x3AC3E#20 : (BitVec 20)))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__490 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__490 <b 383) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__491 : Bool)
                                  then
                                    (do
                                      writeReg SEE 383
                                      let Rd := (BitVec.slice __opcode 0 5)
                                      let Rn := (BitVec.slice __opcode 5 5)
                                      let o1 := (BitVec.slice __opcode 23 1)
                                      let Q := (BitVec.slice __opcode 30 1)
                                      (decode_fminv_advsimd_aarch64_instrs_vector_reduce_fp16_max_simd
                                        Rd Rn o1 Q)
                                      (pure false))
                                  else
                                    (do
                                      let w__493 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                   __opcode 29 23)) == (0b1011101#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                   __opcode 21 10)) == (0xC3E#12 : (BitVec 12))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__492 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__492 <b 384) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__493 : Bool)
                                      then
                                        (do
                                          writeReg SEE 384
                                          let Rd := (BitVec.slice __opcode 0 5)
                                          let Rn := (BitVec.slice __opcode 5 5)
                                          let sz := (BitVec.slice __opcode 22 1)
                                          let o1 := (BitVec.slice __opcode 23 1)
                                          let Q := (BitVec.slice __opcode 30 1)
                                          (decode_fminv_advsimd_aarch64_instrs_vector_reduce_fp_max_simd
                                            Rd Rn sz o1 Q)
                                          (pure false))
                                      else
                                        (do
                                          let w__495 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                     __opcode 31 22)) == (0b0101111100#10 : (BitVec 10))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                       __opcode 15 12)) == (0x1#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 10 10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__494 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__494 <b 385) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__495 : Bool)
                                          then
                                            (do
                                              writeReg SEE 385
                                              let Rd := (BitVec.slice __opcode 0 5)
                                              let Rn := (BitVec.slice __opcode 5 5)
                                              let H := (BitVec.slice __opcode 11 1)
                                              let o2 := (BitVec.slice __opcode 14 1)
                                              let Rm := (BitVec.slice __opcode 16 4)
                                              let M := (BitVec.slice __opcode 20 1)
                                              let L := (BitVec.slice __opcode 21 1)
                                              (decode_fmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_sisd
                                                Rd Rn H o2 Rm M L)
                                              (pure false))
                                          else
                                            (do
                                              let w__497 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                         __opcode 31 23)) == (0b010111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                           __opcode 15 12)) == (0x1#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 10 10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__496 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__496 <b 386) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__497 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 386
                                                  let Rd := (BitVec.slice __opcode 0 5)
                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                  let H := (BitVec.slice __opcode 11 1)
                                                  let o2 := (BitVec.slice __opcode 14 1)
                                                  let Rm := (BitVec.slice __opcode 16 4)
                                                  let M := (BitVec.slice __opcode 20 1)
                                                  let L := (BitVec.slice __opcode 21 1)
                                                  let sz := (BitVec.slice __opcode 22 1)
                                                  (decode_fmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp_sisd
                                                    Rd Rn H o2 Rm M L sz)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__499 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                             __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                               __opcode 29 22)) == (0x3C#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                 __opcode 15 12)) == (0x1#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                 __opcode 10 10)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__498 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__498 <b 387) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__499 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 387
                                                      let Rd := (BitVec.slice __opcode 0 5)
                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                      let H := (BitVec.slice __opcode 11 1)
                                                      let o2 := (BitVec.slice __opcode 14 1)
                                                      let Rm := (BitVec.slice __opcode 16 4)
                                                      let M := (BitVec.slice __opcode 20 1)
                                                      let L := (BitVec.slice __opcode 21 1)
                                                      let Q := (BitVec.slice __opcode 30 1)
                                                      (decode_fmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_simd
                                                        Rd Rn H o2 Rm M L Q)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__501 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                 __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                   __opcode 29 23)) == (0b0011111#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                     __opcode 15 12)) == (0x1#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                     __opcode 10 10)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__500 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__500 <b 388) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__501 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 388
                                                          let Rd := (BitVec.slice __opcode 0 5)
                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                          let H := (BitVec.slice __opcode 11 1)
                                                          let o2 := (BitVec.slice __opcode 14 1)
                                                          let Rm := (BitVec.slice __opcode 16 4)
                                                          let M := (BitVec.slice __opcode 20 1)
                                                          let L := (BitVec.slice __opcode 21 1)
                                                          let sz := (BitVec.slice __opcode 22 1)
                                                          let Q := (BitVec.slice __opcode 30 1)
                                                          (decode_fmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp_simd
                                                            Rd Rn H o2 Rm M L sz Q)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__503 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                     __opcode 31 22)) == (0b0101111100#10 : (BitVec 10))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                       __opcode 15 12)) == (0x5#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 10 10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__502 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__502 <b 389) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__503 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 389
                                                              let Rd := (BitVec.slice __opcode 0 5)
                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                              let H := (BitVec.slice __opcode 11 1)
                                                              let o2 := (BitVec.slice __opcode 14 1)
                                                              let Rm := (BitVec.slice __opcode 16 4)
                                                              let M := (BitVec.slice __opcode 20 1)
                                                              let L := (BitVec.slice __opcode 21 1)
                                                              (decode_fmls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_sisd
                                                                Rd Rn H o2 Rm M L)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__505 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                         __opcode 31 23)) == (0b010111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                           __opcode 15 12)) == (0x5#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 10 10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__504 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__504 <b 390) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__505 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 390
                                                                  let Rd :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let H :=
                                                                    (BitVec.slice __opcode 11 1)
                                                                  let o2 :=
                                                                    (BitVec.slice __opcode 14 1)
                                                                  let Rm :=
                                                                    (BitVec.slice __opcode 16 4)
                                                                  let M :=
                                                                    (BitVec.slice __opcode 20 1)
                                                                  let L :=
                                                                    (BitVec.slice __opcode 21 1)
                                                                  let sz :=
                                                                    (BitVec.slice __opcode 22 1)
                                                                  (decode_fmls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp_sisd
                                                                    Rd Rn H o2 Rm M L sz)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__507 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                             __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                               __opcode 29 22)) == (0x3C#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                 __opcode 15 12)) == (0x5#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 10 10)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__506 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__506 <b 391) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__507 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 391
                                                                      let Rd :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let H :=
                                                                        (BitVec.slice __opcode 11 1)
                                                                      let o2 :=
                                                                        (BitVec.slice __opcode 14 1)
                                                                      let Rm :=
                                                                        (BitVec.slice __opcode 16 4)
                                                                      let M :=
                                                                        (BitVec.slice __opcode 20 1)
                                                                      let L :=
                                                                        (BitVec.slice __opcode 21 1)
                                                                      let Q :=
                                                                        (BitVec.slice __opcode 30 1)
                                                                      (decode_fmls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_simd
                                                                        Rd Rn H o2 Rm M L Q)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__509 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                   __opcode 29 23)) == (0b0011111#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                     __opcode 15 12)) == (0x5#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                     __opcode 10 10)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__508 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__508 <b 392) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__509 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 392
                                                                          let Rd :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let H :=
                                                                            (BitVec.slice __opcode
                                                                              11 1)
                                                                          let o2 :=
                                                                            (BitVec.slice __opcode
                                                                              14 1)
                                                                          let Rm :=
                                                                            (BitVec.slice __opcode
                                                                              16 4)
                                                                          let M :=
                                                                            (BitVec.slice __opcode
                                                                              20 1)
                                                                          let L :=
                                                                            (BitVec.slice __opcode
                                                                              21 1)
                                                                          let sz :=
                                                                            (BitVec.slice __opcode
                                                                              22 1)
                                                                          let Q :=
                                                                            (BitVec.slice __opcode
                                                                              30 1)
                                                                          (decode_fmls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp_simd
                                                                            Rd Rn H o2 Rm M L sz Q)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__511 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                       __opcode 29
                                                                                       21)) == (0b001110010#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                       __opcode 15
                                                                                       10)) == (0b000011#6 : (BitVec 6))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__510 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__510 <b 393) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__511 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 393
                                                                              let Rd :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let Rm :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 5)
                                                                              let a :=
                                                                                (BitVec.slice
                                                                                  __opcode 23 1)
                                                                              let Q :=
                                                                                (BitVec.slice
                                                                                  __opcode 30 1)
                                                                              (decode_fmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_fused
                                                                                Rd Rn Rm a Q)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__513 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           29 23)) == (0b0011100#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             15 10)) == (0b110011#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__512 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__512 <b 394) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__513 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 394
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
                                                                                  let op :=
                                                                                    (BitVec.slice
                                                                                      __opcode 23 1)
                                                                                  let Q :=
                                                                                    (BitVec.slice
                                                                                      __opcode 30 1)
                                                                                  (decode_fmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_fused
                                                                                    Rd Rn Rm sz op Q)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__515 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               29 21)) == (0b001110110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               15 10)) == (0b000011#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__514 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__514 <b 395) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__515 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 395
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
                                                                                      let a :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          23 1)
                                                                                      let Q :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          30 1)
                                                                                      (decode_fmls_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_fused
                                                                                        Rd Rn Rm a Q)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__517 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   29
                                                                                                   23)) == (0b0011101#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     21
                                                                                                     21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     15
                                                                                                     10)) == (0b110011#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__516 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__516 <b 396) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__517 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 396
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
                                                                                          let op :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              23 1)
                                                                                          let Q :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              30 1)
                                                                                          (decode_fmls_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_fused
                                                                                            Rd Rn Rm
                                                                                            sz op Q)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__519 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       29
                                                                                                       22)) == (0x3E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         15
                                                                                                         12)) == (0x0#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         10
                                                                                                         10)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__518 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__518 <b 397) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__519 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 397
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
                                                                                              let H :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  11
                                                                                                  1)
                                                                                              let S :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  14
                                                                                                  1)
                                                                                              let Rm :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  4)
                                                                                              let M :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  20
                                                                                                  1)
                                                                                              let L :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  21
                                                                                                  1)
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
                                                                                              (decode_fmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_mul_norounding_i_lower
                                                                                                Rd
                                                                                                Rn H
                                                                                                S Rm
                                                                                                M L
                                                                                                sz Q)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__521 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           29
                                                                                                           22)) == (0xBE#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             15
                                                                                                             12)) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             10
                                                                                                             10)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__520 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__520 <b 398) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__521 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 398
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
                                                                                                  let H :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      11
                                                                                                      1)
                                                                                                  let S :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      14
                                                                                                      1)
                                                                                                  let Rm :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      4)
                                                                                                  let M :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      20
                                                                                                      1)
                                                                                                  let L :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      21
                                                                                                      1)
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
                                                                                                  (decode_fmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_mul_norounding_i_upper
                                                                                                    Rd
                                                                                                    Rn
                                                                                                    H
                                                                                                    S
                                                                                                    Rm
                                                                                                    M
                                                                                                    L
                                                                                                    sz
                                                                                                    Q)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__523 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               29
                                                                                                               22)) == (0x3E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 15
                                                                                                                 12)) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 10
                                                                                                                 10)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__522 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__522 <b 399) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__523 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 399
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
                                                                                                      let H :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          11
                                                                                                          1)
                                                                                                      let S :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          14
                                                                                                          1)
                                                                                                      let Rm :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          4)
                                                                                                      let M :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          20
                                                                                                          1)
                                                                                                      let L :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          21
                                                                                                          1)
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
                                                                                                      (decode_fmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_mul_norounding_i_lower
                                                                                                        Rd
                                                                                                        Rn
                                                                                                        H
                                                                                                        S
                                                                                                        Rm
                                                                                                        M
                                                                                                        L
                                                                                                        sz
                                                                                                        Q)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__525 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   29
                                                                                                                   22)) == (0xBE#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     15
                                                                                                                     12)) == (0xC#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     10
                                                                                                                     10)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__524 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__524 <b 400) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__525 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 400
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
                                                                                                          let H :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              11
                                                                                                              1)
                                                                                                          let S :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              14
                                                                                                              1)
                                                                                                          let Rm :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              4)
                                                                                                          let M :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              20
                                                                                                              1)
                                                                                                          let L :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              21
                                                                                                              1)
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
                                                                                                          (decode_fmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_mul_norounding_i_upper
                                                                                                            Rd
                                                                                                            Rn
                                                                                                            H
                                                                                                            S
                                                                                                            Rm
                                                                                                            M
                                                                                                            L
                                                                                                            sz
                                                                                                            Q)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__527 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       29
                                                                                                                       21)) == (0b001110001#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       15
                                                                                                                       10)) == (0b111011#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__526 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__526 <b 401) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__527 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 401
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
                                                                                                              let Rm :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  5)
                                                                                                              let sz :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  22
                                                                                                                  1)
                                                                                                              let S :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  23
                                                                                                                  1)
                                                                                                              let Q :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  30
                                                                                                                  1)
                                                                                                              (decode_fmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_mul_norounding_lower
                                                                                                                Rd
                                                                                                                Rn
                                                                                                                Rm
                                                                                                                sz
                                                                                                                S
                                                                                                                Q)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__529 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           29
                                                                                                                           21)) == (0b101110001#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           15
                                                                                                                           10)) == (0b110011#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__528 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__528 <b 402) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__529 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 402
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
                                                                                                                  let Rm :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      5)
                                                                                                                  let sz :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      22
                                                                                                                      1)
                                                                                                                  let S :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      23
                                                                                                                      1)
                                                                                                                  let Q :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      30
                                                                                                                      1)
                                                                                                                  (decode_fmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_mul_norounding_upper
                                                                                                                    Rd
                                                                                                                    Rn
                                                                                                                    Rm
                                                                                                                    sz
                                                                                                                    S
                                                                                                                    Q)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__531 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               29
                                                                                                                               21)) == (0b001110101#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               15
                                                                                                                               10)) == (0b111011#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__530 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__530 <b 403) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__531 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 403
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
                                                                                                                      let Rm :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          16
                                                                                                                          5)
                                                                                                                      let sz :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          22
                                                                                                                          1)
                                                                                                                      let S :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          23
                                                                                                                          1)
                                                                                                                      let Q :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          30
                                                                                                                          1)
                                                                                                                      (decode_fmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_mul_norounding_lower
                                                                                                                        Rd
                                                                                                                        Rn
                                                                                                                        Rm
                                                                                                                        sz
                                                                                                                        S
                                                                                                                        Q)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__533 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   29
                                                                                                                                   21)) == (0b101110101#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   15
                                                                                                                                   10)) == (0b110011#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__532 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__532 <b 404) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__533 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 404
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
                                                                                                                          let Rm :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              5)
                                                                                                                          let sz :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              22
                                                                                                                              1)
                                                                                                                          let S :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              23
                                                                                                                              1)
                                                                                                                          let Q :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              30
                                                                                                                              1)
                                                                                                                          (decode_fmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_mul_norounding_upper
                                                                                                                            Rd
                                                                                                                            Rn
                                                                                                                            Rm
                                                                                                                            sz
                                                                                                                            S
                                                                                                                            Q)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__535 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       29
                                                                                                                                       19)) == (0b00111100000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       15
                                                                                                                                       10)) == (0b111111#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__534 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__534 <b 405) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__535 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 405
                                                                                                                              let Rd :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  5)
                                                                                                                              let h :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  5
                                                                                                                                  1)
                                                                                                                              let g :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  6
                                                                                                                                  1)
                                                                                                                              let f :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  7
                                                                                                                                  1)
                                                                                                                              let e :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  8
                                                                                                                                  1)
                                                                                                                              let d :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  9
                                                                                                                                  1)
                                                                                                                              let c :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
                                                                                                                                  1)
                                                                                                                              let b :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  17
                                                                                                                                  1)
                                                                                                                              let a :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  18
                                                                                                                                  1)
                                                                                                                              let Q :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  30
                                                                                                                                  1)
                                                                                                                              (decode_fmov_advsimd_aarch64_instrs_vector_fp16_movi
                                                                                                                                Rd
                                                                                                                                h
                                                                                                                                g
                                                                                                                                f
                                                                                                                                e
                                                                                                                                d
                                                                                                                                c
                                                                                                                                b
                                                                                                                                a
                                                                                                                                Q)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__537 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           28
                                                                                                                                           19)) == (0b0111100000#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           15
                                                                                                                                           10)) == (0b111101#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__536 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__536 <b 406) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__537 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 406
                                                                                                                                  let Rd :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      5)
                                                                                                                                  let h :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      5
                                                                                                                                      1)
                                                                                                                                  let g :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      6
                                                                                                                                      1)
                                                                                                                                  let f :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      7
                                                                                                                                      1)
                                                                                                                                  let e :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      8
                                                                                                                                      1)
                                                                                                                                  let d :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      9
                                                                                                                                      1)
                                                                                                                                  let cmode :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      12
                                                                                                                                      4)
                                                                                                                                  let c :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      1)
                                                                                                                                  let b :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      17
                                                                                                                                      1)
                                                                                                                                  let a :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      18
                                                                                                                                      1)
                                                                                                                                  let op :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      29
                                                                                                                                      1)
                                                                                                                                  let Q :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      30
                                                                                                                                      1)
                                                                                                                                  (decode_fmov_advsimd_aarch64_instrs_vector_logical
                                                                                                                                    Rd
                                                                                                                                    h
                                                                                                                                    g
                                                                                                                                    f
                                                                                                                                    e
                                                                                                                                    d
                                                                                                                                    cmode
                                                                                                                                    c
                                                                                                                                    b
                                                                                                                                    a
                                                                                                                                    op
                                                                                                                                    Q)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__539 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             24)) == (0x1E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               21
                                                                                                                                               21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               12
                                                                                                                                               5)) == (0x80#8 : (BitVec 8))))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__538 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__538 <b 407) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__539 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 407
                                                                                                                                      let Rd :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          5)
                                                                                                                                      let imm8 :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          13
                                                                                                                                          8)
                                                                                                                                      let ftype :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          22
                                                                                                                                          2)
                                                                                                                                      (decode_fmov_float_imm_aarch64_instrs_float_move_fp_imm
                                                                                                                                        Rd
                                                                                                                                        imm8
                                                                                                                                        ftype)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__541 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   29
                                                                                                                                                   21)) == (0b101110010#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   15
                                                                                                                                                   10)) == (0b000111#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__540 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__540 <b 408) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__541 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 408
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
                                                                                                                                          let Rm :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              16
                                                                                                                                              5)
                                                                                                                                          let Q :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              30
                                                                                                                                              1)
                                                                                                                                          (decode_fmul_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_product
                                                                                                                                            Rd
                                                                                                                                            Rn
                                                                                                                                            Rm
                                                                                                                                            Q)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__543 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       29
                                                                                                                                                       23)) == (0b1011100#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         21
                                                                                                                                                         21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         15
                                                                                                                                                         10)) == (0b110111#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__542 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__542 <b 409) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__543 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 409
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
                                                                                                                                              let Rm :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  16
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
                                                                                                                                              (decode_fmul_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_product
                                                                                                                                                Rd
                                                                                                                                                Rn
                                                                                                                                                Rm
                                                                                                                                                sz
                                                                                                                                                Q)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (pure true)))))))))))))))))))))))))))))))))))


end ArmFull.Functions
