import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0932
import ArmFull.Fn.M1099
import ArmFull.Fn.M1100
import ArmFull.Fn.M1101
import ArmFull.Fn.M1102
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
def __DecodeA64_DataProcFPSIMD__seg3 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__233 ← (( do
    if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb __opcode 31 10)) == (0b0111111011111000110010#22 : (BitVec 22))) : Bool) : Bool)
    then
      (do
        let w__232 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__232 <b 254) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__233 : Bool)
  then
    (do
      writeReg SEE 254
      let Rd := (BitVec.slice __opcode 0 5)
      let Rn := (BitVec.slice __opcode 5 5)
      let op := (BitVec.slice __opcode 12 1)
      let U := (BitVec.slice __opcode 29 1)
      (decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd Rd Rn op
        U)
      (pure false))
  else
    (do
      let w__235 ← (( do
        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b011111101#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                 __opcode 21 10)) == (0x832#12 : (BitVec 12)))) : Bool) : Bool)
        then
          (do
            let w__234 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__234 <b 255) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__235 : Bool)
      then
        (do
          writeReg SEE 255
          let Rd := (BitVec.slice __opcode 0 5)
          let Rn := (BitVec.slice __opcode 5 5)
          let op := (BitVec.slice __opcode 12 1)
          let sz := (BitVec.slice __opcode 22 1)
          let U := (BitVec.slice __opcode 29 1)
          (decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd Rd
            Rn op sz U)
          (pure false))
      else
        (do
          let w__237 ← (( do
            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                     __opcode 29 10)) == (0xBBE32#20 : (BitVec 20)))) : Bool) : Bool)
            then
              (do
                let w__236 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__236 <b 256) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__237 : Bool)
          then
            (do
              writeReg SEE 256
              let Rd := (BitVec.slice __opcode 0 5)
              let Rn := (BitVec.slice __opcode 5 5)
              let op := (BitVec.slice __opcode 12 1)
              let U := (BitVec.slice __opcode 29 1)
              let Q := (BitVec.slice __opcode 30 1)
              (decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd
                Rd Rn op U Q)
              (pure false))
          else
            (do
              let w__239 ← (( do
                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                           __opcode 29 23)) == (0b1011101#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                           __opcode 21 10)) == (0x832#12 : (BitVec 12))))) : Bool) : Bool)
                then
                  (do
                    let w__238 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__238 <b 257) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__239 : Bool)
              then
                (do
                  writeReg SEE 257
                  let Rd := (BitVec.slice __opcode 0 5)
                  let Rn := (BitVec.slice __opcode 5 5)
                  let op := (BitVec.slice __opcode 12 1)
                  let sz := (BitVec.slice __opcode 22 1)
                  let U := (BitVec.slice __opcode 29 1)
                  let Q := (BitVec.slice __opcode 30 1)
                  (decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd
                    Rd Rn op sz U Q)
                  (pure false))
              else
                (do
                  let w__241 ← (( do
                    if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb __opcode 31 10)) == (0b0101111011111000110010#22 : (BitVec 22))) : Bool) : Bool)
                    then
                      (do
                        let w__240 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__240 <b 258) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__241 : Bool)
                  then
                    (do
                      writeReg SEE 258
                      let Rd := (BitVec.slice __opcode 0 5)
                      let Rn := (BitVec.slice __opcode 5 5)
                      let op := (BitVec.slice __opcode 12 1)
                      let U := (BitVec.slice __opcode 29 1)
                      (decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd
                        Rd Rn op U)
                      (pure false))
                  else
                    (do
                      let w__243 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31
                                 23)) == (0b010111101#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                 __opcode 21 10)) == (0x832#12 : (BitVec 12)))) : Bool) : Bool)
                        then
                          (do
                            let w__242 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__242 <b 259) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__243 : Bool)
                      then
                        (do
                          writeReg SEE 259
                          let Rd := (BitVec.slice __opcode 0 5)
                          let Rn := (BitVec.slice __opcode 5 5)
                          let op := (BitVec.slice __opcode 12 1)
                          let sz := (BitVec.slice __opcode 22 1)
                          let U := (BitVec.slice __opcode 29 1)
                          (decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd
                            Rd Rn op sz U)
                          (pure false))
                      else
                        (do
                          let w__245 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode
                                     31 31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                     __opcode 29 10)) == (0x3BE32#20 : (BitVec 20)))) : Bool) : Bool)
                            then
                              (do
                                let w__244 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__244 <b 260) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__245 : Bool)
                          then
                            (do
                              writeReg SEE 260
                              let Rd := (BitVec.slice __opcode 0 5)
                              let Rn := (BitVec.slice __opcode 5 5)
                              let op := (BitVec.slice __opcode 12 1)
                              let U := (BitVec.slice __opcode 29 1)
                              let Q := (BitVec.slice __opcode 30 1)
                              (decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd
                                Rd Rn op U Q)
                              (pure false))
                          else
                            (do
                              let w__247 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                         __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                           __opcode 29 23)) == (0b0011101#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                           __opcode 21 10)) == (0x832#12 : (BitVec 12))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__246 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__246 <b 261) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__247 : Bool)
                              then
                                (do
                                  writeReg SEE 261
                                  let Rd := (BitVec.slice __opcode 0 5)
                                  let Rn := (BitVec.slice __opcode 5 5)
                                  let op := (BitVec.slice __opcode 12 1)
                                  let sz := (BitVec.slice __opcode 22 1)
                                  let U := (BitVec.slice __opcode 29 1)
                                  let Q := (BitVec.slice __opcode 30 1)
                                  (decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd
                                    Rd Rn op sz U Q)
                                  (pure false))
                              else
                                (do
                                  let w__249 ← (( do
                                    if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                           __opcode 31 10)) == (0b0111111011111000110110#22 : (BitVec 22))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__248 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__248 <b 262) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__249 : Bool)
                                  then
                                    (do
                                      writeReg SEE 262
                                      let Rd := (BitVec.slice __opcode 0 5)
                                      let Rn := (BitVec.slice __opcode 5 5)
                                      let op := (BitVec.slice __opcode 12 1)
                                      let U := (BitVec.slice __opcode 29 1)
                                      (decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd
                                        Rd Rn op U)
                                      (pure false))
                                  else
                                    (do
                                      let w__251 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                 __opcode 31 23)) == (0b011111101#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                 __opcode 21 10)) == (0x836#12 : (BitVec 12)))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__250 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__250 <b 263) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__251 : Bool)
                                      then
                                        (do
                                          writeReg SEE 263
                                          let Rd := (BitVec.slice __opcode 0 5)
                                          let Rn := (BitVec.slice __opcode 5 5)
                                          let op := (BitVec.slice __opcode 12 1)
                                          let sz := (BitVec.slice __opcode 22 1)
                                          let U := (BitVec.slice __opcode 29 1)
                                          (decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd
                                            Rd Rn op sz U)
                                          (pure false))
                                      else
                                        (do
                                          let w__253 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                     __opcode 31 31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                     __opcode 29 10)) == (0xBBE36#20 : (BitVec 20)))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__252 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__252 <b 264) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__253 : Bool)
                                          then
                                            (do
                                              writeReg SEE 264
                                              let Rd := (BitVec.slice __opcode 0 5)
                                              let Rn := (BitVec.slice __opcode 5 5)
                                              let op := (BitVec.slice __opcode 12 1)
                                              let U := (BitVec.slice __opcode 29 1)
                                              let Q := (BitVec.slice __opcode 30 1)
                                              (decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd
                                                Rd Rn op U Q)
                                              (pure false))
                                          else
                                            (do
                                              let w__255 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                         __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                           __opcode 29 23)) == (0b1011101#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                           __opcode 21 10)) == (0x836#12 : (BitVec 12))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__254 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__254 <b 265) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__255 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 265
                                                  let Rd := (BitVec.slice __opcode 0 5)
                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                  let op := (BitVec.slice __opcode 12 1)
                                                  let sz := (BitVec.slice __opcode 22 1)
                                                  let U := (BitVec.slice __opcode 29 1)
                                                  let Q := (BitVec.slice __opcode 30 1)
                                                  (decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd
                                                    Rd Rn op sz U Q)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__257 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                             __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                               __opcode 29 24)) == (0b101110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                 __opcode 21 21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                   __opcode 15 13)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 10 10)) == (1#1 : (BitVec 1))))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__256 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__256 <b 266) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__257 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 266
                                                      let Rd := (BitVec.slice __opcode 0 5)
                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                      let rot := (BitVec.slice __opcode 11 2)
                                                      let Rm := (BitVec.slice __opcode 16 5)
                                                      let size := (BitVec.slice __opcode 22 2)
                                                      let Q := (BitVec.slice __opcode 30 1)
                                                      (decode_fcmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_complex
                                                        Rd Rn rot Rm size Q)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__259 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                 __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                   __opcode 29 24)) == (0b101111#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                     __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 12 12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 10 10)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__258 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__258 <b 267) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__259 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 267
                                                          let Rd := (BitVec.slice __opcode 0 5)
                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                          let H := (BitVec.slice __opcode 11 1)
                                                          let rot := (BitVec.slice __opcode 13 2)
                                                          let Rm := (BitVec.slice __opcode 16 4)
                                                          let M := (BitVec.slice __opcode 20 1)
                                                          let L := (BitVec.slice __opcode 21 1)
                                                          let size := (BitVec.slice __opcode 22 2)
                                                          let Q := (BitVec.slice __opcode 30 1)
                                                          (decode_fcmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_complex
                                                            Rd Rn H rot Rm M L size Q)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__261 ← (( do
                                                            if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                   __opcode 31 10)) == (0b0101111011111000111010#22 : (BitVec 22))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__260 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__260 <b 268) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__261 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 268
                                                              let Rd := (BitVec.slice __opcode 0 5)
                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                              (decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_sisd
                                                                Rd Rn)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__263 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                         __opcode 31 23)) == (0b010111101#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                         __opcode 21 10)) == (0x83A#12 : (BitVec 12)))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__262 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__262 <b 269) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__263 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 269
                                                                  let Rd :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let sz :=
                                                                    (BitVec.slice __opcode 22 1)
                                                                  (decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_lessthan_sisd
                                                                    Rd Rn sz)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__265 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                             __opcode 31 31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                                             __opcode 29 10)) == (0x3BE3A#20 : (BitVec 20)))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__264 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__264 <b 270) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__265 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 270
                                                                      let Rd :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let Q :=
                                                                        (BitVec.slice __opcode 30 1)
                                                                      (decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_simd
                                                                        Rd Rn Q)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__267 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                   __opcode 29 23)) == (0b0011101#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                   __opcode 21 10)) == (0x83A#12 : (BitVec 12))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__266 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__266 <b 271) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__267 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 271
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
                                                                          (decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_lessthan_simd
                                                                            Rd Rn sz Q)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__269 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 24)) == (0x1E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 21
                                                                                       21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                         __opcode 15
                                                                                         10)) == (0b001000#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           4 4)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           2 0)) == (0b000#3 : (BitVec 3))))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__268 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__268 <b 272) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__269 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 272
                                                                              let opc :=
                                                                                (BitVec.slice
                                                                                  __opcode 3 2)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let Rm :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 5)
                                                                              let ftype :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 2)
                                                                              (decode_fcmp_float_aarch64_instrs_float_compare_uncond
                                                                                opc Rn Rm ftype)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__271 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         24)) == (0x1E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             15 10)) == (0b001000#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               4 4)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               2 0)) == (0b000#3 : (BitVec 3))))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__270 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__270 <b 273) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__271 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 273
                                                                                  let opc :=
                                                                                    (BitVec.slice
                                                                                      __opcode 3 2)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let Rm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 5)
                                                                                  let ftype :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 2)
                                                                                  (decode_fcmpe_float_aarch64_instrs_float_compare_uncond
                                                                                    opc Rn Rm ftype)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__273 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 24)) == (0x1E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               11 10)) == (0b11#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__272 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__272 <b 274) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__273 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 274
                                                                                      let Rd :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          5)
                                                                                      let Rn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let cond :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          12 4)
                                                                                      let Rm :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 5)
                                                                                      let ftype :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 2)
                                                                                      (decode_fcsel_float_aarch64_instrs_float_move_fp_select
                                                                                        Rd Rn cond
                                                                                        Rm ftype)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__275 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 24)) == (0x1E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   21
                                                                                                   17)) == (0b10001#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   14
                                                                                                   10)) == (0b10000#5 : (BitVec 5))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__274 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__274 <b 275) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__275 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 275
                                                                                          let Rd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 5)
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let opc :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              15 2)
                                                                                          let ftype :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 2)
                                                                                          (decode_fcvt_float_aarch64_instrs_float_convert_fp
                                                                                            Rd Rn
                                                                                            opc
                                                                                            ftype)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__277 ← (( do
                                                                                            if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   31
                                                                                                   10)) == (0b0101111001111001110010#22 : (BitVec 22))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__276 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__276 <b 276) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__277 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 276
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
                                                                                              let U :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  29
                                                                                                  1)
                                                                                              (decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd
                                                                                                Rd
                                                                                                Rn U)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__279 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         23)) == (0b010111100#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         21
                                                                                                         10)) == (0x872#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__278 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__278 <b 277) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__279 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 277
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
                                                                                                  let U :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      29
                                                                                                      1)
                                                                                                  (decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_sisd
                                                                                                    Rd
                                                                                                    Rn
                                                                                                    sz
                                                                                                    U)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__281 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             29
                                                                                                             10)) == (0x39E72#20 : (BitVec 20)))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__280 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__280 <b 278) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__281 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 278
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
                                                                                                      (decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_simd
                                                                                                        Rd
                                                                                                        Rn
                                                                                                        U
                                                                                                        Q)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__283 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   29
                                                                                                                   23)) == (0b0011100#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   21
                                                                                                                   10)) == (0x872#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__282 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__282 <b 279) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__283 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 279
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
                                                                                                          (decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_simd
                                                                                                            Rd
                                                                                                            Rn
                                                                                                            sz
                                                                                                            U
                                                                                                            Q)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__285 ← (( do
                                                                                                            if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   31
                                                                                                                   10)) == (0b0111111001111001110010#22 : (BitVec 22))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__284 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__284 <b 280) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__285 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 280
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
                                                                                                              let U :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  29
                                                                                                                  1)
                                                                                                              (decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd
                                                                                                                Rd
                                                                                                                Rn
                                                                                                                U)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__287 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         23)) == (0b011111100#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         21
                                                                                                                         10)) == (0x872#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__286 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__286 <b 281) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__287 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 281
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
                                                                                                                  let U :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      29
                                                                                                                      1)
                                                                                                                  (decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_sisd
                                                                                                                    Rd
                                                                                                                    Rn
                                                                                                                    sz
                                                                                                                    U)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__289 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             29
                                                                                                                             10)) == (0xB9E72#20 : (BitVec 20)))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__288 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__288 <b 282) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__289 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 282
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
                                                                                                                      (decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_simd
                                                                                                                        Rd
                                                                                                                        Rn
                                                                                                                        U
                                                                                                                        Q)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__291 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   29
                                                                                                                                   23)) == (0b1011100#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   21
                                                                                                                                   10)) == (0x872#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__290 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__290 <b 283) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__291 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 283
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
                                                                                                                          (decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_simd
                                                                                                                            Rd
                                                                                                                            Rn
                                                                                                                            sz
                                                                                                                            U
                                                                                                                            Q)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__293 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     30
                                                                                                                                     24)) == (0b0011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     21
                                                                                                                                     10)) == (0x900#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__292 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__292 <b 284) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__293 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 284
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
                                                                                                                              (decode_fcvtas_float_aarch64_instrs_float_convert_int
                                                                                                                                Rd
                                                                                                                                Rn
                                                                                                                                opcode
                                                                                                                                rmode
                                                                                                                                ftype
                                                                                                                                sf)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__295 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         30
                                                                                                                                         24)) == (0b0011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         21
                                                                                                                                         10)) == (0x940#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__294 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__294 <b 285) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__295 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 285
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
                                                                                                                                  (decode_fcvtau_float_aarch64_instrs_float_convert_int
                                                                                                                                    Rd
                                                                                                                                    Rn
                                                                                                                                    opcode
                                                                                                                                    rmode
                                                                                                                                    ftype
                                                                                                                                    sf)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__297 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             30
                                                                                                                                             24)) == (0b0011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             21
                                                                                                                                             10)) == (0xC00#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__296 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__296 <b 286) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__297 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 286
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
                                                                                                                                      (decode_fcvtms_float_aarch64_instrs_float_convert_int
                                                                                                                                        Rd
                                                                                                                                        Rn
                                                                                                                                        opcode
                                                                                                                                        rmode
                                                                                                                                        ftype
                                                                                                                                        sf)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__299 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 30
                                                                                                                                                 24)) == (0b0011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 21
                                                                                                                                                 10)) == (0xC40#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__298 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__298 <b 287) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__299 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 287
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
                                                                                                                                          (decode_fcvtmu_float_aarch64_instrs_float_convert_int
                                                                                                                                            Rd
                                                                                                                                            Rn
                                                                                                                                            opcode
                                                                                                                                            rmode
                                                                                                                                            ftype
                                                                                                                                            sf)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__301 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     30
                                                                                                                                                     24)) == (0b0011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     21
                                                                                                                                                     10)) == (0x800#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__300 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__300 <b 288) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__301 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 288
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
                                                                                                                                              (decode_fcvtns_float_aarch64_instrs_float_convert_int
                                                                                                                                                Rd
                                                                                                                                                Rn
                                                                                                                                                opcode
                                                                                                                                                rmode
                                                                                                                                                ftype
                                                                                                                                                sf)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__303 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         30
                                                                                                                                                         24)) == (0b0011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         21
                                                                                                                                                         10)) == (0x840#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__302 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__302 <b 289) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__303 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 289
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
                                                                                                                                                  (decode_fcvtnu_float_aarch64_instrs_float_convert_int
                                                                                                                                                    Rd
                                                                                                                                                    Rn
                                                                                                                                                    opcode
                                                                                                                                                    rmode
                                                                                                                                                    ftype
                                                                                                                                                    sf)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__305 ← (( do
                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             30
                                                                                                                                                             24)) == (0b0011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             21
                                                                                                                                                             10)) == (0xA00#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__304 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__304 <b 290) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__305 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 290
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
                                                                                                                                                      (decode_fcvtps_float_aarch64_instrs_float_convert_int
                                                                                                                                                        Rd
                                                                                                                                                        Rn
                                                                                                                                                        opcode
                                                                                                                                                        rmode
                                                                                                                                                        ftype
                                                                                                                                                        sf)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__307 ← (( do
                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 30
                                                                                                                                                                 24)) == (0b0011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 21
                                                                                                                                                                 10)) == (0xA40#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__306 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__306 <b 291) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false)
                                                                                                                                                        )
                                                                                                                                                        :
                                                                                                                                                        SailM
                                                                                                                                                        Bool
                                                                                                                                                        )
                                                                                                                                                      if (w__307 : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 291
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
                                                                                                                                                          (decode_fcvtpu_float_aarch64_instrs_float_convert_int
                                                                                                                                                            Rd
                                                                                                                                                            Rn
                                                                                                                                                            opcode
                                                                                                                                                            rmode
                                                                                                                                                            ftype
                                                                                                                                                            sf)
                                                                                                                                                          (pure false))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          let w__309 ← (( do
                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     30
                                                                                                                                                                     24)) == (0b0011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     21
                                                                                                                                                                     10)) == (0xE00#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let w__308 ← (( do
                                                                                                                                                                  readReg SEE
                                                                                                                                                                  )
                                                                                                                                                                  :
                                                                                                                                                                  SailM
                                                                                                                                                                  Int
                                                                                                                                                                  )
                                                                                                                                                                (pure (((w__308 <b 292) : Bool))))
                                                                                                                                                            else
                                                                                                                                                              (pure false)
                                                                                                                                                            )
                                                                                                                                                            :
                                                                                                                                                            SailM
                                                                                                                                                            Bool
                                                                                                                                                            )
                                                                                                                                                          if (w__309 : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 292
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
                                                                                                                                                              (decode_fcvtzs_float_int_aarch64_instrs_float_convert_int
                                                                                                                                                                Rd
                                                                                                                                                                Rn
                                                                                                                                                                opcode
                                                                                                                                                                rmode
                                                                                                                                                                ftype
                                                                                                                                                                sf)
                                                                                                                                                              (pure false))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              let w__311 ← (( do
                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         30
                                                                                                                                                                         24)) == (0b0011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         21
                                                                                                                                                                         10)) == (0xE40#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    let w__310 ← (( do
                                                                                                                                                                      readReg SEE
                                                                                                                                                                      )
                                                                                                                                                                      :
                                                                                                                                                                      SailM
                                                                                                                                                                      Int
                                                                                                                                                                      )
                                                                                                                                                                    (pure (((w__310 <b 293) : Bool))))
                                                                                                                                                                else
                                                                                                                                                                  (pure false)
                                                                                                                                                                )
                                                                                                                                                                :
                                                                                                                                                                SailM
                                                                                                                                                                Bool
                                                                                                                                                                )
                                                                                                                                                              if (w__311 : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 293
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
                                                                                                                                                                  (decode_fcvtzu_float_int_aarch64_instrs_float_convert_int
                                                                                                                                                                    Rd
                                                                                                                                                                    Rn
                                                                                                                                                                    opcode
                                                                                                                                                                    rmode
                                                                                                                                                                    ftype
                                                                                                                                                                    sf)
                                                                                                                                                                  (pure false))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  let w__313 ← (( do
                                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           31
                                                                                                                                                                           10)) == (0b0001111001111110000000#22 : (BitVec 22))) : Bool) : Bool)
                                                                                                                                                                    then
                                                                                                                                                                      (do
                                                                                                                                                                        let w__312 ← (( do
                                                                                                                                                                          readReg SEE
                                                                                                                                                                          )
                                                                                                                                                                          :
                                                                                                                                                                          SailM
                                                                                                                                                                          Int
                                                                                                                                                                          )
                                                                                                                                                                        (pure (((w__312 <b 294) : Bool))))
                                                                                                                                                                    else
                                                                                                                                                                      (pure false)
                                                                                                                                                                    )
                                                                                                                                                                    :
                                                                                                                                                                    SailM
                                                                                                                                                                    Bool
                                                                                                                                                                    )
                                                                                                                                                                  if (w__313 : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      writeReg SEE 294
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
                                                                                                                                                                      (decode_fjcvtzs_aarch64_instrs_float_convert_int
                                                                                                                                                                        Rd
                                                                                                                                                                        Rn
                                                                                                                                                                        opcode
                                                                                                                                                                        rmode
                                                                                                                                                                        ftype
                                                                                                                                                                        sf)
                                                                                                                                                                      (pure false))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      let w__315 ← (( do
                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 30
                                                                                                                                                                                 24)) == (0b0011110#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                   __opcode
                                                                                                                                                                                   21
                                                                                                                                                                                   20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                     __opcode
                                                                                                                                                                                     18
                                                                                                                                                                                     17)) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                     __opcode
                                                                                                                                                                                     15
                                                                                                                                                                                     10)) == (0b000000#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                                                                                                        then
                                                                                                                                                                          (do
                                                                                                                                                                            let w__314 ← (( do
                                                                                                                                                                              readReg SEE
                                                                                                                                                                              )
                                                                                                                                                                              :
                                                                                                                                                                              SailM
                                                                                                                                                                              Int
                                                                                                                                                                              )
                                                                                                                                                                            (pure (((w__314 <b 295) : Bool))))
                                                                                                                                                                        else
                                                                                                                                                                          (pure false)
                                                                                                                                                                        )
                                                                                                                                                                        :
                                                                                                                                                                        SailM
                                                                                                                                                                        Bool
                                                                                                                                                                        )
                                                                                                                                                                      if (w__315 : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (do
                                                                                                                                                                          writeReg SEE 295
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
                                                                                                                                                                          (decode_fmov_float_gen_aarch64_instrs_float_convert_int
                                                                                                                                                                            Rd
                                                                                                                                                                            Rn
                                                                                                                                                                            opcode
                                                                                                                                                                            rmode
                                                                                                                                                                            ftype
                                                                                                                                                                            sf)
                                                                                                                                                                          (pure false))
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          let w__317 ← (( do
                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                                                     __opcode
                                                                                                                                                                                     30
                                                                                                                                                                                     24)) == (0b0011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                                     __opcode
                                                                                                                                                                                     21
                                                                                                                                                                                     10)) == (0x880#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                                                                            then
                                                                                                                                                                              (do
                                                                                                                                                                                let w__316 ← (( do
                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                  )
                                                                                                                                                                                  :
                                                                                                                                                                                  SailM
                                                                                                                                                                                  Int
                                                                                                                                                                                  )
                                                                                                                                                                                (pure (((w__316 <b 296) : Bool))))
                                                                                                                                                                            else
                                                                                                                                                                              (pure false)
                                                                                                                                                                            )
                                                                                                                                                                            :
                                                                                                                                                                            SailM
                                                                                                                                                                            Bool
                                                                                                                                                                            )
                                                                                                                                                                          if (w__317 : Bool)
                                                                                                                                                                          then
                                                                                                                                                                            (do
                                                                                                                                                                              writeReg SEE 296
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
                                                                                                                                                                              (decode_scvtf_float_int_aarch64_instrs_float_convert_int
                                                                                                                                                                                Rd
                                                                                                                                                                                Rn
                                                                                                                                                                                opcode
                                                                                                                                                                                rmode
                                                                                                                                                                                ftype
                                                                                                                                                                                sf)
                                                                                                                                                                              (pure false))
                                                                                                                                                                          else
                                                                                                                                                                            (pure true)))))))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
