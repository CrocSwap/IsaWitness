import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M1108
import ArmFull.Fn.M1109
import ArmFull.Fn.M1297
import ArmFull.Fn.M1298

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
def __DecodeA64_LoadStore__seg2 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__137 ← (( do
    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb
             __opcode 29 12)) == (0b001100010000000000#18 : (BitVec 18)))) : Bool) : Bool)
    then
      (do
        let w__136 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__136 <b 514) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__137 : Bool)
  then
    (do
      writeReg SEE 514
      let Rt := (BitVec.slice __opcode 0 5)
      let Rn := (BitVec.slice __opcode 5 5)
      let size := (BitVec.slice __opcode 10 2)
      let opcode := (BitVec.slice __opcode 12 4)
      let L := (BitVec.slice __opcode 22 1)
      let Q := (BitVec.slice __opcode 30 1)
      (decode_ld4_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn size opcode L Q)
      (pure false))
  else
    (do
      let w__139 ← (( do
        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                   __opcode 29 21)) == (0b001100110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                   __opcode 15 12)) == (0x0#4 : (BitVec 4))))) : Bool) : Bool)
        then
          (do
            let w__138 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__138 <b 515) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__139 : Bool)
      then
        (do
          writeReg SEE 515
          let Rt := (BitVec.slice __opcode 0 5)
          let Rn := (BitVec.slice __opcode 5 5)
          let size := (BitVec.slice __opcode 10 2)
          let opcode := (BitVec.slice __opcode 12 4)
          let Rm := (BitVec.slice __opcode 16 5)
          let L := (BitVec.slice __opcode 22 1)
          let Q := (BitVec.slice __opcode 30 1)
          (decode_ld4_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt Rn size opcode
            Rm L Q)
          (pure false))
      else
        (do
          let w__141 ← (( do
            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb
                       __opcode 29 16)) == (0b00110000000000#14 : (BitVec 14))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       __opcode 13 13)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
            then
              (do
                let w__140 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__140 <b 516) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__141 : Bool)
          then
            (do
              writeReg SEE 516
              let Rt := (BitVec.slice __opcode 0 5)
              let Rn := (BitVec.slice __opcode 5 5)
              let size := (BitVec.slice __opcode 10 2)
              let opcode := (BitVec.slice __opcode 12 4)
              let L := (BitVec.slice __opcode 22 1)
              let Q := (BitVec.slice __opcode 30 1)
              (decode_st1_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn size opcode
                L Q)
              (pure false))
          else
            (do
              let w__143 ← (( do
                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                           __opcode 29 21)) == (0b001100100#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           __opcode 13 13)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                then
                  (do
                    let w__142 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__142 <b 517) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__143 : Bool)
              then
                (do
                  writeReg SEE 517
                  let Rt := (BitVec.slice __opcode 0 5)
                  let Rn := (BitVec.slice __opcode 5 5)
                  let size := (BitVec.slice __opcode 10 2)
                  let opcode := (BitVec.slice __opcode 12 4)
                  let Rm := (BitVec.slice __opcode 16 5)
                  let L := (BitVec.slice __opcode 22 1)
                  let Q := (BitVec.slice __opcode 30 1)
                  (decode_st1_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt Rn size
                    opcode Rm L Q)
                  (pure false))
              else
                (do
                  let w__145 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb
                             __opcode 29 12)) == (0b001100000000001000#18 : (BitVec 18)))) : Bool) : Bool)
                    then
                      (do
                        let w__144 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__144 <b 518) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__145 : Bool)
                  then
                    (do
                      writeReg SEE 518
                      let Rt := (BitVec.slice __opcode 0 5)
                      let Rn := (BitVec.slice __opcode 5 5)
                      let size := (BitVec.slice __opcode 10 2)
                      let opcode := (BitVec.slice __opcode 12 4)
                      let L := (BitVec.slice __opcode 22 1)
                      let Q := (BitVec.slice __opcode 30 1)
                      (decode_st2_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn
                        size opcode L Q)
                      (pure false))
                  else
                    (do
                      let w__147 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31
                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                   __opcode 29 21)) == (0b001100100#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                   __opcode 15 12)) == (0x8#4 : (BitVec 4))))) : Bool) : Bool)
                        then
                          (do
                            let w__146 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__146 <b 519) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__147 : Bool)
                      then
                        (do
                          writeReg SEE 519
                          let Rt := (BitVec.slice __opcode 0 5)
                          let Rn := (BitVec.slice __opcode 5 5)
                          let size := (BitVec.slice __opcode 10 2)
                          let opcode := (BitVec.slice __opcode 12 4)
                          let Rm := (BitVec.slice __opcode 16 5)
                          let L := (BitVec.slice __opcode 22 1)
                          let Q := (BitVec.slice __opcode 30 1)
                          (decode_st2_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt
                            Rn size opcode Rm L Q)
                          (pure false))
                      else
                        (do
                          let w__149 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode
                                     31 31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb
                                     __opcode 29 12)) == (0b001100000000000100#18 : (BitVec 18)))) : Bool) : Bool)
                            then
                              (do
                                let w__148 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__148 <b 520) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__149 : Bool)
                          then
                            (do
                              writeReg SEE 520
                              let Rt := (BitVec.slice __opcode 0 5)
                              let Rn := (BitVec.slice __opcode 5 5)
                              let size := (BitVec.slice __opcode 10 2)
                              let opcode := (BitVec.slice __opcode 12 4)
                              let L := (BitVec.slice __opcode 22 1)
                              let Q := (BitVec.slice __opcode 30 1)
                              (decode_st3_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb
                                Rt Rn size opcode L Q)
                              (pure false))
                          else
                            (do
                              let w__151 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                         __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                           __opcode 29 21)) == (0b001100100#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                           __opcode 15 12)) == (0x4#4 : (BitVec 4))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__150 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__150 <b 521) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__151 : Bool)
                              then
                                (do
                                  writeReg SEE 521
                                  let Rt := (BitVec.slice __opcode 0 5)
                                  let Rn := (BitVec.slice __opcode 5 5)
                                  let size := (BitVec.slice __opcode 10 2)
                                  let opcode := (BitVec.slice __opcode 12 4)
                                  let Rm := (BitVec.slice __opcode 16 5)
                                  let L := (BitVec.slice __opcode 22 1)
                                  let Q := (BitVec.slice __opcode 30 1)
                                  (decode_st3_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc
                                    Rt Rn size opcode Rm L Q)
                                  (pure false))
                              else
                                (do
                                  let w__153 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             __opcode 31 31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb
                                             __opcode 29 12)) == (0b001100000000000000#18 : (BitVec 18)))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__152 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__152 <b 522) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__153 : Bool)
                                  then
                                    (do
                                      writeReg SEE 522
                                      let Rt := (BitVec.slice __opcode 0 5)
                                      let Rn := (BitVec.slice __opcode 5 5)
                                      let size := (BitVec.slice __opcode 10 2)
                                      let opcode := (BitVec.slice __opcode 12 4)
                                      let L := (BitVec.slice __opcode 22 1)
                                      let Q := (BitVec.slice __opcode 30 1)
                                      (decode_st4_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb
                                        Rt Rn size opcode L Q)
                                      (pure false))
                                  else
                                    (do
                                      let w__155 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                   __opcode 29 21)) == (0b001100100#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                   __opcode 15 12)) == (0x0#4 : (BitVec 4))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__154 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__154 <b 523) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__155 : Bool)
                                      then
                                        (do
                                          writeReg SEE 523
                                          let Rt := (BitVec.slice __opcode 0 5)
                                          let Rn := (BitVec.slice __opcode 5 5)
                                          let size := (BitVec.slice __opcode 10 2)
                                          let opcode := (BitVec.slice __opcode 12 4)
                                          let Rm := (BitVec.slice __opcode 16 5)
                                          let L := (BitVec.slice __opcode 22 1)
                                          let Q := (BitVec.slice __opcode 30 1)
                                          (decode_st4_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc
                                            Rt Rn size opcode Rm L Q)
                                          (pure false))
                                      else
                                        (do
                                          let w__157 ← (( do
                                            if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                   __opcode 31 10)) == (0b1111100000111111110100#22 : (BitVec 22))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__156 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__156 <b 524) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__157 : Bool)
                                          then
                                            (do
                                              writeReg SEE 524
                                              let Rt := (BitVec.slice __opcode 0 5)
                                              let Rn := (BitVec.slice __opcode 5 5)
                                              (decode_ld64b_aarch64_instrs_memory_atomicops_ld_acc
                                                Rt Rn)
                                              (pure false))
                                          else
                                            (do
                                              let w__159 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                         __opcode 31 31)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                           __opcode 29 24)) == (0b111000#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                             __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                             __opcode 15 10)) == (0b000000#6 : (BitVec 6)))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__158 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__158 <b 525) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__159 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 525
                                                  let Rt := (BitVec.slice __opcode 0 5)
                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                  let opc := (BitVec.slice __opcode 12 3)
                                                  let Rs := (BitVec.slice __opcode 16 5)
                                                  let R := (BitVec.slice __opcode 22 1)
                                                  let A := (BitVec.slice __opcode 23 1)
                                                  let size := (BitVec.slice __opcode 30 2)
                                                  (decode_ldadd_aarch64_instrs_memory_atomicops_ld
                                                    Rt Rn opc Rs R A size)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__161 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                             __opcode 31 24)) == (0x38#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                               __opcode 15 10)) == (0b000000#6 : (BitVec 6))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__160 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__160 <b 526) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__161 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 526
                                                      let Rt := (BitVec.slice __opcode 0 5)
                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                      let opc := (BitVec.slice __opcode 12 3)
                                                      let Rs := (BitVec.slice __opcode 16 5)
                                                      let R := (BitVec.slice __opcode 22 1)
                                                      let A := (BitVec.slice __opcode 23 1)
                                                      let size := (BitVec.slice __opcode 30 2)
                                                      (decode_ldaddb_aarch64_instrs_memory_atomicops_ld
                                                        Rt Rn opc Rs R A size)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__163 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                 __opcode 31 24)) == (0x78#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                   __opcode 15 10)) == (0b000000#6 : (BitVec 6))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__162 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__162 <b 527) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__163 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 527
                                                          let Rt := (BitVec.slice __opcode 0 5)
                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                          let opc := (BitVec.slice __opcode 12 3)
                                                          let Rs := (BitVec.slice __opcode 16 5)
                                                          let R := (BitVec.slice __opcode 22 1)
                                                          let A := (BitVec.slice __opcode 23 1)
                                                          let size := (BitVec.slice __opcode 30 2)
                                                          (decode_ldaddh_aarch64_instrs_memory_atomicops_ld
                                                            Rt Rn opc Rs R A size)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__165 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                     __opcode 31 31)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                       __opcode 29 24)) == (0b111000#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                         __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                         __opcode 15 10)) == (0b000100#6 : (BitVec 6)))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__164 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__164 <b 528) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__165 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 528
                                                              let Rt := (BitVec.slice __opcode 0 5)
                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                              let opc :=
                                                                (BitVec.slice __opcode 12 3)
                                                              let Rs := (BitVec.slice __opcode 16 5)
                                                              let R := (BitVec.slice __opcode 22 1)
                                                              let A := (BitVec.slice __opcode 23 1)
                                                              let size :=
                                                                (BitVec.slice __opcode 30 2)
                                                              (decode_ldclr_aarch64_instrs_memory_atomicops_ld
                                                                Rt Rn opc Rs R A size)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__167 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                         __opcode 31 24)) == (0x38#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                           __opcode 15 10)) == (0b000100#6 : (BitVec 6))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__166 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__166 <b 529) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__167 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 529
                                                                  let Rt :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let opc :=
                                                                    (BitVec.slice __opcode 12 3)
                                                                  let Rs :=
                                                                    (BitVec.slice __opcode 16 5)
                                                                  let R :=
                                                                    (BitVec.slice __opcode 22 1)
                                                                  let A :=
                                                                    (BitVec.slice __opcode 23 1)
                                                                  let size :=
                                                                    (BitVec.slice __opcode 30 2)
                                                                  (decode_ldclrb_aarch64_instrs_memory_atomicops_ld
                                                                    Rt Rn opc Rs R A size)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__169 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                             __opcode 31 24)) == (0x78#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                               __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                               __opcode 15 10)) == (0b000100#6 : (BitVec 6))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__168 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__168 <b 530) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__169 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 530
                                                                      let Rt :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let opc :=
                                                                        (BitVec.slice __opcode 12 3)
                                                                      let Rs :=
                                                                        (BitVec.slice __opcode 16 5)
                                                                      let R :=
                                                                        (BitVec.slice __opcode 22 1)
                                                                      let A :=
                                                                        (BitVec.slice __opcode 23 1)
                                                                      let size :=
                                                                        (BitVec.slice __opcode 30 2)
                                                                      (decode_ldclrh_aarch64_instrs_memory_atomicops_ld
                                                                        Rt Rn opc Rs R A size)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__171 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 31)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                   __opcode 29 24)) == (0b111000#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                     __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                     __opcode 15 10)) == (0b001000#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__170 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__170 <b 531) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__171 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 531
                                                                          let Rt :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let opc :=
                                                                            (BitVec.slice __opcode
                                                                              12 3)
                                                                          let Rs :=
                                                                            (BitVec.slice __opcode
                                                                              16 5)
                                                                          let R :=
                                                                            (BitVec.slice __opcode
                                                                              22 1)
                                                                          let A :=
                                                                            (BitVec.slice __opcode
                                                                              23 1)
                                                                          let size :=
                                                                            (BitVec.slice __opcode
                                                                              30 2)
                                                                          (decode_ldeor_aarch64_instrs_memory_atomicops_ld
                                                                            Rt Rn opc Rs R A size)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__173 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 24)) == (0x38#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 21
                                                                                       21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                       __opcode 15
                                                                                       10)) == (0b001000#6 : (BitVec 6))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__172 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__172 <b 532) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__173 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 532
                                                                              let Rt :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let opc :=
                                                                                (BitVec.slice
                                                                                  __opcode 12 3)
                                                                              let Rs :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 5)
                                                                              let R :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 1)
                                                                              let A :=
                                                                                (BitVec.slice
                                                                                  __opcode 23 1)
                                                                              let size :=
                                                                                (BitVec.slice
                                                                                  __opcode 30 2)
                                                                              (decode_ldeorb_aarch64_instrs_memory_atomicops_ld
                                                                                Rt Rn opc Rs R A
                                                                                size)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__175 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         24)) == (0x78#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           15 10)) == (0b001000#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__174 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__174 <b 533) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__175 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 533
                                                                                  let Rt :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let opc :=
                                                                                    (BitVec.slice
                                                                                      __opcode 12 3)
                                                                                  let Rs :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 5)
                                                                                  let R :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 1)
                                                                                  let A :=
                                                                                    (BitVec.slice
                                                                                      __opcode 23 1)
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 30 2)
                                                                                  (decode_ldeorh_aarch64_instrs_memory_atomicops_ld
                                                                                    Rt Rn opc Rs R A
                                                                                    size)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__177 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 31)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               29 24)) == (0b111000#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 21
                                                                                                 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 15
                                                                                                 10)) == (0b001100#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__176 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__176 <b 534) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__177 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 534
                                                                                      let Rt :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          5)
                                                                                      let Rn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let opc :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          12 3)
                                                                                      let Rs :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 5)
                                                                                      let R :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 1)
                                                                                      let A :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          23 1)
                                                                                      let size :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          30 2)
                                                                                      (decode_ldset_aarch64_instrs_memory_atomicops_ld
                                                                                        Rt Rn opc Rs
                                                                                        R A size)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__179 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 24)) == (0x38#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   21
                                                                                                   21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   15
                                                                                                   10)) == (0b001100#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__178 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__178 <b 535) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__179 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 535
                                                                                          let Rt :=
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
                                                                                              12 3)
                                                                                          let Rs :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 5)
                                                                                          let R :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 1)
                                                                                          let A :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              23 1)
                                                                                          let size :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              30 2)
                                                                                          (decode_ldsetb_aarch64_instrs_memory_atomicops_ld
                                                                                            Rt Rn
                                                                                            opc Rs R
                                                                                            A size)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__181 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     24)) == (0x78#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       21
                                                                                                       21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       15
                                                                                                       10)) == (0b001100#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__180 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__180 <b 536) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__181 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 536
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
                                                                                              let opc :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  12
                                                                                                  3)
                                                                                              let Rs :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  5)
                                                                                              let R :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  22
                                                                                                  1)
                                                                                              let A :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  23
                                                                                                  1)
                                                                                              let size :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  30
                                                                                                  2)
                                                                                              (decode_ldseth_aarch64_instrs_memory_atomicops_ld
                                                                                                Rt
                                                                                                Rn
                                                                                                opc
                                                                                                Rs R
                                                                                                A
                                                                                                size)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__183 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         31)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           29
                                                                                                           24)) == (0b111000#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             21
                                                                                                             21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             15
                                                                                                             10)) == (0b010000#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__182 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__182 <b 537) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__183 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 537
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
                                                                                                  let opc :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      12
                                                                                                      3)
                                                                                                  let Rs :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      5)
                                                                                                  let R :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      22
                                                                                                      1)
                                                                                                  let A :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      23
                                                                                                      1)
                                                                                                  let size :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      30
                                                                                                      2)
                                                                                                  (decode_ldsmax_aarch64_instrs_memory_atomicops_ld
                                                                                                    Rt
                                                                                                    Rn
                                                                                                    opc
                                                                                                    Rs
                                                                                                    R
                                                                                                    A
                                                                                                    size)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__185 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             24)) == (0x38#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               21
                                                                                                               21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               15
                                                                                                               10)) == (0b010000#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__184 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__184 <b 538) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__185 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 538
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
                                                                                                      let opc :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          12
                                                                                                          3)
                                                                                                      let Rs :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          5)
                                                                                                      let R :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          22
                                                                                                          1)
                                                                                                      let A :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          23
                                                                                                          1)
                                                                                                      let size :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          30
                                                                                                          2)
                                                                                                      (decode_ldsmaxb_aarch64_instrs_memory_atomicops_ld
                                                                                                        Rt
                                                                                                        Rn
                                                                                                        opc
                                                                                                        Rs
                                                                                                        R
                                                                                                        A
                                                                                                        size)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__187 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 24)) == (0x78#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   21
                                                                                                                   21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   15
                                                                                                                   10)) == (0b010000#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__186 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__186 <b 539) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__187 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 539
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
                                                                                                          let opc :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              12
                                                                                                              3)
                                                                                                          let Rs :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              5)
                                                                                                          let R :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              22
                                                                                                              1)
                                                                                                          let A :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              23
                                                                                                              1)
                                                                                                          let size :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              30
                                                                                                              2)
                                                                                                          (decode_ldsmaxh_aarch64_instrs_memory_atomicops_ld
                                                                                                            Rt
                                                                                                            Rn
                                                                                                            opc
                                                                                                            Rs
                                                                                                            R
                                                                                                            A
                                                                                                            size)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__189 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     31)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       29
                                                                                                                       24)) == (0b111000#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         21
                                                                                                                         21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         15
                                                                                                                         10)) == (0b010100#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__188 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__188 <b 540) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__189 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 540
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
                                                                                                              let opc :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  12
                                                                                                                  3)
                                                                                                              let Rs :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  5)
                                                                                                              let R :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  22
                                                                                                                  1)
                                                                                                              let A :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  23
                                                                                                                  1)
                                                                                                              let size :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  30
                                                                                                                  2)
                                                                                                              (decode_ldsmin_aarch64_instrs_memory_atomicops_ld
                                                                                                                Rt
                                                                                                                Rn
                                                                                                                opc
                                                                                                                Rs
                                                                                                                R
                                                                                                                A
                                                                                                                size)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__191 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         24)) == (0x38#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           21
                                                                                                                           21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           15
                                                                                                                           10)) == (0b010100#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__190 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__190 <b 541) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__191 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 541
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
                                                                                                                  let opc :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      12
                                                                                                                      3)
                                                                                                                  let Rs :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      5)
                                                                                                                  let R :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      22
                                                                                                                      1)
                                                                                                                  let A :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      23
                                                                                                                      1)
                                                                                                                  let size :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      30
                                                                                                                      2)
                                                                                                                  (decode_ldsminb_aarch64_instrs_memory_atomicops_ld
                                                                                                                    Rt
                                                                                                                    Rn
                                                                                                                    opc
                                                                                                                    Rs
                                                                                                                    R
                                                                                                                    A
                                                                                                                    size)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__193 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             24)) == (0x78#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               21
                                                                                                                               21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               15
                                                                                                                               10)) == (0b010100#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__192 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__192 <b 542) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__193 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 542
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
                                                                                                                      let opc :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          12
                                                                                                                          3)
                                                                                                                      let Rs :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          16
                                                                                                                          5)
                                                                                                                      let R :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          22
                                                                                                                          1)
                                                                                                                      let A :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          23
                                                                                                                          1)
                                                                                                                      let size :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          30
                                                                                                                          2)
                                                                                                                      (decode_ldsminh_aarch64_instrs_memory_atomicops_ld
                                                                                                                        Rt
                                                                                                                        Rn
                                                                                                                        opc
                                                                                                                        Rs
                                                                                                                        R
                                                                                                                        A
                                                                                                                        size)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__195 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 31)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   29
                                                                                                                                   24)) == (0b111000#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     21
                                                                                                                                     21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     15
                                                                                                                                     10)) == (0b011000#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__194 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__194 <b 543) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__195 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 543
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
                                                                                                                          let opc :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              12
                                                                                                                              3)
                                                                                                                          let Rs :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              5)
                                                                                                                          let R :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              22
                                                                                                                              1)
                                                                                                                          let A :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              23
                                                                                                                              1)
                                                                                                                          let size :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              30
                                                                                                                              2)
                                                                                                                          (decode_ldumax_aarch64_instrs_memory_atomicops_ld
                                                                                                                            Rt
                                                                                                                            Rn
                                                                                                                            opc
                                                                                                                            Rs
                                                                                                                            R
                                                                                                                            A
                                                                                                                            size)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__197 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     24)) == (0x38#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       21
                                                                                                                                       21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       15
                                                                                                                                       10)) == (0b011000#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__196 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__196 <b 544) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__197 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 544
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
                                                                                                                              let opc :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  12
                                                                                                                                  3)
                                                                                                                              let Rs :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
                                                                                                                                  5)
                                                                                                                              let R :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  22
                                                                                                                                  1)
                                                                                                                              let A :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  23
                                                                                                                                  1)
                                                                                                                              let size :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  30
                                                                                                                                  2)
                                                                                                                              (decode_ldumaxb_aarch64_instrs_memory_atomicops_ld
                                                                                                                                Rt
                                                                                                                                Rn
                                                                                                                                opc
                                                                                                                                Rs
                                                                                                                                R
                                                                                                                                A
                                                                                                                                size)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__199 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         24)) == (0x78#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           21
                                                                                                                                           21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           15
                                                                                                                                           10)) == (0b011000#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__198 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__198 <b 545) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__199 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 545
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
                                                                                                                                  let opc :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      12
                                                                                                                                      3)
                                                                                                                                  let Rs :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      5)
                                                                                                                                  let R :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      22
                                                                                                                                      1)
                                                                                                                                  let A :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      23
                                                                                                                                      1)
                                                                                                                                  let size :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      30
                                                                                                                                      2)
                                                                                                                                  (decode_ldumaxh_aarch64_instrs_memory_atomicops_ld
                                                                                                                                    Rt
                                                                                                                                    Rn
                                                                                                                                    opc
                                                                                                                                    Rs
                                                                                                                                    R
                                                                                                                                    A
                                                                                                                                    size)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__201 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             31)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               29
                                                                                                                                               24)) == (0b111000#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 21
                                                                                                                                                 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 15
                                                                                                                                                 10)) == (0b011100#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__200 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__200 <b 546) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__201 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 546
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
                                                                                                                                      let opc :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          12
                                                                                                                                          3)
                                                                                                                                      let Rs :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          16
                                                                                                                                          5)
                                                                                                                                      let R :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          22
                                                                                                                                          1)
                                                                                                                                      let A :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          23
                                                                                                                                          1)
                                                                                                                                      let size :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          30
                                                                                                                                          2)
                                                                                                                                      (decode_ldumin_aarch64_instrs_memory_atomicops_ld
                                                                                                                                        Rt
                                                                                                                                        Rn
                                                                                                                                        opc
                                                                                                                                        Rs
                                                                                                                                        R
                                                                                                                                        A
                                                                                                                                        size)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__203 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 24)) == (0x38#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   21
                                                                                                                                                   21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   15
                                                                                                                                                   10)) == (0b011100#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__202 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__202 <b 547) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__203 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 547
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
                                                                                                                                          let opc :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              12
                                                                                                                                              3)
                                                                                                                                          let Rs :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              16
                                                                                                                                              5)
                                                                                                                                          let R :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              22
                                                                                                                                              1)
                                                                                                                                          let A :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              23
                                                                                                                                              1)
                                                                                                                                          let size :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              30
                                                                                                                                              2)
                                                                                                                                          (decode_lduminb_aarch64_instrs_memory_atomicops_ld
                                                                                                                                            Rt
                                                                                                                                            Rn
                                                                                                                                            opc
                                                                                                                                            Rs
                                                                                                                                            R
                                                                                                                                            A
                                                                                                                                            size)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (pure true))))))))))))))))))))))))))))))))))


end ArmFull.Functions
