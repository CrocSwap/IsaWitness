import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M1021
import ArmFull.Fn.M1022
import ArmFull.Fn.M1023

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
def __DecodeA64_DataProcFPSIMD__seg13 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__999 ← (( do
    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x7E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
               __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
               __opcode 15 10)) == (0b010011#6 : (BitVec 6))))) : Bool) : Bool)
    then
      (do
        let w__998 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__998 <b 913) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__999 : Bool)
  then
    (do
      writeReg SEE 913
      let Rd := (BitVec.slice __opcode 0 5)
      let Rn := (BitVec.slice __opcode 5 5)
      let S := (BitVec.slice __opcode 11 1)
      let R := (BitVec.slice __opcode 12 1)
      let Rm := (BitVec.slice __opcode 16 5)
      let size := (BitVec.slice __opcode 22 2)
      let U := (BitVec.slice __opcode 29 1)
      (decode_uqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd Rd Rn S R
        Rm size U)
      (pure false))
  else
    (do
      let w__1001 ← (( do
        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                   __opcode 29 24)) == (0b101110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                     __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                     __opcode 15 10)) == (0b010011#6 : (BitVec 6)))))) : Bool) : Bool)
        then
          (do
            let w__1000 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__1000 <b 914) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__1001 : Bool)
      then
        (do
          writeReg SEE 914
          let Rd := (BitVec.slice __opcode 0 5)
          let Rn := (BitVec.slice __opcode 5 5)
          let S := (BitVec.slice __opcode 11 1)
          let R := (BitVec.slice __opcode 12 1)
          let Rm := (BitVec.slice __opcode 16 5)
          let size := (BitVec.slice __opcode 22 2)
          let U := (BitVec.slice __opcode 29 1)
          let Q := (BitVec.slice __opcode 30 1)
          (decode_uqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd Rd Rn
            S R Rm size U Q)
          (pure false))
      else
        (do
          let w__1003 ← (( do
            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x7E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                       __opcode 15 10)) == (0b010101#6 : (BitVec 6))))) : Bool) : Bool)
            then
              (do
                let w__1002 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__1002 <b 915) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__1003 : Bool)
          then
            (do
              writeReg SEE 915
              let Rd := (BitVec.slice __opcode 0 5)
              let Rn := (BitVec.slice __opcode 5 5)
              let S := (BitVec.slice __opcode 11 1)
              let R := (BitVec.slice __opcode 12 1)
              let Rm := (BitVec.slice __opcode 16 5)
              let size := (BitVec.slice __opcode 22 2)
              let U := (BitVec.slice __opcode 29 1)
              (decode_urshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd Rd Rn
                S R Rm size U)
              (pure false))
          else
            (do
              let w__1005 ← (( do
                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                           __opcode 29 24)) == (0b101110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                             __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                             __opcode 15 10)) == (0b010101#6 : (BitVec 6)))))) : Bool) : Bool)
                then
                  (do
                    let w__1004 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__1004 <b 916) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__1005 : Bool)
              then
                (do
                  writeReg SEE 916
                  let Rd := (BitVec.slice __opcode 0 5)
                  let Rn := (BitVec.slice __opcode 5 5)
                  let S := (BitVec.slice __opcode 11 1)
                  let R := (BitVec.slice __opcode 12 1)
                  let Rm := (BitVec.slice __opcode 16 5)
                  let size := (BitVec.slice __opcode 22 2)
                  let U := (BitVec.slice __opcode 29 1)
                  let Q := (BitVec.slice __opcode 30 1)
                  (decode_urshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd
                    Rd Rn S R Rm size U Q)
                  (pure false))
              else
                (do
                  let w__1007 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x7E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                               __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                               __opcode 15 10)) == (0b010001#6 : (BitVec 6))))) : Bool) : Bool)
                    then
                      (do
                        let w__1006 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__1006 <b 917) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__1007 : Bool)
                  then
                    (do
                      writeReg SEE 917
                      let Rd := (BitVec.slice __opcode 0 5)
                      let Rn := (BitVec.slice __opcode 5 5)
                      let S := (BitVec.slice __opcode 11 1)
                      let R := (BitVec.slice __opcode 12 1)
                      let Rm := (BitVec.slice __opcode 16 5)
                      let size := (BitVec.slice __opcode 22 2)
                      let U := (BitVec.slice __opcode 29 1)
                      (decode_ushl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd
                        Rd Rn S R Rm size U)
                      (pure false))
                  else
                    (do
                      let w__1009 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31
                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                   __opcode 29 24)) == (0b101110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                     __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                     __opcode 15 10)) == (0b010001#6 : (BitVec 6)))))) : Bool) : Bool)
                        then
                          (do
                            let w__1008 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__1008 <b 918) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__1009 : Bool)
                      then
                        (do
                          writeReg SEE 918
                          let Rd := (BitVec.slice __opcode 0 5)
                          let Rn := (BitVec.slice __opcode 5 5)
                          let S := (BitVec.slice __opcode 11 1)
                          let R := (BitVec.slice __opcode 12 1)
                          let Rm := (BitVec.slice __opcode 16 5)
                          let size := (BitVec.slice __opcode 22 2)
                          let U := (BitVec.slice __opcode 29 1)
                          let Q := (BitVec.slice __opcode 30 1)
                          (decode_ushl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd
                            Rd Rn S R Rm size U Q)
                          (pure false))
                      else
                        (do
                          let w__1011 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode
                                     31 23)) == (0b010111110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                     __opcode 15 10)) == (0b100111#6 : (BitVec 6)))) : Bool) : Bool)
                            then
                              (do
                                let w__1010 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__1010 <b 919) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__1011 : Bool)
                          then
                            (do
                              writeReg SEE 919
                              let Rd := (BitVec.slice __opcode 0 5)
                              let Rn := (BitVec.slice __opcode 5 5)
                              let op := (BitVec.slice __opcode 11 1)
                              let immb := (BitVec.slice __opcode 16 3)
                              let immh := (BitVec.slice __opcode 19 4)
                              let U := (BitVec.slice __opcode 29 1)
                              (decode_sqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd
                                Rd Rn op immb immh U)
                              (pure false))
                          else
                            (do
                              let w__1013 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                         __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                           __opcode 29 23)) == (0b0011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                           __opcode 15 10)) == (0b100111#6 : (BitVec 6))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__1012 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__1012 <b 920) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__1013 : Bool)
                              then
                                (do
                                  writeReg SEE 920
                                  let Rd := (BitVec.slice __opcode 0 5)
                                  let Rn := (BitVec.slice __opcode 5 5)
                                  let op := (BitVec.slice __opcode 11 1)
                                  let immb := (BitVec.slice __opcode 16 3)
                                  let immh := (BitVec.slice __opcode 19 4)
                                  let U := (BitVec.slice __opcode 29 1)
                                  let Q := (BitVec.slice __opcode 30 1)
                                  (decode_sqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd
                                    Rd Rn op immb immh U Q)
                                  (pure false))
                              else
                                (do
                                  let w__1015 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                             __opcode 31 23)) == (0b010111110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                             __opcode 15 10)) == (0b100101#6 : (BitVec 6)))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__1014 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__1014 <b 921) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__1015 : Bool)
                                  then
                                    (do
                                      writeReg SEE 921
                                      let Rd := (BitVec.slice __opcode 0 5)
                                      let Rn := (BitVec.slice __opcode 5 5)
                                      let op := (BitVec.slice __opcode 11 1)
                                      let immb := (BitVec.slice __opcode 16 3)
                                      let immh := (BitVec.slice __opcode 19 4)
                                      let U := (BitVec.slice __opcode 29 1)
                                      (decode_sqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd
                                        Rd Rn op immb immh U)
                                      (pure false))
                                  else
                                    (do
                                      let w__1017 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                   __opcode 29 23)) == (0b0011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                   __opcode 15 10)) == (0b100101#6 : (BitVec 6))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__1016 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__1016 <b 922) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__1017 : Bool)
                                      then
                                        (do
                                          writeReg SEE 922
                                          let Rd := (BitVec.slice __opcode 0 5)
                                          let Rn := (BitVec.slice __opcode 5 5)
                                          let op := (BitVec.slice __opcode 11 1)
                                          let immb := (BitVec.slice __opcode 16 3)
                                          let immh := (BitVec.slice __opcode 19 4)
                                          let U := (BitVec.slice __opcode 29 1)
                                          let Q := (BitVec.slice __opcode 30 1)
                                          (decode_sqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd
                                            Rd Rn op immb immh U Q)
                                          (pure false))
                                      else
                                        (do
                                          let w__1019 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                     __opcode 31 23)) == (0b011111110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                     __opcode 15 10)) == (0b100111#6 : (BitVec 6)))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__1018 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__1018 <b 923) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__1019 : Bool)
                                          then
                                            (do
                                              writeReg SEE 923
                                              let Rd := (BitVec.slice __opcode 0 5)
                                              let Rn := (BitVec.slice __opcode 5 5)
                                              let op := (BitVec.slice __opcode 11 1)
                                              let immb := (BitVec.slice __opcode 16 3)
                                              let immh := (BitVec.slice __opcode 19 4)
                                              let U := (BitVec.slice __opcode 29 1)
                                              (decode_uqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd
                                                Rd Rn op immb immh U)
                                              (pure false))
                                          else
                                            (do
                                              let w__1021 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                         __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                           __opcode 29 23)) == (0b1011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                           __opcode 15 10)) == (0b100111#6 : (BitVec 6))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__1020 ← (( do readReg SEE ) : SailM Int
                                                      )
                                                    (pure (((w__1020 <b 924) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__1021 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 924
                                                  let Rd := (BitVec.slice __opcode 0 5)
                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                  let op := (BitVec.slice __opcode 11 1)
                                                  let immb := (BitVec.slice __opcode 16 3)
                                                  let immh := (BitVec.slice __opcode 19 4)
                                                  let U := (BitVec.slice __opcode 29 1)
                                                  let Q := (BitVec.slice __opcode 30 1)
                                                  (decode_uqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd
                                                    Rd Rn op immb immh U Q)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__1023 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                             __opcode 31 23)) == (0b011111110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                             __opcode 15 10)) == (0b100101#6 : (BitVec 6)))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__1022 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__1022 <b 925) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__1023 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 925
                                                      let Rd := (BitVec.slice __opcode 0 5)
                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                      let op := (BitVec.slice __opcode 11 1)
                                                      let immb := (BitVec.slice __opcode 16 3)
                                                      let immh := (BitVec.slice __opcode 19 4)
                                                      let U := (BitVec.slice __opcode 29 1)
                                                      (decode_uqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd
                                                        Rd Rn op immb immh U)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__1025 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                 __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                   __opcode 29 23)) == (0b1011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                   __opcode 15 10)) == (0b100101#6 : (BitVec 6))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__1024 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__1024 <b 926) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__1025 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 926
                                                          let Rd := (BitVec.slice __opcode 0 5)
                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                          let op := (BitVec.slice __opcode 11 1)
                                                          let immb := (BitVec.slice __opcode 16 3)
                                                          let immh := (BitVec.slice __opcode 19 4)
                                                          let U := (BitVec.slice __opcode 29 1)
                                                          let Q := (BitVec.slice __opcode 30 1)
                                                          (decode_uqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd
                                                            Rd Rn op immb immh U Q)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__1027 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                     __opcode 31 23)) == (0b011111110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                     __opcode 15 10)) == (0b100011#6 : (BitVec 6)))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__1026 ← (( do readReg SEE )
                                                                  : SailM Int )
                                                                (pure (((w__1026 <b 927) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__1027 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 927
                                                              let Rd := (BitVec.slice __opcode 0 5)
                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                              let op := (BitVec.slice __opcode 11 1)
                                                              let immb :=
                                                                (BitVec.slice __opcode 16 3)
                                                              let immh :=
                                                                (BitVec.slice __opcode 19 4)
                                                              (decode_sqrshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd
                                                                Rd Rn op immb immh)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__1029 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                         __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                           __opcode 29 23)) == (0b1011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                           __opcode 15 10)) == (0b100011#6 : (BitVec 6))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__1028 ← (( do
                                                                      readReg SEE ) : SailM Int )
                                                                    (pure (((w__1028 <b 928) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__1029 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 928
                                                                  let Rd :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let op :=
                                                                    (BitVec.slice __opcode 11 1)
                                                                  let immb :=
                                                                    (BitVec.slice __opcode 16 3)
                                                                  let immh :=
                                                                    (BitVec.slice __opcode 19 4)
                                                                  let Q :=
                                                                    (BitVec.slice __opcode 30 1)
                                                                  (decode_sqrshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_simd
                                                                    Rd Rn op immb immh Q)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__1031 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                             __opcode 31 23)) == (0b011111110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                             __opcode 15 10)) == (0b100001#6 : (BitVec 6)))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__1030 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__1030 <b 929) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__1031 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 929
                                                                      let Rd :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let op :=
                                                                        (BitVec.slice __opcode 11 1)
                                                                      let immb :=
                                                                        (BitVec.slice __opcode 16 3)
                                                                      let immh :=
                                                                        (BitVec.slice __opcode 19 4)
                                                                      (decode_sqshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd
                                                                        Rd Rn op immb immh)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__1033 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                   __opcode 29 23)) == (0b1011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                   __opcode 15 10)) == (0b100001#6 : (BitVec 6))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__1032 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__1032 <b 930) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__1033 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 930
                                                                          let Rd :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let op :=
                                                                            (BitVec.slice __opcode
                                                                              11 1)
                                                                          let immb :=
                                                                            (BitVec.slice __opcode
                                                                              16 3)
                                                                          let immh :=
                                                                            (BitVec.slice __opcode
                                                                              19 4)
                                                                          let Q :=
                                                                            (BitVec.slice __opcode
                                                                              30 1)
                                                                          (decode_sqshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_simd
                                                                            Rd Rn op immb immh Q)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__1035 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 23)) == (0b010111110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                     __opcode 15 10)) == (0b011101#6 : (BitVec 6)))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__1034 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__1034 <b 931) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__1035 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 931
                                                                              let Rd :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let op :=
                                                                                (BitVec.slice
                                                                                  __opcode 12 1)
                                                                              let immb :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 3)
                                                                              let immh :=
                                                                                (BitVec.slice
                                                                                  __opcode 19 4)
                                                                              let U :=
                                                                                (BitVec.slice
                                                                                  __opcode 29 1)
                                                                              (decode_sqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_sisd
                                                                                Rd Rn op immb immh U)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__1037 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           29 23)) == (0b0011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           15 10)) == (0b011101#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__1036 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__1036 <b 932) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__1037 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 932
                                                                                  let Rd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let op :=
                                                                                    (BitVec.slice
                                                                                      __opcode 12 1)
                                                                                  let immb :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 3)
                                                                                  let immh :=
                                                                                    (BitVec.slice
                                                                                      __opcode 19 4)
                                                                                  let U :=
                                                                                    (BitVec.slice
                                                                                      __opcode 29 1)
                                                                                  let Q :=
                                                                                    (BitVec.slice
                                                                                      __opcode 30 1)
                                                                                  (decode_sqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_simd
                                                                                    Rd Rn op immb
                                                                                    immh U Q)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__1039 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 23)) == (0b011111110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             15 10)) == (0b011001#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__1038 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__1038 <b 933) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__1039 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 933
                                                                                      let Rd :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          5)
                                                                                      let Rn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let op :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          12 1)
                                                                                      let immb :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 3)
                                                                                      let immh :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          19 4)
                                                                                      let U :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          29 1)
                                                                                      (decode_sqshlu_advsimd_aarch64_instrs_vector_shift_left_sat_sisd
                                                                                        Rd Rn op
                                                                                        immb immh U)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__1041 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   29
                                                                                                   23)) == (0b1011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   15
                                                                                                   10)) == (0b011001#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__1040 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__1040 <b 934) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__1041 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 934
                                                                                          let Rd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 5)
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let op :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              12 1)
                                                                                          let immb :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 3)
                                                                                          let immh :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              19 4)
                                                                                          let U :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              29 1)
                                                                                          let Q :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              30 1)
                                                                                          (decode_sqshlu_advsimd_aarch64_instrs_vector_shift_left_sat_simd
                                                                                            Rd Rn op
                                                                                            immb
                                                                                            immh U Q)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__1043 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     23)) == (0b011111110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     15
                                                                                                     10)) == (0b011101#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__1042 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__1042 <b 935) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__1043 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 935
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
                                                                                              let immb :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  3)
                                                                                              let immh :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  19
                                                                                                  4)
                                                                                              let U :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  29
                                                                                                  1)
                                                                                              (decode_uqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_sisd
                                                                                                Rd
                                                                                                Rn
                                                                                                op
                                                                                                immb
                                                                                                immh
                                                                                                U)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__1045 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           29
                                                                                                           23)) == (0b1011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           15
                                                                                                           10)) == (0b011101#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__1044 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__1044 <b 936) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__1045 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 936
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
                                                                                                  let immb :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      3)
                                                                                                  let immh :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      19
                                                                                                      4)
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
                                                                                                  (decode_uqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_simd
                                                                                                    Rd
                                                                                                    Rn
                                                                                                    op
                                                                                                    immb
                                                                                                    immh
                                                                                                    U
                                                                                                    Q)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__1047 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             24)) == (0x5E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               21
                                                                                                               21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               15
                                                                                                               10)) == (0b001011#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__1046 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__1046 <b 937) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__1047 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 937
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
                                                                                                      let size :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          22
                                                                                                          2)
                                                                                                      let U :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          29
                                                                                                          1)
                                                                                                      (decode_sqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd
                                                                                                        Rd
                                                                                                        Rn
                                                                                                        Rm
                                                                                                        size
                                                                                                        U)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__1049 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   29
                                                                                                                   24)) == (0b001110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     21
                                                                                                                     21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     15
                                                                                                                     10)) == (0b001011#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__1048 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__1048 <b 938) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__1049 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 938
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
                                                                                                          let size :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              22
                                                                                                              2)
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
                                                                                                          (decode_sqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_simd
                                                                                                            Rd
                                                                                                            Rn
                                                                                                            Rm
                                                                                                            size
                                                                                                            U
                                                                                                            Q)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__1051 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     24)) == (0x7E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       21
                                                                                                                       21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       15
                                                                                                                       10)) == (0b001011#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__1050 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__1050 <b 939) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__1051 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 939
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
                                                                                                              let size :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  22
                                                                                                                  2)
                                                                                                              let U :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  29
                                                                                                                  1)
                                                                                                              (decode_uqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd
                                                                                                                Rd
                                                                                                                Rn
                                                                                                                Rm
                                                                                                                size
                                                                                                                U)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__1053 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           29
                                                                                                                           24)) == (0b101110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             21
                                                                                                                             21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             15
                                                                                                                             10)) == (0b001011#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__1052 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__1052 <b 940) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__1053 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 940
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
                                                                                                                  let size :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      22
                                                                                                                      2)
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
                                                                                                                  (decode_uqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_simd
                                                                                                                    Rd
                                                                                                                    Rn
                                                                                                                    Rm
                                                                                                                    size
                                                                                                                    U
                                                                                                                    Q)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__1055 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             24)) == (0x5E#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             21
                                                                                                                             10)) == (0x852#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__1054 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__1054 <b 941) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__1055 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 941
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
                                                                                                                      let size :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          22
                                                                                                                          2)
                                                                                                                      let U :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          29
                                                                                                                          1)
                                                                                                                      (decode_sqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd
                                                                                                                        Rd
                                                                                                                        Rn
                                                                                                                        size
                                                                                                                        U)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__1057 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   29
                                                                                                                                   24)) == (0b001110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   21
                                                                                                                                   10)) == (0x852#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__1056 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__1056 <b 942) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__1057 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 942
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
                                                                                                                          let size :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              22
                                                                                                                              2)
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
                                                                                                                          (decode_sqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_simd
                                                                                                                            Rd
                                                                                                                            Rn
                                                                                                                            size
                                                                                                                            U
                                                                                                                            Q)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__1059 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     24)) == (0x7E#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     21
                                                                                                                                     10)) == (0x852#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__1058 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__1058 <b 943) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__1059 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 943
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
                                                                                                                              let size :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  22
                                                                                                                                  2)
                                                                                                                              let U :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  29
                                                                                                                                  1)
                                                                                                                              (decode_uqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd
                                                                                                                                Rd
                                                                                                                                Rn
                                                                                                                                size
                                                                                                                                U)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__1061 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           29
                                                                                                                                           24)) == (0b101110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           21
                                                                                                                                           10)) == (0x852#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__1060 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__1060 <b 944) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__1061 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 944
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
                                                                                                                                  let size :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      22
                                                                                                                                      2)
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
                                                                                                                                  (decode_uqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_simd
                                                                                                                                    Rd
                                                                                                                                    Rn
                                                                                                                                    size
                                                                                                                                    U
                                                                                                                                    Q)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__1063 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             24)) == (0x7E#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             21
                                                                                                                                             10)) == (0x84A#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__1062 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__1062 <b 945) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__1063 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 945
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
                                                                                                                                      let size :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          22
                                                                                                                                          2)
                                                                                                                                      (decode_sqxtun_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_sisd
                                                                                                                                        Rd
                                                                                                                                        Rn
                                                                                                                                        size)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__1065 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   29
                                                                                                                                                   24)) == (0b101110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   21
                                                                                                                                                   10)) == (0x84A#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__1064 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__1064 <b 946) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__1065 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 946
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
                                                                                                                                          let size :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              22
                                                                                                                                              2)
                                                                                                                                          let Q :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              30
                                                                                                                                              1)
                                                                                                                                          (decode_sqxtun_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_simd
                                                                                                                                            Rd
                                                                                                                                            Rn
                                                                                                                                            size
                                                                                                                                            Q)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__1067 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       29
                                                                                                                                                       24)) == (0b001110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         21
                                                                                                                                                         21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         15
                                                                                                                                                         10)) == (0b000101#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__1066 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__1066 <b 947) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__1067 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 947
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
                                                                                                                                              let size :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  22
                                                                                                                                                  2)
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
                                                                                                                                              (decode_srhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding
                                                                                                                                                Rd
                                                                                                                                                Rn
                                                                                                                                                Rm
                                                                                                                                                size
                                                                                                                                                U
                                                                                                                                                Q)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__1069 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         31
                                                                                                                                                         31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           29
                                                                                                                                                           24)) == (0b101110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             21
                                                                                                                                                             21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             15
                                                                                                                                                             10)) == (0b000101#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__1068 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__1068 <b 948) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__1069 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 948
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
                                                                                                                                                  let size :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      22
                                                                                                                                                      2)
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
                                                                                                                                                  (decode_urhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding
                                                                                                                                                    Rd
                                                                                                                                                    Rn
                                                                                                                                                    Rm
                                                                                                                                                    size
                                                                                                                                                    U
                                                                                                                                                    Q)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__1071 ← (( do
                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             31
                                                                                                                                                             23)) == (0b011111110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             15
                                                                                                                                                             10)) == (0b010001#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__1070 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__1070 <b 949) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__1071 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 949
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
                                                                                                                                                      let immb :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          16
                                                                                                                                                          3)
                                                                                                                                                      let immh :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          19
                                                                                                                                                          4)
                                                                                                                                                      (decode_sri_advsimd_aarch64_instrs_vector_shift_right_insert_sisd
                                                                                                                                                        Rd
                                                                                                                                                        Rn
                                                                                                                                                        immb
                                                                                                                                                        immh)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (pure true)))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
