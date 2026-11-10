import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0937
import ArmFull.Fn.M1023
import ArmFull.Fn.M1024

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
def __DecodeA64_DataProcFPSIMD__seg14 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__1073 ← (( do
    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
               __opcode 29 23)) == (0b1011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
               __opcode 15 10)) == (0b010001#6 : (BitVec 6))))) : Bool) : Bool)
    then
      (do
        let w__1072 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__1072 <b 950) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1073 : Bool)
  then
    (do
      writeReg SEE 950
      let Rd := (BitVec.slice __opcode 0 5)
      let Rn := (BitVec.slice __opcode 5 5)
      let immb := (BitVec.slice __opcode 16 3)
      let immh := (BitVec.slice __opcode 19 4)
      let Q := (BitVec.slice __opcode 30 1)
      (decode_sri_advsimd_aarch64_instrs_vector_shift_right_insert_simd Rd Rn immb immh Q)
      (pure false))
  else
    (do
      let w__1075 ← (( do
        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b010111110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                 __opcode 15 10)) == (0b001001#6 : (BitVec 6)))) : Bool) : Bool)
        then
          (do
            let w__1074 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__1074 <b 951) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__1075 : Bool)
      then
        (do
          writeReg SEE 951
          let Rd := (BitVec.slice __opcode 0 5)
          let Rn := (BitVec.slice __opcode 5 5)
          let o0 := (BitVec.slice __opcode 12 1)
          let o1 := (BitVec.slice __opcode 13 1)
          let immb := (BitVec.slice __opcode 16 3)
          let immh := (BitVec.slice __opcode 19 4)
          let U := (BitVec.slice __opcode 29 1)
          (decode_srshr_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1 immb immh U)
          (pure false))
      else
        (do
          let w__1077 ← (( do
            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                       __opcode 29 23)) == (0b0011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                       __opcode 15 10)) == (0b001001#6 : (BitVec 6))))) : Bool) : Bool)
            then
              (do
                let w__1076 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__1076 <b 952) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__1077 : Bool)
          then
            (do
              writeReg SEE 952
              let Rd := (BitVec.slice __opcode 0 5)
              let Rn := (BitVec.slice __opcode 5 5)
              let o0 := (BitVec.slice __opcode 12 1)
              let o1 := (BitVec.slice __opcode 13 1)
              let immb := (BitVec.slice __opcode 16 3)
              let immh := (BitVec.slice __opcode 19 4)
              let U := (BitVec.slice __opcode 29 1)
              let Q := (BitVec.slice __opcode 30 1)
              (decode_srshr_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0 o1 immb immh U Q)
              (pure false))
          else
            (do
              let w__1079 ← (( do
                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b010111110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                         __opcode 15 10)) == (0b001101#6 : (BitVec 6)))) : Bool) : Bool)
                then
                  (do
                    let w__1078 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__1078 <b 953) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__1079 : Bool)
              then
                (do
                  writeReg SEE 953
                  let Rd := (BitVec.slice __opcode 0 5)
                  let Rn := (BitVec.slice __opcode 5 5)
                  let o0 := (BitVec.slice __opcode 12 1)
                  let o1 := (BitVec.slice __opcode 13 1)
                  let immb := (BitVec.slice __opcode 16 3)
                  let immh := (BitVec.slice __opcode 19 4)
                  let U := (BitVec.slice __opcode 29 1)
                  (decode_srsra_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1 immb immh
                    U)
                  (pure false))
              else
                (do
                  let w__1081 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                               __opcode 29 23)) == (0b0011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                               __opcode 15 10)) == (0b001101#6 : (BitVec 6))))) : Bool) : Bool)
                    then
                      (do
                        let w__1080 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__1080 <b 954) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__1081 : Bool)
                  then
                    (do
                      writeReg SEE 954
                      let Rd := (BitVec.slice __opcode 0 5)
                      let Rn := (BitVec.slice __opcode 5 5)
                      let o0 := (BitVec.slice __opcode 12 1)
                      let o1 := (BitVec.slice __opcode 13 1)
                      let immb := (BitVec.slice __opcode 16 3)
                      let immh := (BitVec.slice __opcode 19 4)
                      let U := (BitVec.slice __opcode 29 1)
                      let Q := (BitVec.slice __opcode 30 1)
                      (decode_srsra_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0 o1 immb
                        immh U Q)
                      (pure false))
                  else
                    (do
                      let w__1083 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31
                                 23)) == (0b010111110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                 __opcode 15 10)) == (0b000001#6 : (BitVec 6)))) : Bool) : Bool)
                        then
                          (do
                            let w__1082 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__1082 <b 955) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__1083 : Bool)
                      then
                        (do
                          writeReg SEE 955
                          let Rd := (BitVec.slice __opcode 0 5)
                          let Rn := (BitVec.slice __opcode 5 5)
                          let o0 := (BitVec.slice __opcode 12 1)
                          let o1 := (BitVec.slice __opcode 13 1)
                          let immb := (BitVec.slice __opcode 16 3)
                          let immh := (BitVec.slice __opcode 19 4)
                          let U := (BitVec.slice __opcode 29 1)
                          (decode_sshr_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1
                            immb immh U)
                          (pure false))
                      else
                        (do
                          let w__1085 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode
                                     31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                       __opcode 29 23)) == (0b0011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                       __opcode 15 10)) == (0b000001#6 : (BitVec 6))))) : Bool) : Bool)
                            then
                              (do
                                let w__1084 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__1084 <b 956) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__1085 : Bool)
                          then
                            (do
                              writeReg SEE 956
                              let Rd := (BitVec.slice __opcode 0 5)
                              let Rn := (BitVec.slice __opcode 5 5)
                              let o0 := (BitVec.slice __opcode 12 1)
                              let o1 := (BitVec.slice __opcode 13 1)
                              let immb := (BitVec.slice __opcode 16 3)
                              let immh := (BitVec.slice __opcode 19 4)
                              let U := (BitVec.slice __opcode 29 1)
                              let Q := (BitVec.slice __opcode 30 1)
                              (decode_sshr_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0
                                o1 immb immh U Q)
                              (pure false))
                          else
                            (do
                              let w__1087 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                         __opcode 31 23)) == (0b010111110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                         __opcode 15 10)) == (0b000101#6 : (BitVec 6)))) : Bool) : Bool)
                                then
                                  (do
                                    let w__1086 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__1086 <b 957) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__1087 : Bool)
                              then
                                (do
                                  writeReg SEE 957
                                  let Rd := (BitVec.slice __opcode 0 5)
                                  let Rn := (BitVec.slice __opcode 5 5)
                                  let o0 := (BitVec.slice __opcode 12 1)
                                  let o1 := (BitVec.slice __opcode 13 1)
                                  let immb := (BitVec.slice __opcode 16 3)
                                  let immh := (BitVec.slice __opcode 19 4)
                                  let U := (BitVec.slice __opcode 29 1)
                                  (decode_ssra_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn
                                    o0 o1 immb immh U)
                                  (pure false))
                              else
                                (do
                                  let w__1089 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                               __opcode 29 23)) == (0b0011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                               __opcode 15 10)) == (0b000101#6 : (BitVec 6))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__1088 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__1088 <b 958) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__1089 : Bool)
                                  then
                                    (do
                                      writeReg SEE 958
                                      let Rd := (BitVec.slice __opcode 0 5)
                                      let Rn := (BitVec.slice __opcode 5 5)
                                      let o0 := (BitVec.slice __opcode 12 1)
                                      let o1 := (BitVec.slice __opcode 13 1)
                                      let immb := (BitVec.slice __opcode 16 3)
                                      let immh := (BitVec.slice __opcode 19 4)
                                      let U := (BitVec.slice __opcode 29 1)
                                      let Q := (BitVec.slice __opcode 30 1)
                                      (decode_ssra_advsimd_aarch64_instrs_vector_shift_right_simd Rd
                                        Rn o0 o1 immb immh U Q)
                                      (pure false))
                                  else
                                    (do
                                      let w__1091 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                 __opcode 31 23)) == (0b011111110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                 __opcode 15 10)) == (0b001001#6 : (BitVec 6)))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__1090 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__1090 <b 959) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__1091 : Bool)
                                      then
                                        (do
                                          writeReg SEE 959
                                          let Rd := (BitVec.slice __opcode 0 5)
                                          let Rn := (BitVec.slice __opcode 5 5)
                                          let o0 := (BitVec.slice __opcode 12 1)
                                          let o1 := (BitVec.slice __opcode 13 1)
                                          let immb := (BitVec.slice __opcode 16 3)
                                          let immh := (BitVec.slice __opcode 19 4)
                                          let U := (BitVec.slice __opcode 29 1)
                                          (decode_urshr_advsimd_aarch64_instrs_vector_shift_right_sisd
                                            Rd Rn o0 o1 immb immh U)
                                          (pure false))
                                      else
                                        (do
                                          let w__1093 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                     __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                       __opcode 29 23)) == (0b1011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                       __opcode 15 10)) == (0b001001#6 : (BitVec 6))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__1092 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__1092 <b 960) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__1093 : Bool)
                                          then
                                            (do
                                              writeReg SEE 960
                                              let Rd := (BitVec.slice __opcode 0 5)
                                              let Rn := (BitVec.slice __opcode 5 5)
                                              let o0 := (BitVec.slice __opcode 12 1)
                                              let o1 := (BitVec.slice __opcode 13 1)
                                              let immb := (BitVec.slice __opcode 16 3)
                                              let immh := (BitVec.slice __opcode 19 4)
                                              let U := (BitVec.slice __opcode 29 1)
                                              let Q := (BitVec.slice __opcode 30 1)
                                              (decode_urshr_advsimd_aarch64_instrs_vector_shift_right_simd
                                                Rd Rn o0 o1 immb immh U Q)
                                              (pure false))
                                          else
                                            (do
                                              let w__1095 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                         __opcode 31 23)) == (0b011111110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                         __opcode 15 10)) == (0b001101#6 : (BitVec 6)))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__1094 ← (( do readReg SEE ) : SailM Int
                                                      )
                                                    (pure (((w__1094 <b 961) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__1095 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 961
                                                  let Rd := (BitVec.slice __opcode 0 5)
                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                  let o0 := (BitVec.slice __opcode 12 1)
                                                  let o1 := (BitVec.slice __opcode 13 1)
                                                  let immb := (BitVec.slice __opcode 16 3)
                                                  let immh := (BitVec.slice __opcode 19 4)
                                                  let U := (BitVec.slice __opcode 29 1)
                                                  (decode_ursra_advsimd_aarch64_instrs_vector_shift_right_sisd
                                                    Rd Rn o0 o1 immb immh U)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__1097 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                             __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                               __opcode 29 23)) == (0b1011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                               __opcode 15 10)) == (0b001101#6 : (BitVec 6))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__1096 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__1096 <b 962) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__1097 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 962
                                                      let Rd := (BitVec.slice __opcode 0 5)
                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                      let o0 := (BitVec.slice __opcode 12 1)
                                                      let o1 := (BitVec.slice __opcode 13 1)
                                                      let immb := (BitVec.slice __opcode 16 3)
                                                      let immh := (BitVec.slice __opcode 19 4)
                                                      let U := (BitVec.slice __opcode 29 1)
                                                      let Q := (BitVec.slice __opcode 30 1)
                                                      (decode_ursra_advsimd_aarch64_instrs_vector_shift_right_simd
                                                        Rd Rn o0 o1 immb immh U Q)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__1099 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                 __opcode 31 23)) == (0b011111110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                 __opcode 15 10)) == (0b000001#6 : (BitVec 6)))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__1098 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__1098 <b 963) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__1099 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 963
                                                          let Rd := (BitVec.slice __opcode 0 5)
                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                          let o0 := (BitVec.slice __opcode 12 1)
                                                          let o1 := (BitVec.slice __opcode 13 1)
                                                          let immb := (BitVec.slice __opcode 16 3)
                                                          let immh := (BitVec.slice __opcode 19 4)
                                                          let U := (BitVec.slice __opcode 29 1)
                                                          (decode_ushr_advsimd_aarch64_instrs_vector_shift_right_sisd
                                                            Rd Rn o0 o1 immb immh U)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__1101 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                     __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                       __opcode 29 23)) == (0b1011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                       __opcode 15 10)) == (0b000001#6 : (BitVec 6))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__1100 ← (( do readReg SEE )
                                                                  : SailM Int )
                                                                (pure (((w__1100 <b 964) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__1101 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 964
                                                              let Rd := (BitVec.slice __opcode 0 5)
                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                              let o0 := (BitVec.slice __opcode 12 1)
                                                              let o1 := (BitVec.slice __opcode 13 1)
                                                              let immb :=
                                                                (BitVec.slice __opcode 16 3)
                                                              let immh :=
                                                                (BitVec.slice __opcode 19 4)
                                                              let U := (BitVec.slice __opcode 29 1)
                                                              let Q := (BitVec.slice __opcode 30 1)
                                                              (decode_ushr_advsimd_aarch64_instrs_vector_shift_right_simd
                                                                Rd Rn o0 o1 immb immh U Q)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__1103 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                         __opcode 31 23)) == (0b011111110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                         __opcode 15 10)) == (0b000101#6 : (BitVec 6)))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__1102 ← (( do
                                                                      readReg SEE ) : SailM Int )
                                                                    (pure (((w__1102 <b 965) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__1103 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 965
                                                                  let Rd :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let o0 :=
                                                                    (BitVec.slice __opcode 12 1)
                                                                  let o1 :=
                                                                    (BitVec.slice __opcode 13 1)
                                                                  let immb :=
                                                                    (BitVec.slice __opcode 16 3)
                                                                  let immh :=
                                                                    (BitVec.slice __opcode 19 4)
                                                                  let U :=
                                                                    (BitVec.slice __opcode 29 1)
                                                                  (decode_usra_advsimd_aarch64_instrs_vector_shift_right_sisd
                                                                    Rd Rn o0 o1 immb immh U)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__1105 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                             __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                               __opcode 29 23)) == (0b1011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                               __opcode 15 10)) == (0b000101#6 : (BitVec 6))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__1104 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__1104 <b 966) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__1105 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 966
                                                                      let Rd :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let o0 :=
                                                                        (BitVec.slice __opcode 12 1)
                                                                      let o1 :=
                                                                        (BitVec.slice __opcode 13 1)
                                                                      let immb :=
                                                                        (BitVec.slice __opcode 16 3)
                                                                      let immh :=
                                                                        (BitVec.slice __opcode 19 4)
                                                                      let U :=
                                                                        (BitVec.slice __opcode 29 1)
                                                                      let Q :=
                                                                        (BitVec.slice __opcode 30 1)
                                                                      (decode_usra_advsimd_aarch64_instrs_vector_shift_right_simd
                                                                        Rd Rn o0 o1 immb immh U Q)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__1107 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                   __opcode 29 23)) == (0b0011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                   __opcode 15 10)) == (0b101001#6 : (BitVec 6))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__1106 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__1106 <b 967) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__1107 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 967
                                                                          let Rd :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let immb :=
                                                                            (BitVec.slice __opcode
                                                                              16 3)
                                                                          let immh :=
                                                                            (BitVec.slice __opcode
                                                                              19 4)
                                                                          let U :=
                                                                            (BitVec.slice __opcode
                                                                              29 1)
                                                                          let Q :=
                                                                            (BitVec.slice __opcode
                                                                              30 1)
                                                                          (decode_sshll_advsimd_aarch64_instrs_vector_shift_left_long
                                                                            Rd Rn immb immh U Q)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__1109 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                       __opcode 29
                                                                                       23)) == (0b1011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                       __opcode 15
                                                                                       10)) == (0b101001#6 : (BitVec 6))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__1108 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__1108 <b 968) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__1109 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 968
                                                                              let Rd :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
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
                                                                              (decode_ushll_advsimd_aarch64_instrs_vector_shift_left_long
                                                                                Rd Rn immb immh U Q)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__1111 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           29 22)) == (0x3C#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             15 12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             10 10)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__1110 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__1110 <b 993) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__1111 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 993
                                                                                  let Rd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let H :=
                                                                                    (BitVec.slice
                                                                                      __opcode 11 1)
                                                                                  let Rm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 4)
                                                                                  let M :=
                                                                                    (BitVec.slice
                                                                                      __opcode 20 1)
                                                                                  let L :=
                                                                                    (BitVec.slice
                                                                                      __opcode 21 1)
                                                                                  let US :=
                                                                                    (BitVec.slice
                                                                                      __opcode 23 1)
                                                                                  let Q :=
                                                                                    (BitVec.slice
                                                                                      __opcode 30 1)
                                                                                  (decode_sudot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mat_mul_int_dotp
                                                                                    Rd Rn H Rm M L
                                                                                    US Q)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__1113 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               29 22)) == (0x3E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 15
                                                                                                 12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 10
                                                                                                 10)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__1112 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__1112 <b 994) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__1113 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 994
                                                                                      let Rd :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          5)
                                                                                      let Rn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let H :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          11 1)
                                                                                      let Rm :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 4)
                                                                                      let M :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          20 1)
                                                                                      let L :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          21 1)
                                                                                      let US :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          23 1)
                                                                                      let Q :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          30 1)
                                                                                      (decode_usdot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mat_mul_int_dotp
                                                                                        Rd Rn H Rm M
                                                                                        L US Q)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__1115 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 24)) == (0x5E#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 21
                                                                                                 10)) == (0x80E#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__1114 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__1114 <b 995) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__1115 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 995
                                                                                          let Rd :=
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
                                                                                              22 2)
                                                                                          let U :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              29 1)
                                                                                          (decode_suqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd
                                                                                            Rd Rn
                                                                                            size U)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__1117 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       29
                                                                                                       24)) == (0b001110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       21
                                                                                                       10)) == (0x80E#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__1116 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__1116 <b 996) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__1117 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 996
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
                                                                                              (decode_suqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_simd
                                                                                                Rd
                                                                                                Rn
                                                                                                size
                                                                                                U Q)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__1119 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         24)) == (0x7E#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         21
                                                                                                         10)) == (0x80E#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__1118 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__1118 <b 997) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__1119 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 997
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
                                                                                                  (decode_usqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd
                                                                                                    Rd
                                                                                                    Rn
                                                                                                    size
                                                                                                    U)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__1121 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               29
                                                                                                               24)) == (0b101110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               21
                                                                                                               10)) == (0x80E#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__1120 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__1120 <b 998) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__1121 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 998
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
                                                                                                      (decode_usqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_simd
                                                                                                        Rd
                                                                                                        Rn
                                                                                                        size
                                                                                                        U
                                                                                                        Q)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__1123 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   29
                                                                                                                   21)) == (0b001110000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     15
                                                                                                                     15)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     12
                                                                                                                     10)) == (0b000#3 : (BitVec 3)))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__1122 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__1122 <b 1007) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__1123 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 1007
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
                                                                                                          let len :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              13
                                                                                                              2)
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
                                                                                                          (decode_tbl_advsimd_aarch64_instrs_vector_transfer_vector_table
                                                                                                            Rd
                                                                                                            Rn
                                                                                                            op
                                                                                                            len
                                                                                                            Rm
                                                                                                            Q)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__1125 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       29
                                                                                                                       21)) == (0b001110000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         15
                                                                                                                         15)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         12
                                                                                                                         10)) == (0b100#3 : (BitVec 3)))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__1124 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__1124 <b 1008) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__1125 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 1008
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
                                                                                                              let len :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  13
                                                                                                                  2)
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
                                                                                                              (decode_tbx_advsimd_aarch64_instrs_vector_transfer_vector_table
                                                                                                                Rd
                                                                                                                Rn
                                                                                                                op
                                                                                                                len
                                                                                                                Rm
                                                                                                                Q)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__1127 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           29
                                                                                                                           24)) == (0b001110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             21
                                                                                                                             21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             15
                                                                                                                             10)) == (0b001010#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__1126 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__1126 <b 1013) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__1127 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 1013
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
                                                                                                                      14
                                                                                                                      1)
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
                                                                                                                  let Q :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      30
                                                                                                                      1)
                                                                                                                  (decode_trn1_advsimd_aarch64_instrs_vector_transfer_vector_permute_transpose
                                                                                                                    Rd
                                                                                                                    Rn
                                                                                                                    op
                                                                                                                    Rm
                                                                                                                    size
                                                                                                                    Q)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__1129 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               29
                                                                                                                               24)) == (0b001110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 21
                                                                                                                                 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 15
                                                                                                                                 10)) == (0b011010#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__1128 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__1128 <b 1014) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__1129 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 1014
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
                                                                                                                          14
                                                                                                                          1)
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
                                                                                                                      let Q :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          30
                                                                                                                          1)
                                                                                                                      (decode_trn2_advsimd_aarch64_instrs_vector_transfer_vector_permute_transpose
                                                                                                                        Rd
                                                                                                                        Rn
                                                                                                                        op
                                                                                                                        Rm
                                                                                                                        size
                                                                                                                        Q)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__1131 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   29
                                                                                                                                   21)) == (0b001110000#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   15
                                                                                                                                   10)) == (0b001111#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__1130 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__1130 <b 1022) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__1131 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 1022
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
                                                                                                                          let imm5 :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              5)
                                                                                                                          let Q :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              30
                                                                                                                              1)
                                                                                                                          (decode_umov_advsimd_aarch64_instrs_vector_transfer_integer_move_unsigned
                                                                                                                            Rd
                                                                                                                            Rn
                                                                                                                            imm5
                                                                                                                            Q)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__1133 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       29
                                                                                                                                       23)) == (0b0011101#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       21
                                                                                                                                       10)) == (0x872#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__1132 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__1132 <b 1023) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__1133 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 1023
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
                                                                                                                              (decode_urecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_int
                                                                                                                                Rd
                                                                                                                                Rn
                                                                                                                                sz
                                                                                                                                Q)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__1135 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           29
                                                                                                                                           23)) == (0b1011101#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           21
                                                                                                                                           10)) == (0x872#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__1134 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__1134 <b 1024) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__1135 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 1024
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
                                                                                                                                  (decode_ursqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_int
                                                                                                                                    Rd
                                                                                                                                    Rn
                                                                                                                                    sz
                                                                                                                                    Q)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__1137 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               29
                                                                                                                                               21)) == (0b001110100#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               15
                                                                                                                                               10)) == (0b100111#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__1136 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__1136 <b 1025) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__1137 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 1025
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
                                                                                                                                      (decode_usdot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_usdot
                                                                                                                                        Rd
                                                                                                                                        Rn
                                                                                                                                        Rm
                                                                                                                                        Q)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__1139 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   29
                                                                                                                                                   24)) == (0b001110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     21
                                                                                                                                                     21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     15
                                                                                                                                                     10)) == (0b000110#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__1138 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__1138 <b 1026) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__1139 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 1026
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
                                                                                                                                              14
                                                                                                                                              1)
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
                                                                                                                                          let Q :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              30
                                                                                                                                              1)
                                                                                                                                          (decode_uzp1_advsimd_aarch64_instrs_vector_transfer_vector_permute_unzip
                                                                                                                                            Rd
                                                                                                                                            Rn
                                                                                                                                            op
                                                                                                                                            Rm
                                                                                                                                            size
                                                                                                                                            Q)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__1141 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       29
                                                                                                                                                       24)) == (0b001110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         21
                                                                                                                                                         21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         15
                                                                                                                                                         10)) == (0b010110#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__1140 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__1140 <b 1027) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__1141 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 1027
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
                                                                                                                                                  14
                                                                                                                                                  1)
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
                                                                                                                                              let Q :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  30
                                                                                                                                                  1)
                                                                                                                                              (decode_uzp2_advsimd_aarch64_instrs_vector_transfer_vector_permute_unzip
                                                                                                                                                Rd
                                                                                                                                                Rn
                                                                                                                                                op
                                                                                                                                                Rm
                                                                                                                                                size
                                                                                                                                                Q)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__1143 ← (( do
                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       31
                                                                                                                                                       21)) == (0b11001110100#11 : (BitVec 11))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__1142 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__1142 <b 1031) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__1143 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 1031
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
                                                                                                                                                  let imm6 :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      10
                                                                                                                                                      6)
                                                                                                                                                  let Rm :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      16
                                                                                                                                                      5)
                                                                                                                                                  (decode_xar_advsimd_aarch64_instrs_vector_crypto_sha3_xar
                                                                                                                                                    Rd
                                                                                                                                                    Rn
                                                                                                                                                    imm6
                                                                                                                                                    Rm)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (pure true))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
