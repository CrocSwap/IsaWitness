import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M1020
import ArmFull.Fn.M1021

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
def __DecodeA64_DataProcFPSIMD__seg12 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__935 ← (( do
    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x5E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
               __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
               __opcode 15 10)) == (0b101100#6 : (BitVec 6))))) : Bool) : Bool)
    then
      (do
        let w__934 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__934 <b 881) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__935 : Bool)
  then
    (do
      writeReg SEE 881
      let Rd := (BitVec.slice __opcode 0 5)
      let Rn := (BitVec.slice __opcode 5 5)
      let o1 := (BitVec.slice __opcode 13 1)
      let Rm := (BitVec.slice __opcode 16 5)
      let size := (BitVec.slice __opcode 22 2)
      (decode_sqdmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd
        Rd Rn o1 Rm size)
      (pure false))
  else
    (do
      let w__937 ← (( do
        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                   __opcode 29 24)) == (0b001110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                     __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                     __opcode 15 10)) == (0b101100#6 : (BitVec 6)))))) : Bool) : Bool)
        then
          (do
            let w__936 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__936 <b 882) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__937 : Bool)
      then
        (do
          writeReg SEE 882
          let Rd := (BitVec.slice __opcode 0 5)
          let Rn := (BitVec.slice __opcode 5 5)
          let o1 := (BitVec.slice __opcode 13 1)
          let Rm := (BitVec.slice __opcode 16 5)
          let size := (BitVec.slice __opcode 22 2)
          let Q := (BitVec.slice __opcode 30 1)
          (decode_sqdmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_simd
            Rd Rn o1 Rm size Q)
          (pure false))
      else
        (do
          let w__939 ← (( do
            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x5E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                       __opcode 15 10)) == (0b101101#6 : (BitVec 6))))) : Bool) : Bool)
            then
              (do
                let w__938 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__938 <b 883) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__939 : Bool)
          then
            (do
              writeReg SEE 883
              let Rd := (BitVec.slice __opcode 0 5)
              let Rn := (BitVec.slice __opcode 5 5)
              let Rm := (BitVec.slice __opcode 16 5)
              let size := (BitVec.slice __opcode 22 2)
              let U := (BitVec.slice __opcode 29 1)
              (decode_sqdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd
                Rd Rn Rm size U)
              (pure false))
          else
            (do
              let w__941 ← (( do
                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                           __opcode 29 24)) == (0b001110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                             __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                             __opcode 15 10)) == (0b101101#6 : (BitVec 6)))))) : Bool) : Bool)
                then
                  (do
                    let w__940 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__940 <b 884) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__941 : Bool)
              then
                (do
                  writeReg SEE 884
                  let Rd := (BitVec.slice __opcode 0 5)
                  let Rn := (BitVec.slice __opcode 5 5)
                  let Rm := (BitVec.slice __opcode 16 5)
                  let size := (BitVec.slice __opcode 22 2)
                  let U := (BitVec.slice __opcode 29 1)
                  let Q := (BitVec.slice __opcode 30 1)
                  (decode_sqdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_simd
                    Rd Rn Rm size U Q)
                  (pure false))
              else
                (do
                  let w__943 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x7E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                               __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                               __opcode 15 10)) == (0b101101#6 : (BitVec 6))))) : Bool) : Bool)
                    then
                      (do
                        let w__942 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__942 <b 885) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__943 : Bool)
                  then
                    (do
                      writeReg SEE 885
                      let Rd := (BitVec.slice __opcode 0 5)
                      let Rn := (BitVec.slice __opcode 5 5)
                      let Rm := (BitVec.slice __opcode 16 5)
                      let size := (BitVec.slice __opcode 22 2)
                      let U := (BitVec.slice __opcode 29 1)
                      (decode_sqrdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd
                        Rd Rn Rm size U)
                      (pure false))
                  else
                    (do
                      let w__945 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31
                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                   __opcode 29 24)) == (0b101110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                     __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                     __opcode 15 10)) == (0b101101#6 : (BitVec 6)))))) : Bool) : Bool)
                        then
                          (do
                            let w__944 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__944 <b 886) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__945 : Bool)
                      then
                        (do
                          writeReg SEE 886
                          let Rd := (BitVec.slice __opcode 0 5)
                          let Rn := (BitVec.slice __opcode 5 5)
                          let Rm := (BitVec.slice __opcode 16 5)
                          let size := (BitVec.slice __opcode 22 2)
                          let U := (BitVec.slice __opcode 29 1)
                          let Q := (BitVec.slice __opcode 30 1)
                          (decode_sqrdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_simd
                            Rd Rn Rm size U Q)
                          (pure false))
                      else
                        (do
                          let w__947 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode
                                     31 24)) == (0x5F#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                       __opcode 15 12)) == (0xC#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                       __opcode 10 10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                            then
                              (do
                                let w__946 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__946 <b 887) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__947 : Bool)
                          then
                            (do
                              writeReg SEE 887
                              let Rd := (BitVec.slice __opcode 0 5)
                              let Rn := (BitVec.slice __opcode 5 5)
                              let H := (BitVec.slice __opcode 11 1)
                              let op := (BitVec.slice __opcode 12 1)
                              let Rm := (BitVec.slice __opcode 16 4)
                              let M := (BitVec.slice __opcode 20 1)
                              let L := (BitVec.slice __opcode 21 1)
                              let size := (BitVec.slice __opcode 22 2)
                              (decode_sqdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd
                                Rd Rn H op Rm M L size)
                              (pure false))
                          else
                            (do
                              let w__949 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                         __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                           __opcode 29 24)) == (0b001111#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                             __opcode 15 12)) == (0xC#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             __opcode 10 10)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__948 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__948 <b 888) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__949 : Bool)
                              then
                                (do
                                  writeReg SEE 888
                                  let Rd := (BitVec.slice __opcode 0 5)
                                  let Rn := (BitVec.slice __opcode 5 5)
                                  let H := (BitVec.slice __opcode 11 1)
                                  let op := (BitVec.slice __opcode 12 1)
                                  let Rm := (BitVec.slice __opcode 16 4)
                                  let M := (BitVec.slice __opcode 20 1)
                                  let L := (BitVec.slice __opcode 21 1)
                                  let size := (BitVec.slice __opcode 22 2)
                                  let Q := (BitVec.slice __opcode 30 1)
                                  (decode_sqdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_simd
                                    Rd Rn H op Rm M L size Q)
                                  (pure false))
                              else
                                (do
                                  let w__951 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                             __opcode 31 24)) == (0x5F#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                               __opcode 15 12)) == (0xD#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                               __opcode 10 10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__950 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__950 <b 889) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__951 : Bool)
                                  then
                                    (do
                                      writeReg SEE 889
                                      let Rd := (BitVec.slice __opcode 0 5)
                                      let Rn := (BitVec.slice __opcode 5 5)
                                      let H := (BitVec.slice __opcode 11 1)
                                      let op := (BitVec.slice __opcode 12 1)
                                      let Rm := (BitVec.slice __opcode 16 4)
                                      let M := (BitVec.slice __opcode 20 1)
                                      let L := (BitVec.slice __opcode 21 1)
                                      let size := (BitVec.slice __opcode 22 2)
                                      (decode_sqrdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd
                                        Rd Rn H op Rm M L size)
                                      (pure false))
                                  else
                                    (do
                                      let w__953 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                   __opcode 29 24)) == (0b001111#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                     __opcode 15 12)) == (0xD#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                     __opcode 10 10)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__952 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__952 <b 890) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__953 : Bool)
                                      then
                                        (do
                                          writeReg SEE 890
                                          let Rd := (BitVec.slice __opcode 0 5)
                                          let Rn := (BitVec.slice __opcode 5 5)
                                          let H := (BitVec.slice __opcode 11 1)
                                          let op := (BitVec.slice __opcode 12 1)
                                          let Rm := (BitVec.slice __opcode 16 4)
                                          let M := (BitVec.slice __opcode 20 1)
                                          let L := (BitVec.slice __opcode 21 1)
                                          let size := (BitVec.slice __opcode 22 2)
                                          let Q := (BitVec.slice __opcode 30 1)
                                          (decode_sqrdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_simd
                                            Rd Rn H op Rm M L size Q)
                                          (pure false))
                                      else
                                        (do
                                          let w__955 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                     __opcode 31 24)) == (0x5E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                       __opcode 15 10)) == (0b110100#6 : (BitVec 6))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__954 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__954 <b 891) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__955 : Bool)
                                          then
                                            (do
                                              writeReg SEE 891
                                              let Rd := (BitVec.slice __opcode 0 5)
                                              let Rn := (BitVec.slice __opcode 5 5)
                                              let Rm := (BitVec.slice __opcode 16 5)
                                              let size := (BitVec.slice __opcode 22 2)
                                              (decode_sqdmull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_sisd
                                                Rd Rn Rm size)
                                              (pure false))
                                          else
                                            (do
                                              let w__957 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                         __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                           __opcode 29 24)) == (0b001110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                             __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                             __opcode 15 10)) == (0b110100#6 : (BitVec 6)))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__956 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__956 <b 892) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__957 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 892
                                                  let Rd := (BitVec.slice __opcode 0 5)
                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                  let Rm := (BitVec.slice __opcode 16 5)
                                                  let size := (BitVec.slice __opcode 22 2)
                                                  let Q := (BitVec.slice __opcode 30 1)
                                                  (decode_sqdmull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_simd
                                                    Rd Rn Rm size Q)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__959 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                             __opcode 31 24)) == (0x5F#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                               __opcode 15 12)) == (0xB#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 10 10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__958 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__958 <b 893) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__959 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 893
                                                      let Rd := (BitVec.slice __opcode 0 5)
                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                      let H := (BitVec.slice __opcode 11 1)
                                                      let Rm := (BitVec.slice __opcode 16 4)
                                                      let M := (BitVec.slice __opcode 20 1)
                                                      let L := (BitVec.slice __opcode 21 1)
                                                      let size := (BitVec.slice __opcode 22 2)
                                                      (decode_sqdmull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_double_sisd
                                                        Rd Rn H Rm M L size)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__961 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                 __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                   __opcode 29 24)) == (0b001111#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                     __opcode 15 12)) == (0xB#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                     __opcode 10 10)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__960 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__960 <b 894) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__961 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 894
                                                          let Rd := (BitVec.slice __opcode 0 5)
                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                          let H := (BitVec.slice __opcode 11 1)
                                                          let Rm := (BitVec.slice __opcode 16 4)
                                                          let M := (BitVec.slice __opcode 20 1)
                                                          let L := (BitVec.slice __opcode 21 1)
                                                          let size := (BitVec.slice __opcode 22 2)
                                                          let Q := (BitVec.slice __opcode 30 1)
                                                          (decode_sqdmull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_double_simd
                                                            Rd Rn H Rm M L size Q)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__963 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                     __opcode 31 24)) == (0x7E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                       __opcode 15 10)) == (0b100001#6 : (BitVec 6))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__962 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__962 <b 895) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__963 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 895
                                                              let Rd := (BitVec.slice __opcode 0 5)
                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                              let S := (BitVec.slice __opcode 11 1)
                                                              let Rm := (BitVec.slice __opcode 16 5)
                                                              let size :=
                                                                (BitVec.slice __opcode 22 2)
                                                              (decode_sqrdmlah_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd
                                                                Rd Rn S Rm size)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__965 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                         __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                           __opcode 29 24)) == (0b101110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                             __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                             __opcode 15 10)) == (0b100001#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__964 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__964 <b 896) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__965 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 896
                                                                  let Rd :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let S :=
                                                                    (BitVec.slice __opcode 11 1)
                                                                  let Rm :=
                                                                    (BitVec.slice __opcode 16 5)
                                                                  let size :=
                                                                    (BitVec.slice __opcode 22 2)
                                                                  let Q :=
                                                                    (BitVec.slice __opcode 30 1)
                                                                  (decode_sqrdmlah_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd
                                                                    Rd Rn S Rm size Q)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__967 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                             __opcode 31 24)) == (0x7E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                               __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                               __opcode 15 10)) == (0b100011#6 : (BitVec 6))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__966 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__966 <b 897) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__967 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 897
                                                                      let Rd :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let S :=
                                                                        (BitVec.slice __opcode 11 1)
                                                                      let Rm :=
                                                                        (BitVec.slice __opcode 16 5)
                                                                      let size :=
                                                                        (BitVec.slice __opcode 22 2)
                                                                      (decode_sqrdmlsh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd
                                                                        Rd Rn S Rm size)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__969 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                   __opcode 29 24)) == (0b101110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                     __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                     __opcode 15 10)) == (0b100011#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__968 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__968 <b 898) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__969 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 898
                                                                          let Rd :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let S :=
                                                                            (BitVec.slice __opcode
                                                                              11 1)
                                                                          let Rm :=
                                                                            (BitVec.slice __opcode
                                                                              16 5)
                                                                          let size :=
                                                                            (BitVec.slice __opcode
                                                                              22 2)
                                                                          let Q :=
                                                                            (BitVec.slice __opcode
                                                                              30 1)
                                                                          (decode_sqrdmlsh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd
                                                                            Rd Rn S Rm size Q)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__971 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 24)) == (0x7F#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                       __opcode 15
                                                                                       12)) == (0xD#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 10
                                                                                       10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__970 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__970 <b 899) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__971 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 899
                                                                              let Rd :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let H :=
                                                                                (BitVec.slice
                                                                                  __opcode 11 1)
                                                                              let S :=
                                                                                (BitVec.slice
                                                                                  __opcode 13 1)
                                                                              let Rm :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 4)
                                                                              let M :=
                                                                                (BitVec.slice
                                                                                  __opcode 20 1)
                                                                              let L :=
                                                                                (BitVec.slice
                                                                                  __opcode 21 1)
                                                                              let size :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 2)
                                                                              (decode_sqrdmlah_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd
                                                                                Rd Rn H S Rm M L
                                                                                size)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__973 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           29 24)) == (0b101111#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             15 12)) == (0xD#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             10 10)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__972 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__972 <b 900) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__973 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 900
                                                                                  let Rd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let H :=
                                                                                    (BitVec.slice
                                                                                      __opcode 11 1)
                                                                                  let S :=
                                                                                    (BitVec.slice
                                                                                      __opcode 13 1)
                                                                                  let Rm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 4)
                                                                                  let M :=
                                                                                    (BitVec.slice
                                                                                      __opcode 20 1)
                                                                                  let L :=
                                                                                    (BitVec.slice
                                                                                      __opcode 21 1)
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 2)
                                                                                  let Q :=
                                                                                    (BitVec.slice
                                                                                      __opcode 30 1)
                                                                                  (decode_sqrdmlah_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_simd
                                                                                    Rd Rn H S Rm M L
                                                                                    size Q)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__975 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 24)) == (0x7F#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               15 12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               10 10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__974 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__974 <b 901) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__975 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 901
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
                                                                                      let S :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          13 1)
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
                                                                                      let size :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 2)
                                                                                      (decode_sqrdmlsh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd
                                                                                        Rd Rn H S Rm
                                                                                        M L size)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__977 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   29
                                                                                                   24)) == (0b101111#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     15
                                                                                                     12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     10
                                                                                                     10)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__976 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__976 <b 902) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__977 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 902
                                                                                          let Rd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 5)
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let H :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              11 1)
                                                                                          let S :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              13 1)
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
                                                                                          let size :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 2)
                                                                                          let Q :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              30 1)
                                                                                          (decode_sqrdmlsh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_simd
                                                                                            Rd Rn H
                                                                                            S Rm M L
                                                                                            size Q)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__979 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     24)) == (0x5E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       21
                                                                                                       21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       15
                                                                                                       10)) == (0b010111#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__978 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__978 <b 903) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__979 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 903
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
                                                                                              let S :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  11
                                                                                                  1)
                                                                                              let R :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  12
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
                                                                                              let U :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  29
                                                                                                  1)
                                                                                              (decode_sqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd
                                                                                                Rd
                                                                                                Rn S
                                                                                                R Rm
                                                                                                size
                                                                                                U)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__981 ← (( do
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
                                                                                                             10)) == (0b010111#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__980 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__980 <b 904) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__981 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 904
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
                                                                                                  let S :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      11
                                                                                                      1)
                                                                                                  let R :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      12
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
                                                                                                  (decode_sqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd
                                                                                                    Rd
                                                                                                    Rn
                                                                                                    S
                                                                                                    R
                                                                                                    Rm
                                                                                                    size
                                                                                                    U
                                                                                                    Q)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__983 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             24)) == (0x5E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               21
                                                                                                               21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               15
                                                                                                               10)) == (0b010011#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__982 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__982 <b 905) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__983 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 905
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
                                                                                                      let S :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          11
                                                                                                          1)
                                                                                                      let R :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          12
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
                                                                                                      let U :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          29
                                                                                                          1)
                                                                                                      (decode_sqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd
                                                                                                        Rd
                                                                                                        Rn
                                                                                                        S
                                                                                                        R
                                                                                                        Rm
                                                                                                        size
                                                                                                        U)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__985 ← (( do
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
                                                                                                                     10)) == (0b010011#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__984 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__984 <b 906) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__985 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 906
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
                                                                                                          let S :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              11
                                                                                                              1)
                                                                                                          let R :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              12
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
                                                                                                          (decode_sqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd
                                                                                                            Rd
                                                                                                            Rn
                                                                                                            S
                                                                                                            R
                                                                                                            Rm
                                                                                                            size
                                                                                                            U
                                                                                                            Q)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__987 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     24)) == (0x5E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       21
                                                                                                                       21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       15
                                                                                                                       10)) == (0b010101#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__986 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__986 <b 907) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__987 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 907
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
                                                                                                              let S :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  11
                                                                                                                  1)
                                                                                                              let R :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  12
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
                                                                                                              let U :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  29
                                                                                                                  1)
                                                                                                              (decode_srshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd
                                                                                                                Rd
                                                                                                                Rn
                                                                                                                S
                                                                                                                R
                                                                                                                Rm
                                                                                                                size
                                                                                                                U)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__989 ← (( do
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
                                                                                                                             10)) == (0b010101#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__988 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__988 <b 908) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__989 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 908
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
                                                                                                                  let S :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      11
                                                                                                                      1)
                                                                                                                  let R :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      12
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
                                                                                                                  (decode_srshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd
                                                                                                                    Rd
                                                                                                                    Rn
                                                                                                                    S
                                                                                                                    R
                                                                                                                    Rm
                                                                                                                    size
                                                                                                                    U
                                                                                                                    Q)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__991 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             24)) == (0x5E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               21
                                                                                                                               21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               15
                                                                                                                               10)) == (0b010001#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__990 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__990 <b 909) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__991 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 909
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
                                                                                                                      let S :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          11
                                                                                                                          1)
                                                                                                                      let R :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          12
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
                                                                                                                      let U :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          29
                                                                                                                          1)
                                                                                                                      (decode_sshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd
                                                                                                                        Rd
                                                                                                                        Rn
                                                                                                                        S
                                                                                                                        R
                                                                                                                        Rm
                                                                                                                        size
                                                                                                                        U)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__993 ← (( do
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
                                                                                                                                     10)) == (0b010001#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__992 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__992 <b 910) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__993 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 910
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
                                                                                                                          let S :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              11
                                                                                                                              1)
                                                                                                                          let R :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              12
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
                                                                                                                          (decode_sshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd
                                                                                                                            Rd
                                                                                                                            Rn
                                                                                                                            S
                                                                                                                            R
                                                                                                                            Rm
                                                                                                                            size
                                                                                                                            U
                                                                                                                            Q)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__995 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     24)) == (0x7E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       21
                                                                                                                                       21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       15
                                                                                                                                       10)) == (0b010111#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__994 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__994 <b 911) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__995 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 911
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
                                                                                                                              let S :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  11
                                                                                                                                  1)
                                                                                                                              let R :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  12
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
                                                                                                                              let U :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  29
                                                                                                                                  1)
                                                                                                                              (decode_uqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd
                                                                                                                                Rd
                                                                                                                                Rn
                                                                                                                                S
                                                                                                                                R
                                                                                                                                Rm
                                                                                                                                size
                                                                                                                                U)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__997 ← (( do
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
                                                                                                                                             10)) == (0b010111#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__996 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__996 <b 912) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__997 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 912
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
                                                                                                                                  let S :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      11
                                                                                                                                      1)
                                                                                                                                  let R :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      12
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
                                                                                                                                  (decode_uqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd
                                                                                                                                    Rd
                                                                                                                                    Rn
                                                                                                                                    S
                                                                                                                                    R
                                                                                                                                    Rm
                                                                                                                                    size
                                                                                                                                    U
                                                                                                                                    Q)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (pure true))))))))))))))))))))))))))))))))


end ArmFull.Functions
