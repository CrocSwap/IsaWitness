import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M1019
import ArmFull.Fn.M1020

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
def __DecodeA64_DataProcFPSIMD__seg11 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__867 ← (( do
    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
               __opcode 29 24)) == (0b001110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
               __opcode 21 10)) == (0xC2A#12 : (BitVec 12))))) : Bool) : Bool)
    then
      (do
        let w__866 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__866 <b 842) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__867 : Bool)
  then
    (do
      writeReg SEE 842
      let Rd := (BitVec.slice __opcode 0 5)
      let Rn := (BitVec.slice __opcode 5 5)
      let op := (BitVec.slice __opcode 16 1)
      let size := (BitVec.slice __opcode 22 2)
      let U := (BitVec.slice __opcode 29 1)
      let Q := (BitVec.slice __opcode 30 1)
      (decode_smaxv_advsimd_aarch64_instrs_vector_reduce_int_max Rd Rn op size U Q)
      (pure false))
  else
    (do
      let w__869 ← (( do
        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                   __opcode 29 24)) == (0b001110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                   __opcode 21 10)) == (0xC6A#12 : (BitVec 12))))) : Bool) : Bool)
        then
          (do
            let w__868 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__868 <b 843) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__869 : Bool)
      then
        (do
          writeReg SEE 843
          let Rd := (BitVec.slice __opcode 0 5)
          let Rn := (BitVec.slice __opcode 5 5)
          let op := (BitVec.slice __opcode 16 1)
          let size := (BitVec.slice __opcode 22 2)
          let U := (BitVec.slice __opcode 29 1)
          let Q := (BitVec.slice __opcode 30 1)
          (decode_sminv_advsimd_aarch64_instrs_vector_reduce_int_max Rd Rn op size U Q)
          (pure false))
      else
        (do
          let w__871 ← (( do
            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                       __opcode 29 24)) == (0b101110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                       __opcode 21 10)) == (0xC2A#12 : (BitVec 12))))) : Bool) : Bool)
            then
              (do
                let w__870 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__870 <b 844) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__871 : Bool)
          then
            (do
              writeReg SEE 844
              let Rd := (BitVec.slice __opcode 0 5)
              let Rn := (BitVec.slice __opcode 5 5)
              let op := (BitVec.slice __opcode 16 1)
              let size := (BitVec.slice __opcode 22 2)
              let U := (BitVec.slice __opcode 29 1)
              let Q := (BitVec.slice __opcode 30 1)
              (decode_umaxv_advsimd_aarch64_instrs_vector_reduce_int_max Rd Rn op size U Q)
              (pure false))
          else
            (do
              let w__873 ← (( do
                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                           __opcode 29 24)) == (0b101110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                           __opcode 21 10)) == (0xC6A#12 : (BitVec 12))))) : Bool) : Bool)
                then
                  (do
                    let w__872 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__872 <b 845) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__873 : Bool)
              then
                (do
                  writeReg SEE 845
                  let Rd := (BitVec.slice __opcode 0 5)
                  let Rn := (BitVec.slice __opcode 5 5)
                  let op := (BitVec.slice __opcode 16 1)
                  let size := (BitVec.slice __opcode 22 2)
                  let U := (BitVec.slice __opcode 29 1)
                  let Q := (BitVec.slice __opcode 30 1)
                  (decode_uminv_advsimd_aarch64_instrs_vector_reduce_int_max Rd Rn op size U Q)
                  (pure false))
              else
                (do
                  let w__875 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                               __opcode 29 24)) == (0b001110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                 __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                 __opcode 15 10)) == (0b100000#6 : (BitVec 6)))))) : Bool) : Bool)
                    then
                      (do
                        let w__874 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__874 <b 849) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__875 : Bool)
                  then
                    (do
                      writeReg SEE 849
                      let Rd := (BitVec.slice __opcode 0 5)
                      let Rn := (BitVec.slice __opcode 5 5)
                      let o1 := (BitVec.slice __opcode 13 1)
                      let Rm := (BitVec.slice __opcode 16 5)
                      let size := (BitVec.slice __opcode 22 2)
                      let U := (BitVec.slice __opcode 29 1)
                      let Q := (BitVec.slice __opcode 30 1)
                      (decode_smlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum
                        Rd Rn o1 Rm size U Q)
                      (pure false))
                  else
                    (do
                      let w__877 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31
                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                   __opcode 29 24)) == (0b001110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                     __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                     __opcode 15 10)) == (0b101000#6 : (BitVec 6)))))) : Bool) : Bool)
                        then
                          (do
                            let w__876 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__876 <b 850) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__877 : Bool)
                      then
                        (do
                          writeReg SEE 850
                          let Rd := (BitVec.slice __opcode 0 5)
                          let Rn := (BitVec.slice __opcode 5 5)
                          let o1 := (BitVec.slice __opcode 13 1)
                          let Rm := (BitVec.slice __opcode 16 5)
                          let size := (BitVec.slice __opcode 22 2)
                          let U := (BitVec.slice __opcode 29 1)
                          let Q := (BitVec.slice __opcode 30 1)
                          (decode_smlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum
                            Rd Rn o1 Rm size U Q)
                          (pure false))
                      else
                        (do
                          let w__879 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode
                                     31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                       __opcode 29 24)) == (0b101110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                         __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                         __opcode 15 10)) == (0b100000#6 : (BitVec 6)))))) : Bool) : Bool)
                            then
                              (do
                                let w__878 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__878 <b 851) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__879 : Bool)
                          then
                            (do
                              writeReg SEE 851
                              let Rd := (BitVec.slice __opcode 0 5)
                              let Rn := (BitVec.slice __opcode 5 5)
                              let o1 := (BitVec.slice __opcode 13 1)
                              let Rm := (BitVec.slice __opcode 16 5)
                              let size := (BitVec.slice __opcode 22 2)
                              let U := (BitVec.slice __opcode 29 1)
                              let Q := (BitVec.slice __opcode 30 1)
                              (decode_umlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum
                                Rd Rn o1 Rm size U Q)
                              (pure false))
                          else
                            (do
                              let w__881 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                         __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                           __opcode 29 24)) == (0b101110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                             __opcode 15 10)) == (0b101000#6 : (BitVec 6)))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__880 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__880 <b 852) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__881 : Bool)
                              then
                                (do
                                  writeReg SEE 852
                                  let Rd := (BitVec.slice __opcode 0 5)
                                  let Rn := (BitVec.slice __opcode 5 5)
                                  let o1 := (BitVec.slice __opcode 13 1)
                                  let Rm := (BitVec.slice __opcode 16 5)
                                  let size := (BitVec.slice __opcode 22 2)
                                  let U := (BitVec.slice __opcode 29 1)
                                  let Q := (BitVec.slice __opcode 30 1)
                                  (decode_umlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum
                                    Rd Rn o1 Rm size U Q)
                                  (pure false))
                              else
                                (do
                                  let w__883 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                               __opcode 29 24)) == (0b001111#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                 __opcode 15 12)) == (0x2#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 __opcode 10 10)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__882 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__882 <b 853) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__883 : Bool)
                                  then
                                    (do
                                      writeReg SEE 853
                                      let Rd := (BitVec.slice __opcode 0 5)
                                      let Rn := (BitVec.slice __opcode 5 5)
                                      let H := (BitVec.slice __opcode 11 1)
                                      let o2 := (BitVec.slice __opcode 14 1)
                                      let Rm := (BitVec.slice __opcode 16 4)
                                      let M := (BitVec.slice __opcode 20 1)
                                      let L := (BitVec.slice __opcode 21 1)
                                      let size := (BitVec.slice __opcode 22 2)
                                      let U := (BitVec.slice __opcode 29 1)
                                      let Q := (BitVec.slice __opcode 30 1)
                                      (decode_smlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long
                                        Rd Rn H o2 Rm M L size U Q)
                                      (pure false))
                                  else
                                    (do
                                      let w__885 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                   __opcode 29 24)) == (0b001111#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                     __opcode 15 12)) == (0x6#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                     __opcode 10 10)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__884 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__884 <b 854) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__885 : Bool)
                                      then
                                        (do
                                          writeReg SEE 854
                                          let Rd := (BitVec.slice __opcode 0 5)
                                          let Rn := (BitVec.slice __opcode 5 5)
                                          let H := (BitVec.slice __opcode 11 1)
                                          let o2 := (BitVec.slice __opcode 14 1)
                                          let Rm := (BitVec.slice __opcode 16 4)
                                          let M := (BitVec.slice __opcode 20 1)
                                          let L := (BitVec.slice __opcode 21 1)
                                          let size := (BitVec.slice __opcode 22 2)
                                          let U := (BitVec.slice __opcode 29 1)
                                          let Q := (BitVec.slice __opcode 30 1)
                                          (decode_smlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long
                                            Rd Rn H o2 Rm M L size U Q)
                                          (pure false))
                                      else
                                        (do
                                          let w__887 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                     __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                       __opcode 29 24)) == (0b101111#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                         __opcode 15 12)) == (0x2#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                         __opcode 10 10)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__886 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__886 <b 855) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__887 : Bool)
                                          then
                                            (do
                                              writeReg SEE 855
                                              let Rd := (BitVec.slice __opcode 0 5)
                                              let Rn := (BitVec.slice __opcode 5 5)
                                              let H := (BitVec.slice __opcode 11 1)
                                              let o2 := (BitVec.slice __opcode 14 1)
                                              let Rm := (BitVec.slice __opcode 16 4)
                                              let M := (BitVec.slice __opcode 20 1)
                                              let L := (BitVec.slice __opcode 21 1)
                                              let size := (BitVec.slice __opcode 22 2)
                                              let U := (BitVec.slice __opcode 29 1)
                                              let Q := (BitVec.slice __opcode 30 1)
                                              (decode_umlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long
                                                Rd Rn H o2 Rm M L size U Q)
                                              (pure false))
                                          else
                                            (do
                                              let w__889 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                         __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                           __opcode 29 24)) == (0b101111#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                             __opcode 15 12)) == (0x6#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                             __opcode 10 10)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__888 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__888 <b 856) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__889 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 856
                                                  let Rd := (BitVec.slice __opcode 0 5)
                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                  let H := (BitVec.slice __opcode 11 1)
                                                  let o2 := (BitVec.slice __opcode 14 1)
                                                  let Rm := (BitVec.slice __opcode 16 4)
                                                  let M := (BitVec.slice __opcode 20 1)
                                                  let L := (BitVec.slice __opcode 21 1)
                                                  let size := (BitVec.slice __opcode 22 2)
                                                  let U := (BitVec.slice __opcode 29 1)
                                                  let Q := (BitVec.slice __opcode 30 1)
                                                  (decode_umlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long
                                                    Rd Rn H o2 Rm M L size U Q)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__891 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                             __opcode 31 21)) == (0b01001110100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                             __opcode 15 10)) == (0b101001#6 : (BitVec 6)))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__890 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__890 <b 857) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__891 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 857
                                                      let Rd := (BitVec.slice __opcode 0 5)
                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                      let B := (BitVec.slice __opcode 11 1)
                                                      let Rm := (BitVec.slice __opcode 16 5)
                                                      let U := (BitVec.slice __opcode 29 1)
                                                      (decode_smmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla
                                                        Rd Rn B Rm U)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__893 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                 __opcode 31 21)) == (0b01101110100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                 __opcode 15 10)) == (0b101001#6 : (BitVec 6)))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__892 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__892 <b 858) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__893 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 858
                                                          let Rd := (BitVec.slice __opcode 0 5)
                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                          let B := (BitVec.slice __opcode 11 1)
                                                          let Rm := (BitVec.slice __opcode 16 5)
                                                          let U := (BitVec.slice __opcode 29 1)
                                                          (decode_ummla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla
                                                            Rd Rn B Rm U)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__895 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                     __opcode 31 21)) == (0b01001110100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                     __opcode 15 10)) == (0b101011#6 : (BitVec 6)))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__894 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__894 <b 859) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__895 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 859
                                                              let Rd := (BitVec.slice __opcode 0 5)
                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                              let B := (BitVec.slice __opcode 11 1)
                                                              let Rm := (BitVec.slice __opcode 16 5)
                                                              let U := (BitVec.slice __opcode 29 1)
                                                              (decode_usmmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla
                                                                Rd Rn B Rm U)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__897 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                         __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                           __opcode 29 21)) == (0b001110000#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                           __opcode 15 10)) == (0b001011#6 : (BitVec 6))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__896 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__896 <b 860) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__897 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 860
                                                                  let Rd :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let imm5 :=
                                                                    (BitVec.slice __opcode 16 5)
                                                                  let Q :=
                                                                    (BitVec.slice __opcode 30 1)
                                                                  (decode_smov_advsimd_aarch64_instrs_vector_transfer_integer_move_signed
                                                                    Rd Rn imm5 Q)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__899 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                             __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                               __opcode 29 24)) == (0b001110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                 __opcode 15 10)) == (0b110000#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__898 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__898 <b 863) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__899 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 863
                                                                      let Rd :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let Rm :=
                                                                        (BitVec.slice __opcode 16 5)
                                                                      let size :=
                                                                        (BitVec.slice __opcode 22 2)
                                                                      let U :=
                                                                        (BitVec.slice __opcode 29 1)
                                                                      let Q :=
                                                                        (BitVec.slice __opcode 30 1)
                                                                      (decode_smull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product
                                                                        Rd Rn Rm size U Q)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__901 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                   __opcode 29 24)) == (0b101110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                     __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                     __opcode 15 10)) == (0b110000#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__900 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__900 <b 864) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__901 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 864
                                                                          let Rd :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let Rm :=
                                                                            (BitVec.slice __opcode
                                                                              16 5)
                                                                          let size :=
                                                                            (BitVec.slice __opcode
                                                                              22 2)
                                                                          let U :=
                                                                            (BitVec.slice __opcode
                                                                              29 1)
                                                                          let Q :=
                                                                            (BitVec.slice __opcode
                                                                              30 1)
                                                                          (decode_umull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product
                                                                            Rd Rn Rm size U Q)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__903 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                       __opcode 29
                                                                                       24)) == (0b001111#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                         __opcode 15
                                                                                         12)) == (0xA#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                         __opcode 10
                                                                                         10)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__902 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__902 <b 865) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__903 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 865
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
                                                                              let size :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 2)
                                                                              let U :=
                                                                                (BitVec.slice
                                                                                  __opcode 29 1)
                                                                              let Q :=
                                                                                (BitVec.slice
                                                                                  __opcode 30 1)
                                                                              (decode_smull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_long
                                                                                Rd Rn H Rm M L size
                                                                                U Q)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__905 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           29 24)) == (0b101111#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             15 12)) == (0xA#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             10 10)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__904 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__904 <b 866) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__905 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 866
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
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 2)
                                                                                  let U :=
                                                                                    (BitVec.slice
                                                                                      __opcode 29 1)
                                                                                  let Q :=
                                                                                    (BitVec.slice
                                                                                      __opcode 30 1)
                                                                                  (decode_umull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_long
                                                                                    Rd Rn H Rm M L
                                                                                    size U Q)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__907 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 24)) == (0x5E#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             21 10)) == (0x81E#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__906 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__906 <b 867) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__907 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 867
                                                                                      let Rd :=
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
                                                                                          22 2)
                                                                                      let U :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          29 1)
                                                                                      (decode_sqabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd
                                                                                        Rd Rn size U)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__909 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   29
                                                                                                   24)) == (0b001110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   21
                                                                                                   10)) == (0x81E#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__908 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__908 <b 868) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__909 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 868
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
                                                                                          let Q :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              30 1)
                                                                                          (decode_sqabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_simd
                                                                                            Rd Rn
                                                                                            size U Q)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__911 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     24)) == (0x7E#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     21
                                                                                                     10)) == (0x81E#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__910 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__910 <b 869) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__911 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 869
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
                                                                                              (decode_sqneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd
                                                                                                Rd
                                                                                                Rn
                                                                                                size
                                                                                                U)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__913 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           29
                                                                                                           24)) == (0b101110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           21
                                                                                                           10)) == (0x81E#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__912 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__912 <b 870) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__913 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 870
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
                                                                                                  (decode_sqneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_simd
                                                                                                    Rd
                                                                                                    Rn
                                                                                                    size
                                                                                                    U
                                                                                                    Q)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__915 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             24)) == (0x5E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               21
                                                                                                               21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               15
                                                                                                               10)) == (0b000011#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__914 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__914 <b 871) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__915 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 871
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
                                                                                                      (decode_sqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd
                                                                                                        Rd
                                                                                                        Rn
                                                                                                        Rm
                                                                                                        size
                                                                                                        U)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__917 ← (( do
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
                                                                                                                     10)) == (0b000011#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__916 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__916 <b 872) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__917 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 872
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
                                                                                                          (decode_sqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_simd
                                                                                                            Rd
                                                                                                            Rn
                                                                                                            Rm
                                                                                                            size
                                                                                                            U
                                                                                                            Q)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__919 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     24)) == (0x7E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       21
                                                                                                                       21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       15
                                                                                                                       10)) == (0b000011#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__918 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__918 <b 873) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__919 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 873
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
                                                                                                              (decode_uqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd
                                                                                                                Rd
                                                                                                                Rn
                                                                                                                Rm
                                                                                                                size
                                                                                                                U)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__921 ← (( do
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
                                                                                                                             10)) == (0b000011#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__920 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__920 <b 874) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__921 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 874
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
                                                                                                                  (decode_uqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_simd
                                                                                                                    Rd
                                                                                                                    Rn
                                                                                                                    Rm
                                                                                                                    size
                                                                                                                    U
                                                                                                                    Q)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__923 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             24)) == (0x5F#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               15
                                                                                                                               12)) == (0x3#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               10
                                                                                                                               10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__922 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__922 <b 875) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__923 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 875
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
                                                                                                                      let o2 :=
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
                                                                                                                      let size :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          22
                                                                                                                          2)
                                                                                                                      (decode_sqdmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd
                                                                                                                        Rd
                                                                                                                        Rn
                                                                                                                        H
                                                                                                                        o2
                                                                                                                        Rm
                                                                                                                        M
                                                                                                                        L
                                                                                                                        size)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__925 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   29
                                                                                                                                   24)) == (0b001111#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     15
                                                                                                                                     12)) == (0x3#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     10
                                                                                                                                     10)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__924 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__924 <b 876) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__925 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 876
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
                                                                                                                          let o2 :=
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
                                                                                                                          (decode_sqdmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_simd
                                                                                                                            Rd
                                                                                                                            Rn
                                                                                                                            H
                                                                                                                            o2
                                                                                                                            Rm
                                                                                                                            M
                                                                                                                            L
                                                                                                                            size
                                                                                                                            Q)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__927 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     24)) == (0x5F#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       15
                                                                                                                                       12)) == (0x7#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       10
                                                                                                                                       10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__926 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__926 <b 877) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__927 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 877
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
                                                                                                                              let o2 :=
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
                                                                                                                              let size :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  22
                                                                                                                                  2)
                                                                                                                              (decode_sqdmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd
                                                                                                                                Rd
                                                                                                                                Rn
                                                                                                                                H
                                                                                                                                o2
                                                                                                                                Rm
                                                                                                                                M
                                                                                                                                L
                                                                                                                                size)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__929 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           29
                                                                                                                                           24)) == (0b001111#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             15
                                                                                                                                             12)) == (0x7#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             10
                                                                                                                                             10)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__928 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__928 <b 878) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__929 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 878
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
                                                                                                                                  let o2 :=
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
                                                                                                                                  (decode_sqdmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_simd
                                                                                                                                    Rd
                                                                                                                                    Rn
                                                                                                                                    H
                                                                                                                                    o2
                                                                                                                                    Rm
                                                                                                                                    M
                                                                                                                                    L
                                                                                                                                    size
                                                                                                                                    Q)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__931 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             24)) == (0x5E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               21
                                                                                                                                               21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               15
                                                                                                                                               10)) == (0b100100#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__930 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__930 <b 879) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__931 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 879
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
                                                                                                                                          13
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
                                                                                                                                      (decode_sqdmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd
                                                                                                                                        Rd
                                                                                                                                        Rn
                                                                                                                                        o1
                                                                                                                                        Rm
                                                                                                                                        size)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__933 ← (( do
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
                                                                                                                                                     10)) == (0b100100#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__932 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__932 <b 880) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__933 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 880
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
                                                                                                                                              13
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
                                                                                                                                          (decode_sqdmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_simd
                                                                                                                                            Rd
                                                                                                                                            Rn
                                                                                                                                            o1
                                                                                                                                            Rm
                                                                                                                                            size
                                                                                                                                            Q)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (pure true))))))))))))))))))))))))))))))))))


end ArmFull.Functions
