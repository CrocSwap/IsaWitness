import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M1017
import ArmFull.Fn.M1018
import ArmFull.Fn.M1110

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
def __DecodeA64_DataProcFPSIMD__seg9 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__709 ← (( do
    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
               __opcode 29 23)) == (0b0011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
               __opcode 15 10)) == (0b100001#6 : (BitVec 6))))) : Bool) : Bool)
    then
      (do
        let w__708 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__708 <b 745) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__709 : Bool)
  then
    (do
      writeReg SEE 745
      let Rd := (BitVec.slice __opcode 0 5)
      let Rn := (BitVec.slice __opcode 5 5)
      let op := (BitVec.slice __opcode 11 1)
      let immb := (BitVec.slice __opcode 16 3)
      let immh := (BitVec.slice __opcode 19 4)
      let Q := (BitVec.slice __opcode 30 1)
      (decode_shrn_advsimd_aarch64_instrs_vector_shift_right_narrow_logical Rd Rn op immb immh Q)
      (pure false))
  else
    (do
      let w__711 ← (( do
        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                   __opcode 29 24)) == (0b001110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                     __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                     __opcode 15 10)) == (0b011111#6 : (BitVec 6)))))) : Bool) : Bool)
        then
          (do
            let w__710 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__710 <b 746) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__711 : Bool)
      then
        (do
          writeReg SEE 746
          let Rd := (BitVec.slice __opcode 0 5)
          let Rn := (BitVec.slice __opcode 5 5)
          let ac := (BitVec.slice __opcode 11 1)
          let Rm := (BitVec.slice __opcode 16 5)
          let size := (BitVec.slice __opcode 22 2)
          let U := (BitVec.slice __opcode 29 1)
          let Q := (BitVec.slice __opcode 30 1)
          (decode_saba_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff Rd Rn ac Rm size
            U Q)
          (pure false))
      else
        (do
          let w__713 ← (( do
            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                       __opcode 29 24)) == (0b001110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                         __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                         __opcode 15 10)) == (0b011101#6 : (BitVec 6)))))) : Bool) : Bool)
            then
              (do
                let w__712 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__712 <b 747) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__713 : Bool)
          then
            (do
              writeReg SEE 747
              let Rd := (BitVec.slice __opcode 0 5)
              let Rn := (BitVec.slice __opcode 5 5)
              let ac := (BitVec.slice __opcode 11 1)
              let Rm := (BitVec.slice __opcode 16 5)
              let size := (BitVec.slice __opcode 22 2)
              let U := (BitVec.slice __opcode 29 1)
              let Q := (BitVec.slice __opcode 30 1)
              (decode_sabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff Rd Rn ac Rm
                size U Q)
              (pure false))
          else
            (do
              let w__715 ← (( do
                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                           __opcode 29 24)) == (0b101110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                             __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                             __opcode 15 10)) == (0b011111#6 : (BitVec 6)))))) : Bool) : Bool)
                then
                  (do
                    let w__714 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__714 <b 748) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__715 : Bool)
              then
                (do
                  writeReg SEE 748
                  let Rd := (BitVec.slice __opcode 0 5)
                  let Rn := (BitVec.slice __opcode 5 5)
                  let ac := (BitVec.slice __opcode 11 1)
                  let Rm := (BitVec.slice __opcode 16 5)
                  let size := (BitVec.slice __opcode 22 2)
                  let U := (BitVec.slice __opcode 29 1)
                  let Q := (BitVec.slice __opcode 30 1)
                  (decode_uaba_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff Rd Rn ac
                    Rm size U Q)
                  (pure false))
              else
                (do
                  let w__717 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                               __opcode 29 24)) == (0b101110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                 __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                 __opcode 15 10)) == (0b011101#6 : (BitVec 6)))))) : Bool) : Bool)
                    then
                      (do
                        let w__716 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__716 <b 749) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__717 : Bool)
                  then
                    (do
                      writeReg SEE 749
                      let Rd := (BitVec.slice __opcode 0 5)
                      let Rn := (BitVec.slice __opcode 5 5)
                      let ac := (BitVec.slice __opcode 11 1)
                      let Rm := (BitVec.slice __opcode 16 5)
                      let size := (BitVec.slice __opcode 22 2)
                      let U := (BitVec.slice __opcode 29 1)
                      let Q := (BitVec.slice __opcode 30 1)
                      (decode_uabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff Rd
                        Rn ac Rm size U Q)
                      (pure false))
                  else
                    (do
                      let w__719 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31
                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                   __opcode 29 24)) == (0b001110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                     __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                     __opcode 15 10)) == (0b010100#6 : (BitVec 6)))))) : Bool) : Bool)
                        then
                          (do
                            let w__718 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__718 <b 750) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__719 : Bool)
                      then
                        (do
                          writeReg SEE 750
                          let Rd := (BitVec.slice __opcode 0 5)
                          let Rn := (BitVec.slice __opcode 5 5)
                          let op := (BitVec.slice __opcode 13 1)
                          let Rm := (BitVec.slice __opcode 16 5)
                          let size := (BitVec.slice __opcode 22 2)
                          let U := (BitVec.slice __opcode 29 1)
                          let Q := (BitVec.slice __opcode 30 1)
                          (decode_sabal_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff
                            Rd Rn op Rm size U Q)
                          (pure false))
                      else
                        (do
                          let w__721 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode
                                     31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                       __opcode 29 24)) == (0b001110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                         __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                         __opcode 15 10)) == (0b011100#6 : (BitVec 6)))))) : Bool) : Bool)
                            then
                              (do
                                let w__720 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__720 <b 751) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__721 : Bool)
                          then
                            (do
                              writeReg SEE 751
                              let Rd := (BitVec.slice __opcode 0 5)
                              let Rn := (BitVec.slice __opcode 5 5)
                              let op := (BitVec.slice __opcode 13 1)
                              let Rm := (BitVec.slice __opcode 16 5)
                              let size := (BitVec.slice __opcode 22 2)
                              let U := (BitVec.slice __opcode 29 1)
                              let Q := (BitVec.slice __opcode 30 1)
                              (decode_sabdl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff
                                Rd Rn op Rm size U Q)
                              (pure false))
                          else
                            (do
                              let w__723 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                         __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                           __opcode 29 24)) == (0b101110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                             __opcode 15 10)) == (0b010100#6 : (BitVec 6)))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__722 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__722 <b 752) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__723 : Bool)
                              then
                                (do
                                  writeReg SEE 752
                                  let Rd := (BitVec.slice __opcode 0 5)
                                  let Rn := (BitVec.slice __opcode 5 5)
                                  let op := (BitVec.slice __opcode 13 1)
                                  let Rm := (BitVec.slice __opcode 16 5)
                                  let size := (BitVec.slice __opcode 22 2)
                                  let U := (BitVec.slice __opcode 29 1)
                                  let Q := (BitVec.slice __opcode 30 1)
                                  (decode_uabal_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff
                                    Rd Rn op Rm size U Q)
                                  (pure false))
                              else
                                (do
                                  let w__725 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                               __opcode 29 24)) == (0b101110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                 __opcode 15 10)) == (0b011100#6 : (BitVec 6)))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__724 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__724 <b 753) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__725 : Bool)
                                  then
                                    (do
                                      writeReg SEE 753
                                      let Rd := (BitVec.slice __opcode 0 5)
                                      let Rn := (BitVec.slice __opcode 5 5)
                                      let op := (BitVec.slice __opcode 13 1)
                                      let Rm := (BitVec.slice __opcode 16 5)
                                      let size := (BitVec.slice __opcode 22 2)
                                      let U := (BitVec.slice __opcode 29 1)
                                      let Q := (BitVec.slice __opcode 30 1)
                                      (decode_uabdl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff
                                        Rd Rn op Rm size U Q)
                                      (pure false))
                                  else
                                    (do
                                      let w__727 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                   __opcode 29 24)) == (0b001110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                   __opcode 21 10)) == (0x81A#12 : (BitVec 12))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__726 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__726 <b 754) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__727 : Bool)
                                      then
                                        (do
                                          writeReg SEE 754
                                          let Rd := (BitVec.slice __opcode 0 5)
                                          let Rn := (BitVec.slice __opcode 5 5)
                                          let op := (BitVec.slice __opcode 14 1)
                                          let size := (BitVec.slice __opcode 22 2)
                                          let U := (BitVec.slice __opcode 29 1)
                                          let Q := (BitVec.slice __opcode 30 1)
                                          (decode_sadalp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise
                                            Rd Rn op size U Q)
                                          (pure false))
                                      else
                                        (do
                                          let w__729 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                     __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                       __opcode 29 24)) == (0b001110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                       __opcode 21 10)) == (0x80A#12 : (BitVec 12))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__728 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__728 <b 755) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__729 : Bool)
                                          then
                                            (do
                                              writeReg SEE 755
                                              let Rd := (BitVec.slice __opcode 0 5)
                                              let Rn := (BitVec.slice __opcode 5 5)
                                              let op := (BitVec.slice __opcode 14 1)
                                              let size := (BitVec.slice __opcode 22 2)
                                              let U := (BitVec.slice __opcode 29 1)
                                              let Q := (BitVec.slice __opcode 30 1)
                                              (decode_saddlp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise
                                                Rd Rn op size U Q)
                                              (pure false))
                                          else
                                            (do
                                              let w__731 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                         __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                           __opcode 29 24)) == (0b101110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                           __opcode 21 10)) == (0x81A#12 : (BitVec 12))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__730 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__730 <b 756) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__731 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 756
                                                  let Rd := (BitVec.slice __opcode 0 5)
                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                  let op := (BitVec.slice __opcode 14 1)
                                                  let size := (BitVec.slice __opcode 22 2)
                                                  let U := (BitVec.slice __opcode 29 1)
                                                  let Q := (BitVec.slice __opcode 30 1)
                                                  (decode_uadalp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise
                                                    Rd Rn op size U Q)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__733 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                             __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                               __opcode 29 24)) == (0b101110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                               __opcode 21 10)) == (0x80A#12 : (BitVec 12))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__732 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__732 <b 757) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__733 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 757
                                                      let Rd := (BitVec.slice __opcode 0 5)
                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                      let op := (BitVec.slice __opcode 14 1)
                                                      let size := (BitVec.slice __opcode 22 2)
                                                      let U := (BitVec.slice __opcode 29 1)
                                                      let Q := (BitVec.slice __opcode 30 1)
                                                      (decode_uaddlp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise
                                                        Rd Rn op size U Q)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__735 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                 __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                   __opcode 29 24)) == (0b001110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                     __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                     __opcode 15 10)) == (0b000000#6 : (BitVec 6)))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__734 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__734 <b 758) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__735 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 758
                                                          let Rd := (BitVec.slice __opcode 0 5)
                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                          let o1 := (BitVec.slice __opcode 13 1)
                                                          let Rm := (BitVec.slice __opcode 16 5)
                                                          let size := (BitVec.slice __opcode 22 2)
                                                          let U := (BitVec.slice __opcode 29 1)
                                                          let Q := (BitVec.slice __opcode 30 1)
                                                          (decode_saddl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long
                                                            Rd Rn o1 Rm size U Q)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__737 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                     __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                       __opcode 29 24)) == (0b001110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                         __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                         __opcode 15 10)) == (0b001000#6 : (BitVec 6)))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__736 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__736 <b 759) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__737 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 759
                                                              let Rd := (BitVec.slice __opcode 0 5)
                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                              let o1 := (BitVec.slice __opcode 13 1)
                                                              let Rm := (BitVec.slice __opcode 16 5)
                                                              let size :=
                                                                (BitVec.slice __opcode 22 2)
                                                              let U := (BitVec.slice __opcode 29 1)
                                                              let Q := (BitVec.slice __opcode 30 1)
                                                              (decode_ssubl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long
                                                                Rd Rn o1 Rm size U Q)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__739 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                         __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                           __opcode 29 24)) == (0b101110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                             __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                             __opcode 15 10)) == (0b000000#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__738 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__738 <b 760) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__739 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 760
                                                                  let Rd :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let o1 :=
                                                                    (BitVec.slice __opcode 13 1)
                                                                  let Rm :=
                                                                    (BitVec.slice __opcode 16 5)
                                                                  let size :=
                                                                    (BitVec.slice __opcode 22 2)
                                                                  let U :=
                                                                    (BitVec.slice __opcode 29 1)
                                                                  let Q :=
                                                                    (BitVec.slice __opcode 30 1)
                                                                  (decode_uaddl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long
                                                                    Rd Rn o1 Rm size U Q)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__741 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                             __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                               __opcode 29 24)) == (0b101110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                 __opcode 15 10)) == (0b001000#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__740 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__740 <b 761) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__741 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 761
                                                                      let Rd :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let o1 :=
                                                                        (BitVec.slice __opcode 13 1)
                                                                      let Rm :=
                                                                        (BitVec.slice __opcode 16 5)
                                                                      let size :=
                                                                        (BitVec.slice __opcode 22 2)
                                                                      let U :=
                                                                        (BitVec.slice __opcode 29 1)
                                                                      let Q :=
                                                                        (BitVec.slice __opcode 30 1)
                                                                      (decode_usubl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long
                                                                        Rd Rn o1 Rm size U Q)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__743 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                   __opcode 29 24)) == (0b001110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                   __opcode 21 10)) == (0xC0E#12 : (BitVec 12))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__742 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__742 <b 762) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__743 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 762
                                                                          let Rd :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let size :=
                                                                            (BitVec.slice __opcode
                                                                              22 2)
                                                                          let U :=
                                                                            (BitVec.slice __opcode
                                                                              29 1)
                                                                          let Q :=
                                                                            (BitVec.slice __opcode
                                                                              30 1)
                                                                          (decode_saddlv_advsimd_aarch64_instrs_vector_reduce_add_long
                                                                            Rd Rn size U Q)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__745 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                       __opcode 29
                                                                                       24)) == (0b101110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                       __opcode 21
                                                                                       10)) == (0xC0E#12 : (BitVec 12))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__744 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__744 <b 763) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__745 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 763
                                                                              let Rd :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let size :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 2)
                                                                              let U :=
                                                                                (BitVec.slice
                                                                                  __opcode 29 1)
                                                                              let Q :=
                                                                                (BitVec.slice
                                                                                  __opcode 30 1)
                                                                              (decode_uaddlv_advsimd_aarch64_instrs_vector_reduce_add_long
                                                                                Rd Rn size U Q)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__747 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           29 24)) == (0b001110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             15 10)) == (0b000100#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__746 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__746 <b 764) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__747 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 764
                                                                                  let Rd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let o1 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 13 1)
                                                                                  let Rm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 5)
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 2)
                                                                                  let U :=
                                                                                    (BitVec.slice
                                                                                      __opcode 29 1)
                                                                                  let Q :=
                                                                                    (BitVec.slice
                                                                                      __opcode 30 1)
                                                                                  (decode_saddw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide
                                                                                    Rd Rn o1 Rm size
                                                                                    U Q)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__749 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               29 24)) == (0b001110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 21
                                                                                                 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 15
                                                                                                 10)) == (0b001100#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__748 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__748 <b 765) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__749 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 765
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
                                                                                          13 1)
                                                                                      let Rm :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 5)
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
                                                                                      (decode_ssubw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide
                                                                                        Rd Rn o1 Rm
                                                                                        size U Q)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__751 ← (( do
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
                                                                                                     10)) == (0b000100#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__750 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__750 <b 766) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__751 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 766
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
                                                                                              13 1)
                                                                                          let Rm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 5)
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
                                                                                          (decode_uaddw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide
                                                                                            Rd Rn o1
                                                                                            Rm size
                                                                                            U Q)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__753 ← (( do
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
                                                                                                         10)) == (0b001100#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__752 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__752 <b 767) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__753 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 767
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
                                                                                              (decode_usubw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide
                                                                                                Rd
                                                                                                Rn
                                                                                                o1
                                                                                                Rm
                                                                                                size
                                                                                                U Q)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__755 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         23)) == (0b010111110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         15
                                                                                                         10)) == (0b111001#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__754 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__754 <b 769) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__755 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 769
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
                                                                                                  let U :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      29
                                                                                                      1)
                                                                                                  (decode_scvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_sisd
                                                                                                    Rd
                                                                                                    Rn
                                                                                                    immb
                                                                                                    immh
                                                                                                    U)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__757 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               29
                                                                                                               23)) == (0b0011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               15
                                                                                                               10)) == (0b111001#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__756 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__756 <b 770) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__757 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 770
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
                                                                                                      (decode_scvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_simd
                                                                                                        Rd
                                                                                                        Rn
                                                                                                        immb
                                                                                                        immh
                                                                                                        U
                                                                                                        Q)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__759 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 23)) == (0b011111110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 15
                                                                                                                 10)) == (0b111001#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__758 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__758 <b 771) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__759 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 771
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
                                                                                                          let U :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              29
                                                                                                              1)
                                                                                                          (decode_ucvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_sisd
                                                                                                            Rd
                                                                                                            Rn
                                                                                                            immb
                                                                                                            immh
                                                                                                            U)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__761 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       29
                                                                                                                       23)) == (0b1011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       15
                                                                                                                       10)) == (0b111001#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__760 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__760 <b 772) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__761 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 772
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
                                                                                                              (decode_ucvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_simd
                                                                                                                Rd
                                                                                                                Rn
                                                                                                                immb
                                                                                                                immh
                                                                                                                U
                                                                                                                Q)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__763 ← (( do
                                                                                                                if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       31
                                                                                                                       10)) == (0b0101111001111001110110#22 : (BitVec 22))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__762 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__762 <b 773) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__763 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 773
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
                                                                                                                  (decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd
                                                                                                                    Rd
                                                                                                                    Rn
                                                                                                                    U)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__765 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             23)) == (0b010111100#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             21
                                                                                                                             10)) == (0x876#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__764 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__764 <b 774) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__765 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 774
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
                                                                                                                      (decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_sisd
                                                                                                                        Rd
                                                                                                                        Rn
                                                                                                                        sz
                                                                                                                        U)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__767 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 29
                                                                                                                                 10)) == (0x39E76#20 : (BitVec 20)))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__766 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__766 <b 775) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__767 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 775
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
                                                                                                                          (decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_simd
                                                                                                                            Rd
                                                                                                                            Rn
                                                                                                                            U
                                                                                                                            Q)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__769 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       29
                                                                                                                                       23)) == (0b0011100#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       21
                                                                                                                                       10)) == (0x876#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__768 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__768 <b 776) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__769 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 776
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
                                                                                                                              (decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_simd
                                                                                                                                Rd
                                                                                                                                Rn
                                                                                                                                sz
                                                                                                                                U
                                                                                                                                Q)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__771 ← (( do
                                                                                                                                if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       31
                                                                                                                                       10)) == (0b0111111001111001110110#22 : (BitVec 22))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__770 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__770 <b 777) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__771 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 777
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
                                                                                                                                  (decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd
                                                                                                                                    Rd
                                                                                                                                    Rn
                                                                                                                                    U)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__773 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             23)) == (0b011111100#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             21
                                                                                                                                             10)) == (0x876#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__772 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__772 <b 778) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__773 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 778
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
                                                                                                                                      (decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_sisd
                                                                                                                                        Rd
                                                                                                                                        Rn
                                                                                                                                        sz
                                                                                                                                        U)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__775 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 29
                                                                                                                                                 10)) == (0xB9E76#20 : (BitVec 20)))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__774 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__774 <b 779) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__775 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 779
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
                                                                                                                                          (decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_simd
                                                                                                                                            Rd
                                                                                                                                            Rn
                                                                                                                                            U
                                                                                                                                            Q)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__777 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       29
                                                                                                                                                       23)) == (0b1011100#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       21
                                                                                                                                                       10)) == (0x876#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__776 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__776 <b 780) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__777 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 780
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
                                                                                                                                              (decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_simd
                                                                                                                                                Rd
                                                                                                                                                Rn
                                                                                                                                                sz
                                                                                                                                                U
                                                                                                                                                Q)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__779 ← (( do
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
                                                                                                                                                             10)) == (0b100101#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__778 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__778 <b 783) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__779 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 783
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
                                                                                                                                                  (decode_sdot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp
                                                                                                                                                    Rd
                                                                                                                                                    Rn
                                                                                                                                                    Rm
                                                                                                                                                    size
                                                                                                                                                    U
                                                                                                                                                    Q)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (pure true))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
