import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0932
import ArmFull.Fn.M1015
import ArmFull.Fn.M1016
import ArmFull.Fn.M1097
import ArmFull.Fn.M1148
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
def __DecodeA64_DataProcFPSIMD__seg1 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__79 ← (( do
    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
               __opcode 29 24)) == (0b001110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
               __opcode 21 10)) == (0x812#12 : (BitVec 12))))) : Bool) : Bool)
    then
      (do
        let w__78 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__78 <b 125) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__79 : Bool)
  then
    (do
      writeReg SEE 125
      let Rd := (BitVec.slice __opcode 0 5)
      let Rn := (BitVec.slice __opcode 5 5)
      let size := (BitVec.slice __opcode 22 2)
      let U := (BitVec.slice __opcode 29 1)
      let Q := (BitVec.slice __opcode 30 1)
      (decode_cls_advsimd_aarch64_instrs_vector_arithmetic_unary_clsz Rd Rn size U Q)
      (pure false))
  else
    (do
      let w__81 ← (( do
        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                   __opcode 29 24)) == (0b101110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                   __opcode 21 10)) == (0x812#12 : (BitVec 12))))) : Bool) : Bool)
        then
          (do
            let w__80 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__80 <b 126) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__81 : Bool)
      then
        (do
          writeReg SEE 126
          let Rd := (BitVec.slice __opcode 0 5)
          let Rn := (BitVec.slice __opcode 5 5)
          let size := (BitVec.slice __opcode 22 2)
          let U := (BitVec.slice __opcode 29 1)
          let Q := (BitVec.slice __opcode 30 1)
          (decode_clz_advsimd_aarch64_instrs_vector_arithmetic_unary_clsz Rd Rn size U Q)
          (pure false))
      else
        (do
          let w__83 ← (( do
            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x5E#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                     __opcode 21 10)) == (0x826#12 : (BitVec 12)))) : Bool) : Bool)
            then
              (do
                let w__82 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__82 <b 129) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__83 : Bool)
          then
            (do
              writeReg SEE 129
              let Rd := (BitVec.slice __opcode 0 5)
              let Rn := (BitVec.slice __opcode 5 5)
              let op := (BitVec.slice __opcode 12 1)
              let size := (BitVec.slice __opcode 22 2)
              let U := (BitVec.slice __opcode 29 1)
              (decode_cmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd Rd
                Rn op size U)
              (pure false))
          else
            (do
              let w__85 ← (( do
                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                           __opcode 29 24)) == (0b001110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                           __opcode 21 10)) == (0x826#12 : (BitVec 12))))) : Bool) : Bool)
                then
                  (do
                    let w__84 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__84 <b 130) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__85 : Bool)
              then
                (do
                  writeReg SEE 130
                  let Rd := (BitVec.slice __opcode 0 5)
                  let Rn := (BitVec.slice __opcode 5 5)
                  let op := (BitVec.slice __opcode 12 1)
                  let size := (BitVec.slice __opcode 22 2)
                  let U := (BitVec.slice __opcode 29 1)
                  let Q := (BitVec.slice __opcode 30 1)
                  (decode_cmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd
                    Rd Rn op size U Q)
                  (pure false))
              else
                (do
                  let w__87 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x7E#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                             __opcode 21 10)) == (0x822#12 : (BitVec 12)))) : Bool) : Bool)
                    then
                      (do
                        let w__86 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__86 <b 131) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__87 : Bool)
                  then
                    (do
                      writeReg SEE 131
                      let Rd := (BitVec.slice __opcode 0 5)
                      let Rn := (BitVec.slice __opcode 5 5)
                      let op := (BitVec.slice __opcode 12 1)
                      let size := (BitVec.slice __opcode 22 2)
                      let U := (BitVec.slice __opcode 29 1)
                      (decode_cmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd
                        Rd Rn op size U)
                      (pure false))
                  else
                    (do
                      let w__89 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31
                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                   __opcode 29 24)) == (0b101110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                   __opcode 21 10)) == (0x822#12 : (BitVec 12))))) : Bool) : Bool)
                        then
                          (do
                            let w__88 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__88 <b 132) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__89 : Bool)
                      then
                        (do
                          writeReg SEE 132
                          let Rd := (BitVec.slice __opcode 0 5)
                          let Rn := (BitVec.slice __opcode 5 5)
                          let op := (BitVec.slice __opcode 12 1)
                          let size := (BitVec.slice __opcode 22 2)
                          let U := (BitVec.slice __opcode 29 1)
                          let Q := (BitVec.slice __opcode 30 1)
                          (decode_cmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd
                            Rd Rn op size U Q)
                          (pure false))
                      else
                        (do
                          let w__91 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode
                                     31 24)) == (0x5E#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                     __opcode 21 10)) == (0x822#12 : (BitVec 12)))) : Bool) : Bool)
                            then
                              (do
                                let w__90 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__90 <b 133) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__91 : Bool)
                          then
                            (do
                              writeReg SEE 133
                              let Rd := (BitVec.slice __opcode 0 5)
                              let Rn := (BitVec.slice __opcode 5 5)
                              let op := (BitVec.slice __opcode 12 1)
                              let size := (BitVec.slice __opcode 22 2)
                              let U := (BitVec.slice __opcode 29 1)
                              (decode_cmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd
                                Rd Rn op size U)
                              (pure false))
                          else
                            (do
                              let w__93 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                         __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                           __opcode 29 24)) == (0b001110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                           __opcode 21 10)) == (0x822#12 : (BitVec 12))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__92 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__92 <b 134) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__93 : Bool)
                              then
                                (do
                                  writeReg SEE 134
                                  let Rd := (BitVec.slice __opcode 0 5)
                                  let Rn := (BitVec.slice __opcode 5 5)
                                  let op := (BitVec.slice __opcode 12 1)
                                  let size := (BitVec.slice __opcode 22 2)
                                  let U := (BitVec.slice __opcode 29 1)
                                  let Q := (BitVec.slice __opcode 30 1)
                                  (decode_cmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd
                                    Rd Rn op size U Q)
                                  (pure false))
                              else
                                (do
                                  let w__95 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                             __opcode 31 24)) == (0x7E#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                             __opcode 21 10)) == (0x826#12 : (BitVec 12)))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__94 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__94 <b 135) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__95 : Bool)
                                  then
                                    (do
                                      writeReg SEE 135
                                      let Rd := (BitVec.slice __opcode 0 5)
                                      let Rn := (BitVec.slice __opcode 5 5)
                                      let op := (BitVec.slice __opcode 12 1)
                                      let size := (BitVec.slice __opcode 22 2)
                                      let U := (BitVec.slice __opcode 29 1)
                                      (decode_cmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd
                                        Rd Rn op size U)
                                      (pure false))
                                  else
                                    (do
                                      let w__97 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                   __opcode 29 24)) == (0b101110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                   __opcode 21 10)) == (0x826#12 : (BitVec 12))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__96 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__96 <b 136) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__97 : Bool)
                                      then
                                        (do
                                          writeReg SEE 136
                                          let Rd := (BitVec.slice __opcode 0 5)
                                          let Rn := (BitVec.slice __opcode 5 5)
                                          let op := (BitVec.slice __opcode 12 1)
                                          let size := (BitVec.slice __opcode 22 2)
                                          let U := (BitVec.slice __opcode 29 1)
                                          let Q := (BitVec.slice __opcode 30 1)
                                          (decode_cmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd
                                            Rd Rn op size U Q)
                                          (pure false))
                                      else
                                        (do
                                          let w__99 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                     __opcode 31 24)) == (0x7E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                       __opcode 15 10)) == (0b100011#6 : (BitVec 6))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__98 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__98 <b 137) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__99 : Bool)
                                          then
                                            (do
                                              writeReg SEE 137
                                              let Rd := (BitVec.slice __opcode 0 5)
                                              let Rn := (BitVec.slice __opcode 5 5)
                                              let Rm := (BitVec.slice __opcode 16 5)
                                              let size := (BitVec.slice __opcode 22 2)
                                              let U := (BitVec.slice __opcode 29 1)
                                              (decode_cmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd
                                                Rd Rn Rm size U)
                                              (pure false))
                                          else
                                            (do
                                              let w__101 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                         __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                           __opcode 29 24)) == (0b101110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                             __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                             __opcode 15 10)) == (0b100011#6 : (BitVec 6)))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__100 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__100 <b 138) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__101 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 138
                                                  let Rd := (BitVec.slice __opcode 0 5)
                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                  let Rm := (BitVec.slice __opcode 16 5)
                                                  let size := (BitVec.slice __opcode 22 2)
                                                  let U := (BitVec.slice __opcode 29 1)
                                                  let Q := (BitVec.slice __opcode 30 1)
                                                  (decode_cmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_simd
                                                    Rd Rn Rm size U Q)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__103 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                             __opcode 31 24)) == (0x5E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                               __opcode 15 10)) == (0b100011#6 : (BitVec 6))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__102 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__102 <b 139) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__103 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 139
                                                      let Rd := (BitVec.slice __opcode 0 5)
                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                      let Rm := (BitVec.slice __opcode 16 5)
                                                      let size := (BitVec.slice __opcode 22 2)
                                                      let U := (BitVec.slice __opcode 29 1)
                                                      (decode_cmtst_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd
                                                        Rd Rn Rm size U)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__105 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                 __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                   __opcode 29 24)) == (0b001110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                     __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                     __opcode 15 10)) == (0b100011#6 : (BitVec 6)))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__104 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__104 <b 140) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__105 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 140
                                                          let Rd := (BitVec.slice __opcode 0 5)
                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                          let Rm := (BitVec.slice __opcode 16 5)
                                                          let size := (BitVec.slice __opcode 22 2)
                                                          let U := (BitVec.slice __opcode 29 1)
                                                          let Q := (BitVec.slice __opcode 30 1)
                                                          (decode_cmtst_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_simd
                                                            Rd Rn Rm size U Q)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__107 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                     __opcode 31 24)) == (0x5E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                       __opcode 15 10)) == (0b001111#6 : (BitVec 6))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__106 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__106 <b 141) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__107 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 141
                                                              let Rd := (BitVec.slice __opcode 0 5)
                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                              let eq := (BitVec.slice __opcode 11 1)
                                                              let Rm := (BitVec.slice __opcode 16 5)
                                                              let size :=
                                                                (BitVec.slice __opcode 22 2)
                                                              let U := (BitVec.slice __opcode 29 1)
                                                              (decode_cmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd
                                                                Rd Rn eq Rm size U)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__109 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                         __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                           __opcode 29 24)) == (0b001110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                             __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                             __opcode 15 10)) == (0b001111#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__108 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__108 <b 142) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__109 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 142
                                                                  let Rd :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let eq :=
                                                                    (BitVec.slice __opcode 11 1)
                                                                  let Rm :=
                                                                    (BitVec.slice __opcode 16 5)
                                                                  let size :=
                                                                    (BitVec.slice __opcode 22 2)
                                                                  let U :=
                                                                    (BitVec.slice __opcode 29 1)
                                                                  let Q :=
                                                                    (BitVec.slice __opcode 30 1)
                                                                  (decode_cmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd
                                                                    Rd Rn eq Rm size U Q)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__111 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                             __opcode 31 24)) == (0x5E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                               __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                               __opcode 15 10)) == (0b001101#6 : (BitVec 6))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__110 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__110 <b 143) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__111 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 143
                                                                      let Rd :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let eq :=
                                                                        (BitVec.slice __opcode 11 1)
                                                                      let Rm :=
                                                                        (BitVec.slice __opcode 16 5)
                                                                      let size :=
                                                                        (BitVec.slice __opcode 22 2)
                                                                      let U :=
                                                                        (BitVec.slice __opcode 29 1)
                                                                      (decode_cmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd
                                                                        Rd Rn eq Rm size U)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__113 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                   __opcode 29 24)) == (0b001110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                     __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                     __opcode 15 10)) == (0b001101#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__112 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__112 <b 144) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__113 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 144
                                                                          let Rd :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let eq :=
                                                                            (BitVec.slice __opcode
                                                                              11 1)
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
                                                                          (decode_cmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd
                                                                            Rd Rn eq Rm size U Q)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__115 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 24)) == (0x7E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 21
                                                                                       21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                       __opcode 15
                                                                                       10)) == (0b001101#6 : (BitVec 6))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__114 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__114 <b 145) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__115 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 145
                                                                              let Rd :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let eq :=
                                                                                (BitVec.slice
                                                                                  __opcode 11 1)
                                                                              let Rm :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 5)
                                                                              let size :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 2)
                                                                              let U :=
                                                                                (BitVec.slice
                                                                                  __opcode 29 1)
                                                                              (decode_cmhi_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd
                                                                                Rd Rn eq Rm size U)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__117 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           29 24)) == (0b101110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             15 10)) == (0b001101#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__116 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__116 <b 146) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__117 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 146
                                                                                  let Rd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let eq :=
                                                                                    (BitVec.slice
                                                                                      __opcode 11 1)
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
                                                                                  (decode_cmhi_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd
                                                                                    Rd Rn eq Rm size
                                                                                    U Q)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__119 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 24)) == (0x7E#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               15 10)) == (0b001111#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__118 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__118 <b 147) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__119 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 147
                                                                                      let Rd :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          5)
                                                                                      let Rn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let eq :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          11 1)
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
                                                                                      (decode_cmhs_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd
                                                                                        Rd Rn eq Rm
                                                                                        size U)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__121 ← (( do
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
                                                                                                     10)) == (0b001111#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__120 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__120 <b 148) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__121 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 148
                                                                                          let Rd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 5)
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let eq :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              11 1)
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
                                                                                          (decode_cmhs_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd
                                                                                            Rd Rn eq
                                                                                            Rm size
                                                                                            U Q)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__123 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     24)) == (0x5E#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     21
                                                                                                     10)) == (0x82A#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__122 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__122 <b 149) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__123 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 149
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
                                                                                              (decode_cmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_sisd
                                                                                                Rd
                                                                                                Rn
                                                                                                size)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__125 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           29
                                                                                                           24)) == (0b001110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           21
                                                                                                           10)) == (0x82A#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__124 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__124 <b 150) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__125 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 150
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
                                                                                                  (decode_cmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_simd
                                                                                                    Rd
                                                                                                    Rn
                                                                                                    size
                                                                                                    Q)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__127 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               29
                                                                                                               24)) == (0b001110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               21
                                                                                                               10)) == (0x816#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__126 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__126 <b 152) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__127 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 152
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
                                                                                                      (decode_cnt_advsimd_aarch64_instrs_vector_arithmetic_unary_cnt
                                                                                                        Rd
                                                                                                        Rn
                                                                                                        size
                                                                                                        Q)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__129 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 21)) == (0b01011110000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 15
                                                                                                                 10)) == (0b000001#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__128 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__128 <b 199) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__129 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 199
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
                                                                                                          (decode_dup_advsimd_elt_aarch64_instrs_vector_transfer_vector_cpy_dup_sisd
                                                                                                            Rd
                                                                                                            Rn
                                                                                                            imm5)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__131 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       29
                                                                                                                       21)) == (0b001110000#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       15
                                                                                                                       10)) == (0b000001#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__130 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__130 <b 200) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__131 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 200
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
                                                                                                              (decode_dup_advsimd_elt_aarch64_instrs_vector_transfer_vector_cpy_dup_simd
                                                                                                                Rd
                                                                                                                Rn
                                                                                                                imm5
                                                                                                                Q)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__133 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           29
                                                                                                                           21)) == (0b001110000#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           15
                                                                                                                           10)) == (0b000011#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__132 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__132 <b 201) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__133 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 201
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
                                                                                                                  (decode_dup_advsimd_gen_aarch64_instrs_vector_transfer_integer_dup
                                                                                                                    Rd
                                                                                                                    Rn
                                                                                                                    imm5
                                                                                                                    Q)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__135 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             21)) == (0b11001110000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             15
                                                                                                                             15)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__134 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__134 <b 202) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__135 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 202
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
                                                                                                                      let Ra :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          10
                                                                                                                          5)
                                                                                                                      let Rm :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          16
                                                                                                                          5)
                                                                                                                      (decode_eor3_advsimd_aarch64_instrs_vector_crypto_sha3_eor3
                                                                                                                        Rd
                                                                                                                        Rn
                                                                                                                        Ra
                                                                                                                        Rm)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__137 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   29
                                                                                                                                   21)) == (0b101110000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     15
                                                                                                                                     15)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     10
                                                                                                                                     10)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__136 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__136 <b 205) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__137 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 205
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
                                                                                                                          let imm4 :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              11
                                                                                                                              4)
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
                                                                                                                          (decode_ext_advsimd_aarch64_instrs_vector_transfer_vector_extract
                                                                                                                            Rd
                                                                                                                            Rn
                                                                                                                            imm4
                                                                                                                            Rm
                                                                                                                            Q)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__139 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     21)) == (0b01111110110#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     15
                                                                                                                                     10)) == (0b000101#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__138 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__138 <b 207) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__139 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 207
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
                                                                                                                              (decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_sisd
                                                                                                                                Rd
                                                                                                                                Rn
                                                                                                                                Rm)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__141 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         23)) == (0b011111101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           21
                                                                                                                                           21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           15
                                                                                                                                           10)) == (0b110101#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__140 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__140 <b 208) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__141 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 208
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
                                                                                                                                  (decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp_sisd
                                                                                                                                    Rd
                                                                                                                                    Rn
                                                                                                                                    Rm
                                                                                                                                    sz)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__143 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               29
                                                                                                                                               21)) == (0b101110110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               15
                                                                                                                                               10)) == (0b000101#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__142 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__142 <b 209) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__143 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 209
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
                                                                                                                                      (decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_simd
                                                                                                                                        Rd
                                                                                                                                        Rn
                                                                                                                                        Rm
                                                                                                                                        U
                                                                                                                                        Q)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__145 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   29
                                                                                                                                                   23)) == (0b1011101#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     21
                                                                                                                                                     21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     15
                                                                                                                                                     10)) == (0b110101#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__144 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__144 <b 210) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__145 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 210
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
                                                                                                                                          (decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp_simd
                                                                                                                                            Rd
                                                                                                                                            Rn
                                                                                                                                            Rm
                                                                                                                                            sz
                                                                                                                                            U
                                                                                                                                            Q)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__147 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     24)) == (0x1E#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     21
                                                                                                                                                     10)) == (0x830#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__146 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__146 <b 211) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__147 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 211
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
                                                                                                                                              let opc :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  15
                                                                                                                                                  2)
                                                                                                                                              let ftype :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  22
                                                                                                                                                  2)
                                                                                                                                              (decode_fabs_float_aarch64_instrs_float_arithmetic_unary
                                                                                                                                                Rd
                                                                                                                                                Rn
                                                                                                                                                opc
                                                                                                                                                ftype)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__149 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         31
                                                                                                                                                         24)) == (0x1E#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         21
                                                                                                                                                         10)) == (0x810#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__148 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__148 <b 212) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__149 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 212
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
                                                                                                                                                  let opc :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      15
                                                                                                                                                      2)
                                                                                                                                                  let ftype :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      22
                                                                                                                                                      2)
                                                                                                                                                  (decode_fmov_float_aarch64_instrs_float_arithmetic_unary
                                                                                                                                                    Rd
                                                                                                                                                    Rn
                                                                                                                                                    opc
                                                                                                                                                    ftype)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__151 ← (( do
                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             31
                                                                                                                                                             24)) == (0x1E#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             21
                                                                                                                                                             10)) == (0x850#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__150 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__150 <b 213) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__151 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 213
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
                                                                                                                                                      let opc :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          15
                                                                                                                                                          2)
                                                                                                                                                      let ftype :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          22
                                                                                                                                                          2)
                                                                                                                                                      (decode_fneg_float_aarch64_instrs_float_arithmetic_unary
                                                                                                                                                        Rd
                                                                                                                                                        Rn
                                                                                                                                                        opc
                                                                                                                                                        ftype)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__153 ← (( do
                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 31
                                                                                                                                                                 24)) == (0x1E#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 21
                                                                                                                                                                 10)) == (0x870#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__152 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__152 <b 214) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false)
                                                                                                                                                        )
                                                                                                                                                        :
                                                                                                                                                        SailM
                                                                                                                                                        Bool
                                                                                                                                                        )
                                                                                                                                                      if (w__153 : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 214
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
                                                                                                                                                          let opc :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              15
                                                                                                                                                              2)
                                                                                                                                                          let ftype :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              22
                                                                                                                                                              2)
                                                                                                                                                          (decode_fsqrt_float_aarch64_instrs_float_arithmetic_unary
                                                                                                                                                            Rd
                                                                                                                                                            Rn
                                                                                                                                                            opc
                                                                                                                                                            ftype)
                                                                                                                                                          (pure false))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          let w__155 ← (( do
                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     31
                                                                                                                                                                     31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     29
                                                                                                                                                                     10)) == (0x3BE3E#20 : (BitVec 20)))) : Bool) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let w__154 ← (( do
                                                                                                                                                                  readReg SEE
                                                                                                                                                                  )
                                                                                                                                                                  :
                                                                                                                                                                  SailM
                                                                                                                                                                  Int
                                                                                                                                                                  )
                                                                                                                                                                (pure (((w__154 <b 215) : Bool))))
                                                                                                                                                            else
                                                                                                                                                              (pure false)
                                                                                                                                                            )
                                                                                                                                                            :
                                                                                                                                                            SailM
                                                                                                                                                            Bool
                                                                                                                                                            )
                                                                                                                                                          if (w__155 : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 215
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
                                                                                                                                                              (decode_fabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16
                                                                                                                                                                Rd
                                                                                                                                                                Rn
                                                                                                                                                                U
                                                                                                                                                                Q)
                                                                                                                                                              (pure false))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              let w__157 ← (( do
                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         31
                                                                                                                                                                         31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           29
                                                                                                                                                                           23)) == (0b0011101#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           21
                                                                                                                                                                           10)) == (0x83E#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    let w__156 ← (( do
                                                                                                                                                                      readReg SEE
                                                                                                                                                                      )
                                                                                                                                                                      :
                                                                                                                                                                      SailM
                                                                                                                                                                      Int
                                                                                                                                                                      )
                                                                                                                                                                    (pure (((w__156 <b 216) : Bool))))
                                                                                                                                                                else
                                                                                                                                                                  (pure false)
                                                                                                                                                                )
                                                                                                                                                                :
                                                                                                                                                                SailM
                                                                                                                                                                Bool
                                                                                                                                                                )
                                                                                                                                                              if (w__157 : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 216
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
                                                                                                                                                                  (decode_fabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_float
                                                                                                                                                                    Rd
                                                                                                                                                                    Rn
                                                                                                                                                                    sz
                                                                                                                                                                    U
                                                                                                                                                                    Q)
                                                                                                                                                                  (pure false))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  let w__159 ← (( do
                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                             __opcode
                                                                                                                                                                             31
                                                                                                                                                                             31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                                                                                                                                             __opcode
                                                                                                                                                                             29
                                                                                                                                                                             10)) == (0xBBE3E#20 : (BitVec 20)))) : Bool) : Bool)
                                                                                                                                                                    then
                                                                                                                                                                      (do
                                                                                                                                                                        let w__158 ← (( do
                                                                                                                                                                          readReg SEE
                                                                                                                                                                          )
                                                                                                                                                                          :
                                                                                                                                                                          SailM
                                                                                                                                                                          Int
                                                                                                                                                                          )
                                                                                                                                                                        (pure (((w__158 <b 217) : Bool))))
                                                                                                                                                                    else
                                                                                                                                                                      (pure false)
                                                                                                                                                                    )
                                                                                                                                                                    :
                                                                                                                                                                    SailM
                                                                                                                                                                    Bool
                                                                                                                                                                    )
                                                                                                                                                                  if (w__159 : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      writeReg SEE 217
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
                                                                                                                                                                      (decode_fneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16
                                                                                                                                                                        Rd
                                                                                                                                                                        Rn
                                                                                                                                                                        U
                                                                                                                                                                        Q)
                                                                                                                                                                      (pure false))
                                                                                                                                                                  else
                                                                                                                                                                    (pure true)))))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
