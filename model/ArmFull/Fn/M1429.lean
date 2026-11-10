import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M1109
import ArmFull.Fn.M1307
import ArmFull.Fn.M1308
import ArmFull.Fn.M1309
import ArmFull.Fn.M1310
import ArmFull.Fn.M1311
import ArmFull.Fn.M1312

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
def __DecodeA64_LoadStore__seg6 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__405 ← (( do
    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
             __opcode 29 22)) == (0xE4#8 : (BitVec 8)))) : Bool) : Bool)
    then
      (do
        let w__404 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__404 <b 648) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__405 : Bool)
  then
    (do
      writeReg SEE 648
      let Rt := (BitVec.slice __opcode 0 5)
      let Rn := (BitVec.slice __opcode 5 5)
      let imm12 := (BitVec.slice __opcode 10 12)
      let opc := (BitVec.slice __opcode 22 2)
      let size := (BitVec.slice __opcode 30 2)
      (decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 opc
        size)
      (pure false))
  else
    (do
      let w__407 ← (( do
        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b00111000000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                 __opcode 11 10)) == (0b01#2 : (BitVec 2)))) : Bool) : Bool)
        then
          (do
            let w__406 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__406 <b 649) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__407 : Bool)
      then
        (do
          writeReg SEE 649
          let Rt := (BitVec.slice __opcode 0 5)
          let Rn := (BitVec.slice __opcode 5 5)
          let imm9 := (BitVec.slice __opcode 12 9)
          let opc := (BitVec.slice __opcode 22 2)
          let size := (BitVec.slice __opcode 30 2)
          (decode_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9
            opc size)
          (pure false))
      else
        (do
          let w__409 ← (( do
            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b00111000000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                     __opcode 11 10)) == (0b11#2 : (BitVec 2)))) : Bool) : Bool)
            then
              (do
                let w__408 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__408 <b 650) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__409 : Bool)
          then
            (do
              writeReg SEE 650
              let Rt := (BitVec.slice __opcode 0 5)
              let Rn := (BitVec.slice __opcode 5 5)
              let imm9 := (BitVec.slice __opcode 12 9)
              let opc := (BitVec.slice __opcode 22 2)
              let size := (BitVec.slice __opcode 30 2)
              (decode_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn
                imm9 opc size)
              (pure false))
          else
            (do
              let w__411 ← (( do
                if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb __opcode 31 22)) == (0b0011100100#10 : (BitVec 10))) : Bool) : Bool)
                then
                  (do
                    let w__410 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__410 <b 651) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__411 : Bool)
              then
                (do
                  writeReg SEE 651
                  let Rt := (BitVec.slice __opcode 0 5)
                  let Rn := (BitVec.slice __opcode 5 5)
                  let imm12 := (BitVec.slice __opcode 10 12)
                  let opc := (BitVec.slice __opcode 22 2)
                  let size := (BitVec.slice __opcode 30 2)
                  (decode_strb_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn
                    imm12 opc size)
                  (pure false))
              else
                (do
                  let w__413 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b01111000000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                             __opcode 11 10)) == (0b01#2 : (BitVec 2)))) : Bool) : Bool)
                    then
                      (do
                        let w__412 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__412 <b 652) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__413 : Bool)
                  then
                    (do
                      writeReg SEE 652
                      let Rt := (BitVec.slice __opcode 0 5)
                      let Rn := (BitVec.slice __opcode 5 5)
                      let imm9 := (BitVec.slice __opcode 12 9)
                      let opc := (BitVec.slice __opcode 22 2)
                      let size := (BitVec.slice __opcode 30 2)
                      (decode_strh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx
                        Rt Rn imm9 opc size)
                      (pure false))
                  else
                    (do
                      let w__415 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31
                                 21)) == (0b01111000000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                 __opcode 11 10)) == (0b11#2 : (BitVec 2)))) : Bool) : Bool)
                        then
                          (do
                            let w__414 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__414 <b 653) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__415 : Bool)
                      then
                        (do
                          writeReg SEE 653
                          let Rt := (BitVec.slice __opcode 0 5)
                          let Rn := (BitVec.slice __opcode 5 5)
                          let imm9 := (BitVec.slice __opcode 12 9)
                          let opc := (BitVec.slice __opcode 22 2)
                          let size := (BitVec.slice __opcode 30 2)
                          (decode_strh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx
                            Rt Rn imm9 opc size)
                          (pure false))
                      else
                        (do
                          let w__417 ← (( do
                            if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb __opcode
                                   31 22)) == (0b0111100100#10 : (BitVec 10))) : Bool) : Bool)
                            then
                              (do
                                let w__416 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__416 <b 654) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__417 : Bool)
                          then
                            (do
                              writeReg SEE 654
                              let Rt := (BitVec.slice __opcode 0 5)
                              let Rn := (BitVec.slice __opcode 5 5)
                              let imm12 := (BitVec.slice __opcode 10 12)
                              let opc := (BitVec.slice __opcode 22 2)
                              let size := (BitVec.slice __opcode 30 2)
                              (decode_strh_imm_aarch64_instrs_memory_single_general_immediate_unsigned
                                Rt Rn imm12 opc size)
                              (pure false))
                          else
                            (do
                              let w__419 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                         __opcode 31 31)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                           __opcode 29 21)) == (0b111000011#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                           __opcode 11 10)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__418 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__418 <b 655) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__419 : Bool)
                              then
                                (do
                                  writeReg SEE 655
                                  let Rt := (BitVec.slice __opcode 0 5)
                                  let Rn := (BitVec.slice __opcode 5 5)
                                  let S := (BitVec.slice __opcode 12 1)
                                  let option_name := (BitVec.slice __opcode 13 3)
                                  let Rm := (BitVec.slice __opcode 16 5)
                                  let opc := (BitVec.slice __opcode 22 2)
                                  let size := (BitVec.slice __opcode 30 2)
                                  (decode_ldr_reg_gen_aarch64_instrs_memory_single_general_register
                                    Rt Rn S option_name Rm opc size)
                                  (pure false))
                              else
                                (do
                                  let w__421 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                             __opcode 31 21)) == (0b00111000011#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                             __opcode 11 10)) == (0b10#2 : (BitVec 2)))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__420 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__420 <b 656) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__421 : Bool)
                                  then
                                    (do
                                      writeReg SEE 656
                                      let Rt := (BitVec.slice __opcode 0 5)
                                      let Rn := (BitVec.slice __opcode 5 5)
                                      let S := (BitVec.slice __opcode 12 1)
                                      let option_name := (BitVec.slice __opcode 13 3)
                                      let Rm := (BitVec.slice __opcode 16 5)
                                      let opc := (BitVec.slice __opcode 22 2)
                                      let size := (BitVec.slice __opcode 30 2)
                                      (decode_ldrb_reg_aarch64_instrs_memory_single_general_register
                                        Rt Rn S option_name Rm opc size)
                                      (pure false))
                                  else
                                    (do
                                      let w__423 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                 __opcode 31 21)) == (0b01111000011#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                 __opcode 11 10)) == (0b10#2 : (BitVec 2)))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__422 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__422 <b 657) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__423 : Bool)
                                      then
                                        (do
                                          writeReg SEE 657
                                          let Rt := (BitVec.slice __opcode 0 5)
                                          let Rn := (BitVec.slice __opcode 5 5)
                                          let S := (BitVec.slice __opcode 12 1)
                                          let option_name := (BitVec.slice __opcode 13 3)
                                          let Rm := (BitVec.slice __opcode 16 5)
                                          let opc := (BitVec.slice __opcode 22 2)
                                          let size := (BitVec.slice __opcode 30 2)
                                          (decode_ldrh_reg_aarch64_instrs_memory_single_general_register
                                            Rt Rn S option_name Rm opc size)
                                          (pure false))
                                      else
                                        (do
                                          let w__425 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                     __opcode 31 23)) == (0b001110001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                       __opcode 11 10)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__424 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__424 <b 658) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__425 : Bool)
                                          then
                                            (do
                                              writeReg SEE 658
                                              let Rt := (BitVec.slice __opcode 0 5)
                                              let Rn := (BitVec.slice __opcode 5 5)
                                              let S := (BitVec.slice __opcode 12 1)
                                              let option_name := (BitVec.slice __opcode 13 3)
                                              let Rm := (BitVec.slice __opcode 16 5)
                                              let opc := (BitVec.slice __opcode 22 2)
                                              let size := (BitVec.slice __opcode 30 2)
                                              (decode_ldrsb_reg_aarch64_instrs_memory_single_general_register
                                                Rt Rn S option_name Rm opc size)
                                              (pure false))
                                          else
                                            (do
                                              let w__427 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                         __opcode 31 23)) == (0b011110001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                           __opcode 11 10)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__426 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__426 <b 659) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__427 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 659
                                                  let Rt := (BitVec.slice __opcode 0 5)
                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                  let S := (BitVec.slice __opcode 12 1)
                                                  let option_name := (BitVec.slice __opcode 13 3)
                                                  let Rm := (BitVec.slice __opcode 16 5)
                                                  let opc := (BitVec.slice __opcode 22 2)
                                                  let size := (BitVec.slice __opcode 30 2)
                                                  (decode_ldrsh_reg_aarch64_instrs_memory_single_general_register
                                                    Rt Rn S option_name Rm opc size)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__429 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                             __opcode 31 21)) == (0b10111000101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                             __opcode 11 10)) == (0b10#2 : (BitVec 2)))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__428 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__428 <b 660) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__429 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 660
                                                      let Rt := (BitVec.slice __opcode 0 5)
                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                      let S := (BitVec.slice __opcode 12 1)
                                                      let option_name :=
                                                        (BitVec.slice __opcode 13 3)
                                                      let Rm := (BitVec.slice __opcode 16 5)
                                                      let opc := (BitVec.slice __opcode 22 2)
                                                      let size := (BitVec.slice __opcode 30 2)
                                                      (decode_ldrsw_reg_aarch64_instrs_memory_single_general_register
                                                        Rt Rn S option_name Rm opc size)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__432 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                 __opcode 31 21)) == (0b11111000101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 14 14)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                   __opcode 11 10)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            if ((let b__0 :=
                                                                 (BitVec.slice __opcode 0 5)
                                                               ((! (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                        b__0 4 3)) == (0b11#2 : (BitVec 2))) : Bool)
                                                                 then true
                                                                 else false : Bool)) : Bool)) : Bool)
                                                            then
                                                              (do
                                                                let w__430 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__430 <b 661) : Bool))))
                                                            else (pure false))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__432 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 661
                                                          let Rt := (BitVec.slice __opcode 0 5)
                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                          let S := (BitVec.slice __opcode 12 1)
                                                          let option_name :=
                                                            (BitVec.slice __opcode 13 3)
                                                          let Rm := (BitVec.slice __opcode 16 5)
                                                          let opc := (BitVec.slice __opcode 22 2)
                                                          let size := (BitVec.slice __opcode 30 2)
                                                          (decode_prfm_reg_aarch64_instrs_memory_single_general_register
                                                            Rt Rn S option_name Rm opc size)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__434 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                     __opcode 31 31)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                       __opcode 29 21)) == (0b111000001#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                       __opcode 11 10)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__433 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__433 <b 662) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__434 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 662
                                                              let Rt := (BitVec.slice __opcode 0 5)
                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                              let S := (BitVec.slice __opcode 12 1)
                                                              let option_name :=
                                                                (BitVec.slice __opcode 13 3)
                                                              let Rm := (BitVec.slice __opcode 16 5)
                                                              let opc :=
                                                                (BitVec.slice __opcode 22 2)
                                                              let size :=
                                                                (BitVec.slice __opcode 30 2)
                                                              (decode_str_reg_gen_aarch64_instrs_memory_single_general_register
                                                                Rt Rn S option_name Rm opc size)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__436 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                         __opcode 31 21)) == (0b00111000001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                         __opcode 11 10)) == (0b10#2 : (BitVec 2)))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__435 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__435 <b 663) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__436 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 663
                                                                  let Rt :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let S :=
                                                                    (BitVec.slice __opcode 12 1)
                                                                  let option_name :=
                                                                    (BitVec.slice __opcode 13 3)
                                                                  let Rm :=
                                                                    (BitVec.slice __opcode 16 5)
                                                                  let opc :=
                                                                    (BitVec.slice __opcode 22 2)
                                                                  let size :=
                                                                    (BitVec.slice __opcode 30 2)
                                                                  (decode_strb_reg_aarch64_instrs_memory_single_general_register
                                                                    Rt Rn S option_name Rm opc size)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__438 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                             __opcode 31 21)) == (0b01111000001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                             __opcode 11 10)) == (0b10#2 : (BitVec 2)))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__437 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__437 <b 664) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__438 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 664
                                                                      let Rt :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let S :=
                                                                        (BitVec.slice __opcode 12 1)
                                                                      let option_name :=
                                                                        (BitVec.slice __opcode 13 3)
                                                                      let Rm :=
                                                                        (BitVec.slice __opcode 16 5)
                                                                      let opc :=
                                                                        (BitVec.slice __opcode 22 2)
                                                                      let size :=
                                                                        (BitVec.slice __opcode 30 2)
                                                                      (decode_strh_reg_aarch64_instrs_memory_single_general_register
                                                                        Rt Rn S option_name Rm opc
                                                                        size)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__440 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                 __opcode 29 24)) == (0b111100#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                   __opcode 22 21)) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                   __opcode 11 10)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__439 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__439 <b 665) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__440 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 665
                                                                          let Rt :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let S :=
                                                                            (BitVec.slice __opcode
                                                                              12 1)
                                                                          let option_name :=
                                                                            (BitVec.slice __opcode
                                                                              13 3)
                                                                          let Rm :=
                                                                            (BitVec.slice __opcode
                                                                              16 5)
                                                                          let opc :=
                                                                            (BitVec.slice __opcode
                                                                              22 2)
                                                                          let size :=
                                                                            (BitVec.slice __opcode
                                                                              30 2)
                                                                          (decode_ldr_reg_fpsimd_aarch64_instrs_memory_single_simdfp_register
                                                                            Rt Rn S option_name Rm
                                                                            opc size)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__442 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                     __opcode 29 24)) == (0b111100#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                       __opcode 22
                                                                                       21)) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                       __opcode 11
                                                                                       10)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__441 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__441 <b 666) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__442 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 666
                                                                              let Rt :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let S :=
                                                                                (BitVec.slice
                                                                                  __opcode 12 1)
                                                                              let option_name :=
                                                                                (BitVec.slice
                                                                                  __opcode 13 3)
                                                                              let Rm :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 5)
                                                                              let opc :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 2)
                                                                              let size :=
                                                                                (BitVec.slice
                                                                                  __opcode 30 2)
                                                                              (decode_str_reg_fpsimd_aarch64_instrs_memory_single_simdfp_register
                                                                                Rt Rn S option_name
                                                                                Rm opc size)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__444 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         24)) == (0xF8#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           10 10)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__443 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__443 <b 667) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__444 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 667
                                                                                  let Rt :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let W :=
                                                                                    (BitVec.slice
                                                                                      __opcode 11 1)
                                                                                  let imm9 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 12 9)
                                                                                  let S :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 1)
                                                                                  let M :=
                                                                                    (BitVec.slice
                                                                                      __opcode 23 1)
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 30 2)
                                                                                  (decode_ldra_aarch64_instrs_memory_single_general_immediate_signed_pac
                                                                                    Rt Rn W imm9 S M
                                                                                    size)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__446 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 24)) == (0x19#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               15 10)) == (0b001100#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__445 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__445 <b 668) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__446 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 668
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
                                                                                      let o3 :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          15 1)
                                                                                      let Rt2 :=
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
                                                                                      let S :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          30 1)
                                                                                      (decode_ldsetp_aarch64_instrs_memory_atomicops_ld_128_ldsetp
                                                                                        Rt Rn opc o3
                                                                                        Rt2 R A S)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__448 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 31)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   29
                                                                                                   21)) == (0b111000010#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   11
                                                                                                   10)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__447 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__447 <b 669) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__448 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 669
                                                                                          let Rt :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 5)
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let imm9 :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              12 9)
                                                                                          let opc :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 2)
                                                                                          let size :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              30 2)
                                                                                          (decode_ldtr_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv
                                                                                            Rt Rn
                                                                                            imm9 opc
                                                                                            size)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__450 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     21)) == (0b00111000010#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     11
                                                                                                     10)) == (0b10#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__449 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__449 <b 670) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__450 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 670
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
                                                                                              let imm9 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  12
                                                                                                  9)
                                                                                              let opc :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  22
                                                                                                  2)
                                                                                              let size :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  30
                                                                                                  2)
                                                                                              (decode_ldtrb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv
                                                                                                Rt
                                                                                                Rn
                                                                                                imm9
                                                                                                opc
                                                                                                size)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__452 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         21)) == (0b01111000010#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         11
                                                                                                         10)) == (0b10#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__451 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__451 <b 671) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__452 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 671
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
                                                                                                  let imm9 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      12
                                                                                                      9)
                                                                                                  let opc :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      22
                                                                                                      2)
                                                                                                  let size :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      30
                                                                                                      2)
                                                                                                  (decode_ldtrh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv
                                                                                                    Rt
                                                                                                    Rn
                                                                                                    imm9
                                                                                                    opc
                                                                                                    size)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__454 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             23)) == (0b001110001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               21
                                                                                                               21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               11
                                                                                                               10)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__453 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__453 <b 672) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__454 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 672
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
                                                                                                      let imm9 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          12
                                                                                                          9)
                                                                                                      let opc :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          22
                                                                                                          2)
                                                                                                      let size :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          30
                                                                                                          2)
                                                                                                      (decode_ldtrsb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv
                                                                                                        Rt
                                                                                                        Rn
                                                                                                        imm9
                                                                                                        opc
                                                                                                        size)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__456 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 23)) == (0b011110001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   21
                                                                                                                   21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   11
                                                                                                                   10)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__455 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__455 <b 673) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__456 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 673
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
                                                                                                          let imm9 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              12
                                                                                                              9)
                                                                                                          let opc :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              22
                                                                                                              2)
                                                                                                          let size :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              30
                                                                                                              2)
                                                                                                          (decode_ldtrsh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv
                                                                                                            Rt
                                                                                                            Rn
                                                                                                            imm9
                                                                                                            opc
                                                                                                            size)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__458 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     21)) == (0b10111000100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     11
                                                                                                                     10)) == (0b10#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__457 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__457 <b 674) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__458 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 674
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
                                                                                                              let imm9 :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  12
                                                                                                                  9)
                                                                                                              let opc :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  22
                                                                                                                  2)
                                                                                                              let size :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  30
                                                                                                                  2)
                                                                                                              (decode_ldtrsw_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv
                                                                                                                Rt
                                                                                                                Rn
                                                                                                                imm9
                                                                                                                opc
                                                                                                                size)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__460 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         31)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           29
                                                                                                                           21)) == (0b111000000#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           11
                                                                                                                           10)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__459 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__459 <b 675) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__460 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 675
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
                                                                                                                  let imm9 :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      12
                                                                                                                      9)
                                                                                                                  let opc :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      22
                                                                                                                      2)
                                                                                                                  let size :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      30
                                                                                                                      2)
                                                                                                                  (decode_sttr_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv
                                                                                                                    Rt
                                                                                                                    Rn
                                                                                                                    imm9
                                                                                                                    opc
                                                                                                                    size)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__462 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             21)) == (0b00111000000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             11
                                                                                                                             10)) == (0b10#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__461 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__461 <b 676) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__462 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 676
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
                                                                                                                      let imm9 :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          12
                                                                                                                          9)
                                                                                                                      let opc :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          22
                                                                                                                          2)
                                                                                                                      let size :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          30
                                                                                                                          2)
                                                                                                                      (decode_sttrb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv
                                                                                                                        Rt
                                                                                                                        Rn
                                                                                                                        imm9
                                                                                                                        opc
                                                                                                                        size)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__464 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 21)) == (0b01111000000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 11
                                                                                                                                 10)) == (0b10#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__463 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__463 <b 677) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__464 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 677
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
                                                                                                                          let imm9 :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              12
                                                                                                                              9)
                                                                                                                          let opc :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              22
                                                                                                                              2)
                                                                                                                          let size :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              30
                                                                                                                              2)
                                                                                                                          (decode_sttrh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv
                                                                                                                            Rt
                                                                                                                            Rn
                                                                                                                            imm9
                                                                                                                            opc
                                                                                                                            size)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__466 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     29
                                                                                                                                     24)) == (0b111100#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       22
                                                                                                                                       21)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       11
                                                                                                                                       10)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__465 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__465 <b 678) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__466 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 678
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
                                                                                                                              let imm9 :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  12
                                                                                                                                  9)
                                                                                                                              let opc :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  22
                                                                                                                                  2)
                                                                                                                              let size :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  30
                                                                                                                                  2)
                                                                                                                              (decode_ldur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal
                                                                                                                                Rt
                                                                                                                                Rn
                                                                                                                                imm9
                                                                                                                                opc
                                                                                                                                size)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__468 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         29
                                                                                                                                         24)) == (0b111100#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           22
                                                                                                                                           21)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           11
                                                                                                                                           10)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__467 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__467 <b 679) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__468 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 679
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
                                                                                                                                  let imm9 :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      12
                                                                                                                                      9)
                                                                                                                                  let opc :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      22
                                                                                                                                      2)
                                                                                                                                  let size :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      30
                                                                                                                                      2)
                                                                                                                                  (decode_stur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal
                                                                                                                                    Rt
                                                                                                                                    Rn
                                                                                                                                    imm9
                                                                                                                                    opc
                                                                                                                                    size)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__470 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             31)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               29
                                                                                                                                               21)) == (0b111000010#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               11
                                                                                                                                               10)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__469 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__469 <b 680) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__470 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 680
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
                                                                                                                                      let imm9 :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          12
                                                                                                                                          9)
                                                                                                                                      let opc :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          22
                                                                                                                                          2)
                                                                                                                                      let size :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          30
                                                                                                                                          2)
                                                                                                                                      (decode_ldur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal
                                                                                                                                        Rt
                                                                                                                                        Rn
                                                                                                                                        imm9
                                                                                                                                        opc
                                                                                                                                        size)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__472 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 21)) == (0b00111000010#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 11
                                                                                                                                                 10)) == (0b00#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__471 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__471 <b 681) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__472 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 681
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
                                                                                                                                          let imm9 :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              12
                                                                                                                                              9)
                                                                                                                                          let opc :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              22
                                                                                                                                              2)
                                                                                                                                          let size :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              30
                                                                                                                                              2)
                                                                                                                                          (decode_ldurb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal
                                                                                                                                            Rt
                                                                                                                                            Rn
                                                                                                                                            imm9
                                                                                                                                            opc
                                                                                                                                            size)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__474 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     21)) == (0b01111000010#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     11
                                                                                                                                                     10)) == (0b00#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__473 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__473 <b 682) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__474 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 682
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
                                                                                                                                              let imm9 :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  12
                                                                                                                                                  9)
                                                                                                                                              let opc :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  22
                                                                                                                                                  2)
                                                                                                                                              let size :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  30
                                                                                                                                                  2)
                                                                                                                                              (decode_ldurh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal
                                                                                                                                                Rt
                                                                                                                                                Rn
                                                                                                                                                imm9
                                                                                                                                                opc
                                                                                                                                                size)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__476 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         31
                                                                                                                                                         23)) == (0b001110001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           21
                                                                                                                                                           21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           11
                                                                                                                                                           10)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__475 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__475 <b 683) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__476 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 683
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
                                                                                                                                                  let imm9 :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      12
                                                                                                                                                      9)
                                                                                                                                                  let opc :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      22
                                                                                                                                                      2)
                                                                                                                                                  let size :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      30
                                                                                                                                                      2)
                                                                                                                                                  (decode_ldursb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal
                                                                                                                                                    Rt
                                                                                                                                                    Rn
                                                                                                                                                    imm9
                                                                                                                                                    opc
                                                                                                                                                    size)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__478 ← (( do
                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             31
                                                                                                                                                             23)) == (0b011110001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                               __opcode
                                                                                                                                                               21
                                                                                                                                                               21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                               __opcode
                                                                                                                                                               11
                                                                                                                                                               10)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__477 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__477 <b 684) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__478 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 684
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
                                                                                                                                                      let imm9 :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          12
                                                                                                                                                          9)
                                                                                                                                                      let opc :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          22
                                                                                                                                                          2)
                                                                                                                                                      let size :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          30
                                                                                                                                                          2)
                                                                                                                                                      (decode_ldursh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal
                                                                                                                                                        Rt
                                                                                                                                                        Rn
                                                                                                                                                        imm9
                                                                                                                                                        opc
                                                                                                                                                        size)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__480 ← (( do
                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 31
                                                                                                                                                                 21)) == (0b10111000100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 11
                                                                                                                                                                 10)) == (0b00#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__479 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__479 <b 685) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false)
                                                                                                                                                        )
                                                                                                                                                        :
                                                                                                                                                        SailM
                                                                                                                                                        Bool
                                                                                                                                                        )
                                                                                                                                                      if (w__480 : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 685
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
                                                                                                                                                          let imm9 :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              12
                                                                                                                                                              9)
                                                                                                                                                          let opc :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              22
                                                                                                                                                              2)
                                                                                                                                                          let size :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              30
                                                                                                                                                              2)
                                                                                                                                                          (decode_ldursw_aarch64_instrs_memory_single_general_immediate_signed_offset_normal
                                                                                                                                                            Rt
                                                                                                                                                            Rn
                                                                                                                                                            imm9
                                                                                                                                                            opc
                                                                                                                                                            size)
                                                                                                                                                          (pure false))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          let w__482 ← (( do
                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     31
                                                                                                                                                                     21)) == (0b11111000100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     11
                                                                                                                                                                     10)) == (0b00#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let w__481 ← (( do
                                                                                                                                                                  readReg SEE
                                                                                                                                                                  )
                                                                                                                                                                  :
                                                                                                                                                                  SailM
                                                                                                                                                                  Int
                                                                                                                                                                  )
                                                                                                                                                                (pure (((w__481 <b 686) : Bool))))
                                                                                                                                                            else
                                                                                                                                                              (pure false)
                                                                                                                                                            )
                                                                                                                                                            :
                                                                                                                                                            SailM
                                                                                                                                                            Bool
                                                                                                                                                            )
                                                                                                                                                          if (w__482 : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 686
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
                                                                                                                                                              let imm9 :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  12
                                                                                                                                                                  9)
                                                                                                                                                              let opc :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  22
                                                                                                                                                                  2)
                                                                                                                                                              let size :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  30
                                                                                                                                                                  2)
                                                                                                                                                              (decode_prfum_aarch64_instrs_memory_single_general_immediate_signed_offset_normal
                                                                                                                                                                Rt
                                                                                                                                                                Rn
                                                                                                                                                                imm9
                                                                                                                                                                opc
                                                                                                                                                                size)
                                                                                                                                                              (pure false))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              let w__484 ← (( do
                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         31
                                                                                                                                                                         31)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           29
                                                                                                                                                                           21)) == (0b111000000#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           11
                                                                                                                                                                           10)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    let w__483 ← (( do
                                                                                                                                                                      readReg SEE
                                                                                                                                                                      )
                                                                                                                                                                      :
                                                                                                                                                                      SailM
                                                                                                                                                                      Int
                                                                                                                                                                      )
                                                                                                                                                                    (pure (((w__483 <b 687) : Bool))))
                                                                                                                                                                else
                                                                                                                                                                  (pure false)
                                                                                                                                                                )
                                                                                                                                                                :
                                                                                                                                                                SailM
                                                                                                                                                                Bool
                                                                                                                                                                )
                                                                                                                                                              if (w__484 : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 687
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
                                                                                                                                                                  let imm9 :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      12
                                                                                                                                                                      9)
                                                                                                                                                                  let opc :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      22
                                                                                                                                                                      2)
                                                                                                                                                                  let size :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      30
                                                                                                                                                                      2)
                                                                                                                                                                  (decode_stur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal
                                                                                                                                                                    Rt
                                                                                                                                                                    Rn
                                                                                                                                                                    imm9
                                                                                                                                                                    opc
                                                                                                                                                                    size)
                                                                                                                                                                  (pure false))
                                                                                                                                                              else
                                                                                                                                                                (pure true))))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
