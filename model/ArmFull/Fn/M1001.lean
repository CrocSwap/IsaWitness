import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0169
import ArmFull.Fn.M0170
import ArmFull.Fn.M0171
import ArmFull.Fn.M0177
import ArmFull.Fn.M0178
import ArmFull.Fn.M0240
import ArmFull.Fn.M0245
import ArmFull.Fn.M0843
import ArmFull.Fn.M0853

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
def __DecodeA64_DataProcReg (pc : Int) (__opcode : (BitVec 32)) : SailM Unit := do
  let w__1 ← (( do
    if ((((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb __opcode 30 10)) == (0b101101011000000001000#21 : (BitVec 21))) : Bool) : Bool)
    then
      (do
        let w__0 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__0 <b 1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      writeReg SEE 1
      let Rd := (BitVec.slice __opcode 0 5)
      let Rn := (BitVec.slice __opcode 5 5)
      let sf := (BitVec.slice __opcode 31 1)
      (decode_abs_aarch64_instrs_integer_arithmetic_unary_abs Rd Rn sf))
  else
    (do
      let w__3 ← (( do
        if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb __opcode 30 21)) == (0b0011010000#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                 __opcode 15 10)) == (0b000000#6 : (BitVec 6)))) : Bool) : Bool)
        then
          (do
            let w__2 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__2 <b 6) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          writeReg SEE 6
          let Rd := (BitVec.slice __opcode 0 5)
          let Rn := (BitVec.slice __opcode 5 5)
          let Rm := (BitVec.slice __opcode 16 5)
          let S := (BitVec.slice __opcode 29 1)
          let op := (BitVec.slice __opcode 30 1)
          let sf := (BitVec.slice __opcode 31 1)
          (decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm S op sf))
      else
        (do
          let w__5 ← (( do
            if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb __opcode 30 21)) == (0b0111010000#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                     __opcode 15 10)) == (0b000000#6 : (BitVec 6)))) : Bool) : Bool)
            then
              (do
                let w__4 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__4 <b 7) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              writeReg SEE 7
              let Rd := (BitVec.slice __opcode 0 5)
              let Rn := (BitVec.slice __opcode 5 5)
              let Rm := (BitVec.slice __opcode 16 5)
              let S := (BitVec.slice __opcode 29 1)
              let op := (BitVec.slice __opcode 30 1)
              let sf := (BitVec.slice __opcode 31 1)
              (decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm S op sf))
          else
            (do
              let w__7 ← (( do
                if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb __opcode 30 21)) == (0b1011010000#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                         __opcode 15 10)) == (0b000000#6 : (BitVec 6)))) : Bool) : Bool)
                then
                  (do
                    let w__6 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__6 <b 8) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__7 : Bool)
              then
                (do
                  writeReg SEE 8
                  let Rd := (BitVec.slice __opcode 0 5)
                  let Rn := (BitVec.slice __opcode 5 5)
                  let Rm := (BitVec.slice __opcode 16 5)
                  let S := (BitVec.slice __opcode 29 1)
                  let op := (BitVec.slice __opcode 30 1)
                  let sf := (BitVec.slice __opcode 31 1)
                  (decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm S op sf))
              else
                (do
                  let w__9 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb __opcode 30 21)) == (0b1111010000#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                             __opcode 15 10)) == (0b000000#6 : (BitVec 6)))) : Bool) : Bool)
                    then
                      (do
                        let w__8 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__8 <b 9) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__9 : Bool)
                  then
                    (do
                      writeReg SEE 9
                      let Rd := (BitVec.slice __opcode 0 5)
                      let Rn := (BitVec.slice __opcode 5 5)
                      let Rm := (BitVec.slice __opcode 16 5)
                      let S := (BitVec.slice __opcode 29 1)
                      let op := (BitVec.slice __opcode 30 1)
                      let sf := (BitVec.slice __opcode 31 1)
                      (decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm S op sf))
                  else
                    (do
                      let w__11 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb __opcode 30
                                 24)) == (0b0001011#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                 __opcode 21 21)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                        then
                          (do
                            let w__10 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__10 <b 14) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__11 : Bool)
                      then
                        (do
                          writeReg SEE 14
                          let Rd := (BitVec.slice __opcode 0 5)
                          let Rn := (BitVec.slice __opcode 5 5)
                          let imm6 := (BitVec.slice __opcode 10 6)
                          let Rm := (BitVec.slice __opcode 16 5)
                          let shift := (BitVec.slice __opcode 22 2)
                          let S := (BitVec.slice __opcode 29 1)
                          let op := (BitVec.slice __opcode 30 1)
                          let sf := (BitVec.slice __opcode 31 1)
                          (decode_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg
                            Rd Rn imm6 Rm shift S op sf))
                      else
                        (do
                          let w__13 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb __opcode
                                     30 24)) == (0b0101011#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                     __opcode 21 21)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                            then
                              (do
                                let w__12 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__12 <b 15) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__13 : Bool)
                          then
                            (do
                              writeReg SEE 15
                              let Rd := (BitVec.slice __opcode 0 5)
                              let Rn := (BitVec.slice __opcode 5 5)
                              let imm6 := (BitVec.slice __opcode 10 6)
                              let Rm := (BitVec.slice __opcode 16 5)
                              let shift := (BitVec.slice __opcode 22 2)
                              let S := (BitVec.slice __opcode 29 1)
                              let op := (BitVec.slice __opcode 30 1)
                              let sf := (BitVec.slice __opcode 31 1)
                              (decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg
                                Rd Rn imm6 Rm shift S op sf))
                          else
                            (do
                              let w__15 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                         __opcode 30 24)) == (0b1001011#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                         __opcode 21 21)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                then
                                  (do
                                    let w__14 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__14 <b 16) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__15 : Bool)
                              then
                                (do
                                  writeReg SEE 16
                                  let Rd := (BitVec.slice __opcode 0 5)
                                  let Rn := (BitVec.slice __opcode 5 5)
                                  let imm6 := (BitVec.slice __opcode 10 6)
                                  let Rm := (BitVec.slice __opcode 16 5)
                                  let shift := (BitVec.slice __opcode 22 2)
                                  let S := (BitVec.slice __opcode 29 1)
                                  let op := (BitVec.slice __opcode 30 1)
                                  let sf := (BitVec.slice __opcode 31 1)
                                  (decode_sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg
                                    Rd Rn imm6 Rm shift S op sf))
                              else
                                (do
                                  let w__17 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                             __opcode 30 24)) == (0b1101011#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             __opcode 21 21)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__16 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__16 <b 17) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__17 : Bool)
                                  then
                                    (do
                                      writeReg SEE 17
                                      let Rd := (BitVec.slice __opcode 0 5)
                                      let Rn := (BitVec.slice __opcode 5 5)
                                      let imm6 := (BitVec.slice __opcode 10 6)
                                      let Rm := (BitVec.slice __opcode 16 5)
                                      let shift := (BitVec.slice __opcode 22 2)
                                      let S := (BitVec.slice __opcode 29 1)
                                      let op := (BitVec.slice __opcode 30 1)
                                      let sf := (BitVec.slice __opcode 31 1)
                                      (decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg
                                        Rd Rn imm6 Rm shift S op sf))
                                  else
                                    (do
                                      let w__19 ← (( do
                                        if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                               __opcode 30 21)) == (0b0001011001#10 : (BitVec 10))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__18 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__18 <b 22) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__19 : Bool)
                                      then
                                        (do
                                          writeReg SEE 22
                                          let Rd := (BitVec.slice __opcode 0 5)
                                          let Rn := (BitVec.slice __opcode 5 5)
                                          let imm3 := (BitVec.slice __opcode 10 3)
                                          let option_name := (BitVec.slice __opcode 13 3)
                                          let Rm := (BitVec.slice __opcode 16 5)
                                          let S := (BitVec.slice __opcode 29 1)
                                          let op := (BitVec.slice __opcode 30 1)
                                          let sf := (BitVec.slice __opcode 31 1)
                                          (decode_add_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg
                                            Rd Rn imm3 option_name Rm S op sf))
                                      else
                                        (do
                                          let w__21 ← (( do
                                            if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                   __opcode 30 21)) == (0b0101011001#10 : (BitVec 10))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__20 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__20 <b 23) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__21 : Bool)
                                          then
                                            (do
                                              writeReg SEE 23
                                              let Rd := (BitVec.slice __opcode 0 5)
                                              let Rn := (BitVec.slice __opcode 5 5)
                                              let imm3 := (BitVec.slice __opcode 10 3)
                                              let option_name := (BitVec.slice __opcode 13 3)
                                              let Rm := (BitVec.slice __opcode 16 5)
                                              let S := (BitVec.slice __opcode 29 1)
                                              let op := (BitVec.slice __opcode 30 1)
                                              let sf := (BitVec.slice __opcode 31 1)
                                              (decode_adds_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg
                                                Rd Rn imm3 option_name Rm S op sf))
                                          else
                                            (do
                                              let w__23 ← (( do
                                                if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                       __opcode 30 21)) == (0b1001011001#10 : (BitVec 10))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__22 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__22 <b 24) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__23 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 24
                                                  let Rd := (BitVec.slice __opcode 0 5)
                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                  let imm3 := (BitVec.slice __opcode 10 3)
                                                  let option_name := (BitVec.slice __opcode 13 3)
                                                  let Rm := (BitVec.slice __opcode 16 5)
                                                  let S := (BitVec.slice __opcode 29 1)
                                                  let op := (BitVec.slice __opcode 30 1)
                                                  let sf := (BitVec.slice __opcode 31 1)
                                                  (decode_sub_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg
                                                    Rd Rn imm3 option_name Rm S op sf))
                                              else
                                                (do
                                                  let w__25 ← (( do
                                                    if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                           __opcode 30 21)) == (0b1101011001#10 : (BitVec 10))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__24 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__24 <b 25) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__25 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 25
                                                      let Rd := (BitVec.slice __opcode 0 5)
                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                      let imm3 := (BitVec.slice __opcode 10 3)
                                                      let option_name :=
                                                        (BitVec.slice __opcode 13 3)
                                                      let Rm := (BitVec.slice __opcode 16 5)
                                                      let S := (BitVec.slice __opcode 29 1)
                                                      let op := (BitVec.slice __opcode 30 1)
                                                      let sf := (BitVec.slice __opcode 31 1)
                                                      (decode_subs_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg
                                                        Rd Rn imm3 option_name Rm S op sf))
                                                  else
                                                    (do
                                                      let w__27 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                 __opcode 30 24)) == (0b0001010#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                 __opcode 21 21)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__26 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__26 <b 48) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__27 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 48
                                                          let Rd := (BitVec.slice __opcode 0 5)
                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                          let imm6 := (BitVec.slice __opcode 10 6)
                                                          let Rm := (BitVec.slice __opcode 16 5)
                                                          let N := (BitVec.slice __opcode 21 1)
                                                          let shift := (BitVec.slice __opcode 22 2)
                                                          let opc := (BitVec.slice __opcode 29 2)
                                                          let sf := (BitVec.slice __opcode 31 1)
                                                          (decode_and_log_shift_aarch64_instrs_integer_logical_shiftedreg
                                                            Rd Rn imm6 Rm N shift opc sf))
                                                      else
                                                        (do
                                                          let w__29 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                     __opcode 30 24)) == (0b1101010#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                     __opcode 21 21)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__28 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__28 <b 49) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__29 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 49
                                                              let Rd := (BitVec.slice __opcode 0 5)
                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                              let imm6 :=
                                                                (BitVec.slice __opcode 10 6)
                                                              let Rm := (BitVec.slice __opcode 16 5)
                                                              let N := (BitVec.slice __opcode 21 1)
                                                              let shift :=
                                                                (BitVec.slice __opcode 22 2)
                                                              let opc :=
                                                                (BitVec.slice __opcode 29 2)
                                                              let sf := (BitVec.slice __opcode 31 1)
                                                              (decode_ands_log_shift_aarch64_instrs_integer_logical_shiftedreg
                                                                Rd Rn imm6 Rm N shift opc sf))
                                                          else
                                                            (do
                                                              let w__31 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                         __opcode 30 24)) == (0b0001010#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                         __opcode 21 21)) == (1#1 : (BitVec 1)))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__30 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__30 <b 50) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__31 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 50
                                                                  let Rd :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let imm6 :=
                                                                    (BitVec.slice __opcode 10 6)
                                                                  let Rm :=
                                                                    (BitVec.slice __opcode 16 5)
                                                                  let N :=
                                                                    (BitVec.slice __opcode 21 1)
                                                                  let shift :=
                                                                    (BitVec.slice __opcode 22 2)
                                                                  let opc :=
                                                                    (BitVec.slice __opcode 29 2)
                                                                  let sf :=
                                                                    (BitVec.slice __opcode 31 1)
                                                                  (decode_bic_log_shift_aarch64_instrs_integer_logical_shiftedreg
                                                                    Rd Rn imm6 Rm N shift opc sf))
                                                              else
                                                                (do
                                                                  let w__33 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                             __opcode 30 24)) == (0b1101010#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                             __opcode 21 21)) == (1#1 : (BitVec 1)))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__32 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__32 <b 51) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__33 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 51
                                                                      let Rd :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let imm6 :=
                                                                        (BitVec.slice __opcode 10 6)
                                                                      let Rm :=
                                                                        (BitVec.slice __opcode 16 5)
                                                                      let N :=
                                                                        (BitVec.slice __opcode 21 1)
                                                                      let shift :=
                                                                        (BitVec.slice __opcode 22 2)
                                                                      let opc :=
                                                                        (BitVec.slice __opcode 29 2)
                                                                      let sf :=
                                                                        (BitVec.slice __opcode 31 1)
                                                                      (decode_bics_aarch64_instrs_integer_logical_shiftedreg
                                                                        Rd Rn imm6 Rm N shift opc sf))
                                                                  else
                                                                    (do
                                                                      let w__35 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                 __opcode 30 24)) == (0b1001010#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 21 21)) == (1#1 : (BitVec 1)))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__34 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__34 <b 52) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__35 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 52
                                                                          let Rd :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let imm6 :=
                                                                            (BitVec.slice __opcode
                                                                              10 6)
                                                                          let Rm :=
                                                                            (BitVec.slice __opcode
                                                                              16 5)
                                                                          let N :=
                                                                            (BitVec.slice __opcode
                                                                              21 1)
                                                                          let shift :=
                                                                            (BitVec.slice __opcode
                                                                              22 2)
                                                                          let opc :=
                                                                            (BitVec.slice __opcode
                                                                              29 2)
                                                                          let sf :=
                                                                            (BitVec.slice __opcode
                                                                              31 1)
                                                                          (decode_eon_aarch64_instrs_integer_logical_shiftedreg
                                                                            Rd Rn imm6 Rm N shift
                                                                            opc sf))
                                                                      else
                                                                        (do
                                                                          let w__37 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                     __opcode 30 24)) == (0b1001010#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                     __opcode 21 21)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__36 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__36 <b 53) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__37 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 53
                                                                              let Rd :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let imm6 :=
                                                                                (BitVec.slice
                                                                                  __opcode 10 6)
                                                                              let Rm :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 5)
                                                                              let N :=
                                                                                (BitVec.slice
                                                                                  __opcode 21 1)
                                                                              let shift :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 2)
                                                                              let opc :=
                                                                                (BitVec.slice
                                                                                  __opcode 29 2)
                                                                              let sf :=
                                                                                (BitVec.slice
                                                                                  __opcode 31 1)
                                                                              (decode_eor_log_shift_aarch64_instrs_integer_logical_shiftedreg
                                                                                Rd Rn imm6 Rm N
                                                                                shift opc sf))
                                                                          else
                                                                            (do
                                                                              let w__39 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                         __opcode 30
                                                                                         24)) == (0b0101010#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                         __opcode 21
                                                                                         21)) == (1#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__38 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__38 <b 54) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__39 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 54
                                                                                  let Rd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let imm6 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 10 6)
                                                                                  let Rm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 5)
                                                                                  let N :=
                                                                                    (BitVec.slice
                                                                                      __opcode 21 1)
                                                                                  let shift :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 2)
                                                                                  let opc :=
                                                                                    (BitVec.slice
                                                                                      __opcode 29 2)
                                                                                  let sf :=
                                                                                    (BitVec.slice
                                                                                      __opcode 31 1)
                                                                                  (decode_orn_log_shift_aarch64_instrs_integer_logical_shiftedreg
                                                                                    Rd Rn imm6 Rm N
                                                                                    shift opc sf))
                                                                              else
                                                                                (do
                                                                                  let w__41 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             30 24)) == (0b0101010#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             21 21)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__40 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__40 <b 55) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__41 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 55
                                                                                      let Rd :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          5)
                                                                                      let Rn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let imm6 :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          10 6)
                                                                                      let Rm :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 5)
                                                                                      let N :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          21 1)
                                                                                      let shift :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 2)
                                                                                      let opc :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          29 2)
                                                                                      let sf :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          31 1)
                                                                                      (decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg
                                                                                        Rd Rn imm6
                                                                                        Rm N shift
                                                                                        opc sf))
                                                                                  else
                                                                                    (do
                                                                                      let w__43 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 30
                                                                                                 21)) == (0b0011010110#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 15
                                                                                                 10)) == (0b001010#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__42 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__42 <b 56) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__43 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 56
                                                                                          let Rd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 5)
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let op2 :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              10 2)
                                                                                          let Rm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 5)
                                                                                          let sf :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              31 1)
                                                                                          (decode_asrv_aarch64_instrs_integer_shift_variable
                                                                                            Rd Rn
                                                                                            op2 Rm
                                                                                            sf))
                                                                                      else
                                                                                        (do
                                                                                          let w__45 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     30
                                                                                                     21)) == (0b0011010110#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     15
                                                                                                     10)) == (0b001000#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__44 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__44 <b 57) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__45 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 57
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
                                                                                              let op2 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  10
                                                                                                  2)
                                                                                              let Rm :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  5)
                                                                                              let sf :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  31
                                                                                                  1)
                                                                                              (decode_lslv_aarch64_instrs_integer_shift_variable
                                                                                                Rd
                                                                                                Rn
                                                                                                op2
                                                                                                Rm
                                                                                                sf))
                                                                                          else
                                                                                            (do
                                                                                              let w__47 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         30
                                                                                                         21)) == (0b0011010110#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         15
                                                                                                         10)) == (0b001001#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__46 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__46 <b 58) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__47 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 58
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
                                                                                                  let op2 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      10
                                                                                                      2)
                                                                                                  let Rm :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      5)
                                                                                                  let sf :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      31
                                                                                                      1)
                                                                                                  (decode_lsrv_aarch64_instrs_integer_shift_variable
                                                                                                    Rd
                                                                                                    Rn
                                                                                                    op2
                                                                                                    Rm
                                                                                                    sf))
                                                                                              else
                                                                                                (do
                                                                                                  let w__49 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             30
                                                                                                             21)) == (0b0011010110#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             15
                                                                                                             10)) == (0b001011#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__48 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__48 <b 59) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__49 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 59
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
                                                                                                      let op2 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          10
                                                                                                          2)
                                                                                                      let Rm :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          5)
                                                                                                      let sf :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          31
                                                                                                          1)
                                                                                                      (decode_rorv_aarch64_instrs_integer_shift_variable
                                                                                                        Rd
                                                                                                        Rn
                                                                                                        op2
                                                                                                        Rm
                                                                                                        sf))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__51 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 14)) == (0b110110101100000100#18 : (BitVec 18))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 12
                                                                                                                 10)) == (0b110#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__50 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__50 <b 60) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__51 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 60
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
                                                                                                          let Z :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              13
                                                                                                              1)
                                                                                                          (decode_autda_aarch64_instrs_integer_pac_autda_dp_1src
                                                                                                            Rd
                                                                                                            Rn
                                                                                                            Z))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__53 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     14)) == (0b110110101100000100#18 : (BitVec 18))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     12
                                                                                                                     10)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__52 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__52 <b 61) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__53 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 61
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
                                                                                                              let Z :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  13
                                                                                                                  1)
                                                                                                              (decode_autdb_aarch64_instrs_integer_pac_autdb_dp_1src
                                                                                                                Rd
                                                                                                                Rn
                                                                                                                Z))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__55 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         14)) == (0b110110101100000100#18 : (BitVec 18))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         12
                                                                                                                         10)) == (0b100#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__54 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__54 <b 62) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__55 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 62
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
                                                                                                                  let Z :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      13
                                                                                                                      1)
                                                                                                                  (decode_autia_aarch64_instrs_integer_pac_autia_dp_1src
                                                                                                                    Rd
                                                                                                                    Rn
                                                                                                                    Z))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__57 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             14)) == (0b110110101100000100#18 : (BitVec 18))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             12
                                                                                                                             10)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__56 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__56 <b 64) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__57 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 64
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
                                                                                                                      let Z :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          13
                                                                                                                          1)
                                                                                                                      (decode_autib_aarch64_instrs_integer_pac_autib_dp_1src
                                                                                                                        Rd
                                                                                                                        Rn
                                                                                                                        Z))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__59 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 30
                                                                                                                                 21)) == (0b0111010010#10 : (BitVec 10))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   11
                                                                                                                                   10)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   4
                                                                                                                                   4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__58 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__58 <b 119) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__59 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 119
                                                                                                                          let nzcv :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              4)
                                                                                                                          let Rn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              5
                                                                                                                              5)
                                                                                                                          let cond :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              12
                                                                                                                              4)
                                                                                                                          let Rm :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              5)
                                                                                                                          let op :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              30
                                                                                                                              1)
                                                                                                                          let sf :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              31
                                                                                                                              1)
                                                                                                                          (decode_ccmn_reg_aarch64_instrs_integer_conditional_compare_register
                                                                                                                            nzcv
                                                                                                                            Rn
                                                                                                                            cond
                                                                                                                            Rm
                                                                                                                            op
                                                                                                                            sf))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__61 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     30
                                                                                                                                     21)) == (0b1111010010#10 : (BitVec 10))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       11
                                                                                                                                       10)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       4
                                                                                                                                       4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__60 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__60 <b 120) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__61 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 120
                                                                                                                              let nzcv :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  4)
                                                                                                                              let Rn :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  5
                                                                                                                                  5)
                                                                                                                              let cond :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  12
                                                                                                                                  4)
                                                                                                                              let Rm :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
                                                                                                                                  5)
                                                                                                                              let op :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  30
                                                                                                                                  1)
                                                                                                                              let sf :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  31
                                                                                                                                  1)
                                                                                                                              (decode_ccmp_reg_aarch64_instrs_integer_conditional_compare_register
                                                                                                                                nzcv
                                                                                                                                Rn
                                                                                                                                cond
                                                                                                                                Rm
                                                                                                                                op
                                                                                                                                sf))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__63 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         30
                                                                                                                                         21)) == (0b0111010010#10 : (BitVec 10))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           11
                                                                                                                                           10)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           4
                                                                                                                                           4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__62 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__62 <b 121) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__63 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 121
                                                                                                                                  let nzcv :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      4)
                                                                                                                                  let Rn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      5
                                                                                                                                      5)
                                                                                                                                  let cond :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      12
                                                                                                                                      4)
                                                                                                                                  let imm5 :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      5)
                                                                                                                                  let op :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      30
                                                                                                                                      1)
                                                                                                                                  let sf :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      31
                                                                                                                                      1)
                                                                                                                                  (decode_ccmn_imm_aarch64_instrs_integer_conditional_compare_immediate
                                                                                                                                    nzcv
                                                                                                                                    Rn
                                                                                                                                    cond
                                                                                                                                    imm5
                                                                                                                                    op
                                                                                                                                    sf))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__65 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             30
                                                                                                                                             21)) == (0b1111010010#10 : (BitVec 10))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               11
                                                                                                                                               10)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               4
                                                                                                                                               4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__64 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__64 <b 122) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__65 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 122
                                                                                                                                      let nzcv :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          4)
                                                                                                                                      let Rn :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          5
                                                                                                                                          5)
                                                                                                                                      let cond :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          12
                                                                                                                                          4)
                                                                                                                                      let imm5 :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          16
                                                                                                                                          5)
                                                                                                                                      let op :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          30
                                                                                                                                          1)
                                                                                                                                      let sf :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          31
                                                                                                                                          1)
                                                                                                                                      (decode_ccmp_imm_aarch64_instrs_integer_conditional_compare_immediate
                                                                                                                                        nzcv
                                                                                                                                        Rn
                                                                                                                                        cond
                                                                                                                                        imm5
                                                                                                                                        op
                                                                                                                                        sf))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__67 ← (( do
                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               30
                                                                                                                                               10)) == (0b101101011000000000101#21 : (BitVec 21))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__66 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__66 <b 127) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__67 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 127
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
                                                                                                                                              10
                                                                                                                                              1)
                                                                                                                                          let sf :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              31
                                                                                                                                              1)
                                                                                                                                          (decode_cls_int_aarch64_instrs_integer_arithmetic_cnt
                                                                                                                                            Rd
                                                                                                                                            Rn
                                                                                                                                            op
                                                                                                                                            sf))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__69 ← (( do
                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   30
                                                                                                                                                   10)) == (0b101101011000000000100#21 : (BitVec 21))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__68 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__68 <b 128) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__69 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 128
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
                                                                                                                                                  10
                                                                                                                                                  1)
                                                                                                                                              let sf :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  31
                                                                                                                                                  1)
                                                                                                                                              (decode_clz_int_aarch64_instrs_integer_arithmetic_cnt
                                                                                                                                                Rd
                                                                                                                                                Rn
                                                                                                                                                op
                                                                                                                                                sf))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__71 ← (( do
                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       30
                                                                                                                                                       10)) == (0b101101011000000000111#21 : (BitVec 21))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__70 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__70 <b 151) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__71 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 151
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
                                                                                                                                                  let sf :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      31
                                                                                                                                                      1)
                                                                                                                                                  (decode_cnt_aarch64_instrs_integer_arithmetic_unary_cnt
                                                                                                                                                    Rd
                                                                                                                                                    Rn
                                                                                                                                                    sf))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__73 ← (( do
                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             30
                                                                                                                                                             21)) == (0b0011010110#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             15
                                                                                                                                                             12)) == (0x4#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__72 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__72 <b 185) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__73 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 185
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
                                                                                                                                                          10
                                                                                                                                                          2)
                                                                                                                                                      let C :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          12
                                                                                                                                                          1)
                                                                                                                                                      let Rm :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          16
                                                                                                                                                          5)
                                                                                                                                                      let sf :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          31
                                                                                                                                                          1)
                                                                                                                                                      (decode_crc32_aarch64_instrs_integer_crc
                                                                                                                                                        Rd
                                                                                                                                                        Rn
                                                                                                                                                        sz
                                                                                                                                                        C
                                                                                                                                                        Rm
                                                                                                                                                        sf))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__75 ← (( do
                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 30
                                                                                                                                                                 21)) == (0b0011010110#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 15
                                                                                                                                                                 12)) == (0x5#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__74 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__74 <b 186) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false)
                                                                                                                                                        )
                                                                                                                                                        :
                                                                                                                                                        SailM
                                                                                                                                                        Bool
                                                                                                                                                        )
                                                                                                                                                      if (w__75 : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 186
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
                                                                                                                                                              10
                                                                                                                                                              2)
                                                                                                                                                          let C :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              12
                                                                                                                                                              1)
                                                                                                                                                          let Rm :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              16
                                                                                                                                                              5)
                                                                                                                                                          let sf :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              31
                                                                                                                                                              1)
                                                                                                                                                          (decode_crc32c_aarch64_instrs_integer_crc
                                                                                                                                                            Rd
                                                                                                                                                            Rn
                                                                                                                                                            sz
                                                                                                                                                            C
                                                                                                                                                            Rm
                                                                                                                                                            sf))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          let w__77 ← (( do
                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     30
                                                                                                                                                                     21)) == (0b0011010100#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     11
                                                                                                                                                                     10)) == (0b00#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let w__76 ← (( do
                                                                                                                                                                  readReg SEE
                                                                                                                                                                  )
                                                                                                                                                                  :
                                                                                                                                                                  SailM
                                                                                                                                                                  Int
                                                                                                                                                                  )
                                                                                                                                                                (pure (((w__76 <b 187) : Bool))))
                                                                                                                                                            else
                                                                                                                                                              (pure false)
                                                                                                                                                            )
                                                                                                                                                            :
                                                                                                                                                            SailM
                                                                                                                                                            Bool
                                                                                                                                                            )
                                                                                                                                                          if (w__77 : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 187
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
                                                                                                                                                              let o2 :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  10
                                                                                                                                                                  1)
                                                                                                                                                              let cond :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  12
                                                                                                                                                                  4)
                                                                                                                                                              let Rm :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  16
                                                                                                                                                                  5)
                                                                                                                                                              let op :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  30
                                                                                                                                                                  1)
                                                                                                                                                              let sf :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  31
                                                                                                                                                                  1)
                                                                                                                                                              (decode_csel_aarch64_instrs_integer_conditional_select
                                                                                                                                                                Rd
                                                                                                                                                                Rn
                                                                                                                                                                o2
                                                                                                                                                                cond
                                                                                                                                                                Rm
                                                                                                                                                                op
                                                                                                                                                                sf))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              let w__79 ← (( do
                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         30
                                                                                                                                                                         21)) == (0b0011010100#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         11
                                                                                                                                                                         10)) == (0b01#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    let w__78 ← (( do
                                                                                                                                                                      readReg SEE
                                                                                                                                                                      )
                                                                                                                                                                      :
                                                                                                                                                                      SailM
                                                                                                                                                                      Int
                                                                                                                                                                      )
                                                                                                                                                                    (pure (((w__78 <b 188) : Bool))))
                                                                                                                                                                else
                                                                                                                                                                  (pure false)
                                                                                                                                                                )
                                                                                                                                                                :
                                                                                                                                                                SailM
                                                                                                                                                                Bool
                                                                                                                                                                )
                                                                                                                                                              if (w__79 : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 188
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
                                                                                                                                                                  let o2 :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      10
                                                                                                                                                                      1)
                                                                                                                                                                  let cond :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      12
                                                                                                                                                                      4)
                                                                                                                                                                  let Rm :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      16
                                                                                                                                                                      5)
                                                                                                                                                                  let op :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      30
                                                                                                                                                                      1)
                                                                                                                                                                  let sf :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      31
                                                                                                                                                                      1)
                                                                                                                                                                  (decode_csinc_aarch64_instrs_integer_conditional_select
                                                                                                                                                                    Rd
                                                                                                                                                                    Rn
                                                                                                                                                                    o2
                                                                                                                                                                    cond
                                                                                                                                                                    Rm
                                                                                                                                                                    op
                                                                                                                                                                    sf))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  let w__81 ← (( do
                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                             __opcode
                                                                                                                                                                             30
                                                                                                                                                                             21)) == (0b1011010100#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                             __opcode
                                                                                                                                                                             11
                                                                                                                                                                             10)) == (0b00#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                                                                                                    then
                                                                                                                                                                      (do
                                                                                                                                                                        let w__80 ← (( do
                                                                                                                                                                          readReg SEE
                                                                                                                                                                          )
                                                                                                                                                                          :
                                                                                                                                                                          SailM
                                                                                                                                                                          Int
                                                                                                                                                                          )
                                                                                                                                                                        (pure (((w__80 <b 189) : Bool))))
                                                                                                                                                                    else
                                                                                                                                                                      (pure false)
                                                                                                                                                                    )
                                                                                                                                                                    :
                                                                                                                                                                    SailM
                                                                                                                                                                    Bool
                                                                                                                                                                    )
                                                                                                                                                                  if (w__81 : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      writeReg SEE 189
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
                                                                                                                                                                      let o2 :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          10
                                                                                                                                                                          1)
                                                                                                                                                                      let cond :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          12
                                                                                                                                                                          4)
                                                                                                                                                                      let Rm :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          16
                                                                                                                                                                          5)
                                                                                                                                                                      let op :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          30
                                                                                                                                                                          1)
                                                                                                                                                                      let sf :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          31
                                                                                                                                                                          1)
                                                                                                                                                                      (decode_csinv_aarch64_instrs_integer_conditional_select
                                                                                                                                                                        Rd
                                                                                                                                                                        Rn
                                                                                                                                                                        o2
                                                                                                                                                                        cond
                                                                                                                                                                        Rm
                                                                                                                                                                        op
                                                                                                                                                                        sf))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      let w__83 ← (( do
                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 30
                                                                                                                                                                                 21)) == (0b1011010100#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 11
                                                                                                                                                                                 10)) == (0b01#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                                                                                                        then
                                                                                                                                                                          (do
                                                                                                                                                                            let w__82 ← (( do
                                                                                                                                                                              readReg SEE
                                                                                                                                                                              )
                                                                                                                                                                              :
                                                                                                                                                                              SailM
                                                                                                                                                                              Int
                                                                                                                                                                              )
                                                                                                                                                                            (pure (((w__82 <b 190) : Bool))))
                                                                                                                                                                        else
                                                                                                                                                                          (pure false)
                                                                                                                                                                        )
                                                                                                                                                                        :
                                                                                                                                                                        SailM
                                                                                                                                                                        Bool
                                                                                                                                                                        )
                                                                                                                                                                      if (w__83 : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (do
                                                                                                                                                                          writeReg SEE 190
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
                                                                                                                                                                          let o2 :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              10
                                                                                                                                                                              1)
                                                                                                                                                                          let cond :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              12
                                                                                                                                                                              4)
                                                                                                                                                                          let Rm :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              16
                                                                                                                                                                              5)
                                                                                                                                                                          let op :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              30
                                                                                                                                                                              1)
                                                                                                                                                                          let sf :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              31
                                                                                                                                                                              1)
                                                                                                                                                                          (decode_csneg_aarch64_instrs_integer_conditional_select
                                                                                                                                                                            Rd
                                                                                                                                                                            Rn
                                                                                                                                                                            o2
                                                                                                                                                                            cond
                                                                                                                                                                            Rm
                                                                                                                                                                            op
                                                                                                                                                                            sf))
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          let w__85 ← (( do
                                                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb
                                                                                                                                                                                   __opcode
                                                                                                                                                                                   30
                                                                                                                                                                                   10)) == (0b101101011000000000110#21 : (BitVec 21))) : Bool) : Bool)
                                                                                                                                                                            then
                                                                                                                                                                              (do
                                                                                                                                                                                let w__84 ← (( do
                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                  )
                                                                                                                                                                                  :
                                                                                                                                                                                  SailM
                                                                                                                                                                                  Int
                                                                                                                                                                                  )
                                                                                                                                                                                (pure (((w__84 <b 191) : Bool))))
                                                                                                                                                                            else
                                                                                                                                                                              (pure false)
                                                                                                                                                                            )
                                                                                                                                                                            :
                                                                                                                                                                            SailM
                                                                                                                                                                            Bool
                                                                                                                                                                            )
                                                                                                                                                                          if (w__85 : Bool)
                                                                                                                                                                          then
                                                                                                                                                                            (do
                                                                                                                                                                              writeReg SEE 191
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
                                                                                                                                                                              let sf :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  31
                                                                                                                                                                                  1)
                                                                                                                                                                              (decode_ctz_aarch64_instrs_integer_arithmetic_unary_ctz
                                                                                                                                                                                Rd
                                                                                                                                                                                Rn
                                                                                                                                                                                sf))
                                                                                                                                                                          else
                                                                                                                                                                            (do
                                                                                                                                                                              let w__87 ← (( do
                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                                         __opcode
                                                                                                                                                                                         31
                                                                                                                                                                                         21)) == (0b10011010110#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                         __opcode
                                                                                                                                                                                         15
                                                                                                                                                                                         10)) == (0b000101#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                                                then
                                                                                                                                                                                  (do
                                                                                                                                                                                    let w__86 ← (( do
                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                      )
                                                                                                                                                                                      :
                                                                                                                                                                                      SailM
                                                                                                                                                                                      Int
                                                                                                                                                                                      )
                                                                                                                                                                                    (pure (((w__86 <b 477) : Bool))))
                                                                                                                                                                                else
                                                                                                                                                                                  (pure false)
                                                                                                                                                                                )
                                                                                                                                                                                :
                                                                                                                                                                                SailM
                                                                                                                                                                                Bool
                                                                                                                                                                                )
                                                                                                                                                                              if (w__87 : Bool)
                                                                                                                                                                              then
                                                                                                                                                                                (do
                                                                                                                                                                                  writeReg SEE 477
                                                                                                                                                                                  let Xd :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      0
                                                                                                                                                                                      5)
                                                                                                                                                                                  let Xn :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      5
                                                                                                                                                                                      5)
                                                                                                                                                                                  let Xm :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      16
                                                                                                                                                                                      5)
                                                                                                                                                                                  (decode_gmi_aarch64_instrs_integer_tags_mcinserttagmask
                                                                                                                                                                                    Xd
                                                                                                                                                                                    Xn
                                                                                                                                                                                    Xm))
                                                                                                                                                                              else
                                                                                                                                                                                (do
                                                                                                                                                                                  let w__89 ← (( do
                                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                                             __opcode
                                                                                                                                                                                             31
                                                                                                                                                                                             21)) == (0b10011010110#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                             __opcode
                                                                                                                                                                                             15
                                                                                                                                                                                             10)) == (0b000100#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                                                    then
                                                                                                                                                                                      (do
                                                                                                                                                                                        let w__88 ← (( do
                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                          )
                                                                                                                                                                                          :
                                                                                                                                                                                          SailM
                                                                                                                                                                                          Int
                                                                                                                                                                                          )
                                                                                                                                                                                        (pure (((w__88 <b 482) : Bool))))
                                                                                                                                                                                    else
                                                                                                                                                                                      (pure false)
                                                                                                                                                                                    )
                                                                                                                                                                                    :
                                                                                                                                                                                    SailM
                                                                                                                                                                                    Bool
                                                                                                                                                                                    )
                                                                                                                                                                                  if (w__89 : Bool)
                                                                                                                                                                                  then
                                                                                                                                                                                    (do
                                                                                                                                                                                      writeReg SEE 482
                                                                                                                                                                                      let Xd :=
                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                          __opcode
                                                                                                                                                                                          0
                                                                                                                                                                                          5)
                                                                                                                                                                                      let Xn :=
                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                          __opcode
                                                                                                                                                                                          5
                                                                                                                                                                                          5)
                                                                                                                                                                                      let Xm :=
                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                          __opcode
                                                                                                                                                                                          16
                                                                                                                                                                                          5)
                                                                                                                                                                                      (decode_irg_aarch64_instrs_integer_tags_mcinsertrandomtag
                                                                                                                                                                                        Xd
                                                                                                                                                                                        Xn
                                                                                                                                                                                        Xm))
                                                                                                                                                                                  else
                                                                                                                                                                                    (do
                                                                                                                                                                                      let w__91 ← (( do
                                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                 30
                                                                                                                                                                                                 21)) == (0b0011011000#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                 15
                                                                                                                                                                                                 15)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                                                                                        then
                                                                                                                                                                                          (do
                                                                                                                                                                                            let w__90 ← (( do
                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                              )
                                                                                                                                                                                              :
                                                                                                                                                                                              SailM
                                                                                                                                                                                              Int
                                                                                                                                                                                              )
                                                                                                                                                                                            (pure (((w__90 <b 690) : Bool))))
                                                                                                                                                                                        else
                                                                                                                                                                                          (pure false)
                                                                                                                                                                                        )
                                                                                                                                                                                        :
                                                                                                                                                                                        SailM
                                                                                                                                                                                        Bool
                                                                                                                                                                                        )
                                                                                                                                                                                      if (w__91 : Bool)
                                                                                                                                                                                      then
                                                                                                                                                                                        (do
                                                                                                                                                                                          writeReg SEE 690
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
                                                                                                                                                                                          let o0 :=
                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                              __opcode
                                                                                                                                                                                              15
                                                                                                                                                                                              1)
                                                                                                                                                                                          let Rm :=
                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                              __opcode
                                                                                                                                                                                              16
                                                                                                                                                                                              5)
                                                                                                                                                                                          let sf :=
                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                              __opcode
                                                                                                                                                                                              31
                                                                                                                                                                                              1)
                                                                                                                                                                                          (decode_madd_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub
                                                                                                                                                                                            Rd
                                                                                                                                                                                            Rn
                                                                                                                                                                                            Ra
                                                                                                                                                                                            o0
                                                                                                                                                                                            Rm
                                                                                                                                                                                            sf))
                                                                                                                                                                                      else
                                                                                                                                                                                        (do
                                                                                                                                                                                          let w__93 ← (( do
                                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                     30
                                                                                                                                                                                                     21)) == (0b0011011000#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                     15
                                                                                                                                                                                                     15)) == (1#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                                                                                            then
                                                                                                                                                                                              (do
                                                                                                                                                                                                let w__92 ← (( do
                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                  )
                                                                                                                                                                                                  :
                                                                                                                                                                                                  SailM
                                                                                                                                                                                                  Int
                                                                                                                                                                                                  )
                                                                                                                                                                                                (pure (((w__92 <b 691) : Bool))))
                                                                                                                                                                                            else
                                                                                                                                                                                              (pure false)
                                                                                                                                                                                            )
                                                                                                                                                                                            :
                                                                                                                                                                                            SailM
                                                                                                                                                                                            Bool
                                                                                                                                                                                            )
                                                                                                                                                                                          if (w__93 : Bool)
                                                                                                                                                                                          then
                                                                                                                                                                                            (do
                                                                                                                                                                                              writeReg SEE 691
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
                                                                                                                                                                                              let o0 :=
                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                  15
                                                                                                                                                                                                  1)
                                                                                                                                                                                              let Rm :=
                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                  16
                                                                                                                                                                                                  5)
                                                                                                                                                                                              let sf :=
                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                  31
                                                                                                                                                                                                  1)
                                                                                                                                                                                              (decode_msub_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub
                                                                                                                                                                                                Rd
                                                                                                                                                                                                Rn
                                                                                                                                                                                                Ra
                                                                                                                                                                                                o0
                                                                                                                                                                                                Rm
                                                                                                                                                                                                sf))
                                                                                                                                                                                          else
                                                                                                                                                                                            (do
                                                                                                                                                                                              let w__95 ← (( do
                                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb
                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                         31
                                                                                                                                                                                                         14)) == (0b110110101100000100#18 : (BitVec 18))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                         12
                                                                                                                                                                                                         10)) == (0b010#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                                                                then
                                                                                                                                                                                                  (do
                                                                                                                                                                                                    let w__94 ← (( do
                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                      )
                                                                                                                                                                                                      :
                                                                                                                                                                                                      SailM
                                                                                                                                                                                                      Int
                                                                                                                                                                                                      )
                                                                                                                                                                                                    (pure (((w__94 <b 708) : Bool))))
                                                                                                                                                                                                else
                                                                                                                                                                                                  (pure false)
                                                                                                                                                                                                )
                                                                                                                                                                                                :
                                                                                                                                                                                                SailM
                                                                                                                                                                                                Bool
                                                                                                                                                                                                )
                                                                                                                                                                                              if (w__95 : Bool)
                                                                                                                                                                                              then
                                                                                                                                                                                                (do
                                                                                                                                                                                                  writeReg SEE 708
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
                                                                                                                                                                                                  let Z :=
                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                      13
                                                                                                                                                                                                      1)
                                                                                                                                                                                                  (decode_pacda_aarch64_instrs_integer_pac_pacda_dp_1src
                                                                                                                                                                                                    Rd
                                                                                                                                                                                                    Rn
                                                                                                                                                                                                    Z))
                                                                                                                                                                                              else
                                                                                                                                                                                                (do
                                                                                                                                                                                                  let w__97 ← (( do
                                                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb
                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                             31
                                                                                                                                                                                                             14)) == (0b110110101100000100#18 : (BitVec 18))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                             12
                                                                                                                                                                                                             10)) == (0b011#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                                                                    then
                                                                                                                                                                                                      (do
                                                                                                                                                                                                        let w__96 ← (( do
                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                          )
                                                                                                                                                                                                          :
                                                                                                                                                                                                          SailM
                                                                                                                                                                                                          Int
                                                                                                                                                                                                          )
                                                                                                                                                                                                        (pure (((w__96 <b 709) : Bool))))
                                                                                                                                                                                                    else
                                                                                                                                                                                                      (pure false)
                                                                                                                                                                                                    )
                                                                                                                                                                                                    :
                                                                                                                                                                                                    SailM
                                                                                                                                                                                                    Bool
                                                                                                                                                                                                    )
                                                                                                                                                                                                  if (w__97 : Bool)
                                                                                                                                                                                                  then
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      writeReg SEE 709
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
                                                                                                                                                                                                      let Z :=
                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                          13
                                                                                                                                                                                                          1)
                                                                                                                                                                                                      (decode_pacdb_aarch64_instrs_integer_pac_pacdb_dp_1src
                                                                                                                                                                                                        Rd
                                                                                                                                                                                                        Rn
                                                                                                                                                                                                        Z))
                                                                                                                                                                                                  else
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      let w__99 ← (( do
                                                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                 31
                                                                                                                                                                                                                 21)) == (0b10011010110#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                 15
                                                                                                                                                                                                                 10)) == (0b001100#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                                                                        then
                                                                                                                                                                                                          (do
                                                                                                                                                                                                            let w__98 ← (( do
                                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                                              )
                                                                                                                                                                                                              :
                                                                                                                                                                                                              SailM
                                                                                                                                                                                                              Int
                                                                                                                                                                                                              )
                                                                                                                                                                                                            (pure (((w__98 <b 710) : Bool))))
                                                                                                                                                                                                        else
                                                                                                                                                                                                          (pure false)
                                                                                                                                                                                                        )
                                                                                                                                                                                                        :
                                                                                                                                                                                                        SailM
                                                                                                                                                                                                        Bool
                                                                                                                                                                                                        )
                                                                                                                                                                                                      if (w__99 : Bool)
                                                                                                                                                                                                      then
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          writeReg SEE 710
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
                                                                                                                                                                                                          (decode_pacga_aarch64_instrs_integer_pac_pacga_dp_2src
                                                                                                                                                                                                            Rd
                                                                                                                                                                                                            Rn
                                                                                                                                                                                                            Rm))
                                                                                                                                                                                                      else
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          let w__101 ← (( do
                                                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                     31
                                                                                                                                                                                                                     14)) == (0b110110101100000100#18 : (BitVec 18))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                     12
                                                                                                                                                                                                                     10)) == (0b000#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                                                                            then
                                                                                                                                                                                                              (do
                                                                                                                                                                                                                let w__100 ← (( do
                                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                                  )
                                                                                                                                                                                                                  :
                                                                                                                                                                                                                  SailM
                                                                                                                                                                                                                  Int
                                                                                                                                                                                                                  )
                                                                                                                                                                                                                (pure (((w__100 <b 711) : Bool))))
                                                                                                                                                                                                            else
                                                                                                                                                                                                              (pure false)
                                                                                                                                                                                                            )
                                                                                                                                                                                                            :
                                                                                                                                                                                                            SailM
                                                                                                                                                                                                            Bool
                                                                                                                                                                                                            )
                                                                                                                                                                                                          if (w__101 : Bool)
                                                                                                                                                                                                          then
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              writeReg SEE 711
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
                                                                                                                                                                                                              let Z :=
                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                  13
                                                                                                                                                                                                                  1)
                                                                                                                                                                                                              (decode_pacia_aarch64_instrs_integer_pac_pacia_dp_1src
                                                                                                                                                                                                                Rd
                                                                                                                                                                                                                Rn
                                                                                                                                                                                                                Z))
                                                                                                                                                                                                          else
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              let w__103 ← (( do
                                                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                         31
                                                                                                                                                                                                                         14)) == (0b110110101100000100#18 : (BitVec 18))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                         12
                                                                                                                                                                                                                         10)) == (0b001#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                                                                                then
                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                    let w__102 ← (( do
                                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                                      )
                                                                                                                                                                                                                      :
                                                                                                                                                                                                                      SailM
                                                                                                                                                                                                                      Int
                                                                                                                                                                                                                      )
                                                                                                                                                                                                                    (pure (((w__102 <b 713) : Bool))))
                                                                                                                                                                                                                else
                                                                                                                                                                                                                  (pure false)
                                                                                                                                                                                                                )
                                                                                                                                                                                                                :
                                                                                                                                                                                                                SailM
                                                                                                                                                                                                                Bool
                                                                                                                                                                                                                )
                                                                                                                                                                                                              if (w__103 : Bool)
                                                                                                                                                                                                              then
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  writeReg SEE 713
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
                                                                                                                                                                                                                  let Z :=
                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                      13
                                                                                                                                                                                                                      1)
                                                                                                                                                                                                                  (decode_pacib_aarch64_instrs_integer_pac_pacib_dp_1src
                                                                                                                                                                                                                    Rd
                                                                                                                                                                                                                    Rn
                                                                                                                                                                                                                    Z))
                                                                                                                                                                                                              else
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  let w__105 ← (( do
                                                                                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                           30
                                                                                                                                                                                                                           10)) == (0b101101011000000000000#21 : (BitVec 21))) : Bool) : Bool)
                                                                                                                                                                                                                    then
                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                        let w__104 ← (( do
                                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                                          )
                                                                                                                                                                                                                          :
                                                                                                                                                                                                                          SailM
                                                                                                                                                                                                                          Int
                                                                                                                                                                                                                          )
                                                                                                                                                                                                                        (pure (((w__104 <b 719) : Bool))))
                                                                                                                                                                                                                    else
                                                                                                                                                                                                                      (pure false)
                                                                                                                                                                                                                    )
                                                                                                                                                                                                                    :
                                                                                                                                                                                                                    SailM
                                                                                                                                                                                                                    Bool
                                                                                                                                                                                                                    )
                                                                                                                                                                                                                  if (w__105 : Bool)
                                                                                                                                                                                                                  then
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      writeReg SEE 719
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
                                                                                                                                                                                                                      let sf :=
                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                          31
                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                      (decode_rbit_int_aarch64_instrs_integer_arithmetic_rbit
                                                                                                                                                                                                                        Rd
                                                                                                                                                                                                                        Rn
                                                                                                                                                                                                                        sf))
                                                                                                                                                                                                                  else
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      let w__107 ← (( do
                                                                                                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                                               30
                                                                                                                                                                                                                               11)) == (0xB5801#20 : (BitVec 20))) : Bool) : Bool)
                                                                                                                                                                                                                        then
                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                            let w__106 ← (( do
                                                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                                                              )
                                                                                                                                                                                                                              :
                                                                                                                                                                                                                              SailM
                                                                                                                                                                                                                              Int
                                                                                                                                                                                                                              )
                                                                                                                                                                                                                            (pure (((w__106 <b 736) : Bool))))
                                                                                                                                                                                                                        else
                                                                                                                                                                                                                          (pure false)
                                                                                                                                                                                                                        )
                                                                                                                                                                                                                        :
                                                                                                                                                                                                                        SailM
                                                                                                                                                                                                                        Bool
                                                                                                                                                                                                                        )
                                                                                                                                                                                                                      if (w__107 : Bool)
                                                                                                                                                                                                                      then
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          writeReg SEE 736
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
                                                                                                                                                                                                                              10
                                                                                                                                                                                                                              2)
                                                                                                                                                                                                                          let sf :=
                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                              31
                                                                                                                                                                                                                              1)
                                                                                                                                                                                                                          (decode_rev_aarch64_instrs_integer_arithmetic_rev
                                                                                                                                                                                                                            Rd
                                                                                                                                                                                                                            Rn
                                                                                                                                                                                                                            opc
                                                                                                                                                                                                                            sf))
                                                                                                                                                                                                                      else
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          let w__109 ← (( do
                                                                                                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                                                   30
                                                                                                                                                                                                                                   10)) == (0b101101011000000000001#21 : (BitVec 21))) : Bool) : Bool)
                                                                                                                                                                                                                            then
                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                let w__108 ← (( do
                                                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                  :
                                                                                                                                                                                                                                  SailM
                                                                                                                                                                                                                                  Int
                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                (pure (((w__108 <b 737) : Bool))))
                                                                                                                                                                                                                            else
                                                                                                                                                                                                                              (pure false)
                                                                                                                                                                                                                            )
                                                                                                                                                                                                                            :
                                                                                                                                                                                                                            SailM
                                                                                                                                                                                                                            Bool
                                                                                                                                                                                                                            )
                                                                                                                                                                                                                          if (w__109 : Bool)
                                                                                                                                                                                                                          then
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              writeReg SEE 737
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
                                                                                                                                                                                                                                  10
                                                                                                                                                                                                                                  2)
                                                                                                                                                                                                                              let sf :=
                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                  31
                                                                                                                                                                                                                                  1)
                                                                                                                                                                                                                              (decode_rev16_int_aarch64_instrs_integer_arithmetic_rev
                                                                                                                                                                                                                                Rd
                                                                                                                                                                                                                                Rn
                                                                                                                                                                                                                                opc
                                                                                                                                                                                                                                sf))
                                                                                                                                                                                                                          else
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              let w__111 ← (( do
                                                                                                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                                       31
                                                                                                                                                                                                                                       10)) == (0b1101101011000000000010#22 : (BitVec 22))) : Bool) : Bool)
                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                    let w__110 ← (( do
                                                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                      :
                                                                                                                                                                                                                                      SailM
                                                                                                                                                                                                                                      Int
                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                    (pure (((w__110 <b 738) : Bool))))
                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                  (pure false)
                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                :
                                                                                                                                                                                                                                SailM
                                                                                                                                                                                                                                Bool
                                                                                                                                                                                                                                )
                                                                                                                                                                                                                              if (w__111 : Bool)
                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  writeReg SEE 738
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
                                                                                                                                                                                                                                      10
                                                                                                                                                                                                                                      2)
                                                                                                                                                                                                                                  let sf :=
                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                      31
                                                                                                                                                                                                                                      1)
                                                                                                                                                                                                                                  (decode_rev32_int_aarch64_instrs_integer_arithmetic_rev
                                                                                                                                                                                                                                    Rd
                                                                                                                                                                                                                                    Rn
                                                                                                                                                                                                                                    opc
                                                                                                                                                                                                                                    sf))
                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  let w__113 ← (( do
                                                                                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                             31
                                                                                                                                                                                                                                             21)) == (0b10111010000#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                                                               14
                                                                                                                                                                                                                                               10)) == (0b00001#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                                                               4
                                                                                                                                                                                                                                               4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                        let w__112 ← (( do
                                                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                          :
                                                                                                                                                                                                                                          SailM
                                                                                                                                                                                                                                          Int
                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                        (pure (((w__112 <b 742) : Bool))))
                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                      (pure false)
                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                    :
                                                                                                                                                                                                                                    SailM
                                                                                                                                                                                                                                    Bool
                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                  if (w__113 : Bool)
                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      writeReg SEE 742
                                                                                                                                                                                                                                      let mask :=
                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                          0
                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                      let Rn :=
                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                          5
                                                                                                                                                                                                                                          5)
                                                                                                                                                                                                                                      let imm6 :=
                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                          15
                                                                                                                                                                                                                                          6)
                                                                                                                                                                                                                                      let sf :=
                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                          31
                                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                                      (decode_rmif_aarch64_instrs_integer_flags_rmif
                                                                                                                                                                                                                                        mask
                                                                                                                                                                                                                                        Rn
                                                                                                                                                                                                                                        imm6
                                                                                                                                                                                                                                        sf))
                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      let w__115 ← (( do
                                                                                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                 30
                                                                                                                                                                                                                                                 21)) == (0b0011010110#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                 15
                                                                                                                                                                                                                                                 10)) == (0b000011#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                                                                                                        then
                                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                                            let w__114 ← (( do
                                                                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                              :
                                                                                                                                                                                                                                              SailM
                                                                                                                                                                                                                                              Int
                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                            (pure (((w__114 <b 781) : Bool))))
                                                                                                                                                                                                                                        else
                                                                                                                                                                                                                                          (pure false)
                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                        :
                                                                                                                                                                                                                                        SailM
                                                                                                                                                                                                                                        Bool
                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                      if (w__115 : Bool)
                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          writeReg SEE 781
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
                                                                                                                                                                                                                                              10
                                                                                                                                                                                                                                              1)
                                                                                                                                                                                                                                          let Rm :=
                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                              16
                                                                                                                                                                                                                                              5)
                                                                                                                                                                                                                                          let sf :=
                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                              31
                                                                                                                                                                                                                                              1)
                                                                                                                                                                                                                                          (decode_sdiv_aarch64_instrs_integer_arithmetic_div
                                                                                                                                                                                                                                            Rd
                                                                                                                                                                                                                                            Rn
                                                                                                                                                                                                                                            o1
                                                                                                                                                                                                                                            Rm
                                                                                                                                                                                                                                            sf))
                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          let w__117 ← (( do
                                                                                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                     30
                                                                                                                                                                                                                                                     21)) == (0b0011010110#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                     15
                                                                                                                                                                                                                                                     10)) == (0b000010#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                                                                                                            then
                                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                                let w__116 ← (( do
                                                                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                  :
                                                                                                                                                                                                                                                  SailM
                                                                                                                                                                                                                                                  Int
                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                (pure (((w__116 <b 782) : Bool))))
                                                                                                                                                                                                                                            else
                                                                                                                                                                                                                                              (pure false)
                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                            :
                                                                                                                                                                                                                                            SailM
                                                                                                                                                                                                                                            Bool
                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                          if (w__117 : Bool)
                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              writeReg SEE 782
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
                                                                                                                                                                                                                                                  10
                                                                                                                                                                                                                                                  1)
                                                                                                                                                                                                                                              let Rm :=
                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                  16
                                                                                                                                                                                                                                                  5)
                                                                                                                                                                                                                                              let sf :=
                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                  31
                                                                                                                                                                                                                                                  1)
                                                                                                                                                                                                                                              (decode_udiv_aarch64_instrs_integer_arithmetic_div
                                                                                                                                                                                                                                                Rd
                                                                                                                                                                                                                                                Rn
                                                                                                                                                                                                                                                o1
                                                                                                                                                                                                                                                Rm
                                                                                                                                                                                                                                                sf))
                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              let w__119 ← (( do
                                                                                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                         31
                                                                                                                                                                                                                                                         15)) == (0b00111010000000000#17 : (BitVec 17))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                                                           13
                                                                                                                                                                                                                                                           10)) == (0x2#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                                                           4
                                                                                                                                                                                                                                                           0)) == (0b01101#5 : (BitVec 5))))) : Bool) : Bool)
                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                                    let w__118 ← (( do
                                                                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                      :
                                                                                                                                                                                                                                                      SailM
                                                                                                                                                                                                                                                      Int
                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                    (pure (((w__118 <b 791) : Bool))))
                                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                                  (pure false)
                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                :
                                                                                                                                                                                                                                                SailM
                                                                                                                                                                                                                                                Bool
                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                              if (w__119 : Bool)
                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  writeReg SEE 791
                                                                                                                                                                                                                                                  let Rn :=
                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                      5
                                                                                                                                                                                                                                                      5)
                                                                                                                                                                                                                                                  let sz :=
                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                      14
                                                                                                                                                                                                                                                      1)
                                                                                                                                                                                                                                                  let sf :=
                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                      31
                                                                                                                                                                                                                                                      1)
                                                                                                                                                                                                                                                  (decode_setf_aarch64_instrs_integer_flags_setf
                                                                                                                                                                                                                                                    Rn
                                                                                                                                                                                                                                                    sz
                                                                                                                                                                                                                                                    sf))
                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  let w__121 ← (( do
                                                                                                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                             31
                                                                                                                                                                                                                                                             21)) == (0b10011011001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                             15
                                                                                                                                                                                                                                                             15)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                                        let w__120 ← (( do
                                                                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                          :
                                                                                                                                                                                                                                                          SailM
                                                                                                                                                                                                                                                          Int
                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                        (pure (((w__120 <b 828) : Bool))))
                                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                                      (pure false)
                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                    :
                                                                                                                                                                                                                                                    SailM
                                                                                                                                                                                                                                                    Bool
                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                  if (w__121 : Bool)
                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      writeReg SEE 828
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
                                                                                                                                                                                                                                                      let o0 :=
                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                          15
                                                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                                                      let Rm :=
                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                          16
                                                                                                                                                                                                                                                          5)
                                                                                                                                                                                                                                                      let U :=
                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                          23
                                                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                                                      (decode_smaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64
                                                                                                                                                                                                                                                        Rd
                                                                                                                                                                                                                                                        Rn
                                                                                                                                                                                                                                                        Ra
                                                                                                                                                                                                                                                        o0
                                                                                                                                                                                                                                                        Rm
                                                                                                                                                                                                                                                        U))
                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      let w__123 ← (( do
                                                                                                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                 31
                                                                                                                                                                                                                                                                 21)) == (0b10011011001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                 15
                                                                                                                                                                                                                                                                 15)) == (1#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                                                                                                                                                        then
                                                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                                                            let w__122 ← (( do
                                                                                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                              :
                                                                                                                                                                                                                                                              SailM
                                                                                                                                                                                                                                                              Int
                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                            (pure (((w__122 <b 829) : Bool))))
                                                                                                                                                                                                                                                        else
                                                                                                                                                                                                                                                          (pure false)
                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                        :
                                                                                                                                                                                                                                                        SailM
                                                                                                                                                                                                                                                        Bool
                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                      if (w__123 : Bool)
                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          writeReg SEE 829
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
                                                                                                                                                                                                                                                          let o0 :=
                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                              15
                                                                                                                                                                                                                                                              1)
                                                                                                                                                                                                                                                          let Rm :=
                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                              16
                                                                                                                                                                                                                                                              5)
                                                                                                                                                                                                                                                          let U :=
                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                              23
                                                                                                                                                                                                                                                              1)
                                                                                                                                                                                                                                                          (decode_smsubl_aarch64_instrs_integer_arithmetic_mul_widening_32_64
                                                                                                                                                                                                                                                            Rd
                                                                                                                                                                                                                                                            Rn
                                                                                                                                                                                                                                                            Ra
                                                                                                                                                                                                                                                            o0
                                                                                                                                                                                                                                                            Rm
                                                                                                                                                                                                                                                            U))
                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          let w__125 ← (( do
                                                                                                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                                     31
                                                                                                                                                                                                                                                                     21)) == (0b10011011101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                                     15
                                                                                                                                                                                                                                                                     15)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                                                                                                                                                            then
                                                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                                                let w__124 ← (( do
                                                                                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                  :
                                                                                                                                                                                                                                                                  SailM
                                                                                                                                                                                                                                                                  Int
                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                (pure (((w__124 <b 830) : Bool))))
                                                                                                                                                                                                                                                            else
                                                                                                                                                                                                                                                              (pure false)
                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                            :
                                                                                                                                                                                                                                                            SailM
                                                                                                                                                                                                                                                            Bool
                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                          if (w__125 : Bool)
                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              writeReg SEE 830
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
                                                                                                                                                                                                                                                              let o0 :=
                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                  15
                                                                                                                                                                                                                                                                  1)
                                                                                                                                                                                                                                                              let Rm :=
                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                  16
                                                                                                                                                                                                                                                                  5)
                                                                                                                                                                                                                                                              let U :=
                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                  23
                                                                                                                                                                                                                                                                  1)
                                                                                                                                                                                                                                                              (decode_umaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64
                                                                                                                                                                                                                                                                Rd
                                                                                                                                                                                                                                                                Rn
                                                                                                                                                                                                                                                                Ra
                                                                                                                                                                                                                                                                o0
                                                                                                                                                                                                                                                                Rm
                                                                                                                                                                                                                                                                U))
                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              let w__127 ← (( do
                                                                                                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                                         31
                                                                                                                                                                                                                                                                         21)) == (0b10011011101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                                         15
                                                                                                                                                                                                                                                                         15)) == (1#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                                                    let w__126 ← (( do
                                                                                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                      :
                                                                                                                                                                                                                                                                      SailM
                                                                                                                                                                                                                                                                      Int
                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                    (pure (((w__126 <b 831) : Bool))))
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
                                                                                                                                                                                                                                                                  writeReg SEE 831
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
                                                                                                                                                                                                                                                                  let o0 :=
                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                      15
                                                                                                                                                                                                                                                                      1)
                                                                                                                                                                                                                                                                  let Rm :=
                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                      16
                                                                                                                                                                                                                                                                      5)
                                                                                                                                                                                                                                                                  let U :=
                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                      23
                                                                                                                                                                                                                                                                      1)
                                                                                                                                                                                                                                                                  (decode_umsubl_aarch64_instrs_integer_arithmetic_mul_widening_32_64
                                                                                                                                                                                                                                                                    Rd
                                                                                                                                                                                                                                                                    Rn
                                                                                                                                                                                                                                                                    Ra
                                                                                                                                                                                                                                                                    o0
                                                                                                                                                                                                                                                                    Rm
                                                                                                                                                                                                                                                                    U))
                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  let w__129 ← (( do
                                                                                                                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                                             30
                                                                                                                                                                                                                                                                             21)) == (0b0011010110#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                                             15
                                                                                                                                                                                                                                                                             10)) == (0b011000#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                                                        let w__128 ← (( do
                                                                                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                          :
                                                                                                                                                                                                                                                                          SailM
                                                                                                                                                                                                                                                                          Int
                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                        (pure (((w__128 <b 833) : Bool))))
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
                                                                                                                                                                                                                                                                      writeReg SEE 833
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
                                                                                                                                                                                                                                                                      let sf :=
                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                          31
                                                                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                                                                      (decode_smax_reg_aarch64_instrs_integer_arithmetic_max_min_smax_reg
                                                                                                                                                                                                                                                                        Rd
                                                                                                                                                                                                                                                                        Rn
                                                                                                                                                                                                                                                                        Rm
                                                                                                                                                                                                                                                                        sf))
                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      let w__131 ← (( do
                                                                                                                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                                 30
                                                                                                                                                                                                                                                                                 21)) == (0b0011010110#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                                 15
                                                                                                                                                                                                                                                                                 10)) == (0b011010#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                                                                                                                                        then
                                                                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                                                                            let w__130 ← (( do
                                                                                                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                              :
                                                                                                                                                                                                                                                                              SailM
                                                                                                                                                                                                                                                                              Int
                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                            (pure (((w__130 <b 848) : Bool))))
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
                                                                                                                                                                                                                                                                          writeReg SEE 848
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
                                                                                                                                                                                                                                                                          let sf :=
                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                              31
                                                                                                                                                                                                                                                                              1)
                                                                                                                                                                                                                                                                          (decode_smin_reg_aarch64_instrs_integer_arithmetic_max_min_smin_reg
                                                                                                                                                                                                                                                                            Rd
                                                                                                                                                                                                                                                                            Rn
                                                                                                                                                                                                                                                                            Rm
                                                                                                                                                                                                                                                                            sf))
                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          let w__133 ← (( do
                                                                                                                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                                                     31
                                                                                                                                                                                                                                                                                     21)) == (0b10011011010#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                                                     15
                                                                                                                                                                                                                                                                                     10)) == (0b011111#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                                                                                                                                            then
                                                                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                                                                let w__132 ← (( do
                                                                                                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                  :
                                                                                                                                                                                                                                                                                  SailM
                                                                                                                                                                                                                                                                                  Int
                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                (pure (((w__132 <b 861) : Bool))))
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
                                                                                                                                                                                                                                                                              writeReg SEE 861
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
                                                                                                                                                                                                                                                                              let U :=
                                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                                  23
                                                                                                                                                                                                                                                                                  1)
                                                                                                                                                                                                                                                                              if (((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                                                                                                               10)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                                                                                                               11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                                                             12)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                                                                                           13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                                                         14)])) != 1#1)) : Bool)
                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                                                                                                                  ()))
                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  (decode_smulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi
                                                                                                                                                                                                                                                                                    Rd
                                                                                                                                                                                                                                                                                    Rn
                                                                                                                                                                                                                                                                                    Ra
                                                                                                                                                                                                                                                                                    Rm
                                                                                                                                                                                                                                                                                    U)))
                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              let w__135 ← (( do
                                                                                                                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                                                         31
                                                                                                                                                                                                                                                                                         21)) == (0b10011011110#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                                                         15
                                                                                                                                                                                                                                                                                         10)) == (0b011111#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                                                                    let w__134 ← (( do
                                                                                                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                      :
                                                                                                                                                                                                                                                                                      SailM
                                                                                                                                                                                                                                                                                      Int
                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                    (pure (((w__134 <b 862) : Bool))))
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
                                                                                                                                                                                                                                                                                  writeReg SEE 862
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
                                                                                                                                                                                                                                                                                  let U :=
                                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                                      23
                                                                                                                                                                                                                                                                                      1)
                                                                                                                                                                                                                                                                                  if (((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                                                                                                                   10)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                                                                                                                   11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                                                 12)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                                                                                                               13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                                                             14)])) != 1#1)) : Bool)
                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                                                                                                                      ()))
                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                      (decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi
                                                                                                                                                                                                                                                                                        Rd
                                                                                                                                                                                                                                                                                        Rn
                                                                                                                                                                                                                                                                                        Ra
                                                                                                                                                                                                                                                                                        Rm
                                                                                                                                                                                                                                                                                        U)))
                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  let w__137 ← (( do
                                                                                                                                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                                                             31
                                                                                                                                                                                                                                                                                             21)) == (0b10011010110#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                                                             15
                                                                                                                                                                                                                                                                                             10)) == (0b000000#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                                                                        let w__136 ← (( do
                                                                                                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                          :
                                                                                                                                                                                                                                                                                          SailM
                                                                                                                                                                                                                                                                                          Int
                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                        (pure (((w__136 <b 991) : Bool))))
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
                                                                                                                                                                                                                                                                                      writeReg SEE 991
                                                                                                                                                                                                                                                                                      let Xd :=
                                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                                          0
                                                                                                                                                                                                                                                                                          5)
                                                                                                                                                                                                                                                                                      let Xn :=
                                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                                          5
                                                                                                                                                                                                                                                                                          5)
                                                                                                                                                                                                                                                                                      let Xm :=
                                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                                          16
                                                                                                                                                                                                                                                                                          5)
                                                                                                                                                                                                                                                                                      (decode_subp_aarch64_instrs_integer_arithmetic_pointer_mcsubtracttaggedaddress
                                                                                                                                                                                                                                                                                        Xd
                                                                                                                                                                                                                                                                                        Xn
                                                                                                                                                                                                                                                                                        Xm))
                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                      let w__139 ← (( do
                                                                                                                                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                                                 31
                                                                                                                                                                                                                                                                                                 21)) == (0b10111010110#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                                                 15
                                                                                                                                                                                                                                                                                                 10)) == (0b000000#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                                                                                                                                                        then
                                                                                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                                                                                            let w__138 ← (( do
                                                                                                                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                                              :
                                                                                                                                                                                                                                                                                              SailM
                                                                                                                                                                                                                                                                                              Int
                                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                                            (pure (((w__138 <b 992) : Bool))))
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
                                                                                                                                                                                                                                                                                          writeReg SEE 992
                                                                                                                                                                                                                                                                                          let Xd :=
                                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                                              0
                                                                                                                                                                                                                                                                                              5)
                                                                                                                                                                                                                                                                                          let Xn :=
                                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                                              5
                                                                                                                                                                                                                                                                                              5)
                                                                                                                                                                                                                                                                                          let Xm :=
                                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                                              16
                                                                                                                                                                                                                                                                                              5)
                                                                                                                                                                                                                                                                                          (decode_subps_aarch64_instrs_integer_arithmetic_pointer_mcsubtracttaggedaddresssetflags
                                                                                                                                                                                                                                                                                            Xd
                                                                                                                                                                                                                                                                                            Xn
                                                                                                                                                                                                                                                                                            Xm))
                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                          let w__141 ← (( do
                                                                                                                                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                                                                     30
                                                                                                                                                                                                                                                                                                     21)) == (0b0011010110#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                                                                     15
                                                                                                                                                                                                                                                                                                     10)) == (0b011001#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                                                                                                                                                            then
                                                                                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                                                                                let w__140 ← (( do
                                                                                                                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                                  :
                                                                                                                                                                                                                                                                                                  SailM
                                                                                                                                                                                                                                                                                                  Int
                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                                (pure (((w__140 <b 1019) : Bool))))
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
                                                                                                                                                                                                                                                                                              writeReg SEE 1019
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
                                                                                                                                                                                                                                                                                              let sf :=
                                                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                                                  31
                                                                                                                                                                                                                                                                                                  1)
                                                                                                                                                                                                                                                                                              (decode_umax_reg_aarch64_instrs_integer_arithmetic_max_min_umax_reg
                                                                                                                                                                                                                                                                                                Rd
                                                                                                                                                                                                                                                                                                Rn
                                                                                                                                                                                                                                                                                                Rm
                                                                                                                                                                                                                                                                                                sf))
                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                              let w__143 ← (( do
                                                                                                                                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                                                                         30
                                                                                                                                                                                                                                                                                                         21)) == (0b0011010110#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                                                                         15
                                                                                                                                                                                                                                                                                                         10)) == (0b011011#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                                                                                    let w__142 ← (( do
                                                                                                                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                                      :
                                                                                                                                                                                                                                                                                                      SailM
                                                                                                                                                                                                                                                                                                      Int
                                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                                    (pure (((w__142 <b 1020) : Bool))))
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
                                                                                                                                                                                                                                                                                                  writeReg SEE 1020
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
                                                                                                                                                                                                                                                                                                  let sf :=
                                                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                                                      31
                                                                                                                                                                                                                                                                                                      1)
                                                                                                                                                                                                                                                                                                  (decode_umin_reg_aarch64_instrs_integer_arithmetic_max_min_umin_reg
                                                                                                                                                                                                                                                                                                    Rd
                                                                                                                                                                                                                                                                                                    Rn
                                                                                                                                                                                                                                                                                                    Rm
                                                                                                                                                                                                                                                                                                    sf))
                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                  let w__145 ← (( do
                                                                                                                                                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                                                                             31
                                                                                                                                                                                                                                                                                                             11)) == (0b110110101100000101000#21 : (BitVec 21))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                                                                             9
                                                                                                                                                                                                                                                                                                             5)) == (0b11111#5 : (BitVec 5)))) : Bool) : Bool)
                                                                                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                                                                                        let w__144 ← (( do
                                                                                                                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                          :
                                                                                                                                                                                                                                                                                                          SailM
                                                                                                                                                                                                                                                                                                          Int
                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                        (pure (((w__144 <b 1032) : Bool))))
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
                                                                                                                                                                                                                                                                                                      writeReg SEE 1032
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
                                                                                                                                                                                                                                                                                                      let D :=
                                                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                                                          10
                                                                                                                                                                                                                                                                                                          1)
                                                                                                                                                                                                                                                                                                      (decode_xpac_aarch64_instrs_integer_pac_strip_dp_1src
                                                                                                                                                                                                                                                                                                        Rd
                                                                                                                                                                                                                                                                                                        Rn
                                                                                                                                                                                                                                                                                                        D))
                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                    sailThrow ((Error_Undefined
                                                                                                                                                                                                                                                                                                      ()))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
