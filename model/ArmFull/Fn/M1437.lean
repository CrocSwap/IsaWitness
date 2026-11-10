import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0151
import ArmFull.Fn.M0229
import ArmFull.Fn.M0230
import ArmFull.Fn.M0246
import ArmFull.Fn.M0837
import ArmFull.Fn.M0838
import ArmFull.Fn.M0928
import ArmFull.Fn.M1280

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
def __DecodeA32_DataProMisc__seg0 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__2 ← (( do
    if ((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb __opcode 27 21)) == (0b0010101#7 : (BitVec 7))) : Bool) : Bool)
    then
      (do
        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
        then
          (do
            let w__0 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__0 <b 2813) : Bool))))
        else (pure false))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      writeReg SEE 2813
      let cond := (BitVec.slice __opcode 28 4)
      let S := (BitVec.slice __opcode 20 1)
      let Rn := (BitVec.slice __opcode 16 4)
      let Rd := (BitVec.slice __opcode 12 4)
      let imm12 := (BitVec.slice __opcode 0 12)
      (decode_aarch32_instrs_ADC_i_A1enc_A_txt cond S Rn Rd imm12)
      (pure false))
  else
    (do
      let w__5 ← (( do
        if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb __opcode 27 21)) == (0b0000101#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                 __opcode 4 4)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
        then
          (do
            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
            then
              (do
                let w__3 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__3 <b 2815) : Bool))))
            else (pure false))
        else (pure false) ) : SailM Bool )
      if (w__5 : Bool)
      then
        (do
          writeReg SEE 2815
          let cond := (BitVec.slice __opcode 28 4)
          let S := (BitVec.slice __opcode 20 1)
          let Rn := (BitVec.slice __opcode 16 4)
          let Rd := (BitVec.slice __opcode 12 4)
          let imm5 := (BitVec.slice __opcode 7 5)
          let stype := (BitVec.slice __opcode 5 2)
          let Rm := (BitVec.slice __opcode 0 4)
          (decode_aarch32_instrs_ADC_r_A1enc_A_txt cond S Rn Rd imm5 stype Rm)
          (pure false))
      else
        (do
          let w__8 ← (( do
            if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb __opcode 27 21)) == (0b0000101#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       __opcode 7 7)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       __opcode 4 4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
            then
              (do
                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                then
                  (do
                    let w__6 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__6 <b 2818) : Bool))))
                else (pure false))
            else (pure false) ) : SailM Bool )
          if (w__8 : Bool)
          then
            (do
              writeReg SEE 2818
              let cond := (BitVec.slice __opcode 28 4)
              let S := (BitVec.slice __opcode 20 1)
              let Rn := (BitVec.slice __opcode 16 4)
              let Rd := (BitVec.slice __opcode 12 4)
              let Rs := (BitVec.slice __opcode 8 4)
              let stype := (BitVec.slice __opcode 5 2)
              let Rm := (BitVec.slice __opcode 0 4)
              (decode_aarch32_instrs_ADC_rr_A1enc_A_txt cond S Rn Rd Rs stype Rm)
              (pure false))
          else
            (do
              let w__11 ← (( do
                if ((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb __opcode 27 21)) == (0b0010100#7 : (BitVec 7))) : Bool) : Bool)
                then
                  (do
                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                    then
                      (do
                        let w__9 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__9 <b 2819) : Bool))))
                    else (pure false))
                else (pure false) ) : SailM Bool )
              if (w__11 : Bool)
              then
                (do
                  writeReg SEE 2819
                  let cond := (BitVec.slice __opcode 28 4)
                  let S := (BitVec.slice __opcode 20 1)
                  let Rn := (BitVec.slice __opcode 16 4)
                  let Rd := (BitVec.slice __opcode 12 4)
                  let imm12 := (BitVec.slice __opcode 0 12)
                  (decode_aarch32_instrs_ADD_i_A1enc_A_txt cond S Rn Rd imm12)
                  (pure false))
              else
                (do
                  let w__14 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb __opcode 27 21)) == (0b0000100#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                             __opcode 4 4)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                    then
                      (do
                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                        then
                          (do
                            let w__12 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__12 <b 2824) : Bool))))
                        else (pure false))
                    else (pure false) ) : SailM Bool )
                  if (w__14 : Bool)
                  then
                    (do
                      writeReg SEE 2824
                      let cond := (BitVec.slice __opcode 28 4)
                      let S := (BitVec.slice __opcode 20 1)
                      let Rn := (BitVec.slice __opcode 16 4)
                      let Rd := (BitVec.slice __opcode 12 4)
                      let imm5 := (BitVec.slice __opcode 7 5)
                      let stype := (BitVec.slice __opcode 5 2)
                      let Rm := (BitVec.slice __opcode 0 4)
                      (decode_aarch32_instrs_ADD_r_A1enc_A_txt cond S Rn Rd imm5 stype Rm)
                      (pure false))
                  else
                    (do
                      let w__17 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb __opcode 27
                                 21)) == (0b0000100#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                   __opcode 7 7)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                   __opcode 4 4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                        then
                          (do
                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                            then
                              (do
                                let w__15 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__15 <b 2828) : Bool))))
                            else (pure false))
                        else (pure false) ) : SailM Bool )
                      if (w__17 : Bool)
                      then
                        (do
                          writeReg SEE 2828
                          let cond := (BitVec.slice __opcode 28 4)
                          let S := (BitVec.slice __opcode 20 1)
                          let Rn := (BitVec.slice __opcode 16 4)
                          let Rd := (BitVec.slice __opcode 12 4)
                          let Rs := (BitVec.slice __opcode 8 4)
                          let stype := (BitVec.slice __opcode 5 2)
                          let Rm := (BitVec.slice __opcode 0 4)
                          (decode_aarch32_instrs_ADD_rr_A1enc_A_txt cond S Rn Rd Rs stype Rm)
                          (pure false))
                      else
                        (do
                          let w__20 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb __opcode
                                     27 21)) == (0b0010100#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                     __opcode 19 16)) == (0xD#4 : (BitVec 4)))) : Bool) : Bool)
                            then
                              (do
                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                then
                                  (do
                                    let w__18 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__18 <b 2829) : Bool))))
                                else (pure false))
                            else (pure false) ) : SailM Bool )
                          if (w__20 : Bool)
                          then
                            (do
                              writeReg SEE 2829
                              let cond := (BitVec.slice __opcode 28 4)
                              let S := (BitVec.slice __opcode 20 1)
                              let Rd := (BitVec.slice __opcode 12 4)
                              let imm12 := (BitVec.slice __opcode 0 12)
                              (decode_aarch32_instrs_ADD_SP_i_A1enc_A_txt cond S Rd imm12)
                              (pure false))
                          else
                            (do
                              let w__23 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                         __opcode 27 21)) == (0b0000100#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                           __opcode 19 16)) == (0xD#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                           __opcode 4 4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                then
                                  (do
                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28
                                           4)) != 0b1111#4) : Bool) : Bool)
                                    then
                                      (do
                                        let w__21 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__21 <b 2834) : Bool))))
                                    else (pure false))
                                else (pure false) ) : SailM Bool )
                              if (w__23 : Bool)
                              then
                                (do
                                  writeReg SEE 2834
                                  let cond := (BitVec.slice __opcode 28 4)
                                  let S := (BitVec.slice __opcode 20 1)
                                  let Rd := (BitVec.slice __opcode 12 4)
                                  let imm5 := (BitVec.slice __opcode 7 5)
                                  let stype := (BitVec.slice __opcode 5 2)
                                  let Rm := (BitVec.slice __opcode 0 4)
                                  (decode_aarch32_instrs_ADD_SP_r_A1enc_A_txt cond S Rd imm5 stype
                                    Rm)
                                  (pure false))
                              else
                                (do
                                  let w__26 ← (( do
                                    if ((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                           __opcode 27 16)) == (0x28F#12 : (BitVec 12))) : Bool) : Bool)
                                    then
                                      (do
                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode
                                               28 4)) != 0b1111#4) : Bool) : Bool)
                                        then
                                          (do
                                            let w__24 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__24 <b 2838) : Bool))))
                                        else (pure false))
                                    else (pure false) ) : SailM Bool )
                                  if (w__26 : Bool)
                                  then
                                    (do
                                      writeReg SEE 2838
                                      let cond := (BitVec.slice __opcode 28 4)
                                      let Rd := (BitVec.slice __opcode 12 4)
                                      let imm12 := (BitVec.slice __opcode 0 12)
                                      (decode_aarch32_instrs_ADR_A1enc_A_txt cond Rd imm12)
                                      (pure false))
                                  else
                                    (do
                                      let w__29 ← (( do
                                        if ((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                               __opcode 27 16)) == (0x24F#12 : (BitVec 12))) : Bool) : Bool)
                                        then
                                          (do
                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                   __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                            then
                                              (do
                                                let w__27 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__27 <b 2839) : Bool))))
                                            else (pure false))
                                        else (pure false) ) : SailM Bool )
                                      if (w__29 : Bool)
                                      then
                                        (do
                                          writeReg SEE 2839
                                          let cond := (BitVec.slice __opcode 28 4)
                                          let Rd := (BitVec.slice __opcode 12 4)
                                          let imm12 := (BitVec.slice __opcode 0 12)
                                          (decode_aarch32_instrs_ADR_A2enc_A_txt cond Rd imm12)
                                          (pure false))
                                      else
                                        (do
                                          let w__32 ← (( do
                                            if ((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                   __opcode 27 21)) == (0b0010000#7 : (BitVec 7))) : Bool) : Bool)
                                            then
                                              (do
                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                       __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__30 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__30 <b 2843) : Bool))))
                                                else (pure false))
                                            else (pure false) ) : SailM Bool )
                                          if (w__32 : Bool)
                                          then
                                            (do
                                              writeReg SEE 2843
                                              let cond := (BitVec.slice __opcode 28 4)
                                              let S := (BitVec.slice __opcode 20 1)
                                              let Rn := (BitVec.slice __opcode 16 4)
                                              let Rd := (BitVec.slice __opcode 12 4)
                                              let imm12 := (BitVec.slice __opcode 0 12)
                                              (decode_aarch32_instrs_AND_i_A1enc_A_txt cond S Rn Rd
                                                imm12)
                                              (pure false))
                                          else
                                            (do
                                              let w__35 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                         __opcode 27 21)) == (0b0000000#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                         __opcode 4 4)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                then
                                                  (do
                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                           __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__33 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__33 <b 2845) : Bool))))
                                                    else (pure false))
                                                else (pure false) ) : SailM Bool )
                                              if (w__35 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 2845
                                                  let cond := (BitVec.slice __opcode 28 4)
                                                  let S := (BitVec.slice __opcode 20 1)
                                                  let Rn := (BitVec.slice __opcode 16 4)
                                                  let Rd := (BitVec.slice __opcode 12 4)
                                                  let imm5 := (BitVec.slice __opcode 7 5)
                                                  let stype := (BitVec.slice __opcode 5 2)
                                                  let Rm := (BitVec.slice __opcode 0 4)
                                                  (decode_aarch32_instrs_AND_r_A1enc_A_txt cond S Rn
                                                    Rd imm5 stype Rm)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__38 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                             __opcode 27 21)) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 7 7)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 4 4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                               __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__36 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__36 <b 2848) : Bool))))
                                                        else (pure false))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__38 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 2848
                                                      let cond := (BitVec.slice __opcode 28 4)
                                                      let S := (BitVec.slice __opcode 20 1)
                                                      let Rn := (BitVec.slice __opcode 16 4)
                                                      let Rd := (BitVec.slice __opcode 12 4)
                                                      let Rs := (BitVec.slice __opcode 8 4)
                                                      let stype := (BitVec.slice __opcode 5 2)
                                                      let Rm := (BitVec.slice __opcode 0 4)
                                                      (decode_aarch32_instrs_AND_rr_A1enc_A_txt cond
                                                        S Rn Rd Rs stype Rm)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__41 ← (( do
                                                        if ((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                               __opcode 27 21)) == (0b0011110#7 : (BitVec 7))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                   __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__39 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__39 <b 2860) : Bool))))
                                                            else (pure false))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__41 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 2860
                                                          let cond := (BitVec.slice __opcode 28 4)
                                                          let S := (BitVec.slice __opcode 20 1)
                                                          let Rn := (BitVec.slice __opcode 16 4)
                                                          let Rd := (BitVec.slice __opcode 12 4)
                                                          let imm12 := (BitVec.slice __opcode 0 12)
                                                          (decode_aarch32_instrs_BIC_i_A1enc_A_txt
                                                            cond S Rn Rd imm12)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__44 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                     __opcode 27 21)) == (0b0001110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                     __opcode 4 4)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                       __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__42 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__42 <b 2862) : Bool))))
                                                                else (pure false))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__44 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 2862
                                                              let cond :=
                                                                (BitVec.slice __opcode 28 4)
                                                              let S := (BitVec.slice __opcode 20 1)
                                                              let Rn := (BitVec.slice __opcode 16 4)
                                                              let Rd := (BitVec.slice __opcode 12 4)
                                                              let imm5 :=
                                                                (BitVec.slice __opcode 7 5)
                                                              let stype :=
                                                                (BitVec.slice __opcode 5 2)
                                                              let Rm := (BitVec.slice __opcode 0 4)
                                                              (decode_aarch32_instrs_BIC_r_A1enc_A_txt
                                                                cond S Rn Rd imm5 stype Rm)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__47 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                         __opcode 27 21)) == (0b0001110#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 7 7)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 4 4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                           __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__45 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__45 <b 2865) : Bool))))
                                                                    else (pure false))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__47 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 2865
                                                                  let cond :=
                                                                    (BitVec.slice __opcode 28 4)
                                                                  let S :=
                                                                    (BitVec.slice __opcode 20 1)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 16 4)
                                                                  let Rd :=
                                                                    (BitVec.slice __opcode 12 4)
                                                                  let Rs :=
                                                                    (BitVec.slice __opcode 8 4)
                                                                  let stype :=
                                                                    (BitVec.slice __opcode 5 2)
                                                                  let Rm :=
                                                                    (BitVec.slice __opcode 0 4)
                                                                  (decode_aarch32_instrs_BIC_rr_A1enc_A_txt
                                                                    cond S Rn Rd Rs stype Rm)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__50 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                             __opcode 27 20)) == (0x12#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                             __opcode 7 4)) == (0x7#4 : (BitVec 4)))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                               __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__48 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__48 <b 2866) : Bool))))
                                                                        else (pure false))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__50 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 2866
                                                                      let cond :=
                                                                        (BitVec.slice __opcode 28 4)
                                                                      let imm12 :=
                                                                        (BitVec.slice __opcode 8 12)
                                                                      let imm4 :=
                                                                        (BitVec.slice __opcode 0 4)
                                                                      (decode_aarch32_instrs_BKPT_A1enc_A_txt
                                                                        cond imm12 imm4)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__53 ← (( do
                                                                        if ((((Sail.BitVec.castWidth (m := 24) (Sail.BitVec.extractLsb
                                                                               __opcode 27 4)) == (0x12FFF3#24 : (BitVec 24))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                   __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__51 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__51 <b 2872) : Bool))))
                                                                            else (pure false))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__53 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 2872
                                                                          let cond :=
                                                                            (BitVec.slice __opcode
                                                                              28 4)
                                                                          let Rm :=
                                                                            (BitVec.slice __opcode 0
                                                                              4)
                                                                          if ((((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                         __opcode
                                                                                                         16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                         __opcode
                                                                                                         17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                       __opcode
                                                                                                       18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                     __opcode
                                                                                                     19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                   __opcode
                                                                                                   12)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                 __opcode
                                                                                                 13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                               __opcode
                                                                                               14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                             __opcode
                                                                                             15)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                           __opcode
                                                                                           8)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                       __opcode 10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                     __opcode 11)])) != 1#1)) : Bool)
                                                                          then
                                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                                              ()))
                                                                          else
                                                                            (do
                                                                              (decode_aarch32_instrs_BLX_r_A1enc_A_txt
                                                                                cond Rm))
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__56 ← (( do
                                                                            if ((((Sail.BitVec.castWidth (m := 24) (Sail.BitVec.extractLsb
                                                                                   __opcode 27 4)) == (0x12FFF1#24 : (BitVec 24))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                       __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__54 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__54 <b 2874) : Bool))))
                                                                                else (pure false))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__56 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 2874
                                                                              let cond :=
                                                                                (BitVec.slice
                                                                                  __opcode 28 4)
                                                                              let Rm :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 4)
                                                                              if ((((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                             __opcode
                                                                                                             16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                             __opcode
                                                                                                             17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                           __opcode
                                                                                                           18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                         __opcode
                                                                                                         19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                       __opcode
                                                                                                       12)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                     __opcode
                                                                                                     13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                   __opcode
                                                                                                   14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                 __opcode
                                                                                                 15)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                               __opcode
                                                                                               8)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                             __opcode
                                                                                             9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                           __opcode
                                                                                           10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 11)])) != 1#1)) : Bool)
                                                                              then
                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                  ()))
                                                                              else
                                                                                (do
                                                                                  (decode_aarch32_instrs_BX_A1enc_A_txt
                                                                                    cond Rm))
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__59 ← (( do
                                                                                if ((((Sail.BitVec.castWidth (m := 24) (Sail.BitVec.extractLsb
                                                                                       __opcode 27 4)) == (0x12FFF2#24 : (BitVec 24))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                           __opcode
                                                                                           28 4)) != 0b1111#4) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__57 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__57 <b 2876) : Bool))))
                                                                                    else
                                                                                      (pure false))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__59 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 2876
                                                                                  let cond :=
                                                                                    (BitVec.slice
                                                                                      __opcode 28 4)
                                                                                  let Rm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 4)
                                                                                  if ((((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                 __opcode
                                                                                                                 16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                 __opcode
                                                                                                                 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                               __opcode
                                                                                                               18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                             __opcode
                                                                                                             19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                           __opcode
                                                                                                           12)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                         __opcode
                                                                                                         13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                       __opcode
                                                                                                       14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                     __opcode
                                                                                                     15)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                   __opcode
                                                                                                   8)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                 __opcode
                                                                                                 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                               __opcode
                                                                                               10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                             __opcode
                                                                                             11)])) != 1#1)) : Bool)
                                                                                  then
                                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                                      ()))
                                                                                  else
                                                                                    (do
                                                                                      (decode_aarch32_instrs_BXJ_A1enc_A_txt
                                                                                        cond Rm))
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__62 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             27 16)) == (0x16F#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             11 4)) == (0xF1#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                               __opcode
                                                                                               28 4)) != 0b1111#4) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__60 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__60 <b 2881) : Bool))))
                                                                                        else
                                                                                          (pure false))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__62 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 2881
                                                                                      let cond :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          28 4)
                                                                                      let Rd :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          12 4)
                                                                                      let Rm :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          4)
                                                                                      if ((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                             __opcode
                                                                                                             16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                             __opcode
                                                                                                             17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                           __opcode
                                                                                                           18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                         __opcode
                                                                                                         19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                       __opcode
                                                                                                       8)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                     __opcode
                                                                                                     9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                   __opcode
                                                                                                   10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                 __opcode
                                                                                                 11)])) != 1#1)) : Bool)
                                                                                      then
                                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                                          ()))
                                                                                      else
                                                                                        (do
                                                                                          (decode_aarch32_instrs_CLZ_A1enc_A_txt
                                                                                            cond Rd
                                                                                            Rm))
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__65 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 27
                                                                                                 20)) == (0x37#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 15
                                                                                                 12)) == (0x0#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                   __opcode
                                                                                                   28
                                                                                                   4)) != 0b1111#4) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__63 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__63 <b 2883) : Bool))))
                                                                                            else
                                                                                              (pure false))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__65 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 2883
                                                                                          let cond :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              28 4)
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 4)
                                                                                          let imm12 :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 12)
                                                                                          if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                         __opcode
                                                                                                         12)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                         __opcode
                                                                                                         13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                       __opcode
                                                                                                       14)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                     __opcode
                                                                                                     15)])) != 0#1)) : Bool)
                                                                                          then
                                                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                                                              ()))
                                                                                          else
                                                                                            (do
                                                                                              (decode_aarch32_instrs_CMN_i_A1enc_A_txt
                                                                                                cond
                                                                                                Rn
                                                                                                imm12))
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__68 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     27
                                                                                                     20)) == (0x17#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       15
                                                                                                       12)) == (0x0#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       4
                                                                                                       4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                       __opcode
                                                                                                       28
                                                                                                       4)) != 0b1111#4) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__66 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__66 <b 2885) : Bool))))
                                                                                                else
                                                                                                  (pure false))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__68 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 2885
                                                                                              let cond :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  28
                                                                                                  4)
                                                                                              let Rn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  4)
                                                                                              let imm5 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  7
                                                                                                  5)
                                                                                              let stype :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  5
                                                                                                  2)
                                                                                              let Rm :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  4)
                                                                                              if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                             __opcode
                                                                                                             12)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                             __opcode
                                                                                                             13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                           __opcode
                                                                                                           14)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                         __opcode
                                                                                                         15)])) != 0#1)) : Bool)
                                                                                              then
                                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                                  ()))
                                                                                              else
                                                                                                (do
                                                                                                  (decode_aarch32_instrs_CMN_r_A1enc_A_txt
                                                                                                    cond
                                                                                                    Rn
                                                                                                    imm5
                                                                                                    stype
                                                                                                    Rm))
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__71 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         27
                                                                                                         20)) == (0x17#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           15
                                                                                                           12)) == (0x0#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             7
                                                                                                             7)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             4
                                                                                                             4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                           __opcode
                                                                                                           28
                                                                                                           4)) != 0b1111#4) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__69 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__69 <b 2888) : Bool))))
                                                                                                    else
                                                                                                      (pure false))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__71 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 2888
                                                                                                  let cond :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      28
                                                                                                      4)
                                                                                                  let Rn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      4)
                                                                                                  let Rs :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      8
                                                                                                      4)
                                                                                                  let stype :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      5
                                                                                                      2)
                                                                                                  let Rm :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      4)
                                                                                                  if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                 __opcode
                                                                                                                 12)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                 __opcode
                                                                                                                 13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                               __opcode
                                                                                                               14)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                             __opcode
                                                                                                             15)])) != 0#1)) : Bool)
                                                                                                  then
                                                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                                                      ()))
                                                                                                  else
                                                                                                    (do
                                                                                                      (decode_aarch32_instrs_CMN_rr_A1enc_A_txt
                                                                                                        cond
                                                                                                        Rn
                                                                                                        Rs
                                                                                                        stype
                                                                                                        Rm))
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__74 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             27
                                                                                                             20)) == (0x35#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             15
                                                                                                             12)) == (0x0#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                               __opcode
                                                                                                               28
                                                                                                               4)) != 0b1111#4) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__72 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__72 <b 2889) : Bool))))
                                                                                                        else
                                                                                                          (pure false))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__74 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 2889
                                                                                                      let cond :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          28
                                                                                                          4)
                                                                                                      let Rn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          4)
                                                                                                      let imm12 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          12)
                                                                                                      if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                     __opcode
                                                                                                                     12)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                     __opcode
                                                                                                                     13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                   __opcode
                                                                                                                   14)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                 __opcode
                                                                                                                 15)])) != 0#1)) : Bool)
                                                                                                      then
                                                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                                                          ()))
                                                                                                      else
                                                                                                        (do
                                                                                                          (decode_aarch32_instrs_CMP_i_A1enc_A_txt
                                                                                                            cond
                                                                                                            Rn
                                                                                                            imm12))
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__77 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 27
                                                                                                                 20)) == (0x15#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   15
                                                                                                                   12)) == (0x0#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   4
                                                                                                                   4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                   __opcode
                                                                                                                   28
                                                                                                                   4)) != 0b1111#4) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__75 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__75 <b 2892) : Bool))))
                                                                                                            else
                                                                                                              (pure false))
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
                                                                                                          writeReg SEE 2892
                                                                                                          let cond :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              28
                                                                                                              4)
                                                                                                          let Rn :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              4)
                                                                                                          let imm5 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              7
                                                                                                              5)
                                                                                                          let stype :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              5
                                                                                                              2)
                                                                                                          let Rm :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              4)
                                                                                                          if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                         __opcode
                                                                                                                         12)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                         __opcode
                                                                                                                         13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                       __opcode
                                                                                                                       14)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                     __opcode
                                                                                                                     15)])) != 0#1)) : Bool)
                                                                                                          then
                                                                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                                                                              ()))
                                                                                                          else
                                                                                                            (do
                                                                                                              (decode_aarch32_instrs_CMP_r_A1enc_A_txt
                                                                                                                cond
                                                                                                                Rn
                                                                                                                imm5
                                                                                                                stype
                                                                                                                Rm))
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__80 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     27
                                                                                                                     20)) == (0x15#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       15
                                                                                                                       12)) == (0x0#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         7
                                                                                                                         7)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         4
                                                                                                                         4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                       __opcode
                                                                                                                       28
                                                                                                                       4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__78 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__78 <b 2896) : Bool))))
                                                                                                                else
                                                                                                                  (pure false))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__80 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 2896
                                                                                                              let cond :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  28
                                                                                                                  4)
                                                                                                              let Rn :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  4)
                                                                                                              let Rs :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  8
                                                                                                                  4)
                                                                                                              let stype :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  5
                                                                                                                  2)
                                                                                                              let Rm :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  4)
                                                                                                              if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                             __opcode
                                                                                                                             12)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                             __opcode
                                                                                                                             13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                           __opcode
                                                                                                                           14)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                         __opcode
                                                                                                                         15)])) != 0#1)) : Bool)
                                                                                                              then
                                                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                  ()))
                                                                                                              else
                                                                                                                (do
                                                                                                                  (decode_aarch32_instrs_CMP_rr_A1enc_A_txt
                                                                                                                    cond
                                                                                                                    Rn
                                                                                                                    Rs
                                                                                                                    stype
                                                                                                                    Rm))
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__83 ← (( do
                                                                                                                if ((((Sail.BitVec.castWidth (m := 24) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       27
                                                                                                                       4)) == (0x320F0F#24 : (BitVec 24))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                           __opcode
                                                                                                                           28
                                                                                                                           4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__81 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__81 <b 2897) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false))
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
                                                                                                                  writeReg SEE 2897
                                                                                                                  let cond :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      28
                                                                                                                      4)
                                                                                                                  let option_name :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      4)
                                                                                                                  if ((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                         __opcode
                                                                                                                                         12)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                         __opcode
                                                                                                                                         13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                       __opcode
                                                                                                                                       14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                     __opcode
                                                                                                                                     15)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                   __opcode
                                                                                                                                   8)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                 __opcode
                                                                                                                                 9)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                               __opcode
                                                                                                                               10)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                             __opcode
                                                                                                                             11)])) != 0#1)) : Bool)
                                                                                                                  then
                                                                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                      ()))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      (decode_aarch32_instrs_DBG_A1enc_A_txt
                                                                                                                        cond
                                                                                                                        option_name))
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__86 ← (( do
                                                                                                                    if ((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           27
                                                                                                                           21)) == (0b0010001#7 : (BitVec 7))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                               __opcode
                                                                                                                               28
                                                                                                                               4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__84 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__84 <b 2903) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__86 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 2903
                                                                                                                      let cond :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          28
                                                                                                                          4)
                                                                                                                      let S :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          20
                                                                                                                          1)
                                                                                                                      let Rn :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          16
                                                                                                                          4)
                                                                                                                      let Rd :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          12
                                                                                                                          4)
                                                                                                                      let imm12 :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          12)
                                                                                                                      (decode_aarch32_instrs_EOR_i_A1enc_A_txt
                                                                                                                        cond
                                                                                                                        S
                                                                                                                        Rn
                                                                                                                        Rd
                                                                                                                        imm12)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__89 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 27
                                                                                                                                 21)) == (0b0000001#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 4
                                                                                                                                 4)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                   __opcode
                                                                                                                                   28
                                                                                                                                   4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__87 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__87 <b 2905) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false))
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
                                                                                                                          writeReg SEE 2905
                                                                                                                          let cond :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              28
                                                                                                                              4)
                                                                                                                          let S :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              20
                                                                                                                              1)
                                                                                                                          let Rn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              4)
                                                                                                                          let Rd :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              12
                                                                                                                              4)
                                                                                                                          let imm5 :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              7
                                                                                                                              5)
                                                                                                                          let stype :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              5
                                                                                                                              2)
                                                                                                                          let Rm :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              4)
                                                                                                                          (decode_aarch32_instrs_EOR_r_A1enc_A_txt
                                                                                                                            cond
                                                                                                                            S
                                                                                                                            Rn
                                                                                                                            Rd
                                                                                                                            imm5
                                                                                                                            stype
                                                                                                                            Rm)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__92 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     27
                                                                                                                                     21)) == (0b0000001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       7
                                                                                                                                       7)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       4
                                                                                                                                       4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                       __opcode
                                                                                                                                       28
                                                                                                                                       4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__90 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__90 <b 2908) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__92 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 2908
                                                                                                                              let cond :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  28
                                                                                                                                  4)
                                                                                                                              let S :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  20
                                                                                                                                  1)
                                                                                                                              let Rn :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
                                                                                                                                  4)
                                                                                                                              let Rd :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  12
                                                                                                                                  4)
                                                                                                                              let Rs :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  8
                                                                                                                                  4)
                                                                                                                              let stype :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  5
                                                                                                                                  2)
                                                                                                                              let Rm :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  4)
                                                                                                                              (decode_aarch32_instrs_EOR_rr_A1enc_A_txt
                                                                                                                                cond
                                                                                                                                S
                                                                                                                                Rn
                                                                                                                                Rd
                                                                                                                                Rs
                                                                                                                                stype
                                                                                                                                Rm)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__95 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         27
                                                                                                                                         25)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           22
                                                                                                                                           22)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             20
                                                                                                                                             20)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             7
                                                                                                                                             4)) == (0xD#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                           __opcode
                                                                                                                                           28
                                                                                                                                           4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__93 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__93 <b 2935) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false))
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
                                                                                                                                  writeReg SEE 2935
                                                                                                                                  let cond :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      28
                                                                                                                                      4)
                                                                                                                                  let P :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      24
                                                                                                                                      1)
                                                                                                                                  let U :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      23
                                                                                                                                      1)
                                                                                                                                  let W :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      21
                                                                                                                                      1)
                                                                                                                                  let Rn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      4)
                                                                                                                                  let Rt :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      12
                                                                                                                                      4)
                                                                                                                                  let imm4H :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      8
                                                                                                                                      4)
                                                                                                                                  let imm4L :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      4)
                                                                                                                                  (decode_aarch32_instrs_LDRD_i_A1enc_A_txt
                                                                                                                                    cond
                                                                                                                                    P
                                                                                                                                    U
                                                                                                                                    W
                                                                                                                                    Rn
                                                                                                                                    Rt
                                                                                                                                    imm4H
                                                                                                                                    imm4L)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (pure true))))))))))))))))))))))))))))))))


end ArmFull.Functions
