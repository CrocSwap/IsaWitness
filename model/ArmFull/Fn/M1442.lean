import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0246
import ArmFull.Fn.M1280
import ArmFull.Fn.M1281
import ArmFull.Fn.M1282
import ArmFull.Fn.M1283
import ArmFull.Fn.M1284
import ArmFull.Fn.M1285
import ArmFull.Fn.M1290

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
def __DecodeA32_LoadStoreImmLit (pc : Int) (__opcode : (BitVec 32)) : SailM Unit := do
  let w__2 ← (( do
    if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb __opcode 27 25)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
               __opcode 22 22)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
               __opcode 20 20)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
    then
      (do
        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
        then
          (do
            let w__0 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__0 <b 2923) : Bool))))
        else (pure false))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      writeReg SEE 2923
      let cond := (BitVec.slice __opcode 28 4)
      let P := (BitVec.slice __opcode 24 1)
      let U := (BitVec.slice __opcode 23 1)
      let W := (BitVec.slice __opcode 21 1)
      let Rn := (BitVec.slice __opcode 16 4)
      let Rt := (BitVec.slice __opcode 12 4)
      let imm12 := (BitVec.slice __opcode 0 12)
      (decode_aarch32_instrs_LDRB_i_A1enc_A_txt cond P U W Rn Rt imm12))
  else
    (do
      let w__5 ← (( do
        if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb __opcode 27 25)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                   __opcode 22 22)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                   __opcode 20 16)) == (0b11111#5 : (BitVec 5))))) : Bool) : Bool)
        then
          (do
            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
            then
              (do
                let w__3 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__3 <b 2927) : Bool))))
            else (pure false))
        else (pure false) ) : SailM Bool )
      if (w__5 : Bool)
      then
        (do
          writeReg SEE 2927
          let cond := (BitVec.slice __opcode 28 4)
          let P := (BitVec.slice __opcode 24 1)
          let U := (BitVec.slice __opcode 23 1)
          let W := (BitVec.slice __opcode 21 1)
          let Rt := (BitVec.slice __opcode 12 4)
          let imm12 := (BitVec.slice __opcode 0 12)
          (decode_aarch32_instrs_LDRB_l_A1enc_A_txt cond P U W Rt imm12))
      else
        (do
          let w__8 ← (( do
            if (((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb __opcode 27 24)) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                     __opcode 22 20)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
            then
              (do
                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                then
                  (do
                    let w__6 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__6 <b 2932) : Bool))))
                else (pure false))
            else (pure false) ) : SailM Bool )
          if (w__8 : Bool)
          then
            (do
              writeReg SEE 2932
              let cond := (BitVec.slice __opcode 28 4)
              let U := (BitVec.slice __opcode 23 1)
              let Rn := (BitVec.slice __opcode 16 4)
              let Rt := (BitVec.slice __opcode 12 4)
              let imm12 := (BitVec.slice __opcode 0 12)
              (decode_aarch32_instrs_LDRBT_A1enc_A_txt cond U Rn Rt imm12))
          else
            (do
              let w__11 ← (( do
                if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb __opcode 27 25)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           __opcode 22 22)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           __opcode 20 20)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                then
                  (do
                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                    then
                      (do
                        let w__9 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__9 <b 2960) : Bool))))
                    else (pure false))
                else (pure false) ) : SailM Bool )
              if (w__11 : Bool)
              then
                (do
                  writeReg SEE 2960
                  let cond := (BitVec.slice __opcode 28 4)
                  let P := (BitVec.slice __opcode 24 1)
                  let U := (BitVec.slice __opcode 23 1)
                  let W := (BitVec.slice __opcode 21 1)
                  let Rn := (BitVec.slice __opcode 16 4)
                  let Rt := (BitVec.slice __opcode 12 4)
                  let imm12 := (BitVec.slice __opcode 0 12)
                  (decode_aarch32_instrs_LDR_i_A1enc_A_txt cond P U W Rn Rt imm12))
              else
                (do
                  let w__14 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb __opcode 27 25)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                               __opcode 22 22)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                               __opcode 20 16)) == (0b11111#5 : (BitVec 5))))) : Bool) : Bool)
                    then
                      (do
                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                        then
                          (do
                            let w__12 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__12 <b 2965) : Bool))))
                        else (pure false))
                    else (pure false) ) : SailM Bool )
                  if (w__14 : Bool)
                  then
                    (do
                      writeReg SEE 2965
                      let cond := (BitVec.slice __opcode 28 4)
                      let P := (BitVec.slice __opcode 24 1)
                      let U := (BitVec.slice __opcode 23 1)
                      let W := (BitVec.slice __opcode 21 1)
                      let Rt := (BitVec.slice __opcode 12 4)
                      let imm12 := (BitVec.slice __opcode 0 12)
                      (decode_aarch32_instrs_LDR_l_A1enc_A_txt cond P U W Rt imm12))
                  else
                    (do
                      let w__17 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb __opcode 27
                                 24)) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                 __opcode 22 20)) == (0b011#3 : (BitVec 3)))) : Bool) : Bool)
                        then
                          (do
                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                            then
                              (do
                                let w__15 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__15 <b 2993) : Bool))))
                            else (pure false))
                        else (pure false) ) : SailM Bool )
                      if (w__17 : Bool)
                      then
                        (do
                          writeReg SEE 2993
                          let cond := (BitVec.slice __opcode 28 4)
                          let U := (BitVec.slice __opcode 23 1)
                          let Rn := (BitVec.slice __opcode 16 4)
                          let Rt := (BitVec.slice __opcode 12 4)
                          let imm12 := (BitVec.slice __opcode 0 12)
                          (decode_aarch32_instrs_LDRT_A1enc_A_txt cond U Rn Rt imm12))
                      else
                        (do
                          let w__20 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb __opcode
                                     27 25)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                       __opcode 22 22)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                       __opcode 20 20)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                            then
                              (do
                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                then
                                  (do
                                    let w__18 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__18 <b 3193) : Bool))))
                                else (pure false))
                            else (pure false) ) : SailM Bool )
                          if (w__20 : Bool)
                          then
                            (do
                              writeReg SEE 3193
                              let cond := (BitVec.slice __opcode 28 4)
                              let P := (BitVec.slice __opcode 24 1)
                              let U := (BitVec.slice __opcode 23 1)
                              let W := (BitVec.slice __opcode 21 1)
                              let Rn := (BitVec.slice __opcode 16 4)
                              let Rt := (BitVec.slice __opcode 12 4)
                              let imm12 := (BitVec.slice __opcode 0 12)
                              (decode_aarch32_instrs_STRB_i_A1enc_A_txt cond P U W Rn Rt imm12))
                          else
                            (do
                              let w__23 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                         __opcode 27 24)) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                         __opcode 22 20)) == (0b110#3 : (BitVec 3)))) : Bool) : Bool)
                                then
                                  (do
                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28
                                           4)) != 0b1111#4) : Bool) : Bool)
                                    then
                                      (do
                                        let w__21 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__21 <b 3200) : Bool))))
                                    else (pure false))
                                else (pure false) ) : SailM Bool )
                              if (w__23 : Bool)
                              then
                                (do
                                  writeReg SEE 3200
                                  let cond := (BitVec.slice __opcode 28 4)
                                  let U := (BitVec.slice __opcode 23 1)
                                  let Rn := (BitVec.slice __opcode 16 4)
                                  let Rt := (BitVec.slice __opcode 12 4)
                                  let imm12 := (BitVec.slice __opcode 0 12)
                                  (decode_aarch32_instrs_STRBT_A1enc_A_txt cond U Rn Rt imm12))
                              else
                                (do
                                  let w__26 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                             __opcode 27 25)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                               __opcode 22 22)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                               __opcode 20 20)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                    then
                                      (do
                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode
                                               28 4)) != 0b1111#4) : Bool) : Bool)
                                        then
                                          (do
                                            let w__24 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__24 <b 3224) : Bool))))
                                        else (pure false))
                                    else (pure false) ) : SailM Bool )
                                  if (w__26 : Bool)
                                  then
                                    (do
                                      writeReg SEE 3224
                                      let cond := (BitVec.slice __opcode 28 4)
                                      let P := (BitVec.slice __opcode 24 1)
                                      let U := (BitVec.slice __opcode 23 1)
                                      let W := (BitVec.slice __opcode 21 1)
                                      let Rn := (BitVec.slice __opcode 16 4)
                                      let Rt := (BitVec.slice __opcode 12 4)
                                      let imm12 := (BitVec.slice __opcode 0 12)
                                      (decode_aarch32_instrs_STR_i_A1enc_A_txt cond P U W Rn Rt
                                        imm12))
                                  else
                                    (do
                                      let w__29 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                 __opcode 27 24)) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                 __opcode 22 20)) == (0b010#3 : (BitVec 3)))) : Bool) : Bool)
                                        then
                                          (do
                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                   __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                            then
                                              (do
                                                let w__27 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__27 <b 3232) : Bool))))
                                            else (pure false))
                                        else (pure false) ) : SailM Bool )
                                      if (w__29 : Bool)
                                      then
                                        (do
                                          writeReg SEE 3232
                                          let cond := (BitVec.slice __opcode 28 4)
                                          let U := (BitVec.slice __opcode 23 1)
                                          let Rn := (BitVec.slice __opcode 16 4)
                                          let Rt := (BitVec.slice __opcode 12 4)
                                          let imm12 := (BitVec.slice __opcode 0 12)
                                          (decode_aarch32_instrs_STRT_A1enc_A_txt cond U Rn Rt imm12))
                                      else sailThrow ((Error_Undefined ())))))))))))


/-- Type quantifiers: pc : Int -/
def __DecodeA32_LoadStoreReg (pc : Int) (__opcode : (BitVec 32)) : SailM Unit := do
  let w__2 ← (( do
    if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb __opcode 27 25)) == (0b011#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
               __opcode 22 22)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                 __opcode 20 20)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                 __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
    then
      (do
        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
        then
          (do
            let w__0 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__0 <b 2929) : Bool))))
        else (pure false))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      writeReg SEE 2929
      let cond := (BitVec.slice __opcode 28 4)
      let P := (BitVec.slice __opcode 24 1)
      let U := (BitVec.slice __opcode 23 1)
      let W := (BitVec.slice __opcode 21 1)
      let Rn := (BitVec.slice __opcode 16 4)
      let Rt := (BitVec.slice __opcode 12 4)
      let imm5 := (BitVec.slice __opcode 7 5)
      let stype := (BitVec.slice __opcode 5 2)
      let Rm := (BitVec.slice __opcode 0 4)
      (decode_aarch32_instrs_LDRB_r_A1enc_A_txt cond P U W Rn Rt imm5 stype Rm))
  else
    (do
      let w__5 ← (( do
        if (((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb __opcode 27 24)) == (0x6#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                   __opcode 22 20)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                   __opcode 4 4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
        then
          (do
            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
            then
              (do
                let w__3 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__3 <b 2933) : Bool))))
            else (pure false))
        else (pure false) ) : SailM Bool )
      if (w__5 : Bool)
      then
        (do
          writeReg SEE 2933
          let cond := (BitVec.slice __opcode 28 4)
          let U := (BitVec.slice __opcode 23 1)
          let Rn := (BitVec.slice __opcode 16 4)
          let Rt := (BitVec.slice __opcode 12 4)
          let imm5 := (BitVec.slice __opcode 7 5)
          let stype := (BitVec.slice __opcode 5 2)
          let Rm := (BitVec.slice __opcode 0 4)
          (decode_aarch32_instrs_LDRBT_A2enc_A_txt cond U Rn Rt imm5 stype Rm))
      else
        (do
          let w__8 ← (( do
            if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb __opcode 27 25)) == (0b011#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       __opcode 22 22)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                         __opcode 20 20)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                         __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
            then
              (do
                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                then
                  (do
                    let w__6 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__6 <b 2968) : Bool))))
                else (pure false))
            else (pure false) ) : SailM Bool )
          if (w__8 : Bool)
          then
            (do
              writeReg SEE 2968
              let cond := (BitVec.slice __opcode 28 4)
              let P := (BitVec.slice __opcode 24 1)
              let U := (BitVec.slice __opcode 23 1)
              let W := (BitVec.slice __opcode 21 1)
              let Rn := (BitVec.slice __opcode 16 4)
              let Rt := (BitVec.slice __opcode 12 4)
              let imm5 := (BitVec.slice __opcode 7 5)
              let stype := (BitVec.slice __opcode 5 2)
              let Rm := (BitVec.slice __opcode 0 4)
              (decode_aarch32_instrs_LDR_r_A1enc_A_txt cond P U W Rn Rt imm5 stype Rm))
          else
            (do
              let w__11 ← (( do
                if (((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb __opcode 27 24)) == (0x6#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                           __opcode 22 20)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           __opcode 4 4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                then
                  (do
                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                    then
                      (do
                        let w__9 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__9 <b 2994) : Bool))))
                    else (pure false))
                else (pure false) ) : SailM Bool )
              if (w__11 : Bool)
              then
                (do
                  writeReg SEE 2994
                  let cond := (BitVec.slice __opcode 28 4)
                  let U := (BitVec.slice __opcode 23 1)
                  let Rn := (BitVec.slice __opcode 16 4)
                  let Rt := (BitVec.slice __opcode 12 4)
                  let imm5 := (BitVec.slice __opcode 7 5)
                  let stype := (BitVec.slice __opcode 5 2)
                  let Rm := (BitVec.slice __opcode 0 4)
                  (decode_aarch32_instrs_LDRT_A2enc_A_txt cond U Rn Rt imm5 stype Rm))
              else
                (do
                  let w__14 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb __opcode 27 25)) == (0b011#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                               __opcode 22 22)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                 __opcode 20 20)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                 __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                    then
                      (do
                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                        then
                          (do
                            let w__12 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__12 <b 3197) : Bool))))
                        else (pure false))
                    else (pure false) ) : SailM Bool )
                  if (w__14 : Bool)
                  then
                    (do
                      writeReg SEE 3197
                      let cond := (BitVec.slice __opcode 28 4)
                      let P := (BitVec.slice __opcode 24 1)
                      let U := (BitVec.slice __opcode 23 1)
                      let W := (BitVec.slice __opcode 21 1)
                      let Rn := (BitVec.slice __opcode 16 4)
                      let Rt := (BitVec.slice __opcode 12 4)
                      let imm5 := (BitVec.slice __opcode 7 5)
                      let stype := (BitVec.slice __opcode 5 2)
                      let Rm := (BitVec.slice __opcode 0 4)
                      (decode_aarch32_instrs_STRB_r_A1enc_A_txt cond P U W Rn Rt imm5 stype Rm))
                  else
                    (do
                      let w__17 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb __opcode 27
                                 24)) == (0x6#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                   __opcode 22 20)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                   __opcode 4 4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                        then
                          (do
                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                            then
                              (do
                                let w__15 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__15 <b 3201) : Bool))))
                            else (pure false))
                        else (pure false) ) : SailM Bool )
                      if (w__17 : Bool)
                      then
                        (do
                          writeReg SEE 3201
                          let cond := (BitVec.slice __opcode 28 4)
                          let U := (BitVec.slice __opcode 23 1)
                          let Rn := (BitVec.slice __opcode 16 4)
                          let Rt := (BitVec.slice __opcode 12 4)
                          let imm5 := (BitVec.slice __opcode 7 5)
                          let stype := (BitVec.slice __opcode 5 2)
                          let Rm := (BitVec.slice __opcode 0 4)
                          (decode_aarch32_instrs_STRBT_A2enc_A_txt cond U Rn Rt imm5 stype Rm))
                      else
                        (do
                          let w__20 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb __opcode
                                     27 25)) == (0b011#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                       __opcode 22 22)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                         __opcode 20 20)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                         __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                            then
                              (do
                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                then
                                  (do
                                    let w__18 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__18 <b 3229) : Bool))))
                                else (pure false))
                            else (pure false) ) : SailM Bool )
                          if (w__20 : Bool)
                          then
                            (do
                              writeReg SEE 3229
                              let cond := (BitVec.slice __opcode 28 4)
                              let P := (BitVec.slice __opcode 24 1)
                              let U := (BitVec.slice __opcode 23 1)
                              let W := (BitVec.slice __opcode 21 1)
                              let Rn := (BitVec.slice __opcode 16 4)
                              let Rt := (BitVec.slice __opcode 12 4)
                              let imm5 := (BitVec.slice __opcode 7 5)
                              let stype := (BitVec.slice __opcode 5 2)
                              let Rm := (BitVec.slice __opcode 0 4)
                              (decode_aarch32_instrs_STR_r_A1enc_A_txt cond P U W Rn Rt imm5 stype
                                Rm))
                          else
                            (do
                              let w__23 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                         __opcode 27 24)) == (0x6#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                           __opcode 22 20)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                           __opcode 4 4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                then
                                  (do
                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28
                                           4)) != 0b1111#4) : Bool) : Bool)
                                    then
                                      (do
                                        let w__21 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__21 <b 3233) : Bool))))
                                    else (pure false))
                                else (pure false) ) : SailM Bool )
                              if (w__23 : Bool)
                              then
                                (do
                                  writeReg SEE 3233
                                  let cond := (BitVec.slice __opcode 28 4)
                                  let U := (BitVec.slice __opcode 23 1)
                                  let Rn := (BitVec.slice __opcode 16 4)
                                  let Rt := (BitVec.slice __opcode 12 4)
                                  let imm5 := (BitVec.slice __opcode 7 5)
                                  let stype := (BitVec.slice __opcode 5 2)
                                  let Rm := (BitVec.slice __opcode 0 4)
                                  (decode_aarch32_instrs_STRT_A2enc_A_txt cond U Rn Rt imm5 stype Rm))
                              else sailThrow ((Error_Undefined ())))))))))


/-- Type quantifiers: pc : Int -/
def __DecodeA32_BranchBlock (pc : Int) (__opcode : (BitVec 32)) : SailM Unit := do
  let w__2 ← (( do
    if ((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb __opcode 27 24)) == (0xA#4 : (BitVec 4))) : Bool) : Bool)
    then
      (do
        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
        then
          (do
            let w__0 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__0 <b 2851) : Bool))))
        else (pure false))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      writeReg SEE 2851
      let cond := (BitVec.slice __opcode 28 4)
      let imm24 := (BitVec.slice __opcode 0 24)
      (decode_aarch32_instrs_B_A1enc_A_txt cond imm24))
  else
    (do
      let w__5 ← (( do
        if ((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb __opcode 27 24)) == (0xB#4 : (BitVec 4))) : Bool) : Bool)
        then
          (do
            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
            then
              (do
                let w__3 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__3 <b 2868) : Bool))))
            else (pure false))
        else (pure false) ) : SailM Bool )
      if (w__5 : Bool)
      then
        (do
          writeReg SEE 2868
          let cond := (BitVec.slice __opcode 28 4)
          let imm24 := (BitVec.slice __opcode 0 24)
          (decode_aarch32_instrs_BL_i_A1enc_A_txt cond imm24))
      else
        (do
          let w__7 ← (( do
            if ((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb __opcode 31 25)) == (0b1111101#7 : (BitVec 7))) : Bool) : Bool)
            then
              (do
                let w__6 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__6 <b 2869) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              writeReg SEE 2869
              let H := (BitVec.slice __opcode 24 1)
              let imm24 := (BitVec.slice __opcode 0 24)
              (decode_aarch32_instrs_BL_i_A2enc_A_txt H imm24))
          else
            (do
              let w__10 ← (( do
                if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb __opcode 27 22)) == (0b100010#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                         __opcode 20 20)) == (1#1 : (BitVec 1)))) : Bool) : Bool)
                then
                  (do
                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                    then
                      (do
                        let w__8 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__8 <b 2916) : Bool))))
                    else (pure false))
                else (pure false) ) : SailM Bool )
              if (w__10 : Bool)
              then
                (do
                  writeReg SEE 2916
                  let cond := (BitVec.slice __opcode 28 4)
                  let W := (BitVec.slice __opcode 21 1)
                  let Rn := (BitVec.slice __opcode 16 4)
                  let register_list := (BitVec.slice __opcode 0 16)
                  (decode_aarch32_instrs_LDM_A1enc_A_txt cond W Rn register_list))
              else
                (do
                  let w__13 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb __opcode 27 22)) == (0b100000#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                             __opcode 20 20)) == (1#1 : (BitVec 1)))) : Bool) : Bool)
                    then
                      (do
                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                        then
                          (do
                            let w__11 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__11 <b 2919) : Bool))))
                        else (pure false))
                    else (pure false) ) : SailM Bool )
                  if (w__13 : Bool)
                  then
                    (do
                      writeReg SEE 2919
                      let cond := (BitVec.slice __opcode 28 4)
                      let W := (BitVec.slice __opcode 21 1)
                      let Rn := (BitVec.slice __opcode 16 4)
                      let register_list := (BitVec.slice __opcode 0 16)
                      (decode_aarch32_instrs_LDMDA_A1enc_A_txt cond W Rn register_list))
                  else
                    (do
                      let w__16 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb __opcode 27
                                 22)) == (0b100100#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                 __opcode 20 20)) == (1#1 : (BitVec 1)))) : Bool) : Bool)
                        then
                          (do
                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                            then
                              (do
                                let w__14 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__14 <b 2920) : Bool))))
                            else (pure false))
                        else (pure false) ) : SailM Bool )
                      if (w__16 : Bool)
                      then
                        (do
                          writeReg SEE 2920
                          let cond := (BitVec.slice __opcode 28 4)
                          let W := (BitVec.slice __opcode 21 1)
                          let Rn := (BitVec.slice __opcode 16 4)
                          let register_list := (BitVec.slice __opcode 0 16)
                          (decode_aarch32_instrs_LDMDB_A1enc_A_txt cond W Rn register_list))
                      else
                        (do
                          let w__19 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb __opcode
                                     27 22)) == (0b100110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                     __opcode 20 20)) == (1#1 : (BitVec 1)))) : Bool) : Bool)
                            then
                              (do
                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                then
                                  (do
                                    let w__17 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__17 <b 2922) : Bool))))
                                else (pure false))
                            else (pure false) ) : SailM Bool )
                          if (w__19 : Bool)
                          then
                            (do
                              writeReg SEE 2922
                              let cond := (BitVec.slice __opcode 28 4)
                              let W := (BitVec.slice __opcode 21 1)
                              let Rn := (BitVec.slice __opcode 16 4)
                              let register_list := (BitVec.slice __opcode 0 16)
                              (decode_aarch32_instrs_LDMIB_A1enc_A_txt cond W Rn register_list))
                          else
                            (do
                              let w__22 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                         __opcode 27 22)) == (0b100010#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                         __opcode 20 20)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                then
                                  (do
                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28
                                           4)) != 0b1111#4) : Bool) : Bool)
                                    then
                                      (do
                                        let w__20 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__20 <b 3186) : Bool))))
                                    else (pure false))
                                else (pure false) ) : SailM Bool )
                              if (w__22 : Bool)
                              then
                                (do
                                  writeReg SEE 3186
                                  let cond := (BitVec.slice __opcode 28 4)
                                  let W := (BitVec.slice __opcode 21 1)
                                  let Rn := (BitVec.slice __opcode 16 4)
                                  let register_list := (BitVec.slice __opcode 0 16)
                                  (decode_aarch32_instrs_STM_A1enc_A_txt cond W Rn register_list))
                              else
                                (do
                                  let w__25 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                             __opcode 27 22)) == (0b100000#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             __opcode 20 20)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                    then
                                      (do
                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode
                                               28 4)) != 0b1111#4) : Bool) : Bool)
                                        then
                                          (do
                                            let w__23 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__23 <b 3189) : Bool))))
                                        else (pure false))
                                    else (pure false) ) : SailM Bool )
                                  if (w__25 : Bool)
                                  then
                                    (do
                                      writeReg SEE 3189
                                      let cond := (BitVec.slice __opcode 28 4)
                                      let W := (BitVec.slice __opcode 21 1)
                                      let Rn := (BitVec.slice __opcode 16 4)
                                      let register_list := (BitVec.slice __opcode 0 16)
                                      (decode_aarch32_instrs_STMDA_A1enc_A_txt cond W Rn
                                        register_list))
                                  else
                                    (do
                                      let w__28 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                 __opcode 27 22)) == (0b100100#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 __opcode 20 20)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                        then
                                          (do
                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                   __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                            then
                                              (do
                                                let w__26 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__26 <b 3190) : Bool))))
                                            else (pure false))
                                        else (pure false) ) : SailM Bool )
                                      if (w__28 : Bool)
                                      then
                                        (do
                                          writeReg SEE 3190
                                          let cond := (BitVec.slice __opcode 28 4)
                                          let W := (BitVec.slice __opcode 21 1)
                                          let Rn := (BitVec.slice __opcode 16 4)
                                          let register_list := (BitVec.slice __opcode 0 16)
                                          (decode_aarch32_instrs_STMDB_A1enc_A_txt cond W Rn
                                            register_list))
                                      else
                                        (do
                                          let w__31 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                     __opcode 27 22)) == (0b100110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                     __opcode 20 20)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                            then
                                              (do
                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                       __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__29 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__29 <b 3192) : Bool))))
                                                else (pure false))
                                            else (pure false) ) : SailM Bool )
                                          if (w__31 : Bool)
                                          then
                                            (do
                                              writeReg SEE 3192
                                              let cond := (BitVec.slice __opcode 28 4)
                                              let W := (BitVec.slice __opcode 21 1)
                                              let Rn := (BitVec.slice __opcode 16 4)
                                              let register_list := (BitVec.slice __opcode 0 16)
                                              (decode_aarch32_instrs_STMIB_A1enc_A_txt cond W Rn
                                                register_list))
                                          else
                                            (do
                                              let w__34 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                         __opcode 27 25)) == (0b100#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 22 22)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                             __opcode 20 20)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                             __opcode 15 15)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                           __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__32 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__32 <b 3776) : Bool))))
                                                    else (pure false))
                                                else (pure false) ) : SailM Bool )
                                              if (w__34 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 3776
                                                  let cond := (BitVec.slice __opcode 28 4)
                                                  let P := (BitVec.slice __opcode 24 1)
                                                  let U := (BitVec.slice __opcode 23 1)
                                                  let W := (BitVec.slice __opcode 21 1)
                                                  let Rn := (BitVec.slice __opcode 16 4)
                                                  let register_list := (BitVec.slice __opcode 0 15)
                                                  (decode_aarch32_instrs_LDM_e_A1enc_AS_txt cond P U
                                                    W Rn register_list))
                                              else
                                                (do
                                                  let w__37 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                             __opcode 27 25)) == (0b100#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                               __opcode 22 20)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 15 15)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                               __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__35 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__35 <b 3777) : Bool))))
                                                        else (pure false))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__37 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 3777
                                                      let cond := (BitVec.slice __opcode 28 4)
                                                      let P := (BitVec.slice __opcode 24 1)
                                                      let U := (BitVec.slice __opcode 23 1)
                                                      let Rn := (BitVec.slice __opcode 16 4)
                                                      let register_list :=
                                                        (BitVec.slice __opcode 0 15)
                                                      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                               __opcode 21)])) != 0#1) : Bool)
                                                      then
                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                          ()))
                                                      else
                                                        (do
                                                          (decode_aarch32_instrs_LDM_u_A1enc_AS_txt
                                                            cond P U Rn register_list)))
                                                  else
                                                    (do
                                                      let w__39 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                 __opcode 31 25)) == (0b1111100#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 22 22)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                     __opcode 20 20)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                                     __opcode 15 0)) == (0x0A00#16 : (BitVec 16)))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__38 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__38 <b 3787) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__39 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 3787
                                                          let P := (BitVec.slice __opcode 24 1)
                                                          let U := (BitVec.slice __opcode 23 1)
                                                          let W := (BitVec.slice __opcode 21 1)
                                                          let Rn := (BitVec.slice __opcode 16 4)
                                                          if ((((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 12)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                       __opcode 14)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                     __opcode 15)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                   __opcode 0)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                 __opcode 1)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                               __opcode 2)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                             __opcode 3)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                           __opcode 4)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                         __opcode 5)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                       __opcode 6)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                     __opcode 7)])) != 0#1)) : Bool)
                                                          then
                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                              ()))
                                                          else
                                                            (do
                                                              (decode_aarch32_instrs_RFE_A1enc_AS_txt
                                                                P U W Rn)))
                                                      else
                                                        (do
                                                          let w__41 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                     __opcode 31 25)) == (0b1111100#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 22 22)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                                       __opcode 20 5)) == (0x6828#16 : (BitVec 16))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__40 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__40 <b 3792) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__41 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 3792
                                                              let P := (BitVec.slice __opcode 24 1)
                                                              let U := (BitVec.slice __opcode 23 1)
                                                              let W := (BitVec.slice __opcode 21 1)
                                                              let mode :=
                                                                (BitVec.slice __opcode 0 5)
                                                              if (((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                           __opcode
                                                                                           16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                           __opcode
                                                                                           17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 18)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                       __opcode 19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                     __opcode 12)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                   __opcode 13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                 __opcode 14)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                               __opcode 15)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                             __opcode 5)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                           __opcode 6)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                         __opcode 7)])) != 0#1)) : Bool)
                                                              then
                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                  ()))
                                                              else
                                                                (do
                                                                  (decode_aarch32_instrs_SRS_A1enc_AS_txt
                                                                    P U W mode)))
                                                          else
                                                            (do
                                                              let w__44 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                         __opcode 27 25)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                         __opcode 22 20)) == (0b100#3 : (BitVec 3)))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                           __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__42 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__42 <b 3795) : Bool))))
                                                                    else (pure false))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__44 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 3795
                                                                  let cond :=
                                                                    (BitVec.slice __opcode 28 4)
                                                                  let P :=
                                                                    (BitVec.slice __opcode 24 1)
                                                                  let U :=
                                                                    (BitVec.slice __opcode 23 1)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 16 4)
                                                                  let register_list :=
                                                                    (BitVec.slice __opcode 0 16)
                                                                  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                           __opcode 21)])) != 0#1) : Bool)
                                                                  then
                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                      ()))
                                                                  else
                                                                    (do
                                                                      (decode_aarch32_instrs_STM_u_A1enc_AS_txt
                                                                        cond P U Rn register_list)))
                                                              else sailThrow ((Error_Undefined ())))))))))))))))))


end ArmFull.Functions
