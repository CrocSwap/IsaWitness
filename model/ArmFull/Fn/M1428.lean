import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M1303
import ArmFull.Fn.M1304
import ArmFull.Fn.M1305
import ArmFull.Fn.M1306
import ArmFull.Fn.M1307

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
def __DecodeA64_LoadStore__seg5 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__313 ← (( do
    if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 29 22)) == (0xB0#8 : (BitVec 8))) : Bool) : Bool)
    then
      (do
        let w__312 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__312 <b 602) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__313 : Bool)
  then
    (do
      writeReg SEE 602
      let Rt := (BitVec.slice __opcode 0 5)
      let Rn := (BitVec.slice __opcode 5 5)
      let Rt2 := (BitVec.slice __opcode 10 5)
      let imm7 := (BitVec.slice __opcode 15 7)
      let L := (BitVec.slice __opcode 22 1)
      let opc := (BitVec.slice __opcode 30 2)
      (decode_stnp_fpsimd_aarch64_instrs_memory_pair_simdfp_no_alloc Rt Rn Rt2 imm7 L opc)
      (pure false))
  else
    (do
      let w__315 ← (( do
        if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 29 22)) == (0xB3#8 : (BitVec 8))) : Bool) : Bool)
        then
          (do
            let w__314 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__314 <b 603) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__315 : Bool)
      then
        (do
          writeReg SEE 603
          let Rt := (BitVec.slice __opcode 0 5)
          let Rn := (BitVec.slice __opcode 5 5)
          let Rt2 := (BitVec.slice __opcode 10 5)
          let imm7 := (BitVec.slice __opcode 15 7)
          let L := (BitVec.slice __opcode 22 1)
          let opc := (BitVec.slice __opcode 30 2)
          (decode_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_post_idx Rt Rn Rt2 imm7 L opc)
          (pure false))
      else
        (do
          let w__317 ← (( do
            if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 29 22)) == (0xB7#8 : (BitVec 8))) : Bool) : Bool)
            then
              (do
                let w__316 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__316 <b 604) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__317 : Bool)
          then
            (do
              writeReg SEE 604
              let Rt := (BitVec.slice __opcode 0 5)
              let Rn := (BitVec.slice __opcode 5 5)
              let Rt2 := (BitVec.slice __opcode 10 5)
              let imm7 := (BitVec.slice __opcode 15 7)
              let L := (BitVec.slice __opcode 22 1)
              let opc := (BitVec.slice __opcode 30 2)
              (decode_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_pre_idx Rt Rn Rt2 imm7 L opc)
              (pure false))
          else
            (do
              let w__319 ← (( do
                if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 29 22)) == (0xB5#8 : (BitVec 8))) : Bool) : Bool)
                then
                  (do
                    let w__318 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__318 <b 605) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__319 : Bool)
              then
                (do
                  writeReg SEE 605
                  let Rt := (BitVec.slice __opcode 0 5)
                  let Rn := (BitVec.slice __opcode 5 5)
                  let Rt2 := (BitVec.slice __opcode 10 5)
                  let imm7 := (BitVec.slice __opcode 15 7)
                  let L := (BitVec.slice __opcode 22 1)
                  let opc := (BitVec.slice __opcode 30 2)
                  (decode_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_offset Rt Rn Rt2 imm7 L opc)
                  (pure false))
              else
                (do
                  let w__321 ← (( do
                    if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 29 22)) == (0xB2#8 : (BitVec 8))) : Bool) : Bool)
                    then
                      (do
                        let w__320 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__320 <b 606) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__321 : Bool)
                  then
                    (do
                      writeReg SEE 606
                      let Rt := (BitVec.slice __opcode 0 5)
                      let Rn := (BitVec.slice __opcode 5 5)
                      let Rt2 := (BitVec.slice __opcode 10 5)
                      let imm7 := (BitVec.slice __opcode 15 7)
                      let L := (BitVec.slice __opcode 22 1)
                      let opc := (BitVec.slice __opcode 30 2)
                      (decode_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_post_idx Rt Rn Rt2 imm7 L
                        opc)
                      (pure false))
                  else
                    (do
                      let w__323 ← (( do
                        if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 29 22)) == (0xB6#8 : (BitVec 8))) : Bool) : Bool)
                        then
                          (do
                            let w__322 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__322 <b 607) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__323 : Bool)
                      then
                        (do
                          writeReg SEE 607
                          let Rt := (BitVec.slice __opcode 0 5)
                          let Rn := (BitVec.slice __opcode 5 5)
                          let Rt2 := (BitVec.slice __opcode 10 5)
                          let imm7 := (BitVec.slice __opcode 15 7)
                          let L := (BitVec.slice __opcode 22 1)
                          let opc := (BitVec.slice __opcode 30 2)
                          (decode_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_pre_idx Rt Rn Rt2
                            imm7 L opc)
                          (pure false))
                      else
                        (do
                          let w__325 ← (( do
                            if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode
                                   29 22)) == (0xB4#8 : (BitVec 8))) : Bool) : Bool)
                            then
                              (do
                                let w__324 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__324 <b 608) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__325 : Bool)
                          then
                            (do
                              writeReg SEE 608
                              let Rt := (BitVec.slice __opcode 0 5)
                              let Rn := (BitVec.slice __opcode 5 5)
                              let Rt2 := (BitVec.slice __opcode 10 5)
                              let imm7 := (BitVec.slice __opcode 15 7)
                              let L := (BitVec.slice __opcode 22 1)
                              let opc := (BitVec.slice __opcode 30 2)
                              (decode_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_offset Rt Rn Rt2
                                imm7 L opc)
                              (pure false))
                          else
                            (do
                              let w__327 ← (( do
                                if ((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                       __opcode 30 22)) == (0b010100011#9 : (BitVec 9))) : Bool) : Bool)
                                then
                                  (do
                                    let w__326 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__326 <b 609) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__327 : Bool)
                              then
                                (do
                                  writeReg SEE 609
                                  let Rt := (BitVec.slice __opcode 0 5)
                                  let Rn := (BitVec.slice __opcode 5 5)
                                  let Rt2 := (BitVec.slice __opcode 10 5)
                                  let imm7 := (BitVec.slice __opcode 15 7)
                                  let L := (BitVec.slice __opcode 22 1)
                                  let opc := (BitVec.slice __opcode 30 2)
                                  (decode_ldp_gen_aarch64_instrs_memory_pair_general_post_idx Rt Rn
                                    Rt2 imm7 L opc)
                                  (pure false))
                              else
                                (do
                                  let w__329 ← (( do
                                    if ((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                           __opcode 30 22)) == (0b010100111#9 : (BitVec 9))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__328 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__328 <b 610) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__329 : Bool)
                                  then
                                    (do
                                      writeReg SEE 610
                                      let Rt := (BitVec.slice __opcode 0 5)
                                      let Rn := (BitVec.slice __opcode 5 5)
                                      let Rt2 := (BitVec.slice __opcode 10 5)
                                      let imm7 := (BitVec.slice __opcode 15 7)
                                      let L := (BitVec.slice __opcode 22 1)
                                      let opc := (BitVec.slice __opcode 30 2)
                                      (decode_ldp_gen_aarch64_instrs_memory_pair_general_pre_idx Rt
                                        Rn Rt2 imm7 L opc)
                                      (pure false))
                                  else
                                    (do
                                      let w__331 ← (( do
                                        if ((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                               __opcode 30 22)) == (0b010100101#9 : (BitVec 9))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__330 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__330 <b 611) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__331 : Bool)
                                      then
                                        (do
                                          writeReg SEE 611
                                          let Rt := (BitVec.slice __opcode 0 5)
                                          let Rn := (BitVec.slice __opcode 5 5)
                                          let Rt2 := (BitVec.slice __opcode 10 5)
                                          let imm7 := (BitVec.slice __opcode 15 7)
                                          let L := (BitVec.slice __opcode 22 1)
                                          let opc := (BitVec.slice __opcode 30 2)
                                          (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset
                                            Rt Rn Rt2 imm7 L opc)
                                          (pure false))
                                      else
                                        (do
                                          let w__333 ← (( do
                                            if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                   __opcode 31 22)) == (0b0110100011#10 : (BitVec 10))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__332 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__332 <b 612) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__333 : Bool)
                                          then
                                            (do
                                              writeReg SEE 612
                                              let Rt := (BitVec.slice __opcode 0 5)
                                              let Rn := (BitVec.slice __opcode 5 5)
                                              let Rt2 := (BitVec.slice __opcode 10 5)
                                              let imm7 := (BitVec.slice __opcode 15 7)
                                              let L := (BitVec.slice __opcode 22 1)
                                              let opc := (BitVec.slice __opcode 30 2)
                                              (decode_ldpsw_aarch64_instrs_memory_pair_general_post_idx
                                                Rt Rn Rt2 imm7 L opc)
                                              (pure false))
                                          else
                                            (do
                                              let w__335 ← (( do
                                                if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                       __opcode 31 22)) == (0b0110100111#10 : (BitVec 10))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__334 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__334 <b 613) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__335 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 613
                                                  let Rt := (BitVec.slice __opcode 0 5)
                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                  let Rt2 := (BitVec.slice __opcode 10 5)
                                                  let imm7 := (BitVec.slice __opcode 15 7)
                                                  let L := (BitVec.slice __opcode 22 1)
                                                  let opc := (BitVec.slice __opcode 30 2)
                                                  (decode_ldpsw_aarch64_instrs_memory_pair_general_pre_idx
                                                    Rt Rn Rt2 imm7 L opc)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__337 ← (( do
                                                    if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                           __opcode 31 22)) == (0b0110100101#10 : (BitVec 10))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__336 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__336 <b 614) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__337 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 614
                                                      let Rt := (BitVec.slice __opcode 0 5)
                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                      let Rt2 := (BitVec.slice __opcode 10 5)
                                                      let imm7 := (BitVec.slice __opcode 15 7)
                                                      let L := (BitVec.slice __opcode 22 1)
                                                      let opc := (BitVec.slice __opcode 30 2)
                                                      (decode_ldpsw_aarch64_instrs_memory_pair_general_offset
                                                        Rt Rn Rt2 imm7 L opc)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__339 ← (( do
                                                        if ((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                               __opcode 30 22)) == (0b010100010#9 : (BitVec 9))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__338 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__338 <b 615) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__339 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 615
                                                          let Rt := (BitVec.slice __opcode 0 5)
                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                          let Rt2 := (BitVec.slice __opcode 10 5)
                                                          let imm7 := (BitVec.slice __opcode 15 7)
                                                          let L := (BitVec.slice __opcode 22 1)
                                                          let opc := (BitVec.slice __opcode 30 2)
                                                          (decode_stp_gen_aarch64_instrs_memory_pair_general_post_idx
                                                            Rt Rn Rt2 imm7 L opc)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__341 ← (( do
                                                            if ((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                   __opcode 30 22)) == (0b010100110#9 : (BitVec 9))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__340 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__340 <b 616) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__341 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 616
                                                              let Rt := (BitVec.slice __opcode 0 5)
                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                              let Rt2 :=
                                                                (BitVec.slice __opcode 10 5)
                                                              let imm7 :=
                                                                (BitVec.slice __opcode 15 7)
                                                              let L := (BitVec.slice __opcode 22 1)
                                                              let opc :=
                                                                (BitVec.slice __opcode 30 2)
                                                              (decode_stp_gen_aarch64_instrs_memory_pair_general_pre_idx
                                                                Rt Rn Rt2 imm7 L opc)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__343 ← (( do
                                                                if ((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                       __opcode 30 22)) == (0b010100100#9 : (BitVec 9))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__342 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__342 <b 617) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__343 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 617
                                                                  let Rt :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let Rt2 :=
                                                                    (BitVec.slice __opcode 10 5)
                                                                  let imm7 :=
                                                                    (BitVec.slice __opcode 15 7)
                                                                  let L :=
                                                                    (BitVec.slice __opcode 22 1)
                                                                  let opc :=
                                                                    (BitVec.slice __opcode 30 2)
                                                                  (decode_stp_gen_aarch64_instrs_memory_pair_general_offset
                                                                    Rt Rn Rt2 imm7 L opc)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__345 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                             __opcode 29 24)) == (0b111100#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                               __opcode 22 21)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                               __opcode 11 10)) == (0b01#2 : (BitVec 2))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__344 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__344 <b 618) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__345 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 618
                                                                      let Rt :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let imm9 :=
                                                                        (BitVec.slice __opcode 12 9)
                                                                      let opc :=
                                                                        (BitVec.slice __opcode 22 2)
                                                                      let size :=
                                                                        (BitVec.slice __opcode 30 2)
                                                                      (decode_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx
                                                                        Rt Rn imm9 opc size)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__347 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                 __opcode 29 24)) == (0b111100#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                   __opcode 22 21)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                   __opcode 11 10)) == (0b11#2 : (BitVec 2))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__346 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__346 <b 619) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__347 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 619
                                                                          let Rt :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let imm9 :=
                                                                            (BitVec.slice __opcode
                                                                              12 9)
                                                                          let opc :=
                                                                            (BitVec.slice __opcode
                                                                              22 2)
                                                                          let size :=
                                                                            (BitVec.slice __opcode
                                                                              30 2)
                                                                          (decode_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_pre_idx
                                                                            Rt Rn imm9 opc size)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__349 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                     __opcode 29 24)) == (0b111101#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                     __opcode 22 22)) == (1#1 : (BitVec 1)))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__348 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__348 <b 620) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__349 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 620
                                                                              let Rt :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let imm12 :=
                                                                                (BitVec.slice
                                                                                  __opcode 10 12)
                                                                              let opc :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 2)
                                                                              let size :=
                                                                                (BitVec.slice
                                                                                  __opcode 30 2)
                                                                              (decode_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_unsigned
                                                                                Rt Rn imm12 opc size)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__351 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                         __opcode 29
                                                                                         24)) == (0b111100#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           22 21)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           11 10)) == (0b01#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__350 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__350 <b 621) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__351 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 621
                                                                                  let Rt :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let imm9 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 12 9)
                                                                                  let opc :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 2)
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 30 2)
                                                                                  (decode_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx
                                                                                    Rt Rn imm9 opc
                                                                                    size)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__353 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             29 24)) == (0b111100#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               22 21)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               11 10)) == (0b11#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__352 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__352 <b 622) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__353 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 622
                                                                                      let Rt :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          5)
                                                                                      let Rn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
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
                                                                                      (decode_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_pre_idx
                                                                                        Rt Rn imm9
                                                                                        opc size)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__355 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 29
                                                                                                 24)) == (0b111101#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 22
                                                                                                 22)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__354 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__354 <b 623) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__355 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 623
                                                                                          let Rt :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 5)
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let imm12 :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              10 12)
                                                                                          let opc :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 2)
                                                                                          let size :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              30 2)
                                                                                          (decode_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_unsigned
                                                                                            Rt Rn
                                                                                            imm12
                                                                                            opc size)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__357 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     29
                                                                                                     24)) == (0b011000#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__356 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__356 <b 624) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__357 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 624
                                                                                              let Rt :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  5)
                                                                                              let imm19 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  5
                                                                                                  19)
                                                                                              let opc :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  30
                                                                                                  2)
                                                                                              (decode_ldr_lit_gen_aarch64_instrs_memory_literal_general
                                                                                                Rt
                                                                                                imm19
                                                                                                opc)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__359 ← (( do
                                                                                                if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       31
                                                                                                       24)) == (0x98#8 : (BitVec 8))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__358 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__358 <b 625) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__359 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 625
                                                                                                  let Rt :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      5)
                                                                                                  let imm19 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      5
                                                                                                      19)
                                                                                                  let opc :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      30
                                                                                                      2)
                                                                                                  (decode_ldrsw_lit_aarch64_instrs_memory_literal_general
                                                                                                    Rt
                                                                                                    imm19
                                                                                                    opc)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__361 ← (( do
                                                                                                    if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           31
                                                                                                           24)) == (0xD8#8 : (BitVec 8))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__360 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__360 <b 626) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__361 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 626
                                                                                                      let Rt :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          5)
                                                                                                      let imm19 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          5
                                                                                                          19)
                                                                                                      let opc :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          30
                                                                                                          2)
                                                                                                      (decode_prfm_lit_aarch64_instrs_memory_literal_general
                                                                                                        Rt
                                                                                                        imm19
                                                                                                        opc)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__363 ← (( do
                                                                                                        if ((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               29
                                                                                                               24)) == (0b011100#6 : (BitVec 6))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__362 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__362 <b 627) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__363 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 627
                                                                                                          let Rt :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              5)
                                                                                                          let imm19 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              5
                                                                                                              19)
                                                                                                          let opc :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              30
                                                                                                              2)
                                                                                                          (decode_ldr_lit_fpsimd_aarch64_instrs_memory_literal_simdfp
                                                                                                            Rt
                                                                                                            imm19
                                                                                                            opc)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__365 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     31)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       29
                                                                                                                       21)) == (0b111000010#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       11
                                                                                                                       10)) == (0b01#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__364 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__364 <b 628) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__365 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 628
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
                                                                                                              (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx
                                                                                                                Rt
                                                                                                                Rn
                                                                                                                imm9
                                                                                                                opc
                                                                                                                size)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__367 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         31)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           29
                                                                                                                           21)) == (0b111000010#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           11
                                                                                                                           10)) == (0b11#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__366 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__366 <b 629) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__367 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 629
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
                                                                                                                  (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx
                                                                                                                    Rt
                                                                                                                    Rn
                                                                                                                    imm9
                                                                                                                    opc
                                                                                                                    size)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__369 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             31)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             29
                                                                                                                             22)) == (0xE5#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__368 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__368 <b 630) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__369 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 630
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
                                                                                                                      let imm12 :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          10
                                                                                                                          12)
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
                                                                                                                      (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned
                                                                                                                        Rt
                                                                                                                        Rn
                                                                                                                        imm12
                                                                                                                        opc
                                                                                                                        size)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__371 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 21)) == (0b00111000010#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 11
                                                                                                                                 10)) == (0b01#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__370 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__370 <b 631) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__371 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 631
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
                                                                                                                          (decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx
                                                                                                                            Rt
                                                                                                                            Rn
                                                                                                                            imm9
                                                                                                                            opc
                                                                                                                            size)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__373 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     21)) == (0b00111000010#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     11
                                                                                                                                     10)) == (0b11#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__372 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__372 <b 632) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__373 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 632
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
                                                                                                                              (decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx
                                                                                                                                Rt
                                                                                                                                Rn
                                                                                                                                imm9
                                                                                                                                opc
                                                                                                                                size)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__375 ← (( do
                                                                                                                                if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       31
                                                                                                                                       22)) == (0b0011100101#10 : (BitVec 10))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__374 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__374 <b 633) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__375 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 633
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
                                                                                                                                  let imm12 :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      10
                                                                                                                                      12)
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
                                                                                                                                  (decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_unsigned
                                                                                                                                    Rt
                                                                                                                                    Rn
                                                                                                                                    imm12
                                                                                                                                    opc
                                                                                                                                    size)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__377 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             21)) == (0b01111000010#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             11
                                                                                                                                             10)) == (0b01#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__376 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__376 <b 634) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__377 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 634
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
                                                                                                                                      (decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx
                                                                                                                                        Rt
                                                                                                                                        Rn
                                                                                                                                        imm9
                                                                                                                                        opc
                                                                                                                                        size)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__379 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 21)) == (0b01111000010#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 11
                                                                                                                                                 10)) == (0b11#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__378 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__378 <b 635) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__379 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 635
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
                                                                                                                                          (decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx
                                                                                                                                            Rt
                                                                                                                                            Rn
                                                                                                                                            imm9
                                                                                                                                            opc
                                                                                                                                            size)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__381 ← (( do
                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   31
                                                                                                                                                   22)) == (0b0111100101#10 : (BitVec 10))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__380 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__380 <b 636) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__381 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 636
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
                                                                                                                                              let imm12 :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  10
                                                                                                                                                  12)
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
                                                                                                                                              (decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_unsigned
                                                                                                                                                Rt
                                                                                                                                                Rn
                                                                                                                                                imm12
                                                                                                                                                opc
                                                                                                                                                size)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__383 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         31
                                                                                                                                                         23)) == (0b001110001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           21
                                                                                                                                                           21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           11
                                                                                                                                                           10)) == (0b01#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__382 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__382 <b 637) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__383 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 637
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
                                                                                                                                                  (decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx
                                                                                                                                                    Rt
                                                                                                                                                    Rn
                                                                                                                                                    imm9
                                                                                                                                                    opc
                                                                                                                                                    size)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__385 ← (( do
                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             31
                                                                                                                                                             23)) == (0b001110001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                               __opcode
                                                                                                                                                               21
                                                                                                                                                               21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                               __opcode
                                                                                                                                                               11
                                                                                                                                                               10)) == (0b11#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__384 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__384 <b 638) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__385 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 638
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
                                                                                                                                                      (decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx
                                                                                                                                                        Rt
                                                                                                                                                        Rn
                                                                                                                                                        imm9
                                                                                                                                                        opc
                                                                                                                                                        size)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__387 ← (( do
                                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                               __opcode
                                                                                                                                                               31
                                                                                                                                                               23)) == (0b001110011#9 : (BitVec 9))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__386 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__386 <b 639) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false)
                                                                                                                                                        )
                                                                                                                                                        :
                                                                                                                                                        SailM
                                                                                                                                                        Bool
                                                                                                                                                        )
                                                                                                                                                      if (w__387 : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 639
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
                                                                                                                                                          let imm12 :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              10
                                                                                                                                                              12)
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
                                                                                                                                                          (decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_unsigned
                                                                                                                                                            Rt
                                                                                                                                                            Rn
                                                                                                                                                            imm12
                                                                                                                                                            opc
                                                                                                                                                            size)
                                                                                                                                                          (pure false))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          let w__389 ← (( do
                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     31
                                                                                                                                                                     23)) == (0b011110001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                       __opcode
                                                                                                                                                                       21
                                                                                                                                                                       21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                       __opcode
                                                                                                                                                                       11
                                                                                                                                                                       10)) == (0b01#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let w__388 ← (( do
                                                                                                                                                                  readReg SEE
                                                                                                                                                                  )
                                                                                                                                                                  :
                                                                                                                                                                  SailM
                                                                                                                                                                  Int
                                                                                                                                                                  )
                                                                                                                                                                (pure (((w__388 <b 640) : Bool))))
                                                                                                                                                            else
                                                                                                                                                              (pure false)
                                                                                                                                                            )
                                                                                                                                                            :
                                                                                                                                                            SailM
                                                                                                                                                            Bool
                                                                                                                                                            )
                                                                                                                                                          if (w__389 : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 640
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
                                                                                                                                                              (decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx
                                                                                                                                                                Rt
                                                                                                                                                                Rn
                                                                                                                                                                imm9
                                                                                                                                                                opc
                                                                                                                                                                size)
                                                                                                                                                              (pure false))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              let w__391 ← (( do
                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         31
                                                                                                                                                                         23)) == (0b011110001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           21
                                                                                                                                                                           21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           11
                                                                                                                                                                           10)) == (0b11#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    let w__390 ← (( do
                                                                                                                                                                      readReg SEE
                                                                                                                                                                      )
                                                                                                                                                                      :
                                                                                                                                                                      SailM
                                                                                                                                                                      Int
                                                                                                                                                                      )
                                                                                                                                                                    (pure (((w__390 <b 641) : Bool))))
                                                                                                                                                                else
                                                                                                                                                                  (pure false)
                                                                                                                                                                )
                                                                                                                                                                :
                                                                                                                                                                SailM
                                                                                                                                                                Bool
                                                                                                                                                                )
                                                                                                                                                              if (w__391 : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 641
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
                                                                                                                                                                  (decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx
                                                                                                                                                                    Rt
                                                                                                                                                                    Rn
                                                                                                                                                                    imm9
                                                                                                                                                                    opc
                                                                                                                                                                    size)
                                                                                                                                                                  (pure false))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  let w__393 ← (( do
                                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           31
                                                                                                                                                                           23)) == (0b011110011#9 : (BitVec 9))) : Bool) : Bool)
                                                                                                                                                                    then
                                                                                                                                                                      (do
                                                                                                                                                                        let w__392 ← (( do
                                                                                                                                                                          readReg SEE
                                                                                                                                                                          )
                                                                                                                                                                          :
                                                                                                                                                                          SailM
                                                                                                                                                                          Int
                                                                                                                                                                          )
                                                                                                                                                                        (pure (((w__392 <b 642) : Bool))))
                                                                                                                                                                    else
                                                                                                                                                                      (pure false)
                                                                                                                                                                    )
                                                                                                                                                                    :
                                                                                                                                                                    SailM
                                                                                                                                                                    Bool
                                                                                                                                                                    )
                                                                                                                                                                  if (w__393 : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      writeReg SEE 642
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
                                                                                                                                                                      let imm12 :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          10
                                                                                                                                                                          12)
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
                                                                                                                                                                      (decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_unsigned
                                                                                                                                                                        Rt
                                                                                                                                                                        Rn
                                                                                                                                                                        imm12
                                                                                                                                                                        opc
                                                                                                                                                                        size)
                                                                                                                                                                      (pure false))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      let w__395 ← (( do
                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 31
                                                                                                                                                                                 21)) == (0b10111000100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 11
                                                                                                                                                                                 10)) == (0b01#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                                                                                                        then
                                                                                                                                                                          (do
                                                                                                                                                                            let w__394 ← (( do
                                                                                                                                                                              readReg SEE
                                                                                                                                                                              )
                                                                                                                                                                              :
                                                                                                                                                                              SailM
                                                                                                                                                                              Int
                                                                                                                                                                              )
                                                                                                                                                                            (pure (((w__394 <b 643) : Bool))))
                                                                                                                                                                        else
                                                                                                                                                                          (pure false)
                                                                                                                                                                        )
                                                                                                                                                                        :
                                                                                                                                                                        SailM
                                                                                                                                                                        Bool
                                                                                                                                                                        )
                                                                                                                                                                      if (w__395 : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (do
                                                                                                                                                                          writeReg SEE 643
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
                                                                                                                                                                          (decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx
                                                                                                                                                                            Rt
                                                                                                                                                                            Rn
                                                                                                                                                                            imm9
                                                                                                                                                                            opc
                                                                                                                                                                            size)
                                                                                                                                                                          (pure false))
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          let w__397 ← (( do
                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                                     __opcode
                                                                                                                                                                                     31
                                                                                                                                                                                     21)) == (0b10111000100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                     __opcode
                                                                                                                                                                                     11
                                                                                                                                                                                     10)) == (0b11#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                                                                                                            then
                                                                                                                                                                              (do
                                                                                                                                                                                let w__396 ← (( do
                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                  )
                                                                                                                                                                                  :
                                                                                                                                                                                  SailM
                                                                                                                                                                                  Int
                                                                                                                                                                                  )
                                                                                                                                                                                (pure (((w__396 <b 644) : Bool))))
                                                                                                                                                                            else
                                                                                                                                                                              (pure false)
                                                                                                                                                                            )
                                                                                                                                                                            :
                                                                                                                                                                            SailM
                                                                                                                                                                            Bool
                                                                                                                                                                            )
                                                                                                                                                                          if (w__397 : Bool)
                                                                                                                                                                          then
                                                                                                                                                                            (do
                                                                                                                                                                              writeReg SEE 644
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
                                                                                                                                                                              (decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx
                                                                                                                                                                                Rt
                                                                                                                                                                                Rn
                                                                                                                                                                                imm9
                                                                                                                                                                                opc
                                                                                                                                                                                size)
                                                                                                                                                                              (pure false))
                                                                                                                                                                          else
                                                                                                                                                                            (do
                                                                                                                                                                              let w__399 ← (( do
                                                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                                       __opcode
                                                                                                                                                                                       31
                                                                                                                                                                                       22)) == (0b1011100110#10 : (BitVec 10))) : Bool) : Bool)
                                                                                                                                                                                then
                                                                                                                                                                                  (do
                                                                                                                                                                                    let w__398 ← (( do
                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                      )
                                                                                                                                                                                      :
                                                                                                                                                                                      SailM
                                                                                                                                                                                      Int
                                                                                                                                                                                      )
                                                                                                                                                                                    (pure (((w__398 <b 645) : Bool))))
                                                                                                                                                                                else
                                                                                                                                                                                  (pure false)
                                                                                                                                                                                )
                                                                                                                                                                                :
                                                                                                                                                                                SailM
                                                                                                                                                                                Bool
                                                                                                                                                                                )
                                                                                                                                                                              if (w__399 : Bool)
                                                                                                                                                                              then
                                                                                                                                                                                (do
                                                                                                                                                                                  writeReg SEE 645
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
                                                                                                                                                                                  let imm12 :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      10
                                                                                                                                                                                      12)
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
                                                                                                                                                                                  (decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_unsigned
                                                                                                                                                                                    Rt
                                                                                                                                                                                    Rn
                                                                                                                                                                                    imm12
                                                                                                                                                                                    opc
                                                                                                                                                                                    size)
                                                                                                                                                                                  (pure false))
                                                                                                                                                                              else
                                                                                                                                                                                (do
                                                                                                                                                                                  let w__401 ← (( do
                                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                             __opcode
                                                                                                                                                                                             31
                                                                                                                                                                                             31)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                                               __opcode
                                                                                                                                                                                               29
                                                                                                                                                                                               21)) == (0b111000000#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                               __opcode
                                                                                                                                                                                               11
                                                                                                                                                                                               10)) == (0b01#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                                                                                    then
                                                                                                                                                                                      (do
                                                                                                                                                                                        let w__400 ← (( do
                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                          )
                                                                                                                                                                                          :
                                                                                                                                                                                          SailM
                                                                                                                                                                                          Int
                                                                                                                                                                                          )
                                                                                                                                                                                        (pure (((w__400 <b 646) : Bool))))
                                                                                                                                                                                    else
                                                                                                                                                                                      (pure false)
                                                                                                                                                                                    )
                                                                                                                                                                                    :
                                                                                                                                                                                    SailM
                                                                                                                                                                                    Bool
                                                                                                                                                                                    )
                                                                                                                                                                                  if (w__401 : Bool)
                                                                                                                                                                                  then
                                                                                                                                                                                    (do
                                                                                                                                                                                      writeReg SEE 646
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
                                                                                                                                                                                      (decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx
                                                                                                                                                                                        Rt
                                                                                                                                                                                        Rn
                                                                                                                                                                                        imm9
                                                                                                                                                                                        opc
                                                                                                                                                                                        size)
                                                                                                                                                                                      (pure false))
                                                                                                                                                                                  else
                                                                                                                                                                                    (do
                                                                                                                                                                                      let w__403 ← (( do
                                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                 31
                                                                                                                                                                                                 31)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                   29
                                                                                                                                                                                                   21)) == (0b111000000#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                   11
                                                                                                                                                                                                   10)) == (0b11#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                                                                                        then
                                                                                                                                                                                          (do
                                                                                                                                                                                            let w__402 ← (( do
                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                              )
                                                                                                                                                                                              :
                                                                                                                                                                                              SailM
                                                                                                                                                                                              Int
                                                                                                                                                                                              )
                                                                                                                                                                                            (pure (((w__402 <b 647) : Bool))))
                                                                                                                                                                                        else
                                                                                                                                                                                          (pure false)
                                                                                                                                                                                        )
                                                                                                                                                                                        :
                                                                                                                                                                                        SailM
                                                                                                                                                                                        Bool
                                                                                                                                                                                        )
                                                                                                                                                                                      if (w__403 : Bool)
                                                                                                                                                                                      then
                                                                                                                                                                                        (do
                                                                                                                                                                                          writeReg SEE 647
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
                                                                                                                                                                                          (decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx
                                                                                                                                                                                            Rt
                                                                                                                                                                                            Rn
                                                                                                                                                                                            imm9
                                                                                                                                                                                            opc
                                                                                                                                                                                            size)
                                                                                                                                                                                          (pure false))
                                                                                                                                                                                      else
                                                                                                                                                                                        (pure true))))))))))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
