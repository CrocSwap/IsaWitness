import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0151
import ArmFull.Fn.M0164
import ArmFull.Fn.M0214
import ArmFull.Fn.M1059
import ArmFull.Fn.M1075
import ArmFull.Fn.M1076
import ArmFull.Fn.M1094
import ArmFull.Fn.M1095
import ArmFull.Fn.M1147
import ArmFull.Fn.M1148

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
def __DecodeA32_Unconditional__seg6 (pc : Int) (__opcode : (BitVec 32)) : SailM Unit := do
  let w__357 ← (( do
    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111100100#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
               __opcode 11 8)) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
               __opcode 4 4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
    then
      (do
        let w__356 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__356 <b 3754) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__357 : Bool)
  then
    (do
      writeReg SEE 3754
      let D := (BitVec.slice __opcode 22 1)
      let size := (BitVec.slice __opcode 20 2)
      let Vn := (BitVec.slice __opcode 16 4)
      let Vd := (BitVec.slice __opcode 12 4)
      let N := (BitVec.slice __opcode 7 1)
      let Q := (BitVec.slice __opcode 6 1)
      let M := (BitVec.slice __opcode 5 1)
      let Vm := (BitVec.slice __opcode 0 4)
      (decode_aarch32_instrs_VTST_A1enc_A_txt D size Vn Vd N Q M Vm))
  else
    (do
      let w__359 ← (( do
        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                   __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                     __opcode 17 16)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                       __opcode 11 7)) == (0b00010#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
        then
          (do
            let w__358 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__358 <b 3756) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__359 : Bool)
      then
        (do
          writeReg SEE 3756
          let D := (BitVec.slice __opcode 22 1)
          let size := (BitVec.slice __opcode 18 2)
          let Vd := (BitVec.slice __opcode 12 4)
          let Q := (BitVec.slice __opcode 6 1)
          let M := (BitVec.slice __opcode 5 1)
          let Vm := (BitVec.slice __opcode 0 4)
          (decode_aarch32_instrs_VUZP_A1enc_A_txt D size Vd Q M Vm))
      else
        (do
          let w__361 ← (( do
            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                       __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                         __opcode 17 16)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                           __opcode 11 7)) == (0b00011#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
            then
              (do
                let w__360 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__360 <b 3758) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__361 : Bool)
          then
            (do
              writeReg SEE 3758
              let D := (BitVec.slice __opcode 22 1)
              let size := (BitVec.slice __opcode 18 2)
              let Vd := (BitVec.slice __opcode 12 4)
              let Q := (BitVec.slice __opcode 6 1)
              let M := (BitVec.slice __opcode 5 1)
              let Vm := (BitVec.slice __opcode 0 4)
              (decode_aarch32_instrs_VZIP_A1enc_A_txt D size Vd Q M Vm))
          else
            (do
              let w__363 ← (( do
                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xF10#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                           __opcode 16 9)) == (0x00#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           __opcode 5 5)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                then
                  (do
                    let w__362 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__362 <b 3769) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__363 : Bool)
              then
                (do
                  writeReg SEE 3769
                  let imod := (BitVec.slice __opcode 18 2)
                  let M := (BitVec.slice __opcode 17 1)
                  let A := (BitVec.slice __opcode 8 1)
                  let I := (BitVec.slice __opcode 7 1)
                  let F := (BitVec.slice __opcode 6 1)
                  let mode := (BitVec.slice __opcode 0 5)
                  if (((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 9)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                       __opcode 10)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                     __opcode 11)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                   __opcode 12)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                 __opcode 13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                               __opcode 14)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                             __opcode 15)])) != 0#1)) : Bool)
                  then sailThrow ((Error_ConstrainedUnpredictable ()))
                  else
                    (do
                      (decode_aarch32_instrs_CPS_A1enc_AS_txt imod M A I F mode)))
              else
                (do
                  let w__365 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                               __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                 __opcode 17 16)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                   __opcode 11 6)) == (0b001101#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                   __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                    then
                      (do
                        let w__364 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__364 <b 3800) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__365 : Bool)
                  then
                    (do
                      writeReg SEE 3800
                      let D := (BitVec.slice __opcode 22 1)
                      let size := (BitVec.slice __opcode 18 2)
                      let Vd := (BitVec.slice __opcode 12 4)
                      let M := (BitVec.slice __opcode 5 1)
                      let Vm := (BitVec.slice __opcode 0 4)
                      (decode_aarch32_instrs_AESD_A1enc_A_txt D size Vd M Vm))
                  else
                    (do
                      let w__367 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31
                                 23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                   __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                     __opcode 17 16)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                       __opcode 11 6)) == (0b001100#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                       __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                        then
                          (do
                            let w__366 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__366 <b 3802) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__367 : Bool)
                      then
                        (do
                          writeReg SEE 3802
                          let D := (BitVec.slice __opcode 22 1)
                          let size := (BitVec.slice __opcode 18 2)
                          let Vd := (BitVec.slice __opcode 12 4)
                          let M := (BitVec.slice __opcode 5 1)
                          let Vm := (BitVec.slice __opcode 0 4)
                          (decode_aarch32_instrs_AESE_A1enc_A_txt D size Vd M Vm))
                      else
                        (do
                          let w__369 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode
                                     31 23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                       __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                         __opcode 17 16)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                           __opcode 11 6)) == (0b001111#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                           __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                            then
                              (do
                                let w__368 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__368 <b 3804) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__369 : Bool)
                          then
                            (do
                              writeReg SEE 3804
                              let D := (BitVec.slice __opcode 22 1)
                              let size := (BitVec.slice __opcode 18 2)
                              let Vd := (BitVec.slice __opcode 12 4)
                              let M := (BitVec.slice __opcode 5 1)
                              let Vm := (BitVec.slice __opcode 0 4)
                              (decode_aarch32_instrs_AESIMC_A1enc_A_txt D size Vd M Vm))
                          else
                            (do
                              let w__371 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                         __opcode 31 23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                           __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                             __opcode 17 16)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                               __opcode 11 6)) == (0b001110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                               __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__370 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__370 <b 3806) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__371 : Bool)
                              then
                                (do
                                  writeReg SEE 3806
                                  let D := (BitVec.slice __opcode 22 1)
                                  let size := (BitVec.slice __opcode 18 2)
                                  let Vd := (BitVec.slice __opcode 12 4)
                                  let M := (BitVec.slice __opcode 5 1)
                                  let Vm := (BitVec.slice __opcode 0 4)
                                  (decode_aarch32_instrs_AESMC_A1enc_A_txt D size Vd M Vm))
                              else
                                (do
                                  let w__373 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                             __opcode 31 23)) == (0b111100100#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                               __opcode 21 20)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                 __opcode 11 8)) == (0xC#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__372 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__372 <b 3832) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__373 : Bool)
                                  then
                                    (do
                                      writeReg SEE 3832
                                      let D := (BitVec.slice __opcode 22 1)
                                      let Vn := (BitVec.slice __opcode 16 4)
                                      let Vd := (BitVec.slice __opcode 12 4)
                                      let N := (BitVec.slice __opcode 7 1)
                                      let Q := (BitVec.slice __opcode 6 1)
                                      let M := (BitVec.slice __opcode 5 1)
                                      let Vm := (BitVec.slice __opcode 0 4)
                                      (decode_aarch32_instrs_SHA1C_A1enc_A_txt D Vn Vd N Q M Vm))
                                  else
                                    (do
                                      let w__375 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                 __opcode 31 23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                   __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                     __opcode 17 16)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                       __opcode 11 6)) == (0b001011#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__374 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__374 <b 3834) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__375 : Bool)
                                      then
                                        (do
                                          writeReg SEE 3834
                                          let D := (BitVec.slice __opcode 22 1)
                                          let size := (BitVec.slice __opcode 18 2)
                                          let Vd := (BitVec.slice __opcode 12 4)
                                          let M := (BitVec.slice __opcode 5 1)
                                          let Vm := (BitVec.slice __opcode 0 4)
                                          (decode_aarch32_instrs_SHA1H_A1enc_A_txt D size Vd M Vm))
                                      else
                                        (do
                                          let w__377 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                     __opcode 31 23)) == (0b111100100#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                       __opcode 21 20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                         __opcode 11 8)) == (0xC#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                         __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__376 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__376 <b 3836) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__377 : Bool)
                                          then
                                            (do
                                              writeReg SEE 3836
                                              let D := (BitVec.slice __opcode 22 1)
                                              let Vn := (BitVec.slice __opcode 16 4)
                                              let Vd := (BitVec.slice __opcode 12 4)
                                              let N := (BitVec.slice __opcode 7 1)
                                              let Q := (BitVec.slice __opcode 6 1)
                                              let M := (BitVec.slice __opcode 5 1)
                                              let Vm := (BitVec.slice __opcode 0 4)
                                              (decode_aarch32_instrs_SHA1M_A1enc_A_txt D Vn Vd N Q M
                                                Vm))
                                          else
                                            (do
                                              let w__379 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                         __opcode 31 23)) == (0b111100100#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                           __opcode 21 20)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                             __opcode 11 8)) == (0xC#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                             __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__378 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__378 <b 3838) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__379 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 3838
                                                  let D := (BitVec.slice __opcode 22 1)
                                                  let Vn := (BitVec.slice __opcode 16 4)
                                                  let Vd := (BitVec.slice __opcode 12 4)
                                                  let N := (BitVec.slice __opcode 7 1)
                                                  let Q := (BitVec.slice __opcode 6 1)
                                                  let M := (BitVec.slice __opcode 5 1)
                                                  let Vm := (BitVec.slice __opcode 0 4)
                                                  (decode_aarch32_instrs_SHA1P_A1enc_A_txt D Vn Vd N
                                                    Q M Vm))
                                              else
                                                (do
                                                  let w__381 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                             __opcode 31 23)) == (0b111100100#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                               __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                 __opcode 11 8)) == (0xC#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                 __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__380 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__380 <b 3840) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__381 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 3840
                                                      let D := (BitVec.slice __opcode 22 1)
                                                      let Vn := (BitVec.slice __opcode 16 4)
                                                      let Vd := (BitVec.slice __opcode 12 4)
                                                      let N := (BitVec.slice __opcode 7 1)
                                                      let Q := (BitVec.slice __opcode 6 1)
                                                      let M := (BitVec.slice __opcode 5 1)
                                                      let Vm := (BitVec.slice __opcode 0 4)
                                                      (decode_aarch32_instrs_SHA1SU0_A1enc_A_txt D
                                                        Vn Vd N Q M Vm))
                                                  else
                                                    (do
                                                      let w__383 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                 __opcode 31 23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                   __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                     __opcode 17 16)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                       __opcode 11 6)) == (0b001110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__382 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__382 <b 3842) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__383 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 3842
                                                          let D := (BitVec.slice __opcode 22 1)
                                                          let size := (BitVec.slice __opcode 18 2)
                                                          let Vd := (BitVec.slice __opcode 12 4)
                                                          let M := (BitVec.slice __opcode 5 1)
                                                          let Vm := (BitVec.slice __opcode 0 4)
                                                          (decode_aarch32_instrs_SHA1SU1_A1enc_A_txt
                                                            D size Vd M Vm))
                                                      else
                                                        (do
                                                          let w__385 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                     __opcode 31 23)) == (0b111100110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                       __opcode 21 20)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                         __opcode 11 8)) == (0xC#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                         __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__384 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__384 <b 3844) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__385 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 3844
                                                              let D := (BitVec.slice __opcode 22 1)
                                                              let Vn := (BitVec.slice __opcode 16 4)
                                                              let Vd := (BitVec.slice __opcode 12 4)
                                                              let N := (BitVec.slice __opcode 7 1)
                                                              let Q := (BitVec.slice __opcode 6 1)
                                                              let M := (BitVec.slice __opcode 5 1)
                                                              let Vm := (BitVec.slice __opcode 0 4)
                                                              (decode_aarch32_instrs_SHA256H_A1enc_A_txt
                                                                D Vn Vd N Q M Vm))
                                                          else
                                                            (do
                                                              let w__387 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                         __opcode 31 23)) == (0b111100110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                           __opcode 21 20)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                             __opcode 11 8)) == (0xC#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                             __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__386 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__386 <b 3846) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__387 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 3846
                                                                  let D :=
                                                                    (BitVec.slice __opcode 22 1)
                                                                  let Vn :=
                                                                    (BitVec.slice __opcode 16 4)
                                                                  let Vd :=
                                                                    (BitVec.slice __opcode 12 4)
                                                                  let N :=
                                                                    (BitVec.slice __opcode 7 1)
                                                                  let Q :=
                                                                    (BitVec.slice __opcode 6 1)
                                                                  let M :=
                                                                    (BitVec.slice __opcode 5 1)
                                                                  let Vm :=
                                                                    (BitVec.slice __opcode 0 4)
                                                                  (decode_aarch32_instrs_SHA256H2_A1enc_A_txt
                                                                    D Vn Vd N Q M Vm))
                                                              else
                                                                (do
                                                                  let w__389 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                             __opcode 31 23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                               __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                 __opcode 17 16)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                   __opcode 11 6)) == (0b001111#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                   __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__388 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__388 <b 3848) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__389 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 3848
                                                                      let D :=
                                                                        (BitVec.slice __opcode 22 1)
                                                                      let size :=
                                                                        (BitVec.slice __opcode 18 2)
                                                                      let Vd :=
                                                                        (BitVec.slice __opcode 12 4)
                                                                      let M :=
                                                                        (BitVec.slice __opcode 5 1)
                                                                      let Vm :=
                                                                        (BitVec.slice __opcode 0 4)
                                                                      (decode_aarch32_instrs_SHA256SU0_A1enc_A_txt
                                                                        D size Vd M Vm))
                                                                  else
                                                                    (do
                                                                      let w__391 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 23)) == (0b111100110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                   __opcode 21 20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                     __opcode 11 8)) == (0xC#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                     __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__390 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__390 <b 3850) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__391 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 3850
                                                                          let D :=
                                                                            (BitVec.slice __opcode
                                                                              22 1)
                                                                          let Vn :=
                                                                            (BitVec.slice __opcode
                                                                              16 4)
                                                                          let Vd :=
                                                                            (BitVec.slice __opcode
                                                                              12 4)
                                                                          let N :=
                                                                            (BitVec.slice __opcode 7
                                                                              1)
                                                                          let Q :=
                                                                            (BitVec.slice __opcode 6
                                                                              1)
                                                                          let M :=
                                                                            (BitVec.slice __opcode 5
                                                                              1)
                                                                          let Vm :=
                                                                            (BitVec.slice __opcode 0
                                                                              4)
                                                                          (decode_aarch32_instrs_SHA256SU1_A1enc_A_txt
                                                                            D Vn Vd N Q M Vm))
                                                                      else
                                                                        (do
                                                                          let w__393 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                       __opcode 21
                                                                                       20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                         __opcode 17
                                                                                         16)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           11 10)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__392 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__392 <b 3866) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__393 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 3866
                                                                              let D :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 1)
                                                                              let size :=
                                                                                (BitVec.slice
                                                                                  __opcode 18 2)
                                                                              let Vd :=
                                                                                (BitVec.slice
                                                                                  __opcode 12 4)
                                                                              let RM :=
                                                                                (BitVec.slice
                                                                                  __opcode 8 2)
                                                                              let op :=
                                                                                (BitVec.slice
                                                                                  __opcode 7 1)
                                                                              let Q :=
                                                                                (BitVec.slice
                                                                                  __opcode 6 1)
                                                                              let M :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 1)
                                                                              let Vm :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 4)
                                                                              (decode_aarch32_instrs_VCVTA_asimd_A1enc_A_txt
                                                                                D size Vd RM op Q M
                                                                                Vm))
                                                                          else
                                                                            (do
                                                                              let w__395 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         23)) == (0b111100110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           11 8)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           4 4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__394 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__394 <b 3870) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__395 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 3870
                                                                                  let D :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 1)
                                                                                  let op :=
                                                                                    (BitVec.slice
                                                                                      __opcode 21 1)
                                                                                  let sz :=
                                                                                    (BitVec.slice
                                                                                      __opcode 20 1)
                                                                                  let Vn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 4)
                                                                                  let Vd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 12 4)
                                                                                  let N :=
                                                                                    (BitVec.slice
                                                                                      __opcode 7 1)
                                                                                  let Q :=
                                                                                    (BitVec.slice
                                                                                      __opcode 6 1)
                                                                                  let M :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 1)
                                                                                  let Vm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 4)
                                                                                  (decode_aarch32_instrs_VMAXNM_A1enc_A_txt
                                                                                    D op sz Vn Vd N
                                                                                    Q M Vm))
                                                                              else
                                                                                (do
                                                                                  let w__397 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 17
                                                                                                 16)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   11
                                                                                                   10)) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   4
                                                                                                   4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__396 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__396 <b 3874) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__397 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 3874
                                                                                      let D :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 1)
                                                                                      let size :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          18 2)
                                                                                      let Vd :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          12 4)
                                                                                      let op :=
                                                                                        (BitVec.slice
                                                                                          __opcode 7
                                                                                          3)
                                                                                      let Q :=
                                                                                        (BitVec.slice
                                                                                          __opcode 6
                                                                                          1)
                                                                                      let M :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          1)
                                                                                      let Vm :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          4)
                                                                                      (decode_aarch32_instrs_VRINTA_asimd_A1enc_A_txt
                                                                                        D size Vd op
                                                                                        Q M Vm))
                                                                                  else
                                                                                    (do
                                                                                      let w__399 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   21
                                                                                                   20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     17
                                                                                                     16)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       11
                                                                                                       7)) == (0b01001#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       4
                                                                                                       4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__398 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__398 <b 3878) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__399 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 3878
                                                                                          let D :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 1)
                                                                                          let size :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              18 2)
                                                                                          let Vd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              12 4)
                                                                                          let Q :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              6 1)
                                                                                          let M :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 1)
                                                                                          let Vm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 4)
                                                                                          (decode_aarch32_instrs_VRINTX_asimd_A1enc_A_txt
                                                                                            D size
                                                                                            Vd Q M
                                                                                            Vm))
                                                                                      else
                                                                                        (do
                                                                                          let w__401 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       21
                                                                                                       20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         17
                                                                                                         16)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           11
                                                                                                           7)) == (0b01011#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           4
                                                                                                           4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__400 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__400 <b 3882) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__401 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 3882
                                                                                              let D :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  22
                                                                                                  1)
                                                                                              let size :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  18
                                                                                                  2)
                                                                                              let Vd :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  12
                                                                                                  4)
                                                                                              let Q :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  6
                                                                                                  1)
                                                                                              let M :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  5
                                                                                                  1)
                                                                                              let Vm :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  4)
                                                                                              (decode_aarch32_instrs_VRINTZ_asimd_A1enc_A_txt
                                                                                                D
                                                                                                size
                                                                                                Vd Q
                                                                                                M Vm))
                                                                                          else
                                                                                            (do
                                                                                              let w__403 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         10)) == (0b1111000100010000000000#22 : (BitVec 22))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         8
                                                                                                         0)) == (0b000000000#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__402 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__402 <b 3888) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__403 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 3888
                                                                                                  let imm1 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      9
                                                                                                      1)
                                                                                                  if (((((((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                       __opcode
                                                                                                                                       16)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                       __opcode
                                                                                                                                       17)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                     __opcode
                                                                                                                                     18)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                   __opcode
                                                                                                                                   19)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                 __opcode
                                                                                                                                 10)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                               __opcode
                                                                                                                               11)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                             __opcode
                                                                                                                             12)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                           __opcode
                                                                                                                           13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                         __opcode
                                                                                                                         14)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                       __opcode
                                                                                                                       15)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                     __opcode
                                                                                                                     8)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                   __opcode
                                                                                                                   0)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                 __opcode
                                                                                                                 1)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                               __opcode
                                                                                                               2)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                             __opcode
                                                                                                             3)])) != 0#1)) : Bool)
                                                                                                  then
                                                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                                                      ()))
                                                                                                  else
                                                                                                    (do
                                                                                                      (decode_aarch32_instrs_SETPAN_A1enc_A_txt
                                                                                                        imm1)))
                                                                                              else
                                                                                                (do
                                                                                                  let w__405 ← (( do
                                                                                                    if (((__opcode == 0b11110101011111111111000001000000#32) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__404 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__404 <b 3896) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__405 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 3896
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
                                                                                                          (decode_aarch32_instrs_SSBB_A1enc_A_txt
                                                                                                            ())))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__407 ← (( do
                                                                                                        if (((__opcode == 0b11110101011111111111000001000100#32) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__406 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__406 <b 3898) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__407 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 3898
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
                                                                                                              (decode_aarch32_instrs_PSSBB_A1enc_A_txt
                                                                                                                ())))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__409 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       21
                                                                                                                       16)) == (0b110110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         11
                                                                                                                         6)) == (0b011001#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         4
                                                                                                                         4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__408 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__408 <b 3922) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__409 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 3922
                                                                                                              let D :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  22
                                                                                                                  1)
                                                                                                              let Vd :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  12
                                                                                                                  4)
                                                                                                              let M :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  5
                                                                                                                  1)
                                                                                                              let Vm :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  4)
                                                                                                              (decode_aarch32_instrs_VCVT_A1enc_A_txt
                                                                                                                D
                                                                                                                Vd
                                                                                                                M
                                                                                                                Vm))
                                                                                                          else
                                                                                                            sailThrow ((Error_Undefined
                                                                                                              ()))))))))))))))))))))))))))))


end ArmFull.Functions
