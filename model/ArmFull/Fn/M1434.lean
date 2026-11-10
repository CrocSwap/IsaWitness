import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M1048
import ArmFull.Fn.M1049
import ArmFull.Fn.M1089
import ArmFull.Fn.M1090
import ArmFull.Fn.M1091
import ArmFull.Fn.M1143
import ArmFull.Fn.M1144
import ArmFull.Fn.M1285

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
def __DecodeA32_Unconditional__seg1 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__57 ← (( do
    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111100110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
               __opcode 11 8)) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
               __opcode 4 4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
    then
      (do
        let w__56 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__56 <b 3388) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__57 : Bool)
  then
    (do
      writeReg SEE 3388
      let D := (BitVec.slice __opcode 22 1)
      let size := (BitVec.slice __opcode 20 2)
      let Vn := (BitVec.slice __opcode 16 4)
      let Vd := (BitVec.slice __opcode 12 4)
      let N := (BitVec.slice __opcode 7 1)
      let Q := (BitVec.slice __opcode 6 1)
      let M := (BitVec.slice __opcode 5 1)
      let Vm := (BitVec.slice __opcode 0 4)
      (decode_aarch32_instrs_VCEQ_r_A1enc_A_txt D size Vn Vd N Q M Vm)
      (pure false))
  else
    (do
      let w__59 ← (( do
        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111100100#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                   __opcode 21 21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                     __opcode 11 8)) == (0xE#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                     __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
        then
          (do
            let w__58 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__58 <b 3389) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__59 : Bool)
      then
        (do
          writeReg SEE 3389
          let D := (BitVec.slice __opcode 22 1)
          let sz := (BitVec.slice __opcode 20 1)
          let Vn := (BitVec.slice __opcode 16 4)
          let Vd := (BitVec.slice __opcode 12 4)
          let N := (BitVec.slice __opcode 7 1)
          let Q := (BitVec.slice __opcode 6 1)
          let M := (BitVec.slice __opcode 5 1)
          let Vm := (BitVec.slice __opcode 0 4)
          (decode_aarch32_instrs_VCEQ_r_A2enc_A_txt D sz Vn Vd N Q M Vm)
          (pure false))
      else
        (do
          let w__61 ← (( do
            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                       __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                         __opcode 17 16)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           __opcode 11 11)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                             __opcode 9 7)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                             __opcode 4 4)) == (0#1 : (BitVec 1)))))))) : Bool) : Bool)
            then
              (do
                let w__60 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__60 <b 3392) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__61 : Bool)
          then
            (do
              writeReg SEE 3392
              let D := (BitVec.slice __opcode 22 1)
              let size := (BitVec.slice __opcode 18 2)
              let Vd := (BitVec.slice __opcode 12 4)
              let F := (BitVec.slice __opcode 10 1)
              let Q := (BitVec.slice __opcode 6 1)
              let M := (BitVec.slice __opcode 5 1)
              let Vm := (BitVec.slice __opcode 0 4)
              (decode_aarch32_instrs_VCGE_i_A1enc_A_txt D size Vd F Q M Vm)
              (pure false))
          else
            (do
              let w__63 ← (( do
                if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb __opcode 31 25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           __opcode 23 23)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                             __opcode 11 8)) == (0x3#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                             __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                then
                  (do
                    let w__62 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__62 <b 3394) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__63 : Bool)
              then
                (do
                  writeReg SEE 3394
                  let U := (BitVec.slice __opcode 24 1)
                  let D := (BitVec.slice __opcode 22 1)
                  let size := (BitVec.slice __opcode 20 2)
                  let Vn := (BitVec.slice __opcode 16 4)
                  let Vd := (BitVec.slice __opcode 12 4)
                  let N := (BitVec.slice __opcode 7 1)
                  let Q := (BitVec.slice __opcode 6 1)
                  let M := (BitVec.slice __opcode 5 1)
                  let Vm := (BitVec.slice __opcode 0 4)
                  (decode_aarch32_instrs_VCGE_r_A1enc_A_txt U D size Vn Vd N Q M Vm)
                  (pure false))
              else
                (do
                  let w__65 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111100110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                               __opcode 21 21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                 __opcode 11 8)) == (0xE#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                 __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                    then
                      (do
                        let w__64 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__64 <b 3395) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__65 : Bool)
                  then
                    (do
                      writeReg SEE 3395
                      let D := (BitVec.slice __opcode 22 1)
                      let sz := (BitVec.slice __opcode 20 1)
                      let Vn := (BitVec.slice __opcode 16 4)
                      let Vd := (BitVec.slice __opcode 12 4)
                      let N := (BitVec.slice __opcode 7 1)
                      let Q := (BitVec.slice __opcode 6 1)
                      let M := (BitVec.slice __opcode 5 1)
                      let Vm := (BitVec.slice __opcode 0 4)
                      (decode_aarch32_instrs_VCGE_r_A2enc_A_txt D sz Vn Vd N Q M Vm)
                      (pure false))
                  else
                    (do
                      let w__67 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31
                                 23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                   __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                     __opcode 17 16)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                       __opcode 11 11)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                         __opcode 9 7)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                         __opcode 4 4)) == (0#1 : (BitVec 1)))))))) : Bool) : Bool)
                        then
                          (do
                            let w__66 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__66 <b 3398) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__67 : Bool)
                      then
                        (do
                          writeReg SEE 3398
                          let D := (BitVec.slice __opcode 22 1)
                          let size := (BitVec.slice __opcode 18 2)
                          let Vd := (BitVec.slice __opcode 12 4)
                          let F := (BitVec.slice __opcode 10 1)
                          let Q := (BitVec.slice __opcode 6 1)
                          let M := (BitVec.slice __opcode 5 1)
                          let Vm := (BitVec.slice __opcode 0 4)
                          (decode_aarch32_instrs_VCGT_i_A1enc_A_txt D size Vd F Q M Vm)
                          (pure false))
                      else
                        (do
                          let w__69 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb __opcode
                                     31 25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                       __opcode 23 23)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                         __opcode 11 8)) == (0x3#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                         __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                            then
                              (do
                                let w__68 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__68 <b 3400) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__69 : Bool)
                          then
                            (do
                              writeReg SEE 3400
                              let U := (BitVec.slice __opcode 24 1)
                              let D := (BitVec.slice __opcode 22 1)
                              let size := (BitVec.slice __opcode 20 2)
                              let Vn := (BitVec.slice __opcode 16 4)
                              let Vd := (BitVec.slice __opcode 12 4)
                              let N := (BitVec.slice __opcode 7 1)
                              let Q := (BitVec.slice __opcode 6 1)
                              let M := (BitVec.slice __opcode 5 1)
                              let Vm := (BitVec.slice __opcode 0 4)
                              (decode_aarch32_instrs_VCGT_r_A1enc_A_txt U D size Vn Vd N Q M Vm)
                              (pure false))
                          else
                            (do
                              let w__71 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                         __opcode 31 23)) == (0b111100110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                           __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                             __opcode 11 8)) == (0xE#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__70 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__70 <b 3401) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__71 : Bool)
                              then
                                (do
                                  writeReg SEE 3401
                                  let D := (BitVec.slice __opcode 22 1)
                                  let sz := (BitVec.slice __opcode 20 1)
                                  let Vn := (BitVec.slice __opcode 16 4)
                                  let Vd := (BitVec.slice __opcode 12 4)
                                  let N := (BitVec.slice __opcode 7 1)
                                  let Q := (BitVec.slice __opcode 6 1)
                                  let M := (BitVec.slice __opcode 5 1)
                                  let Vm := (BitVec.slice __opcode 0 4)
                                  (decode_aarch32_instrs_VCGT_r_A2enc_A_txt D sz Vn Vd N Q M Vm)
                                  (pure false))
                              else
                                (do
                                  let w__73 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                             __opcode 31 23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                               __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                 __opcode 17 16)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                   __opcode 11 11)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                     __opcode 9 7)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                     __opcode 4 4)) == (0#1 : (BitVec 1)))))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__72 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__72 <b 3404) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__73 : Bool)
                                  then
                                    (do
                                      writeReg SEE 3404
                                      let D := (BitVec.slice __opcode 22 1)
                                      let size := (BitVec.slice __opcode 18 2)
                                      let Vd := (BitVec.slice __opcode 12 4)
                                      let F := (BitVec.slice __opcode 10 1)
                                      let Q := (BitVec.slice __opcode 6 1)
                                      let M := (BitVec.slice __opcode 5 1)
                                      let Vm := (BitVec.slice __opcode 0 4)
                                      (decode_aarch32_instrs_VCLE_i_A1enc_A_txt D size Vd F Q M Vm)
                                      (pure false))
                                  else
                                    (do
                                      let w__75 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                 __opcode 31 23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                   __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                     __opcode 17 16)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                       __opcode 11 7)) == (0b01000#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__74 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__74 <b 3406) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__75 : Bool)
                                      then
                                        (do
                                          writeReg SEE 3406
                                          let D := (BitVec.slice __opcode 22 1)
                                          let size := (BitVec.slice __opcode 18 2)
                                          let Vd := (BitVec.slice __opcode 12 4)
                                          let Q := (BitVec.slice __opcode 6 1)
                                          let M := (BitVec.slice __opcode 5 1)
                                          let Vm := (BitVec.slice __opcode 0 4)
                                          (decode_aarch32_instrs_VCLS_A1enc_A_txt D size Vd Q M Vm)
                                          (pure false))
                                      else
                                        (do
                                          let w__77 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                     __opcode 31 23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                       __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                         __opcode 17 16)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 11 11)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                             __opcode 9 7)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                             __opcode 4 4)) == (0#1 : (BitVec 1)))))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__76 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__76 <b 3408) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__77 : Bool)
                                          then
                                            (do
                                              writeReg SEE 3408
                                              let D := (BitVec.slice __opcode 22 1)
                                              let size := (BitVec.slice __opcode 18 2)
                                              let Vd := (BitVec.slice __opcode 12 4)
                                              let F := (BitVec.slice __opcode 10 1)
                                              let Q := (BitVec.slice __opcode 6 1)
                                              let M := (BitVec.slice __opcode 5 1)
                                              let Vm := (BitVec.slice __opcode 0 4)
                                              (decode_aarch32_instrs_VCLT_i_A1enc_A_txt D size Vd F
                                                Q M Vm)
                                              (pure false))
                                          else
                                            (do
                                              let w__79 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                         __opcode 31 23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                           __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                             __opcode 17 16)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                               __opcode 11 7)) == (0b01001#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__78 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__78 <b 3410) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__79 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 3410
                                                  let D := (BitVec.slice __opcode 22 1)
                                                  let size := (BitVec.slice __opcode 18 2)
                                                  let Vd := (BitVec.slice __opcode 12 4)
                                                  let Q := (BitVec.slice __opcode 6 1)
                                                  let M := (BitVec.slice __opcode 5 1)
                                                  let Vm := (BitVec.slice __opcode 0 4)
                                                  (decode_aarch32_instrs_VCLZ_A1enc_A_txt D size Vd
                                                    Q M Vm)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__81 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                             __opcode 31 23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                               __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                 __opcode 17 16)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                   __opcode 11 7)) == (0b01010#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__80 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__80 <b 3416) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__81 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 3416
                                                      let D := (BitVec.slice __opcode 22 1)
                                                      let size := (BitVec.slice __opcode 18 2)
                                                      let Vd := (BitVec.slice __opcode 12 4)
                                                      let Q := (BitVec.slice __opcode 6 1)
                                                      let M := (BitVec.slice __opcode 5 1)
                                                      let Vm := (BitVec.slice __opcode 0 4)
                                                      (decode_aarch32_instrs_VCNT_A1enc_A_txt D size
                                                        Vd Q M Vm)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__83 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                 __opcode 31 23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                   __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                     __opcode 17 16)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                       __opcode 11 9)) == (0b011#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                         __opcode 7 6)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                         __opcode 4 4)) == (0#1 : (BitVec 1)))))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__82 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__82 <b 3422) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__83 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 3422
                                                          let D := (BitVec.slice __opcode 22 1)
                                                          let size := (BitVec.slice __opcode 18 2)
                                                          let Vd := (BitVec.slice __opcode 12 4)
                                                          let op := (BitVec.slice __opcode 8 1)
                                                          let M := (BitVec.slice __opcode 5 1)
                                                          let Vm := (BitVec.slice __opcode 0 4)
                                                          (decode_aarch32_instrs_VCVT_hs_A1enc_A_txt
                                                            D size Vd op M Vm)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__85 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                     __opcode 31 23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                       __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                         __opcode 17 16)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                           __opcode 11 9)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__84 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__84 <b 3424) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__85 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 3424
                                                              let D := (BitVec.slice __opcode 22 1)
                                                              let size :=
                                                                (BitVec.slice __opcode 18 2)
                                                              let Vd := (BitVec.slice __opcode 12 4)
                                                              let op := (BitVec.slice __opcode 7 2)
                                                              let Q := (BitVec.slice __opcode 6 1)
                                                              let M := (BitVec.slice __opcode 5 1)
                                                              let Vm := (BitVec.slice __opcode 0 4)
                                                              (decode_aarch32_instrs_VCVT_is_A1enc_A_txt
                                                                D size Vd op Q M Vm)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__87 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                         __opcode 31 25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 23 23)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                             __opcode 11 10)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                               __opcode 7 7)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                               __opcode 4 4)) == (1#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__86 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__86 <b 3428) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__87 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 3428
                                                                  let U :=
                                                                    (BitVec.slice __opcode 24 1)
                                                                  let D :=
                                                                    (BitVec.slice __opcode 22 1)
                                                                  let imm6 :=
                                                                    (BitVec.slice __opcode 16 6)
                                                                  let Vd :=
                                                                    (BitVec.slice __opcode 12 4)
                                                                  let op :=
                                                                    (BitVec.slice __opcode 8 2)
                                                                  let Q :=
                                                                    (BitVec.slice __opcode 6 1)
                                                                  let M :=
                                                                    (BitVec.slice __opcode 5 1)
                                                                  let Vm :=
                                                                    (BitVec.slice __opcode 0 4)
                                                                  (decode_aarch32_instrs_VCVT_xs_A1enc_A_txt
                                                                    U D imm6 Vd op Q M Vm)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__89 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                             __opcode 31 23)) == (0b111100111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                               __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                 __opcode 11 7)) == (0b11000#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__88 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__88 <b 3436) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__89 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 3436
                                                                      let D :=
                                                                        (BitVec.slice __opcode 22 1)
                                                                      let imm4 :=
                                                                        (BitVec.slice __opcode 16 4)
                                                                      let Vd :=
                                                                        (BitVec.slice __opcode 12 4)
                                                                      let Q :=
                                                                        (BitVec.slice __opcode 6 1)
                                                                      let M :=
                                                                        (BitVec.slice __opcode 5 1)
                                                                      let Vm :=
                                                                        (BitVec.slice __opcode 0 4)
                                                                      (decode_aarch32_instrs_VDUP_s_A1enc_A_txt
                                                                        D imm4 Vd Q M Vm)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__91 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 23)) == (0b111100110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                   __opcode 21 20)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                     __opcode 11 8)) == (0x1#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                     __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__90 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__90 <b 3438) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__91 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 3438
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
                                                                          (decode_aarch32_instrs_VEOR_A1enc_A_txt
                                                                            D Vn Vd N Q M Vm)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__93 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 23)) == (0b111100101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                       __opcode 21
                                                                                       20)) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 4 4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__92 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__92 <b 3440) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__93 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 3440
                                                                              let D :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 1)
                                                                              let Vn :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 4)
                                                                              let Vd :=
                                                                                (BitVec.slice
                                                                                  __opcode 12 4)
                                                                              let imm4 :=
                                                                                (BitVec.slice
                                                                                  __opcode 8 4)
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
                                                                              (decode_aarch32_instrs_VEXT_A1enc_A_txt
                                                                                D Vn Vd imm4 N Q M
                                                                                Vm)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__95 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         23)) == (0b111100100#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           11 8)) == (0xC#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           4 4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__94 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__94 <b 3442) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__95 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 3442
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
                                                                                  (decode_aarch32_instrs_VFMA_A1enc_A_txt
                                                                                    D op sz Vn Vd N
                                                                                    Q M Vm)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__97 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 25)) == (0b1111001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               23 23)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 11
                                                                                                 10)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   8
                                                                                                   8)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   4
                                                                                                   4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__96 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__96 <b 3448) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__97 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 3448
                                                                                      let U :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          24 1)
                                                                                      let D :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 1)
                                                                                      let size :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          20 2)
                                                                                      let Vn :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 4)
                                                                                      let Vd :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          12 4)
                                                                                      let op :=
                                                                                        (BitVec.slice
                                                                                          __opcode 9
                                                                                          1)
                                                                                      let N :=
                                                                                        (BitVec.slice
                                                                                          __opcode 7
                                                                                          1)
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
                                                                                      (decode_aarch32_instrs_VHADD_A1enc_A_txt
                                                                                        U D size Vn
                                                                                        Vd op N Q M
                                                                                        Vm)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__99 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 23)) == (0b111101001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   21
                                                                                                   20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   11
                                                                                                   8)) == (0x0#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__98 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__98 <b 3450) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__99 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 3450
                                                                                          let D :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 1)
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 4)
                                                                                          let Vd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              12 4)
                                                                                          let size :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              10 2)
                                                                                          let index_align :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              4 4)
                                                                                          let Rm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 4)
                                                                                          (decode_aarch32_instrs_VLD1_1_A1enc_A_txt
                                                                                            D Rn Vd
                                                                                            size
                                                                                            index_align
                                                                                            Rm)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__101 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     23)) == (0b111101001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       21
                                                                                                       20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       11
                                                                                                       8)) == (0x4#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__100 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__100 <b 3451) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__101 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 3451
                                                                                              let D :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  22
                                                                                                  1)
                                                                                              let Rn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  4)
                                                                                              let Vd :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  12
                                                                                                  4)
                                                                                              let size :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  10
                                                                                                  2)
                                                                                              let index_align :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  4
                                                                                                  4)
                                                                                              let Rm :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  4)
                                                                                              (decode_aarch32_instrs_VLD1_1_A2enc_A_txt
                                                                                                D Rn
                                                                                                Vd
                                                                                                size
                                                                                                index_align
                                                                                                Rm)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__103 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         23)) == (0b111101001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           21
                                                                                                           20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           11
                                                                                                           8)) == (0x8#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__102 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__102 <b 3452) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__103 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 3452
                                                                                                  let D :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      22
                                                                                                      1)
                                                                                                  let Rn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      4)
                                                                                                  let Vd :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      12
                                                                                                      4)
                                                                                                  let size :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      10
                                                                                                      2)
                                                                                                  let index_align :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      4
                                                                                                      4)
                                                                                                  let Rm :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      4)
                                                                                                  (decode_aarch32_instrs_VLD1_1_A3enc_A_txt
                                                                                                    D
                                                                                                    Rn
                                                                                                    Vd
                                                                                                    size
                                                                                                    index_align
                                                                                                    Rm)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__105 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             23)) == (0b111101001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               21
                                                                                                               20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               11
                                                                                                               8)) == (0xC#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__104 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__104 <b 3456) : Bool))))
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
                                                                                                      writeReg SEE 3456
                                                                                                      let D :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          22
                                                                                                          1)
                                                                                                      let Rn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          4)
                                                                                                      let Vd :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          12
                                                                                                          4)
                                                                                                      let size :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          6
                                                                                                          2)
                                                                                                      let T :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          5
                                                                                                          1)
                                                                                                      let a :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          4
                                                                                                          1)
                                                                                                      let Rm :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          4)
                                                                                                      (decode_aarch32_instrs_VLD1_a_A1enc_A_txt
                                                                                                        D
                                                                                                        Rn
                                                                                                        Vd
                                                                                                        size
                                                                                                        T
                                                                                                        a
                                                                                                        Rm)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__107 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 23)) == (0b111101000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   21
                                                                                                                   20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   11
                                                                                                                   8)) == (0x7#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__106 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__106 <b 3458) : Bool))))
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
                                                                                                          writeReg SEE 3458
                                                                                                          let D :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              22
                                                                                                              1)
                                                                                                          let Rn :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              4)
                                                                                                          let Vd :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              12
                                                                                                              4)
                                                                                                          let itype :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              8
                                                                                                              4)
                                                                                                          let size :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              6
                                                                                                              2)
                                                                                                          let align :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              4
                                                                                                              2)
                                                                                                          let Rm :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              4)
                                                                                                          (decode_aarch32_instrs_VLD1_m_A1enc_A_txt
                                                                                                            D
                                                                                                            Rn
                                                                                                            Vd
                                                                                                            itype
                                                                                                            size
                                                                                                            align
                                                                                                            Rm)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__109 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     23)) == (0b111101000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       21
                                                                                                                       20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       11
                                                                                                                       8)) == (0xA#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__108 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__108 <b 3459) : Bool))))
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
                                                                                                              writeReg SEE 3459
                                                                                                              let D :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  22
                                                                                                                  1)
                                                                                                              let Rn :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  4)
                                                                                                              let Vd :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  12
                                                                                                                  4)
                                                                                                              let itype :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  8
                                                                                                                  4)
                                                                                                              let size :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  6
                                                                                                                  2)
                                                                                                              let align :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  4
                                                                                                                  2)
                                                                                                              let Rm :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  4)
                                                                                                              (decode_aarch32_instrs_VLD1_m_A2enc_A_txt
                                                                                                                D
                                                                                                                Rn
                                                                                                                Vd
                                                                                                                itype
                                                                                                                size
                                                                                                                align
                                                                                                                Rm)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__111 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         23)) == (0b111101000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           21
                                                                                                                           20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           11
                                                                                                                           8)) == (0x6#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__110 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__110 <b 3460) : Bool))))
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
                                                                                                                  writeReg SEE 3460
                                                                                                                  let D :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      22
                                                                                                                      1)
                                                                                                                  let Rn :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      4)
                                                                                                                  let Vd :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      12
                                                                                                                      4)
                                                                                                                  let itype :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      8
                                                                                                                      4)
                                                                                                                  let size :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      6
                                                                                                                      2)
                                                                                                                  let align :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      4
                                                                                                                      2)
                                                                                                                  let Rm :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      4)
                                                                                                                  (decode_aarch32_instrs_VLD1_m_A3enc_A_txt
                                                                                                                    D
                                                                                                                    Rn
                                                                                                                    Vd
                                                                                                                    itype
                                                                                                                    size
                                                                                                                    align
                                                                                                                    Rm)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__113 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             23)) == (0b111101000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               21
                                                                                                                               20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               11
                                                                                                                               8)) == (0x2#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__112 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__112 <b 3461) : Bool))))
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
                                                                                                                      writeReg SEE 3461
                                                                                                                      let D :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          22
                                                                                                                          1)
                                                                                                                      let Rn :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          16
                                                                                                                          4)
                                                                                                                      let Vd :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          12
                                                                                                                          4)
                                                                                                                      let itype :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          8
                                                                                                                          4)
                                                                                                                      let size :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          6
                                                                                                                          2)
                                                                                                                      let align :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          4
                                                                                                                          2)
                                                                                                                      let Rm :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          4)
                                                                                                                      (decode_aarch32_instrs_VLD1_m_A4enc_A_txt
                                                                                                                        D
                                                                                                                        Rn
                                                                                                                        Vd
                                                                                                                        itype
                                                                                                                        size
                                                                                                                        align
                                                                                                                        Rm)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__115 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 23)) == (0b111101001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   21
                                                                                                                                   20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   11
                                                                                                                                   8)) == (0x1#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__114 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__114 <b 3466) : Bool))))
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
                                                                                                                          writeReg SEE 3466
                                                                                                                          let D :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              22
                                                                                                                              1)
                                                                                                                          let Rn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              4)
                                                                                                                          let Vd :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              12
                                                                                                                              4)
                                                                                                                          let size :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              10
                                                                                                                              2)
                                                                                                                          let index_align :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              4
                                                                                                                              4)
                                                                                                                          let Rm :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              4)
                                                                                                                          (decode_aarch32_instrs_VLD2_1_A1enc_A_txt
                                                                                                                            D
                                                                                                                            Rn
                                                                                                                            Vd
                                                                                                                            size
                                                                                                                            index_align
                                                                                                                            Rm)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (pure true))))))))))))))))))))))))))))))


end ArmFull.Functions
