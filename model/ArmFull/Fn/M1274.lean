import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0235
import ArmFull.Fn.M0236
import ArmFull.Fn.M1048
import ArmFull.Fn.M1089
import ArmFull.Fn.M1090
import ArmFull.Fn.M1143

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
def __DecodeT32__seg5 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__426 ← (( do
    if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb __opcode 31 22)) == (0b1111001110#10 : (BitVec 10))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
               __opcode 20 20)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                 __opcode 15 15)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                 __opcode 5 5)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
    then
      (do
        let w__425 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__425 <b 3329) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__426 : Bool)
  then
    (do
      writeReg SEE 3329
      let sh := (BitVec.slice __opcode 21 1)
      let Rn := (BitVec.slice __opcode 16 4)
      let imm3 := (BitVec.slice __opcode 12 3)
      let Rd := (BitVec.slice __opcode 8 4)
      let imm2 := (BitVec.slice __opcode 6 2)
      let sat_imm := (BitVec.slice __opcode 0 5)
      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 26)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 __opcode 5)])) != 0#1)) : Bool)
      then sailThrow ((Error_ConstrainedUnpredictable ()))
      else
        (do
          (decode_aarch32_instrs_USAT_T1enc_A_txt sh Rn imm3 Rd imm2 sat_imm))
      (pure false))
  else
    (do
      let w__428 ← (( do
        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xFAE#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                   __opcode 15 12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                   __opcode 7 4)) == (0x4#4 : (BitVec 4))))) : Bool) : Bool)
        then
          (do
            let w__427 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__427 <b 3331) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__428 : Bool)
      then
        (do
          writeReg SEE 3331
          let Rn := (BitVec.slice __opcode 16 4)
          let Rd := (BitVec.slice __opcode 8 4)
          let Rm := (BitVec.slice __opcode 0 4)
          (decode_aarch32_instrs_USAX_T1enc_A_txt Rn Rd Rm)
          (pure false))
      else
        (do
          let w__430 ← (( do
            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xFAD#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                       __opcode 15 12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                       __opcode 7 4)) == (0x4#4 : (BitVec 4))))) : Bool) : Bool)
            then
              (do
                let w__429 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__429 <b 3333) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__430 : Bool)
          then
            (do
              writeReg SEE 3333
              let Rn := (BitVec.slice __opcode 16 4)
              let Rd := (BitVec.slice __opcode 8 4)
              let Rm := (BitVec.slice __opcode 0 4)
              (decode_aarch32_instrs_USUB16_T1enc_A_txt Rn Rd Rm)
              (pure false))
          else
            (do
              let w__432 ← (( do
                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xFAC#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                           __opcode 15 12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                           __opcode 7 4)) == (0x4#4 : (BitVec 4))))) : Bool) : Bool)
                then
                  (do
                    let w__431 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__431 <b 3335) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__432 : Bool)
              then
                (do
                  writeReg SEE 3335
                  let Rn := (BitVec.slice __opcode 16 4)
                  let Rd := (BitVec.slice __opcode 8 4)
                  let Rm := (BitVec.slice __opcode 0 4)
                  (decode_aarch32_instrs_USUB8_T1enc_A_txt Rn Rd Rm)
                  (pure false))
              else
                (do
                  let w__434 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xFA3#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                               __opcode 15 12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                               __opcode 7 6)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                    then
                      (do
                        let w__433 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__433 <b 3337) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__434 : Bool)
                  then
                    (do
                      writeReg SEE 3337
                      let Rn := (BitVec.slice __opcode 16 4)
                      let Rd := (BitVec.slice __opcode 8 4)
                      let rotate := (BitVec.slice __opcode 4 2)
                      let Rm := (BitVec.slice __opcode 0 4)
                      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 6)])) != 0#1) : Bool)
                      then sailThrow ((Error_ConstrainedUnpredictable ()))
                      else
                        (do
                          (decode_aarch32_instrs_UXTAB16_T1enc_A_txt Rn Rd rotate Rm))
                      (pure false))
                  else
                    (do
                      let w__436 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31
                                 20)) == (0xFA5#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                   __opcode 15 12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                   __opcode 7 6)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                        then
                          (do
                            let w__435 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__435 <b 3339) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__436 : Bool)
                      then
                        (do
                          writeReg SEE 3339
                          let Rn := (BitVec.slice __opcode 16 4)
                          let Rd := (BitVec.slice __opcode 8 4)
                          let rotate := (BitVec.slice __opcode 4 2)
                          let Rm := (BitVec.slice __opcode 0 4)
                          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 6)])) != 0#1) : Bool)
                          then sailThrow ((Error_ConstrainedUnpredictable ()))
                          else
                            (do
                              (decode_aarch32_instrs_UXTAB_T1enc_A_txt Rn Rd rotate Rm))
                          (pure false))
                      else
                        (do
                          let w__438 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode
                                     31 20)) == (0xFA1#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                       __opcode 15 12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                       __opcode 7 6)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                            then
                              (do
                                let w__437 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__437 <b 3341) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__438 : Bool)
                          then
                            (do
                              writeReg SEE 3341
                              let Rn := (BitVec.slice __opcode 16 4)
                              let Rd := (BitVec.slice __opcode 8 4)
                              let rotate := (BitVec.slice __opcode 4 2)
                              let Rm := (BitVec.slice __opcode 0 4)
                              if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 6)])) != 0#1) : Bool)
                              then sailThrow ((Error_ConstrainedUnpredictable ()))
                              else
                                (do
                                  (decode_aarch32_instrs_UXTAH_T1enc_A_txt Rn Rd rotate Rm))
                              (pure false))
                          else
                            (do
                              let w__440 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                         __opcode 31 12)) == (0xFA3FF#20 : (BitVec 20))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                         __opcode 7 6)) == (0b10#2 : (BitVec 2)))) : Bool) : Bool)
                                then
                                  (do
                                    let w__439 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__439 <b 3343) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__440 : Bool)
                              then
                                (do
                                  writeReg SEE 3343
                                  let Rd := (BitVec.slice __opcode 8 4)
                                  let rotate := (BitVec.slice __opcode 4 2)
                                  let Rm := (BitVec.slice __opcode 0 4)
                                  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 6)])) != 0#1) : Bool)
                                  then sailThrow ((Error_ConstrainedUnpredictable ()))
                                  else
                                    (do
                                      (decode_aarch32_instrs_UXTB16_T1enc_A_txt Rd rotate Rm))
                                  (pure false))
                              else
                                (do
                                  let w__442 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                             __opcode 31 12)) == (0xFA5FF#20 : (BitVec 20))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                             __opcode 7 6)) == (0b10#2 : (BitVec 2)))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__441 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__441 <b 3346) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__442 : Bool)
                                  then
                                    (do
                                      writeReg SEE 3346
                                      let Rd := (BitVec.slice __opcode 8 4)
                                      let rotate := (BitVec.slice __opcode 4 2)
                                      let Rm := (BitVec.slice __opcode 0 4)
                                      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode
                                               6)])) != 0#1) : Bool)
                                      then sailThrow ((Error_ConstrainedUnpredictable ()))
                                      else
                                        (do
                                          (decode_aarch32_instrs_UXTB_T2enc_A_txt Rd rotate Rm))
                                      (pure false))
                                  else
                                    (do
                                      let w__444 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                 __opcode 31 12)) == (0xFA1FF#20 : (BitVec 20))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                 __opcode 7 6)) == (0b10#2 : (BitVec 2)))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__443 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__443 <b 3349) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__444 : Bool)
                                      then
                                        (do
                                          writeReg SEE 3349
                                          let Rd := (BitVec.slice __opcode 8 4)
                                          let rotate := (BitVec.slice __opcode 4 2)
                                          let Rm := (BitVec.slice __opcode 0 4)
                                          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                   __opcode 6)])) != 0#1) : Bool)
                                          then sailThrow ((Error_ConstrainedUnpredictable ()))
                                          else
                                            (do
                                              (decode_aarch32_instrs_UXTH_T2enc_A_txt Rd rotate Rm))
                                          (pure false))
                                      else
                                        (do
                                          let w__446 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                     __opcode 31 29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                       __opcode 27 23)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                         __opcode 11 8)) == (0x7#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                         __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__445 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__445 <b 3352) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__446 : Bool)
                                          then
                                            (do
                                              writeReg SEE 3352
                                              let U := (BitVec.slice __opcode 28 1)
                                              let D := (BitVec.slice __opcode 22 1)
                                              let size := (BitVec.slice __opcode 20 2)
                                              let Vn := (BitVec.slice __opcode 16 4)
                                              let Vd := (BitVec.slice __opcode 12 4)
                                              let N := (BitVec.slice __opcode 7 1)
                                              let Q := (BitVec.slice __opcode 6 1)
                                              let M := (BitVec.slice __opcode 5 1)
                                              let Vm := (BitVec.slice __opcode 0 4)
                                              (decode_aarch32_instrs_VABA_T1enc_A_txt U D size Vn Vd
                                                N Q M Vm)
                                              (pure false))
                                          else
                                            (do
                                              let w__448 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                         __opcode 31 29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                           __opcode 27 23)) == (0b11111#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                             __opcode 11 8)) == (0x5#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 6 6)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__447 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__447 <b 3353) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__448 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 3353
                                                  let U := (BitVec.slice __opcode 28 1)
                                                  let D := (BitVec.slice __opcode 22 1)
                                                  let size := (BitVec.slice __opcode 20 2)
                                                  let Vn := (BitVec.slice __opcode 16 4)
                                                  let Vd := (BitVec.slice __opcode 12 4)
                                                  let N := (BitVec.slice __opcode 7 1)
                                                  let M := (BitVec.slice __opcode 5 1)
                                                  let Vm := (BitVec.slice __opcode 0 4)
                                                  (decode_aarch32_instrs_VABA_T2enc_A_txt U D size
                                                    Vn Vd N M Vm)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__450 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                             __opcode 31 23)) == (0b111111110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                 __opcode 11 8)) == (0xD#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                 __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__449 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__449 <b 3355) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__450 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 3355
                                                      let D := (BitVec.slice __opcode 22 1)
                                                      let sz := (BitVec.slice __opcode 20 1)
                                                      let Vn := (BitVec.slice __opcode 16 4)
                                                      let Vd := (BitVec.slice __opcode 12 4)
                                                      let N := (BitVec.slice __opcode 7 1)
                                                      let Q := (BitVec.slice __opcode 6 1)
                                                      let M := (BitVec.slice __opcode 5 1)
                                                      let Vm := (BitVec.slice __opcode 0 4)
                                                      (decode_aarch32_instrs_VABD_f_T1enc_A_txt D sz
                                                        Vn Vd N Q M Vm)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__452 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                 __opcode 31 29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                   __opcode 27 23)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                     __opcode 11 8)) == (0x7#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                     __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__451 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__451 <b 3358) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__452 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 3358
                                                          let U := (BitVec.slice __opcode 28 1)
                                                          let D := (BitVec.slice __opcode 22 1)
                                                          let size := (BitVec.slice __opcode 20 2)
                                                          let Vn := (BitVec.slice __opcode 16 4)
                                                          let Vd := (BitVec.slice __opcode 12 4)
                                                          let N := (BitVec.slice __opcode 7 1)
                                                          let Q := (BitVec.slice __opcode 6 1)
                                                          let M := (BitVec.slice __opcode 5 1)
                                                          let Vm := (BitVec.slice __opcode 0 4)
                                                          (decode_aarch32_instrs_VABD_i_T1enc_A_txt
                                                            U D size Vn Vd N Q M Vm)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__454 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                     __opcode 31 29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                       __opcode 27 23)) == (0b11111#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                         __opcode 11 8)) == (0x7#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 6 6)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__453 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__453 <b 3359) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__454 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 3359
                                                              let U := (BitVec.slice __opcode 28 1)
                                                              let D := (BitVec.slice __opcode 22 1)
                                                              let size :=
                                                                (BitVec.slice __opcode 20 2)
                                                              let Vn := (BitVec.slice __opcode 16 4)
                                                              let Vd := (BitVec.slice __opcode 12 4)
                                                              let N := (BitVec.slice __opcode 7 1)
                                                              let M := (BitVec.slice __opcode 5 1)
                                                              let Vm := (BitVec.slice __opcode 0 4)
                                                              (decode_aarch32_instrs_VABD_i_T2enc_A_txt
                                                                U D size Vn Vd N M Vm)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__456 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                         __opcode 31 23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                           __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                             __opcode 17 16)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                               __opcode 11 11)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                 __opcode 9 7)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 4 4)) == (0#1 : (BitVec 1)))))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__455 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__455 <b 3362) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__456 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 3362
                                                                  let D :=
                                                                    (BitVec.slice __opcode 22 1)
                                                                  let size :=
                                                                    (BitVec.slice __opcode 18 2)
                                                                  let Vd :=
                                                                    (BitVec.slice __opcode 12 4)
                                                                  let F :=
                                                                    (BitVec.slice __opcode 10 1)
                                                                  let Q :=
                                                                    (BitVec.slice __opcode 6 1)
                                                                  let M :=
                                                                    (BitVec.slice __opcode 5 1)
                                                                  let Vm :=
                                                                    (BitVec.slice __opcode 0 4)
                                                                  (decode_aarch32_instrs_VABS_T1enc_A_txt
                                                                    D size Vd F Q M Vm)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__458 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                             __opcode 31 23)) == (0b111011101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                               __opcode 21 16)) == (0b110000#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                 __opcode 11 10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                   __opcode 7 6)) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                   __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__457 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__457 <b 3363) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__458 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 3363
                                                                      let D :=
                                                                        (BitVec.slice __opcode 22 1)
                                                                      let Vd :=
                                                                        (BitVec.slice __opcode 12 4)
                                                                      let size :=
                                                                        (BitVec.slice __opcode 8 2)
                                                                      let M :=
                                                                        (BitVec.slice __opcode 5 1)
                                                                      let Vm :=
                                                                        (BitVec.slice __opcode 0 4)
                                                                      (decode_aarch32_instrs_VABS_T2enc_A_txt
                                                                        D Vd size M Vm)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__460 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 23)) == (0b111111110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                   __opcode 11 8)) == (0xE#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                   __opcode 4 4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__459 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__459 <b 3365) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__460 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 3365
                                                                          let D :=
                                                                            (BitVec.slice __opcode
                                                                              22 1)
                                                                          let op :=
                                                                            (BitVec.slice __opcode
                                                                              21 1)
                                                                          let sz :=
                                                                            (BitVec.slice __opcode
                                                                              20 1)
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
                                                                          (decode_aarch32_instrs_VACGE_T1enc_A_txt
                                                                            D op sz Vn Vd N Q M Vm)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__462 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 23)) == (0b111011110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 21
                                                                                       21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                         __opcode 11
                                                                                         8)) == (0xD#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                         __opcode 4
                                                                                         4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__461 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__461 <b 3368) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__462 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 3368
                                                                              let D :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 1)
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
                                                                              (decode_aarch32_instrs_VADD_f_T1enc_A_txt
                                                                                D sz Vn Vd N Q M Vm)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__464 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         23)) == (0b111011100#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             11 10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               6 6)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__463 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__463 <b 3369) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__464 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 3369
                                                                                  let D :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 1)
                                                                                  let Vn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 4)
                                                                                  let Vd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 12 4)
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 8 2)
                                                                                  let N :=
                                                                                    (BitVec.slice
                                                                                      __opcode 7 1)
                                                                                  let M :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 1)
                                                                                  let Vm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 4)
                                                                                  (decode_aarch32_instrs_VADD_f_T2enc_A_txt
                                                                                    D Vn Vd size N M
                                                                                    Vm)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__466 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 23)) == (0b111011111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               11 8)) == (0x4#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 6 6)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__465 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__465 <b 3371) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__466 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 3371
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
                                                                                      let N :=
                                                                                        (BitVec.slice
                                                                                          __opcode 7
                                                                                          1)
                                                                                      let M :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          1)
                                                                                      let Vm :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          4)
                                                                                      (decode_aarch32_instrs_VADDHN_T1enc_A_txt
                                                                                        D size Vn Vd
                                                                                        N M Vm)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__468 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 23)) == (0b111011110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   11
                                                                                                   8)) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   4
                                                                                                   4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__467 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__467 <b 3373) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__468 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 3373
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
                                                                                          let N :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              7 1)
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
                                                                                          (decode_aarch32_instrs_VADD_i_T1enc_A_txt
                                                                                            D size
                                                                                            Vn Vd N
                                                                                            Q M Vm)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__470 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       27
                                                                                                       23)) == (0b11111#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         11
                                                                                                         9)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           6
                                                                                                           6)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           4
                                                                                                           4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__469 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__469 <b 3375) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__470 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 3375
                                                                                              let U :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  28
                                                                                                  1)
                                                                                              let D :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  22
                                                                                                  1)
                                                                                              let size :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  20
                                                                                                  2)
                                                                                              let Vn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  4)
                                                                                              let Vd :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  12
                                                                                                  4)
                                                                                              let op :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  8
                                                                                                  1)
                                                                                              let N :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  7
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
                                                                                              (decode_aarch32_instrs_VADDL_T1enc_A_txt
                                                                                                U D
                                                                                                size
                                                                                                Vn
                                                                                                Vd
                                                                                                op N
                                                                                                M Vm)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__472 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         23)) == (0b111011110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           21
                                                                                                           20)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             11
                                                                                                             8)) == (0x1#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             4
                                                                                                             4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__471 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__471 <b 3377) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__472 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 3377
                                                                                                  let D :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      22
                                                                                                      1)
                                                                                                  let Vn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      4)
                                                                                                  let Vd :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      12
                                                                                                      4)
                                                                                                  let N :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      7
                                                                                                      1)
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
                                                                                                  (decode_aarch32_instrs_VAND_r_T1enc_A_txt
                                                                                                    D
                                                                                                    Vn
                                                                                                    Vd
                                                                                                    N
                                                                                                    Q
                                                                                                    M
                                                                                                    Vm)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__474 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               27
                                                                                                               23)) == (0b11111#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 21
                                                                                                                 19)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   11
                                                                                                                   11)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     8
                                                                                                                     7)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     5
                                                                                                                     4)) == (0b11#2 : (BitVec 2)))))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__473 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__473 <b 3380) : Bool))))
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
                                                                                                      writeReg SEE 3380
                                                                                                      let i :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          28
                                                                                                          1)
                                                                                                      let D :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          22
                                                                                                          1)
                                                                                                      let imm3 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          3)
                                                                                                      let Vd :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          12
                                                                                                          4)
                                                                                                      let cmode :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          8
                                                                                                          4)
                                                                                                      let Q :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          6
                                                                                                          1)
                                                                                                      let imm4 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          4)
                                                                                                      (decode_aarch32_instrs_VBIC_i_T1enc_A_txt
                                                                                                        i
                                                                                                        D
                                                                                                        imm3
                                                                                                        Vd
                                                                                                        cmode
                                                                                                        Q
                                                                                                        imm4)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__476 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   27
                                                                                                                   23)) == (0b11111#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     21
                                                                                                                     19)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       11
                                                                                                                       10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         8
                                                                                                                         7)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         5
                                                                                                                         4)) == (0b11#2 : (BitVec 2)))))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__475 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__475 <b 3381) : Bool))))
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
                                                                                                          writeReg SEE 3381
                                                                                                          let i :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              28
                                                                                                              1)
                                                                                                          let D :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              22
                                                                                                              1)
                                                                                                          let imm3 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              3)
                                                                                                          let Vd :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              12
                                                                                                              4)
                                                                                                          let cmode :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              8
                                                                                                              4)
                                                                                                          let Q :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              6
                                                                                                              1)
                                                                                                          let imm4 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              4)
                                                                                                          (decode_aarch32_instrs_VBIC_i_T2enc_A_txt
                                                                                                            i
                                                                                                            D
                                                                                                            imm3
                                                                                                            Vd
                                                                                                            cmode
                                                                                                            Q
                                                                                                            imm4)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__478 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     23)) == (0b111011110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       21
                                                                                                                       20)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         11
                                                                                                                         8)) == (0x1#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         4
                                                                                                                         4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__477 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__477 <b 3383) : Bool))))
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
                                                                                                              writeReg SEE 3383
                                                                                                              let D :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  22
                                                                                                                  1)
                                                                                                              let Vn :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  4)
                                                                                                              let Vd :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  12
                                                                                                                  4)
                                                                                                              let N :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  7
                                                                                                                  1)
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
                                                                                                              (decode_aarch32_instrs_VBIC_r_T1enc_A_txt
                                                                                                                D
                                                                                                                Vn
                                                                                                                Vd
                                                                                                                N
                                                                                                                Q
                                                                                                                M
                                                                                                                Vm)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__480 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         23)) == (0b111111110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           11
                                                                                                                           8)) == (0x1#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           4
                                                                                                                           4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__479 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__479 <b 3385) : Bool))))
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
                                                                                                                  writeReg SEE 3385
                                                                                                                  let D :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      22
                                                                                                                      1)
                                                                                                                  let op :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      20
                                                                                                                      2)
                                                                                                                  let Vn :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      4)
                                                                                                                  let Vd :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      12
                                                                                                                      4)
                                                                                                                  let N :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      7
                                                                                                                      1)
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
                                                                                                                  (decode_aarch32_instrs_VBIF_T1enc_A_txt
                                                                                                                    D
                                                                                                                    op
                                                                                                                    Vn
                                                                                                                    Vd
                                                                                                                    N
                                                                                                                    Q
                                                                                                                    M
                                                                                                                    Vm)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__482 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               21
                                                                                                                               20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 17
                                                                                                                                 16)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   11
                                                                                                                                   11)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     9
                                                                                                                                     7)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     4
                                                                                                                                     4)) == (0#1 : (BitVec 1)))))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__481 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__481 <b 3387) : Bool))))
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
                                                                                                                      writeReg SEE 3387
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
                                                                                                                      let F :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          10
                                                                                                                          1)
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
                                                                                                                      (decode_aarch32_instrs_VCEQ_i_T1enc_A_txt
                                                                                                                        D
                                                                                                                        size
                                                                                                                        Vd
                                                                                                                        F
                                                                                                                        Q
                                                                                                                        M
                                                                                                                        Vm)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__484 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 23)) == (0b111111110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   11
                                                                                                                                   8)) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   4
                                                                                                                                   4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__483 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__483 <b 3390) : Bool))))
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
                                                                                                                          writeReg SEE 3390
                                                                                                                          let D :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              22
                                                                                                                              1)
                                                                                                                          let size :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              20
                                                                                                                              2)
                                                                                                                          let Vn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              4)
                                                                                                                          let Vd :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              12
                                                                                                                              4)
                                                                                                                          let N :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              7
                                                                                                                              1)
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
                                                                                                                          (decode_aarch32_instrs_VCEQ_r_T1enc_A_txt
                                                                                                                            D
                                                                                                                            size
                                                                                                                            Vn
                                                                                                                            Vd
                                                                                                                            N
                                                                                                                            Q
                                                                                                                            M
                                                                                                                            Vm)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__486 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     23)) == (0b111011110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       21
                                                                                                                                       21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         11
                                                                                                                                         8)) == (0xE#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         4
                                                                                                                                         4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__485 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__485 <b 3391) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__486 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 3391
                                                                                                                              let D :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  22
                                                                                                                                  1)
                                                                                                                              let sz :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  20
                                                                                                                                  1)
                                                                                                                              let Vn :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
                                                                                                                                  4)
                                                                                                                              let Vd :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  12
                                                                                                                                  4)
                                                                                                                              let N :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  7
                                                                                                                                  1)
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
                                                                                                                              (decode_aarch32_instrs_VCEQ_r_T2enc_A_txt
                                                                                                                                D
                                                                                                                                sz
                                                                                                                                Vn
                                                                                                                                Vd
                                                                                                                                N
                                                                                                                                Q
                                                                                                                                M
                                                                                                                                Vm)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__488 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           21
                                                                                                                                           20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             17
                                                                                                                                             16)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               11
                                                                                                                                               11)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 9
                                                                                                                                                 7)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 4
                                                                                                                                                 4)) == (0#1 : (BitVec 1)))))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__487 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__487 <b 3393) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__488 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 3393
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
                                                                                                                                  let F :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      10
                                                                                                                                      1)
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
                                                                                                                                  (decode_aarch32_instrs_VCGE_i_T1enc_A_txt
                                                                                                                                    D
                                                                                                                                    size
                                                                                                                                    Vd
                                                                                                                                    F
                                                                                                                                    Q
                                                                                                                                    M
                                                                                                                                    Vm)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (pure true))))))))))))))))))))))))))))))))


end ArmFull.Functions
