import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0151
import ArmFull.Fn.M0164
import ArmFull.Fn.M0226
import ArmFull.Fn.M0236
import ArmFull.Fn.M0248
import ArmFull.Fn.M0839
import ArmFull.Fn.M0842
import ArmFull.Fn.M0928
import ArmFull.Fn.M1290
import ArmFull.Fn.M1291

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
def __DecodeA32_DataProMisc__seg4 (pc : Int) (__opcode : (BitVec 32)) : SailM Unit := do
  let w__359 ← (( do
    if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb __opcode 27 23)) == (0b00010#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
               __opcode 21 20)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                 __opcode 11 9)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                 __opcode 7 0)) == (0x00#8 : (BitVec 8)))))) : Bool) : Bool)
    then
      (do
        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
        then
          (do
            let w__357 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__357 <b 3780) : Bool))))
        else (pure false))
    else (pure false) ) : SailM Bool )
  if (w__359 : Bool)
  then
    (do
      writeReg SEE 3780
      let cond := (BitVec.slice __opcode 28 4)
      let R := (BitVec.slice __opcode 22 1)
      let M1 := (BitVec.slice __opcode 16 4)
      let Rd := (BitVec.slice __opcode 12 4)
      let M := (BitVec.slice __opcode 8 1)
      if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 10)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                         __opcode 11)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                       __opcode 0)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                     __opcode 1)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   __opcode 2)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 __opcode 3)])) != 0#1)) : Bool)
      then sailThrow ((Error_ConstrainedUnpredictable ()))
      else
        (do
          (decode_aarch32_instrs_MRS_br_A1enc_AS_txt cond R M1 Rd M)))
  else
    (do
      let w__362 ← (( do
        if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb __opcode 27 23)) == (0b00010#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                   __opcode 21 20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                     __opcode 15 9)) == (0b1111001#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                     __opcode 7 4)) == (0x0#4 : (BitVec 4)))))) : Bool) : Bool)
        then
          (do
            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
            then
              (do
                let w__360 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__360 <b 3782) : Bool))))
            else (pure false))
        else (pure false) ) : SailM Bool )
      if (w__362 : Bool)
      then
        (do
          writeReg SEE 3782
          let cond := (BitVec.slice __opcode 28 4)
          let R := (BitVec.slice __opcode 22 1)
          let M1 := (BitVec.slice __opcode 16 4)
          let M := (BitVec.slice __opcode 8 1)
          let Rn := (BitVec.slice __opcode 0 4)
          if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 12)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                             __opcode 13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                           __opcode 14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                         __opcode 15)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                       __opcode 10)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                     __opcode 11)])) != 0#1)) : Bool)
          then sailThrow ((Error_ConstrainedUnpredictable ()))
          else
            (do
              (decode_aarch32_instrs_MSR_br_A1enc_AS_txt cond R M1 M Rn)))
      else
        (do
          let w__365 ← (( do
            if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb __opcode 27 23)) == (0b00110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                       __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                       __opcode 15 12)) == (0xF#4 : (BitVec 4))))) : Bool) : Bool)
            then
              (do
                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                then
                  (do
                    let w__363 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__363 <b 3784) : Bool))))
                else (pure false))
            else (pure false) ) : SailM Bool )
          if (w__365 : Bool)
          then
            (do
              writeReg SEE 3784
              let cond := (BitVec.slice __opcode 28 4)
              let R := (BitVec.slice __opcode 22 1)
              let mask := (BitVec.slice __opcode 16 4)
              let imm12 := (BitVec.slice __opcode 0 12)
              if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 12)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                             __opcode 13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                           __opcode 14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                         __opcode 15)])) != 1#1)) : Bool)
              then sailThrow ((Error_ConstrainedUnpredictable ()))
              else
                (do
                  (decode_aarch32_instrs_MSR_i_A1enc_AS_txt cond R mask imm12)))
          else
            (do
              let w__368 ← (( do
                if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb __opcode 27 23)) == (0b00010#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                           __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                           __opcode 15 4)) == (0xF00#12 : (BitVec 12))))) : Bool) : Bool)
                then
                  (do
                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                    then
                      (do
                        let w__366 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__366 <b 3785) : Bool))))
                    else (pure false))
                else (pure false) ) : SailM Bool )
              if (w__368 : Bool)
              then
                (do
                  writeReg SEE 3785
                  let cond := (BitVec.slice __opcode 28 4)
                  let R := (BitVec.slice __opcode 22 1)
                  let mask := (BitVec.slice __opcode 16 4)
                  let Rn := (BitVec.slice __opcode 0 4)
                  if (((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 12)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                       __opcode 13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                     __opcode 14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                   __opcode 15)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                 __opcode 10)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                               __opcode 11)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                             __opcode 8)])) != 0#1)) : Bool)
                  then sailThrow ((Error_ConstrainedUnpredictable ()))
                  else
                    (do
                      (decode_aarch32_instrs_MSR_r_A1enc_AS_txt cond R mask Rn)))
              else
                (do
                  let w__371 ← (( do
                    if ((((Sail.BitVec.castWidth (m := 24) (Sail.BitVec.extractLsb __opcode 27 4)) == (0x160007#24 : (BitVec 24))) : Bool) : Bool)
                    then
                      (do
                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                        then
                          (do
                            let w__369 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__369 <b 3790) : Bool))))
                        else (pure false))
                    else (pure false) ) : SailM Bool )
                  if (w__371 : Bool)
                  then
                    (do
                      writeReg SEE 3790
                      let cond := (BitVec.slice __opcode 28 4)
                      let imm4 := (BitVec.slice __opcode 0 4)
                      if ((((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 8)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                     __opcode 9)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                   __opcode 10)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                 __opcode 11)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                               __opcode 12)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                             __opcode 13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                           __opcode 14)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                         __opcode 15)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                       __opcode 16)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                     __opcode 17)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                   __opcode 18)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                 __opcode 19)])) != 0#1)) : Bool)
                      then sailThrow ((Error_ConstrainedUnpredictable ()))
                      else
                        (do
                          (decode_aarch32_instrs_SMC_A1enc_AS_txt cond imm4)))
                  else
                    (do
                      let w__374 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb __opcode 27
                                 23)) == (0b00010#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                   __opcode 20 20)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                     __opcode 11 10)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                     __opcode 8 4)) == (0b00100#5 : (BitVec 5)))))) : Bool) : Bool)
                        then
                          (do
                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                            then
                              (do
                                let w__372 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__372 <b 3808) : Bool))))
                            else (pure false))
                        else (pure false) ) : SailM Bool )
                      if (w__374 : Bool)
                      then
                        (do
                          writeReg SEE 3808
                          let cond := (BitVec.slice __opcode 28 4)
                          let sz := (BitVec.slice __opcode 21 2)
                          let Rn := (BitVec.slice __opcode 16 4)
                          let Rd := (BitVec.slice __opcode 12 4)
                          let C := (BitVec.slice __opcode 9 1)
                          let Rm := (BitVec.slice __opcode 0 4)
                          if (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 10)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                       __opcode 11)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                     __opcode 8)])) != 0#1)) : Bool)
                          then sailThrow ((Error_ConstrainedUnpredictable ()))
                          else
                            (do
                              (decode_aarch32_instrs_CRC32_A1enc_A_txt cond sz Rn Rd C Rm)))
                      else
                        (do
                          let w__377 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode
                                     27 20)) == (0x10#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                     __opcode 7 4)) == (0x7#4 : (BitVec 4)))) : Bool) : Bool)
                            then
                              (do
                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                then
                                  (do
                                    let w__375 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__375 <b 3813) : Bool))))
                                else (pure false))
                            else (pure false) ) : SailM Bool )
                          if (w__377 : Bool)
                          then
                            (do
                              writeReg SEE 3813
                              let cond := (BitVec.slice __opcode 28 4)
                              let imm12 := (BitVec.slice __opcode 8 12)
                              let imm4 := (BitVec.slice __opcode 0 4)
                              (decode_aarch32_instrs_HLT_A1enc_A_txt cond imm12 imm4))
                          else
                            (do
                              let w__380 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                         __opcode 27 20)) == (0x19#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                         __opcode 11 0)) == (0xC9F#12 : (BitVec 12)))) : Bool) : Bool)
                                then
                                  (do
                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28
                                           4)) != 0b1111#4) : Bool) : Bool)
                                    then
                                      (do
                                        let w__378 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__378 <b 3815) : Bool))))
                                    else (pure false))
                                else (pure false) ) : SailM Bool )
                              if (w__380 : Bool)
                              then
                                (do
                                  writeReg SEE 3815
                                  let cond := (BitVec.slice __opcode 28 4)
                                  let Rn := (BitVec.slice __opcode 16 4)
                                  let Rt := (BitVec.slice __opcode 12 4)
                                  if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                     __opcode 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                     __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                   __opcode 0)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                 __opcode 1)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                               __opcode 2)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                             __opcode 3)])) != 1#1)) : Bool)
                                  then sailThrow ((Error_ConstrainedUnpredictable ()))
                                  else
                                    (do
                                      (decode_aarch32_instrs_LDA_A1enc_A_txt cond Rn Rt)))
                              else
                                (do
                                  let w__383 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                             __opcode 27 20)) == (0x1D#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                             __opcode 11 0)) == (0xC9F#12 : (BitVec 12)))) : Bool) : Bool)
                                    then
                                      (do
                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode
                                               28 4)) != 0b1111#4) : Bool) : Bool)
                                        then
                                          (do
                                            let w__381 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__381 <b 3817) : Bool))))
                                        else (pure false))
                                    else (pure false) ) : SailM Bool )
                                  if (w__383 : Bool)
                                  then
                                    (do
                                      writeReg SEE 3817
                                      let cond := (BitVec.slice __opcode 28 4)
                                      let Rn := (BitVec.slice __opcode 16 4)
                                      let Rt := (BitVec.slice __opcode 12 4)
                                      if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                         __opcode 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                         __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                       __opcode 0)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                     __opcode 1)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                   __opcode 2)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                 __opcode 3)])) != 1#1)) : Bool)
                                      then sailThrow ((Error_ConstrainedUnpredictable ()))
                                      else
                                        (do
                                          (decode_aarch32_instrs_LDAB_A1enc_A_txt cond Rn Rt)))
                                  else
                                    (do
                                      let w__386 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                 __opcode 27 20)) == (0x19#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                 __opcode 11 0)) == (0xE9F#12 : (BitVec 12)))) : Bool) : Bool)
                                        then
                                          (do
                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                   __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                            then
                                              (do
                                                let w__384 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__384 <b 3819) : Bool))))
                                            else (pure false))
                                        else (pure false) ) : SailM Bool )
                                      if (w__386 : Bool)
                                      then
                                        (do
                                          writeReg SEE 3819
                                          let cond := (BitVec.slice __opcode 28 4)
                                          let Rn := (BitVec.slice __opcode 16 4)
                                          let Rt := (BitVec.slice __opcode 12 4)
                                          if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                             __opcode 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                             __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                           __opcode 0)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                         __opcode 1)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                       __opcode 2)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                     __opcode 3)])) != 1#1)) : Bool)
                                          then sailThrow ((Error_ConstrainedUnpredictable ()))
                                          else
                                            (do
                                              (decode_aarch32_instrs_LDAEX_A1enc_A_txt cond Rn Rt)))
                                      else
                                        (do
                                          let w__389 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                     __opcode 27 20)) == (0x1D#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                     __opcode 11 0)) == (0xE9F#12 : (BitVec 12)))) : Bool) : Bool)
                                            then
                                              (do
                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                       __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__387 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__387 <b 3821) : Bool))))
                                                else (pure false))
                                            else (pure false) ) : SailM Bool )
                                          if (w__389 : Bool)
                                          then
                                            (do
                                              writeReg SEE 3821
                                              let cond := (BitVec.slice __opcode 28 4)
                                              let Rn := (BitVec.slice __opcode 16 4)
                                              let Rt := (BitVec.slice __opcode 12 4)
                                              if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                 __opcode 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                 __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                               __opcode 0)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                             __opcode 1)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                           __opcode 2)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                         __opcode 3)])) != 1#1)) : Bool)
                                              then sailThrow ((Error_ConstrainedUnpredictable ()))
                                              else
                                                (do
                                                  (decode_aarch32_instrs_LDAEXB_A1enc_A_txt cond Rn
                                                    Rt)))
                                          else
                                            (do
                                              let w__392 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                         __opcode 27 20)) == (0x1B#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                         __opcode 11 0)) == (0xE9F#12 : (BitVec 12)))) : Bool) : Bool)
                                                then
                                                  (do
                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                           __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__390 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__390 <b 3823) : Bool))))
                                                    else (pure false))
                                                else (pure false) ) : SailM Bool )
                                              if (w__392 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 3823
                                                  let cond := (BitVec.slice __opcode 28 4)
                                                  let Rn := (BitVec.slice __opcode 16 4)
                                                  let Rt := (BitVec.slice __opcode 12 4)
                                                  if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                     __opcode 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                     __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                   __opcode 0)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                 __opcode 1)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                               __opcode 2)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                             __opcode 3)])) != 1#1)) : Bool)
                                                  then
                                                    sailThrow ((Error_ConstrainedUnpredictable ()))
                                                  else
                                                    (do
                                                      (decode_aarch32_instrs_LDAEXD_A1enc_A_txt cond
                                                        Rn Rt)))
                                              else
                                                (do
                                                  let w__395 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                             __opcode 27 20)) == (0x1F#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                             __opcode 11 0)) == (0xE9F#12 : (BitVec 12)))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                               __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__393 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__393 <b 3825) : Bool))))
                                                        else (pure false))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__395 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 3825
                                                      let cond := (BitVec.slice __opcode 28 4)
                                                      let Rn := (BitVec.slice __opcode 16 4)
                                                      let Rt := (BitVec.slice __opcode 12 4)
                                                      if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                         __opcode 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                         __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                       __opcode 0)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                     __opcode 1)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                   __opcode 2)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                 __opcode 3)])) != 1#1)) : Bool)
                                                      then
                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                          ()))
                                                      else
                                                        (do
                                                          (decode_aarch32_instrs_LDAEXH_A1enc_A_txt
                                                            cond Rn Rt)))
                                                  else
                                                    (do
                                                      let w__398 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                 __opcode 27 20)) == (0x1F#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                 __opcode 11 0)) == (0xC9F#12 : (BitVec 12)))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                   __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__396 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__396 <b 3827) : Bool))))
                                                            else (pure false))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__398 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 3827
                                                          let cond := (BitVec.slice __opcode 28 4)
                                                          let Rn := (BitVec.slice __opcode 16 4)
                                                          let Rt := (BitVec.slice __opcode 12 4)
                                                          if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                             __opcode 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                             __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                           __opcode 0)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                         __opcode 1)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                       __opcode 2)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                     __opcode 3)])) != 1#1)) : Bool)
                                                          then
                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                              ()))
                                                          else
                                                            (do
                                                              (decode_aarch32_instrs_LDAH_A1enc_A_txt
                                                                cond Rn Rt)))
                                                      else
                                                        (do
                                                          let w__401 ← (( do
                                                            if ((((Sail.BitVec.castWidth (m := 28) (Sail.BitVec.extractLsb
                                                                   __opcode 27 0)) == (0x320F005#28 : (BitVec 28))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                       __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__399 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__399 <b 3829) : Bool))))
                                                                else (pure false))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__401 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 3829
                                                              let cond :=
                                                                (BitVec.slice __opcode 28 4)
                                                              if ((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                     __opcode 12)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                     __opcode 13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                   __opcode 14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                 __opcode 15)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                               __opcode 8)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                             __opcode 9)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                           __opcode 10)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                         __opcode 11)])) != 0#1)) : Bool)
                                                              then
                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                  ()))
                                                              else
                                                                (do
                                                                  (decode_aarch32_instrs_SEVL_A1enc_A_txt
                                                                    cond)))
                                                          else
                                                            (do
                                                              let w__404 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                         __opcode 27 20)) == (0x18#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                         __opcode 15 4)) == (0xFC9#12 : (BitVec 12)))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                           __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__402 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__402 <b 3852) : Bool))))
                                                                    else (pure false))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__404 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 3852
                                                                  let cond :=
                                                                    (BitVec.slice __opcode 28 4)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 16 4)
                                                                  let Rt :=
                                                                    (BitVec.slice __opcode 0 4)
                                                                  if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                     __opcode 12)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                     __opcode 13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                   __opcode 14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                 __opcode 15)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                               __opcode 8)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                             __opcode 9)])) != 1#1)) : Bool)
                                                                  then
                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                      ()))
                                                                  else
                                                                    (do
                                                                      (decode_aarch32_instrs_STL_A1enc_A_txt
                                                                        cond Rn Rt)))
                                                              else
                                                                (do
                                                                  let w__407 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                             __opcode 27 20)) == (0x1C#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                             __opcode 15 4)) == (0xFC9#12 : (BitVec 12)))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                               __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__405 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__405 <b 3854) : Bool))))
                                                                        else (pure false))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__407 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 3854
                                                                      let cond :=
                                                                        (BitVec.slice __opcode 28 4)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 16 4)
                                                                      let Rt :=
                                                                        (BitVec.slice __opcode 0 4)
                                                                      if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 12)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                       __opcode 14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                     __opcode 15)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                   __opcode 8)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                 __opcode 9)])) != 1#1)) : Bool)
                                                                      then
                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                          ()))
                                                                      else
                                                                        (do
                                                                          (decode_aarch32_instrs_STLB_A1enc_A_txt
                                                                            cond Rn Rt)))
                                                                  else
                                                                    (do
                                                                      let w__410 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                 __opcode 27 20)) == (0x18#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                 __opcode 11 4)) == (0xE9#8 : (BitVec 8)))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                   __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__408 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__408 <b 3856) : Bool))))
                                                                            else (pure false))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__410 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 3856
                                                                          let cond :=
                                                                            (BitVec.slice __opcode
                                                                              28 4)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode
                                                                              16 4)
                                                                          let Rd :=
                                                                            (BitVec.slice __opcode
                                                                              12 4)
                                                                          let Rt :=
                                                                            (BitVec.slice __opcode 0
                                                                              4)
                                                                          if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                     __opcode 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                     __opcode 9)])) != 1#1)) : Bool)
                                                                          then
                                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                                              ()))
                                                                          else
                                                                            (do
                                                                              (decode_aarch32_instrs_STLEX_A1enc_A_txt
                                                                                cond Rn Rd Rt)))
                                                                      else
                                                                        (do
                                                                          let w__413 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                     __opcode 27 20)) == (0x1C#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                     __opcode 11 4)) == (0xE9#8 : (BitVec 8)))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                       __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__411 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__411 <b 3858) : Bool))))
                                                                                else (pure false))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__413 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 3858
                                                                              let cond :=
                                                                                (BitVec.slice
                                                                                  __opcode 28 4)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 4)
                                                                              let Rd :=
                                                                                (BitVec.slice
                                                                                  __opcode 12 4)
                                                                              let Rt :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 4)
                                                                              if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 9)])) != 1#1)) : Bool)
                                                                              then
                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                  ()))
                                                                              else
                                                                                (do
                                                                                  (decode_aarch32_instrs_STLEXB_A1enc_A_txt
                                                                                    cond Rn Rd Rt)))
                                                                          else
                                                                            (do
                                                                              let w__416 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                         __opcode 27
                                                                                         20)) == (0x1A#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                         __opcode 11
                                                                                         4)) == (0xE9#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                           __opcode
                                                                                           28 4)) != 0b1111#4) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__414 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__414 <b 3860) : Bool))))
                                                                                    else
                                                                                      (pure false))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__416 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 3860
                                                                                  let cond :=
                                                                                    (BitVec.slice
                                                                                      __opcode 28 4)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 4)
                                                                                  let Rd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 12 4)
                                                                                  let Rt :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 4)
                                                                                  if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                             __opcode
                                                                                             8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                             __opcode
                                                                                             9)])) != 1#1)) : Bool)
                                                                                  then
                                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                                      ()))
                                                                                  else
                                                                                    (do
                                                                                      (decode_aarch32_instrs_STLEXD_A1enc_A_txt
                                                                                        cond Rn Rd
                                                                                        Rt)))
                                                                              else
                                                                                (do
                                                                                  let w__419 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             27 20)) == (0x1E#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             11 4)) == (0xE9#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                               __opcode
                                                                                               28 4)) != 0b1111#4) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__417 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__417 <b 3862) : Bool))))
                                                                                        else
                                                                                          (pure false))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__419 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 3862
                                                                                      let cond :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          28 4)
                                                                                      let Rn :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 4)
                                                                                      let Rd :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          12 4)
                                                                                      let Rt :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          4)
                                                                                      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                 __opcode
                                                                                                 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                 __opcode
                                                                                                 9)])) != 1#1)) : Bool)
                                                                                      then
                                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                                          ()))
                                                                                      else
                                                                                        (do
                                                                                          (decode_aarch32_instrs_STLEXH_A1enc_A_txt
                                                                                            cond Rn
                                                                                            Rd Rt)))
                                                                                  else
                                                                                    (do
                                                                                      let w__422 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 27
                                                                                                 20)) == (0x1E#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 15
                                                                                                 4)) == (0xFC9#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                   __opcode
                                                                                                   28
                                                                                                   4)) != 0b1111#4) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__420 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__420 <b 3864) : Bool))))
                                                                                            else
                                                                                              (pure false))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__422 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 3864
                                                                                          let cond :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              28 4)
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 4)
                                                                                          let Rt :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 4)
                                                                                          if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                             __opcode
                                                                                                             12)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                             __opcode
                                                                                                             13)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                           __opcode
                                                                                                           14)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                         __opcode
                                                                                                         15)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                       __opcode
                                                                                                       8)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                     __opcode
                                                                                                     9)])) != 1#1)) : Bool)
                                                                                          then
                                                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                                                              ()))
                                                                                          else
                                                                                            (do
                                                                                              (decode_aarch32_instrs_STLH_A1enc_A_txt
                                                                                                cond
                                                                                                Rn
                                                                                                Rt)))
                                                                                      else
                                                                                        (do
                                                                                          let w__425 ← (( do
                                                                                            if ((((Sail.BitVec.castWidth (m := 28) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   27
                                                                                                   0)) == (0x320F010#28 : (BitVec 28))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                       __opcode
                                                                                                       28
                                                                                                       4)) != 0b1111#4) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__423 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__423 <b 3890) : Bool))))
                                                                                                else
                                                                                                  (pure false))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__425 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 3890
                                                                                              let cond :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  28
                                                                                                  4)
                                                                                              if ((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                     __opcode
                                                                                                                     8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                     __opcode
                                                                                                                     9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                   __opcode
                                                                                                                   10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                 __opcode
                                                                                                                 11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                               __opcode
                                                                                                               12)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
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
                                                                                                  (decode_aarch32_instrs_ESB_A1enc_A_txt
                                                                                                    cond)))
                                                                                          else
                                                                                            (do
                                                                                              let w__428 ← (( do
                                                                                                if ((((Sail.BitVec.castWidth (m := 28) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       27
                                                                                                       0)) == (0x320F012#28 : (BitVec 28))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                           __opcode
                                                                                                           28
                                                                                                           4)) != 0b1111#4) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__426 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__426 <b 3892) : Bool))))
                                                                                                    else
                                                                                                      (pure false))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__428 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 3892
                                                                                                  let cond :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      28
                                                                                                      4)
                                                                                                  if ((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                         __opcode
                                                                                                                         8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                         __opcode
                                                                                                                         9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                       __opcode
                                                                                                                       10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                     __opcode
                                                                                                                     11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                   __opcode
                                                                                                                   12)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
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
                                                                                                      (decode_aarch32_instrs_TSB_A1enc_A_txt
                                                                                                        cond)))
                                                                                              else
                                                                                                (do
                                                                                                  let w__431 ← (( do
                                                                                                    if ((((Sail.BitVec.castWidth (m := 28) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           27
                                                                                                           0)) == (0x320F014#28 : (BitVec 28))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                               __opcode
                                                                                                               28
                                                                                                               4)) != 0b1111#4) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__429 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__429 <b 3894) : Bool))))
                                                                                                        else
                                                                                                          (pure false))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__431 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 3894
                                                                                                      let cond :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          28
                                                                                                          4)
                                                                                                      if ((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                             __opcode
                                                                                                                             8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                             __opcode
                                                                                                                             9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                           __opcode
                                                                                                                           10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                         __opcode
                                                                                                                         11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                       __opcode
                                                                                                                       12)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
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
                                                                                                          (decode_aarch32_instrs_CSDB_A1enc_A_txt
                                                                                                            cond)))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__434 ← (( do
                                                                                                        if ((((Sail.BitVec.castWidth (m := 28) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               27
                                                                                                               0)) == (0x320F016#28 : (BitVec 28))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                   __opcode
                                                                                                                   28
                                                                                                                   4)) != 0b1111#4) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__432 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__432 <b 3938) : Bool))))
                                                                                                            else
                                                                                                              (pure false))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__434 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 3938
                                                                                                          let cond :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              28
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
                                                                                                              (decode_aarch32_instrs_CLRBHB_A1enc_A_txt
                                                                                                                cond)))
                                                                                                      else
                                                                                                        sailThrow ((Error_Undefined
                                                                                                          ())))))))))))))))))))))))))))


end ArmFull.Functions
