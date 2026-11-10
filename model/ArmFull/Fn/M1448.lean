import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0151
import ArmFull.Fn.M1076
import ArmFull.Fn.M1094
import ArmFull.Fn.M1095
import ArmFull.Fn.M1147
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
def __DecodeT32__seg13 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__912 ← (( do
    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xE8D#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
             __opcode 11 0)) == (0xFCF#12 : (BitVec 12)))) : Bool) : Bool)
    then
      (do
        let w__911 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__911 <b 3822) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__912 : Bool)
  then
    (do
      writeReg SEE 3822
      let Rn := (BitVec.slice __opcode 16 4)
      let Rt := (BitVec.slice __opcode 12 4)
      if ((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                             __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                           __opcode 10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                         __opcode 11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                       __opcode 0)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                     __opcode 1)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   __opcode 2)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 __opcode 3)])) != 1#1)) : Bool)
      then sailThrow ((Error_ConstrainedUnpredictable ()))
      else
        (do
          (decode_aarch32_instrs_LDAEXB_T1enc_A_txt Rn Rt))
      (pure false))
  else
    (do
      let w__914 ← (( do
        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xE8D#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                 __opcode 7 0)) == (0xFF#8 : (BitVec 8)))) : Bool) : Bool)
        then
          (do
            let w__913 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__913 <b 3824) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__914 : Bool)
      then
        (do
          writeReg SEE 3824
          let Rn := (BitVec.slice __opcode 16 4)
          let Rt := (BitVec.slice __opcode 12 4)
          let Rt2 := (BitVec.slice __opcode 8 4)
          if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 0)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                         __opcode 1)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                       __opcode 2)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                     __opcode 3)])) != 1#1)) : Bool)
          then sailThrow ((Error_ConstrainedUnpredictable ()))
          else
            (do
              (decode_aarch32_instrs_LDAEXD_T1enc_A_txt Rn Rt Rt2))
          (pure false))
      else
        (do
          let w__916 ← (( do
            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xE8D#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                     __opcode 11 0)) == (0xFDF#12 : (BitVec 12)))) : Bool) : Bool)
            then
              (do
                let w__915 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__915 <b 3826) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__916 : Bool)
          then
            (do
              writeReg SEE 3826
              let Rn := (BitVec.slice __opcode 16 4)
              let Rt := (BitVec.slice __opcode 12 4)
              if ((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                     __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                   __opcode 10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                 __opcode 11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                               __opcode 0)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                             __opcode 1)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                           __opcode 2)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                         __opcode 3)])) != 1#1)) : Bool)
              then sailThrow ((Error_ConstrainedUnpredictable ()))
              else
                (do
                  (decode_aarch32_instrs_LDAEXH_T1enc_A_txt Rn Rt))
              (pure false))
          else
            (do
              let w__918 ← (( do
                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xE8D#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                         __opcode 11 0)) == (0xF9F#12 : (BitVec 12)))) : Bool) : Bool)
                then
                  (do
                    let w__917 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__917 <b 3828) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__918 : Bool)
              then
                (do
                  writeReg SEE 3828
                  let Rn := (BitVec.slice __opcode 16 4)
                  let Rt := (BitVec.slice __opcode 12 4)
                  if ((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                         __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                       __opcode 10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                     __opcode 11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                   __opcode 0)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                 __opcode 1)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                               __opcode 2)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                             __opcode 3)])) != 1#1)) : Bool)
                  then sailThrow ((Error_ConstrainedUnpredictable ()))
                  else
                    (do
                      (decode_aarch32_instrs_LDAH_T1enc_A_txt Rn Rt))
                  (pure false))
              else
                (do
                  let w__920 ← (( do
                    if (((__opcode == 0b11110011101011111000000000000101#32) : Bool) : Bool)
                    then
                      (do
                        let w__919 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__919 <b 3831) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__920 : Bool)
                  then
                    (do
                      writeReg SEE 3831
                      if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                         __opcode 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                       __opcode 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                     __opcode 19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                   __opcode 13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                 __opcode 11)])) != 0#1)) : Bool)
                      then sailThrow ((Error_ConstrainedUnpredictable ()))
                      else
                        (do
                          (decode_aarch32_instrs_SEVL_T2enc_A_txt ()))
                      (pure false))
                  else
                    (do
                      let w__922 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31
                                 23)) == (0b111011110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                   __opcode 21 20)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                     __opcode 11 8)) == (0xC#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                     __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                        then
                          (do
                            let w__921 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__921 <b 3833) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__922 : Bool)
                      then
                        (do
                          writeReg SEE 3833
                          let D := (BitVec.slice __opcode 22 1)
                          let Vn := (BitVec.slice __opcode 16 4)
                          let Vd := (BitVec.slice __opcode 12 4)
                          let N := (BitVec.slice __opcode 7 1)
                          let Q := (BitVec.slice __opcode 6 1)
                          let M := (BitVec.slice __opcode 5 1)
                          let Vm := (BitVec.slice __opcode 0 4)
                          (decode_aarch32_instrs_SHA1C_T1enc_A_txt D Vn Vd N Q M Vm)
                          (pure false))
                      else
                        (do
                          let w__924 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode
                                     31 23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                       __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                         __opcode 17 16)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                           __opcode 11 6)) == (0b001011#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                           __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                            then
                              (do
                                let w__923 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__923 <b 3835) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__924 : Bool)
                          then
                            (do
                              writeReg SEE 3835
                              let D := (BitVec.slice __opcode 22 1)
                              let size := (BitVec.slice __opcode 18 2)
                              let Vd := (BitVec.slice __opcode 12 4)
                              let M := (BitVec.slice __opcode 5 1)
                              let Vm := (BitVec.slice __opcode 0 4)
                              (decode_aarch32_instrs_SHA1H_T1enc_A_txt D size Vd M Vm)
                              (pure false))
                          else
                            (do
                              let w__926 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                         __opcode 31 23)) == (0b111011110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                           __opcode 21 20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                             __opcode 11 8)) == (0xC#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__925 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__925 <b 3837) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__926 : Bool)
                              then
                                (do
                                  writeReg SEE 3837
                                  let D := (BitVec.slice __opcode 22 1)
                                  let Vn := (BitVec.slice __opcode 16 4)
                                  let Vd := (BitVec.slice __opcode 12 4)
                                  let N := (BitVec.slice __opcode 7 1)
                                  let Q := (BitVec.slice __opcode 6 1)
                                  let M := (BitVec.slice __opcode 5 1)
                                  let Vm := (BitVec.slice __opcode 0 4)
                                  (decode_aarch32_instrs_SHA1M_T1enc_A_txt D Vn Vd N Q M Vm)
                                  (pure false))
                              else
                                (do
                                  let w__928 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                             __opcode 31 23)) == (0b111011110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                               __opcode 21 20)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                 __opcode 11 8)) == (0xC#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__927 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__927 <b 3839) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__928 : Bool)
                                  then
                                    (do
                                      writeReg SEE 3839
                                      let D := (BitVec.slice __opcode 22 1)
                                      let Vn := (BitVec.slice __opcode 16 4)
                                      let Vd := (BitVec.slice __opcode 12 4)
                                      let N := (BitVec.slice __opcode 7 1)
                                      let Q := (BitVec.slice __opcode 6 1)
                                      let M := (BitVec.slice __opcode 5 1)
                                      let Vm := (BitVec.slice __opcode 0 4)
                                      (decode_aarch32_instrs_SHA1P_T1enc_A_txt D Vn Vd N Q M Vm)
                                      (pure false))
                                  else
                                    (do
                                      let w__930 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                 __opcode 31 23)) == (0b111011110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                   __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                     __opcode 11 8)) == (0xC#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                     __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__929 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__929 <b 3841) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__930 : Bool)
                                      then
                                        (do
                                          writeReg SEE 3841
                                          let D := (BitVec.slice __opcode 22 1)
                                          let Vn := (BitVec.slice __opcode 16 4)
                                          let Vd := (BitVec.slice __opcode 12 4)
                                          let N := (BitVec.slice __opcode 7 1)
                                          let Q := (BitVec.slice __opcode 6 1)
                                          let M := (BitVec.slice __opcode 5 1)
                                          let Vm := (BitVec.slice __opcode 0 4)
                                          (decode_aarch32_instrs_SHA1SU0_T1enc_A_txt D Vn Vd N Q M
                                            Vm)
                                          (pure false))
                                      else
                                        (do
                                          let w__932 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                     __opcode 31 23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                       __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                         __opcode 17 16)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                           __opcode 11 6)) == (0b001110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__931 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__931 <b 3843) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__932 : Bool)
                                          then
                                            (do
                                              writeReg SEE 3843
                                              let D := (BitVec.slice __opcode 22 1)
                                              let size := (BitVec.slice __opcode 18 2)
                                              let Vd := (BitVec.slice __opcode 12 4)
                                              let M := (BitVec.slice __opcode 5 1)
                                              let Vm := (BitVec.slice __opcode 0 4)
                                              (decode_aarch32_instrs_SHA1SU1_T1enc_A_txt D size Vd M
                                                Vm)
                                              (pure false))
                                          else
                                            (do
                                              let w__934 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                         __opcode 31 23)) == (0b111111110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                           __opcode 21 20)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                             __opcode 11 8)) == (0xC#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                             __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__933 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__933 <b 3845) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__934 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 3845
                                                  let D := (BitVec.slice __opcode 22 1)
                                                  let Vn := (BitVec.slice __opcode 16 4)
                                                  let Vd := (BitVec.slice __opcode 12 4)
                                                  let N := (BitVec.slice __opcode 7 1)
                                                  let Q := (BitVec.slice __opcode 6 1)
                                                  let M := (BitVec.slice __opcode 5 1)
                                                  let Vm := (BitVec.slice __opcode 0 4)
                                                  (decode_aarch32_instrs_SHA256H_T1enc_A_txt D Vn Vd
                                                    N Q M Vm)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__936 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                             __opcode 31 23)) == (0b111111110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                               __opcode 21 20)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                 __opcode 11 8)) == (0xC#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                 __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__935 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__935 <b 3847) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__936 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 3847
                                                      let D := (BitVec.slice __opcode 22 1)
                                                      let Vn := (BitVec.slice __opcode 16 4)
                                                      let Vd := (BitVec.slice __opcode 12 4)
                                                      let N := (BitVec.slice __opcode 7 1)
                                                      let Q := (BitVec.slice __opcode 6 1)
                                                      let M := (BitVec.slice __opcode 5 1)
                                                      let Vm := (BitVec.slice __opcode 0 4)
                                                      (decode_aarch32_instrs_SHA256H2_T1enc_A_txt D
                                                        Vn Vd N Q M Vm)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__938 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                 __opcode 31 23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                   __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                     __opcode 17 16)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                       __opcode 11 6)) == (0b001111#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__937 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__937 <b 3849) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__938 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 3849
                                                          let D := (BitVec.slice __opcode 22 1)
                                                          let size := (BitVec.slice __opcode 18 2)
                                                          let Vd := (BitVec.slice __opcode 12 4)
                                                          let M := (BitVec.slice __opcode 5 1)
                                                          let Vm := (BitVec.slice __opcode 0 4)
                                                          (decode_aarch32_instrs_SHA256SU0_T1enc_A_txt
                                                            D size Vd M Vm)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__940 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                     __opcode 31 23)) == (0b111111110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                       __opcode 21 20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                         __opcode 11 8)) == (0xC#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                         __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__939 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__939 <b 3851) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__940 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 3851
                                                              let D := (BitVec.slice __opcode 22 1)
                                                              let Vn := (BitVec.slice __opcode 16 4)
                                                              let Vd := (BitVec.slice __opcode 12 4)
                                                              let N := (BitVec.slice __opcode 7 1)
                                                              let Q := (BitVec.slice __opcode 6 1)
                                                              let M := (BitVec.slice __opcode 5 1)
                                                              let Vm := (BitVec.slice __opcode 0 4)
                                                              (decode_aarch32_instrs_SHA256SU1_T1enc_A_txt
                                                                D Vn Vd N Q M Vm)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__942 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                         __opcode 31 20)) == (0xE8C#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                         __opcode 11 0)) == (0xFAF#12 : (BitVec 12)))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__941 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__941 <b 3853) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__942 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 3853
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 16 4)
                                                                  let Rt :=
                                                                    (BitVec.slice __opcode 12 4)
                                                                  if ((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                       __opcode 10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                     __opcode 11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                   __opcode 0)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                 __opcode 1)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                               __opcode 2)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                             __opcode 3)])) != 1#1)) : Bool)
                                                                  then
                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                      ()))
                                                                  else
                                                                    (do
                                                                      (decode_aarch32_instrs_STL_T1enc_A_txt
                                                                        Rn Rt))
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__944 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                             __opcode 31 20)) == (0xE8C#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                             __opcode 11 0)) == (0xF8F#12 : (BitVec 12)))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__943 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__943 <b 3855) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__944 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 3855
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 16 4)
                                                                      let Rt :=
                                                                        (BitVec.slice __opcode 12 4)
                                                                      if ((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                             __opcode
                                                                                             8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                             __opcode
                                                                                             9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                           __opcode
                                                                                           10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                       __opcode 0)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                     __opcode 1)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                   __opcode 2)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                 __opcode 3)])) != 1#1)) : Bool)
                                                                      then
                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                          ()))
                                                                      else
                                                                        (do
                                                                          (decode_aarch32_instrs_STLB_T1enc_A_txt
                                                                            Rn Rt))
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__946 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 20)) == (0xE8C#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                 __opcode 11 4)) == (0xFE#8 : (BitVec 8)))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__945 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__945 <b 3857) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__946 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 3857
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode
                                                                              16 4)
                                                                          let Rt :=
                                                                            (BitVec.slice __opcode
                                                                              12 4)
                                                                          let Rd :=
                                                                            (BitVec.slice __opcode 0
                                                                              4)
                                                                          if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                       __opcode 10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                     __opcode 11)])) != 1#1)) : Bool)
                                                                          then
                                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                                              ()))
                                                                          else
                                                                            (do
                                                                              (decode_aarch32_instrs_STLEX_T1enc_A_txt
                                                                                Rn Rt Rd))
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__948 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 20)) == (0xE8C#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                     __opcode 11 4)) == (0xFC#8 : (BitVec 8)))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__947 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__947 <b 3859) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__948 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 3859
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 4)
                                                                              let Rt :=
                                                                                (BitVec.slice
                                                                                  __opcode 12 4)
                                                                              let Rd :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 4)
                                                                              if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                             __opcode
                                                                                             8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
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
                                                                                  (decode_aarch32_instrs_STLEXB_T1enc_A_txt
                                                                                    Rn Rt Rd))
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__950 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         20)) == (0xE8C#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                         __opcode 7
                                                                                         4)) == (0xF#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__949 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__949 <b 3861) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__950 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 3861
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 4)
                                                                                  let Rt :=
                                                                                    (BitVec.slice
                                                                                      __opcode 12 4)
                                                                                  let Rt2 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 8 4)
                                                                                  let Rd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 4)
                                                                                  (decode_aarch32_instrs_STLEXD_T1enc_A_txt
                                                                                    Rn Rt Rt2 Rd)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__952 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 20)) == (0xE8C#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             11 4)) == (0xFD#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__951 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__951 <b 3863) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__952 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 3863
                                                                                      let Rn :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 4)
                                                                                      let Rt :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          12 4)
                                                                                      let Rd :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          4)
                                                                                      if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                     __opcode
                                                                                                     8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
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
                                                                                          (decode_aarch32_instrs_STLEXH_T1enc_A_txt
                                                                                            Rn Rt Rd))
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__954 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 20)) == (0xE8C#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 11
                                                                                                 0)) == (0xF9F#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__953 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__953 <b 3865) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__954 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 3865
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 4)
                                                                                          let Rt :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              12 4)
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
                                                                                                           0)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                         __opcode
                                                                                                         1)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                       __opcode
                                                                                                       2)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                     __opcode
                                                                                                     3)])) != 1#1)) : Bool)
                                                                                          then
                                                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                                                              ()))
                                                                                          else
                                                                                            (do
                                                                                              (decode_aarch32_instrs_STLH_T1enc_A_txt
                                                                                                Rn
                                                                                                Rt))
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__956 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       21
                                                                                                       20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         17
                                                                                                         16)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           11
                                                                                                           10)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           4
                                                                                                           4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__955 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__955 <b 3867) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__956 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 3867
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
                                                                                              let RM :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  8
                                                                                                  2)
                                                                                              let op :=
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
                                                                                              (decode_aarch32_instrs_VCVTA_asimd_T1enc_A_txt
                                                                                                D
                                                                                                size
                                                                                                Vd
                                                                                                RM
                                                                                                op Q
                                                                                                M Vm)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__958 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         23)) == (0b111111101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           21
                                                                                                           18)) == (0xF#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             11
                                                                                                             10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               6
                                                                                                               6)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               4
                                                                                                               4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__957 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__957 <b 3869) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__958 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 3869
                                                                                                  let D :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      22
                                                                                                      1)
                                                                                                  let RM :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      2)
                                                                                                  let Vd :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      12
                                                                                                      4)
                                                                                                  let size :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      8
                                                                                                      2)
                                                                                                  let op :=
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
                                                                                                  (decode_aarch32_instrs_VCVTA_vfp_T1enc_A_txt
                                                                                                    D
                                                                                                    RM
                                                                                                    Vd
                                                                                                    size
                                                                                                    op
                                                                                                    M
                                                                                                    Vm)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__960 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             23)) == (0b111111110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               11
                                                                                                               8)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               4
                                                                                                               4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__959 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__959 <b 3872) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__960 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 3872
                                                                                                      let D :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          22
                                                                                                          1)
                                                                                                      let op :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          21
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
                                                                                                      (decode_aarch32_instrs_VMAXNM_T1enc_A_txt
                                                                                                        D
                                                                                                        op
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
                                                                                                      let w__962 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 23)) == (0b111111101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   21
                                                                                                                   20)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     11
                                                                                                                     10)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     4
                                                                                                                     4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__961 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__961 <b 3873) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__962 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 3873
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
                                                                                                          let size :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              8
                                                                                                              2)
                                                                                                          let N :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              7
                                                                                                              1)
                                                                                                          let op :=
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
                                                                                                          (decode_aarch32_instrs_VMAXNM_T2enc_A_txt
                                                                                                            D
                                                                                                            Vn
                                                                                                            Vd
                                                                                                            size
                                                                                                            N
                                                                                                            op
                                                                                                            M
                                                                                                            Vm)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__964 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       21
                                                                                                                       20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
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
                                                                                                                let w__963 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__963 <b 3875) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__964 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 3875
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
                                                                                                              let op :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  7
                                                                                                                  3)
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
                                                                                                              (decode_aarch32_instrs_VRINTA_asimd_T1enc_A_txt
                                                                                                                D
                                                                                                                size
                                                                                                                Vd
                                                                                                                op
                                                                                                                Q
                                                                                                                M
                                                                                                                Vm)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__966 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         23)) == (0b111111101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           21
                                                                                                                           18)) == (0xE#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             11
                                                                                                                             10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               7
                                                                                                                               6)) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               4
                                                                                                                               4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__965 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__965 <b 3877) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__966 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 3877
                                                                                                                  let D :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      22
                                                                                                                      1)
                                                                                                                  let RM :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      2)
                                                                                                                  let Vd :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      12
                                                                                                                      4)
                                                                                                                  let size :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      8
                                                                                                                      2)
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
                                                                                                                  (decode_aarch32_instrs_VRINTA_vfp_T1enc_A_txt
                                                                                                                    D
                                                                                                                    RM
                                                                                                                    Vd
                                                                                                                    size
                                                                                                                    M
                                                                                                                    Vm)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__968 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
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
                                                                                                                        let w__967 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__967 <b 3879) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__968 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 3879
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
                                                                                                                      (decode_aarch32_instrs_VRINTX_asimd_T1enc_A_txt
                                                                                                                        D
                                                                                                                        size
                                                                                                                        Vd
                                                                                                                        Q
                                                                                                                        M
                                                                                                                        Vm)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__970 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 23)) == (0b111011101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   21
                                                                                                                                   16)) == (0b110111#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     11
                                                                                                                                     10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       7
                                                                                                                                       6)) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       4
                                                                                                                                       4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__969 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__969 <b 3881) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__970 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 3881
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
                                                                                                                          let size :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              8
                                                                                                                              2)
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
                                                                                                                          (decode_aarch32_instrs_VRINTX_vfp_T1enc_A_txt
                                                                                                                            D
                                                                                                                            Vd
                                                                                                                            size
                                                                                                                            M
                                                                                                                            Vm)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__972 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
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
                                                                                                                                let w__971 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__971 <b 3883) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__972 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 3883
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
                                                                                                                              (decode_aarch32_instrs_VRINTZ_asimd_T1enc_A_txt
                                                                                                                                D
                                                                                                                                size
                                                                                                                                Vd
                                                                                                                                Q
                                                                                                                                M
                                                                                                                                Vm)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (pure true)))))))))))))))))))))))))))))))


end ArmFull.Functions
