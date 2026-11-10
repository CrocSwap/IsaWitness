import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0983
import ArmFull.Fn.M1026
import ArmFull.Fn.M1160
import ArmFull.Fn.M1315
import ArmFull.Fn.M1316

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
def __DecodeA64_SVE__seg20 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__1623 ← (( do
    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b100001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
               __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
               __opcode 15 13)) == (0b011#3 : (BitVec 3))))) : Bool) : Bool)
    then
      (do
        let w__1622 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__1622 <b 1848) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1623 : Bool)
  then
    (do
      writeReg SEE 1848
      let xs := (BitVec.slice __opcode 22 1)
      let Zm := (BitVec.slice __opcode 16 5)
      let U := (BitVec.slice __opcode 14 1)
      let ff := (BitVec.slice __opcode 13 1)
      let Pg := (BitVec.slice __opcode 10 3)
      let Rn := (BitVec.slice __opcode 5 5)
      let Zt := (BitVec.slice __opcode 0 5)
      (decode_LDFF1W_Z_P_BZ_S_x32_unscaled xs Zm U ff Pg Rn Zt)
      (pure false))
  else
    (do
      let w__1625 ← (( do
        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b100001000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                   __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                     __opcode 15 13)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                     __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
        then
          (do
            let w__1624 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__1624 <b 1849) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__1625 : Bool)
      then
        (do
          writeReg SEE 1849
          let xs := (BitVec.slice __opcode 22 1)
          let Zm := (BitVec.slice __opcode 16 5)
          let msz := (BitVec.slice __opcode 13 2)
          let Pg := (BitVec.slice __opcode 10 3)
          let Rn := (BitVec.slice __opcode 5 5)
          let prfop := (BitVec.slice __opcode 0 4)
          (decode_PRFB_I_P_BZ_S_x32_scaled xs Zm msz Pg Rn prfop)
          (pure false))
      else
        (do
          let w__1627 ← (( do
            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b100001000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                         __opcode 15 13)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                         __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
            then
              (do
                let w__1626 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__1626 <b 1850) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__1627 : Bool)
          then
            (do
              writeReg SEE 1850
              let xs := (BitVec.slice __opcode 22 1)
              let Zm := (BitVec.slice __opcode 16 5)
              let msz := (BitVec.slice __opcode 13 2)
              let Pg := (BitVec.slice __opcode 10 3)
              let Rn := (BitVec.slice __opcode 5 5)
              let prfop := (BitVec.slice __opcode 0 4)
              (decode_PRFH_I_P_BZ_S_x32_scaled xs Zm msz Pg Rn prfop)
              (pure false))
          else
            (do
              let w__1629 ← (( do
                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b100001000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                             __opcode 15 13)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                             __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                then
                  (do
                    let w__1628 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__1628 <b 1851) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__1629 : Bool)
              then
                (do
                  writeReg SEE 1851
                  let xs := (BitVec.slice __opcode 22 1)
                  let Zm := (BitVec.slice __opcode 16 5)
                  let msz := (BitVec.slice __opcode 13 2)
                  let Pg := (BitVec.slice __opcode 10 3)
                  let Rn := (BitVec.slice __opcode 5 5)
                  let prfop := (BitVec.slice __opcode 0 4)
                  (decode_PRFW_I_P_BZ_S_x32_scaled xs Zm msz Pg Rn prfop)
                  (pure false))
              else
                (do
                  let w__1631 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b100001000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                               __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                 __opcode 15 13)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                 __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                    then
                      (do
                        let w__1630 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__1630 <b 1852) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__1631 : Bool)
                  then
                    (do
                      writeReg SEE 1852
                      let xs := (BitVec.slice __opcode 22 1)
                      let Zm := (BitVec.slice __opcode 16 5)
                      let msz := (BitVec.slice __opcode 13 2)
                      let Pg := (BitVec.slice __opcode 10 3)
                      let Rn := (BitVec.slice __opcode 5 5)
                      let prfop := (BitVec.slice __opcode 0 4)
                      (decode_PRFD_I_P_BZ_S_x32_scaled xs Zm msz Pg Rn prfop)
                      (pure false))
                  else
                    (do
                      let w__1633 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31
                                 23)) == (0b100001001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                   __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                   __opcode 15 13)) == (0b010#3 : (BitVec 3))))) : Bool) : Bool)
                        then
                          (do
                            let w__1632 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__1632 <b 1853) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__1633 : Bool)
                      then
                        (do
                          writeReg SEE 1853
                          let xs := (BitVec.slice __opcode 22 1)
                          let Zm := (BitVec.slice __opcode 16 5)
                          let U := (BitVec.slice __opcode 14 1)
                          let ff := (BitVec.slice __opcode 13 1)
                          let Pg := (BitVec.slice __opcode 10 3)
                          let Rn := (BitVec.slice __opcode 5 5)
                          let Zt := (BitVec.slice __opcode 0 5)
                          (decode_LD1H_Z_P_BZ_S_x32_scaled xs Zm U ff Pg Rn Zt)
                          (pure false))
                      else
                        (do
                          let w__1635 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode
                                     31 23)) == (0b100001001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                       __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                       __opcode 15 13)) == (0b000#3 : (BitVec 3))))) : Bool) : Bool)
                            then
                              (do
                                let w__1634 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__1634 <b 1854) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__1635 : Bool)
                          then
                            (do
                              writeReg SEE 1854
                              let xs := (BitVec.slice __opcode 22 1)
                              let Zm := (BitVec.slice __opcode 16 5)
                              let U := (BitVec.slice __opcode 14 1)
                              let ff := (BitVec.slice __opcode 13 1)
                              let Pg := (BitVec.slice __opcode 10 3)
                              let Rn := (BitVec.slice __opcode 5 5)
                              let Zt := (BitVec.slice __opcode 0 5)
                              (decode_LD1SH_Z_P_BZ_S_x32_scaled xs Zm U ff Pg Rn Zt)
                              (pure false))
                          else
                            (do
                              let w__1637 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                         __opcode 31 23)) == (0b100001001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                           __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                           __opcode 15 13)) == (0b011#3 : (BitVec 3))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__1636 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__1636 <b 1855) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__1637 : Bool)
                              then
                                (do
                                  writeReg SEE 1855
                                  let xs := (BitVec.slice __opcode 22 1)
                                  let Zm := (BitVec.slice __opcode 16 5)
                                  let U := (BitVec.slice __opcode 14 1)
                                  let ff := (BitVec.slice __opcode 13 1)
                                  let Pg := (BitVec.slice __opcode 10 3)
                                  let Rn := (BitVec.slice __opcode 5 5)
                                  let Zt := (BitVec.slice __opcode 0 5)
                                  (decode_LDFF1H_Z_P_BZ_S_x32_scaled xs Zm U ff Pg Rn Zt)
                                  (pure false))
                              else
                                (do
                                  let w__1639 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                             __opcode 31 23)) == (0b100001001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                               __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                               __opcode 15 13)) == (0b001#3 : (BitVec 3))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__1638 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__1638 <b 1856) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__1639 : Bool)
                                  then
                                    (do
                                      writeReg SEE 1856
                                      let xs := (BitVec.slice __opcode 22 1)
                                      let Zm := (BitVec.slice __opcode 16 5)
                                      let U := (BitVec.slice __opcode 14 1)
                                      let ff := (BitVec.slice __opcode 13 1)
                                      let Pg := (BitVec.slice __opcode 10 3)
                                      let Rn := (BitVec.slice __opcode 5 5)
                                      let Zt := (BitVec.slice __opcode 0 5)
                                      (decode_LDFF1SH_Z_P_BZ_S_x32_scaled xs Zm U ff Pg Rn Zt)
                                      (pure false))
                                  else
                                    (do
                                      let w__1641 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                 __opcode 31 23)) == (0b100001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                   __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                   __opcode 15 13)) == (0b010#3 : (BitVec 3))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__1640 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__1640 <b 1857) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__1641 : Bool)
                                      then
                                        (do
                                          writeReg SEE 1857
                                          let xs := (BitVec.slice __opcode 22 1)
                                          let Zm := (BitVec.slice __opcode 16 5)
                                          let U := (BitVec.slice __opcode 14 1)
                                          let ff := (BitVec.slice __opcode 13 1)
                                          let Pg := (BitVec.slice __opcode 10 3)
                                          let Rn := (BitVec.slice __opcode 5 5)
                                          let Zt := (BitVec.slice __opcode 0 5)
                                          (decode_LD1W_Z_P_BZ_S_x32_scaled xs Zm U ff Pg Rn Zt)
                                          (pure false))
                                      else
                                        (do
                                          let w__1643 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                     __opcode 31 23)) == (0b100001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                       __opcode 15 13)) == (0b011#3 : (BitVec 3))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__1642 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__1642 <b 1858) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__1643 : Bool)
                                          then
                                            (do
                                              writeReg SEE 1858
                                              let xs := (BitVec.slice __opcode 22 1)
                                              let Zm := (BitVec.slice __opcode 16 5)
                                              let U := (BitVec.slice __opcode 14 1)
                                              let ff := (BitVec.slice __opcode 13 1)
                                              let Pg := (BitVec.slice __opcode 10 3)
                                              let Rn := (BitVec.slice __opcode 5 5)
                                              let Zt := (BitVec.slice __opcode 0 5)
                                              (decode_LDFF1W_Z_P_BZ_S_x32_scaled xs Zm U ff Pg Rn Zt)
                                              (pure false))
                                          else
                                            (do
                                              let w__1645 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                         __opcode 31 22)) == (0b1000010110#10 : (BitVec 10))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                           __opcode 15 13)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 4 4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__1644 ← (( do readReg SEE ) : SailM Int
                                                      )
                                                    (pure (((w__1644 <b 1859) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__1645 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 1859
                                                  let imm9h := (BitVec.slice __opcode 16 6)
                                                  let imm9l := (BitVec.slice __opcode 10 3)
                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                  let Pt := (BitVec.slice __opcode 0 4)
                                                  (decode_LDR_P_BI__ imm9h imm9l Rn Pt)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__1647 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                             __opcode 31 22)) == (0b1000010110#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                             __opcode 15 13)) == (0b010#3 : (BitVec 3)))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__1646 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__1646 <b 1860) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__1647 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 1860
                                                      let imm9h := (BitVec.slice __opcode 16 6)
                                                      let imm9l := (BitVec.slice __opcode 10 3)
                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                      let Zt := (BitVec.slice __opcode 0 5)
                                                      (decode_LDR_Z_BI__ imm9h imm9l Rn Zt)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__1649 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                 __opcode 31 22)) == (0b1000010111#10 : (BitVec 10))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                   __opcode 15 13)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 4 4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__1648 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__1648 <b 1861) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__1649 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 1861
                                                          let imm6 := (BitVec.slice __opcode 16 6)
                                                          let msz := (BitVec.slice __opcode 13 2)
                                                          let Pg := (BitVec.slice __opcode 10 3)
                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                          let prfop := (BitVec.slice __opcode 0 4)
                                                          (decode_PRFB_I_P_BI_S imm6 msz Pg Rn prfop)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__1651 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                     __opcode 31 22)) == (0b1000010111#10 : (BitVec 10))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                       __opcode 15 13)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 4 4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__1650 ← (( do readReg SEE )
                                                                  : SailM Int )
                                                                (pure (((w__1650 <b 1862) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__1651 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 1862
                                                              let imm6 :=
                                                                (BitVec.slice __opcode 16 6)
                                                              let msz :=
                                                                (BitVec.slice __opcode 13 2)
                                                              let Pg := (BitVec.slice __opcode 10 3)
                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                              let prfop :=
                                                                (BitVec.slice __opcode 0 4)
                                                              (decode_PRFH_I_P_BI_S imm6 msz Pg Rn
                                                                prfop)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__1653 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                         __opcode 31 22)) == (0b1000010111#10 : (BitVec 10))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                           __opcode 15 13)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 4 4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__1652 ← (( do
                                                                      readReg SEE ) : SailM Int )
                                                                    (pure (((w__1652 <b 1863) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__1653 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 1863
                                                                  let imm6 :=
                                                                    (BitVec.slice __opcode 16 6)
                                                                  let msz :=
                                                                    (BitVec.slice __opcode 13 2)
                                                                  let Pg :=
                                                                    (BitVec.slice __opcode 10 3)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let prfop :=
                                                                    (BitVec.slice __opcode 0 4)
                                                                  (decode_PRFW_I_P_BI_S imm6 msz Pg
                                                                    Rn prfop)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__1655 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                             __opcode 31 22)) == (0b1000010111#10 : (BitVec 10))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                               __opcode 15 13)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                               __opcode 4 4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__1654 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__1654 <b 1864) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__1655 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 1864
                                                                      let imm6 :=
                                                                        (BitVec.slice __opcode 16 6)
                                                                      let msz :=
                                                                        (BitVec.slice __opcode 13 2)
                                                                      let Pg :=
                                                                        (BitVec.slice __opcode 10 3)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let prfop :=
                                                                        (BitVec.slice __opcode 0 4)
                                                                      (decode_PRFD_I_P_BI_S imm6 msz
                                                                        Pg Rn prfop)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__1657 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 21)) == (0b10000100000#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                   __opcode 15 13)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                   __opcode 4 4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__1656 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__1656 <b 1865) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__1657 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 1865
                                                                          let msz :=
                                                                            (BitVec.slice __opcode
                                                                              23 2)
                                                                          let Rm :=
                                                                            (BitVec.slice __opcode
                                                                              16 5)
                                                                          let Pg :=
                                                                            (BitVec.slice __opcode
                                                                              10 3)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let prfop :=
                                                                            (BitVec.slice __opcode 0
                                                                              4)
                                                                          (decode_PRFB_I_P_BR_S msz
                                                                            Rm Pg Rn prfop)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__1659 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 21)) == (0b10000100100#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                       __opcode 15
                                                                                       13)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 4 4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__1658 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__1658 <b 1866) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__1659 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 1866
                                                                              let msz :=
                                                                                (BitVec.slice
                                                                                  __opcode 23 2)
                                                                              let Rm :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 5)
                                                                              let Pg :=
                                                                                (BitVec.slice
                                                                                  __opcode 10 3)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let prfop :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 4)
                                                                              (decode_PRFH_I_P_BR_S
                                                                                msz Rm Pg Rn prfop)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__1661 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         21)) == (0b10000101000#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           15 13)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           4 4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__1660 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__1660 <b 1867) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__1661 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 1867
                                                                                  let msz :=
                                                                                    (BitVec.slice
                                                                                      __opcode 23 2)
                                                                                  let Rm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 5)
                                                                                  let Pg :=
                                                                                    (BitVec.slice
                                                                                      __opcode 10 3)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let prfop :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 4)
                                                                                  (decode_PRFW_I_P_BR_S
                                                                                    msz Rm Pg Rn
                                                                                    prfop)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__1663 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 21)) == (0b10000101100#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               15 13)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               4 4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__1662 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__1662 <b 1868) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__1663 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 1868
                                                                                      let msz :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          23 2)
                                                                                      let Rm :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 5)
                                                                                      let Pg :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          10 3)
                                                                                      let Rn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let prfop :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          4)
                                                                                      (decode_PRFD_I_P_BR_S
                                                                                        msz Rm Pg Rn
                                                                                        prfop)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__1665 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 21)) == (0b10000100000#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   15
                                                                                                   13)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   4
                                                                                                   4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__1664 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__1664 <b 1869) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__1665 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 1869
                                                                                          let msz :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              23 2)
                                                                                          let imm5 :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 5)
                                                                                          let Pg :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              10 3)
                                                                                          let Zn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let prfop :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 4)
                                                                                          (decode_PRFB_I_P_AI_S
                                                                                            msz imm5
                                                                                            Pg Zn
                                                                                            prfop)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__1667 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     21)) == (0b10000100100#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       15
                                                                                                       13)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       4
                                                                                                       4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__1666 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__1666 <b 1870) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__1667 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 1870
                                                                                              let msz :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  23
                                                                                                  2)
                                                                                              let imm5 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  5)
                                                                                              let Pg :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  10
                                                                                                  3)
                                                                                              let Zn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  5
                                                                                                  5)
                                                                                              let prfop :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  4)
                                                                                              (decode_PRFH_I_P_AI_S
                                                                                                msz
                                                                                                imm5
                                                                                                Pg
                                                                                                Zn
                                                                                                prfop)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__1669 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         21)) == (0b10000101000#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           15
                                                                                                           13)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           4
                                                                                                           4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__1668 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__1668 <b 1871) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__1669 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 1871
                                                                                                  let msz :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      23
                                                                                                      2)
                                                                                                  let imm5 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      5)
                                                                                                  let Pg :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      10
                                                                                                      3)
                                                                                                  let Zn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      5
                                                                                                      5)
                                                                                                  let prfop :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      4)
                                                                                                  (decode_PRFW_I_P_AI_S
                                                                                                    msz
                                                                                                    imm5
                                                                                                    Pg
                                                                                                    Zn
                                                                                                    prfop)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__1671 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             21)) == (0b10000101100#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               15
                                                                                                               13)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               4
                                                                                                               4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__1670 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__1670 <b 1872) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__1671 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 1872
                                                                                                      let msz :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          23
                                                                                                          2)
                                                                                                      let imm5 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          5)
                                                                                                      let Pg :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          10
                                                                                                          3)
                                                                                                      let Zn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          5
                                                                                                          5)
                                                                                                      let prfop :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          4)
                                                                                                      (decode_PRFD_I_P_AI_S
                                                                                                        msz
                                                                                                        imm5
                                                                                                        Pg
                                                                                                        Zn
                                                                                                        prfop)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__1673 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 21)) == (0b10000100001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 15
                                                                                                                 13)) == (0b110#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__1672 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__1672 <b 1873) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__1673 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 1873
                                                                                                          let msz :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              23
                                                                                                              2)
                                                                                                          let imm5 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              5)
                                                                                                          let U :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              14
                                                                                                              1)
                                                                                                          let ff :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              13
                                                                                                              1)
                                                                                                          let Pg :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              10
                                                                                                              3)
                                                                                                          let Zn :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              5
                                                                                                              5)
                                                                                                          let Zt :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              5)
                                                                                                          (decode_LD1B_Z_P_AI_S
                                                                                                            msz
                                                                                                            imm5
                                                                                                            U
                                                                                                            ff
                                                                                                            Pg
                                                                                                            Zn
                                                                                                            Zt)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__1675 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     21)) == (0b10000100001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     15
                                                                                                                     13)) == (0b100#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__1674 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__1674 <b 1874) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__1675 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 1874
                                                                                                              let msz :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  23
                                                                                                                  2)
                                                                                                              let imm5 :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  5)
                                                                                                              let U :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  14
                                                                                                                  1)
                                                                                                              let ff :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  13
                                                                                                                  1)
                                                                                                              let Pg :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  10
                                                                                                                  3)
                                                                                                              let Zn :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  5
                                                                                                                  5)
                                                                                                              let Zt :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  5)
                                                                                                              (decode_LD1SB_Z_P_AI_S
                                                                                                                msz
                                                                                                                imm5
                                                                                                                U
                                                                                                                ff
                                                                                                                Pg
                                                                                                                Zn
                                                                                                                Zt)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__1677 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         21)) == (0b10000100001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         15
                                                                                                                         13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__1676 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__1676 <b 1875) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__1677 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 1875
                                                                                                                  let msz :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      23
                                                                                                                      2)
                                                                                                                  let imm5 :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      5)
                                                                                                                  let U :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      14
                                                                                                                      1)
                                                                                                                  let ff :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      13
                                                                                                                      1)
                                                                                                                  let Pg :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      10
                                                                                                                      3)
                                                                                                                  let Zn :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      5
                                                                                                                      5)
                                                                                                                  let Zt :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      5)
                                                                                                                  (decode_LDFF1B_Z_P_AI_S
                                                                                                                    msz
                                                                                                                    imm5
                                                                                                                    U
                                                                                                                    ff
                                                                                                                    Pg
                                                                                                                    Zn
                                                                                                                    Zt)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__1679 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             21)) == (0b10000100001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             15
                                                                                                                             13)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__1678 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__1678 <b 1876) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__1679 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 1876
                                                                                                                      let msz :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          23
                                                                                                                          2)
                                                                                                                      let imm5 :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          16
                                                                                                                          5)
                                                                                                                      let U :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          14
                                                                                                                          1)
                                                                                                                      let ff :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          13
                                                                                                                          1)
                                                                                                                      let Pg :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          10
                                                                                                                          3)
                                                                                                                      let Zn :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          5
                                                                                                                          5)
                                                                                                                      let Zt :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          5)
                                                                                                                      (decode_LDFF1SB_Z_P_AI_S
                                                                                                                        msz
                                                                                                                        imm5
                                                                                                                        U
                                                                                                                        ff
                                                                                                                        Pg
                                                                                                                        Zn
                                                                                                                        Zt)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__1681 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 21)) == (0b10000100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 15
                                                                                                                                 13)) == (0b110#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__1680 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__1680 <b 1877) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__1681 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 1877
                                                                                                                          let msz :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              23
                                                                                                                              2)
                                                                                                                          let imm5 :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              5)
                                                                                                                          let U :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              14
                                                                                                                              1)
                                                                                                                          let ff :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              13
                                                                                                                              1)
                                                                                                                          let Pg :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              10
                                                                                                                              3)
                                                                                                                          let Zn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              5
                                                                                                                              5)
                                                                                                                          let Zt :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              5)
                                                                                                                          (decode_LD1H_Z_P_AI_S
                                                                                                                            msz
                                                                                                                            imm5
                                                                                                                            U
                                                                                                                            ff
                                                                                                                            Pg
                                                                                                                            Zn
                                                                                                                            Zt)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__1683 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     21)) == (0b10000100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     15
                                                                                                                                     13)) == (0b100#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__1682 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__1682 <b 1878) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__1683 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 1878
                                                                                                                              let msz :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  23
                                                                                                                                  2)
                                                                                                                              let imm5 :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
                                                                                                                                  5)
                                                                                                                              let U :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  14
                                                                                                                                  1)
                                                                                                                              let ff :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  13
                                                                                                                                  1)
                                                                                                                              let Pg :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  10
                                                                                                                                  3)
                                                                                                                              let Zn :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  5
                                                                                                                                  5)
                                                                                                                              let Zt :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  5)
                                                                                                                              (decode_LD1SH_Z_P_AI_S
                                                                                                                                msz
                                                                                                                                imm5
                                                                                                                                U
                                                                                                                                ff
                                                                                                                                Pg
                                                                                                                                Zn
                                                                                                                                Zt)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__1685 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         21)) == (0b10000100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         15
                                                                                                                                         13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__1684 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__1684 <b 1879) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__1685 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 1879
                                                                                                                                  let msz :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      23
                                                                                                                                      2)
                                                                                                                                  let imm5 :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      5)
                                                                                                                                  let U :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      14
                                                                                                                                      1)
                                                                                                                                  let ff :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      13
                                                                                                                                      1)
                                                                                                                                  let Pg :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      10
                                                                                                                                      3)
                                                                                                                                  let Zn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      5
                                                                                                                                      5)
                                                                                                                                  let Zt :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      5)
                                                                                                                                  (decode_LDFF1H_Z_P_AI_S
                                                                                                                                    msz
                                                                                                                                    imm5
                                                                                                                                    U
                                                                                                                                    ff
                                                                                                                                    Pg
                                                                                                                                    Zn
                                                                                                                                    Zt)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__1687 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             21)) == (0b10000100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             15
                                                                                                                                             13)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__1686 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__1686 <b 1880) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__1687 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 1880
                                                                                                                                      let msz :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          23
                                                                                                                                          2)
                                                                                                                                      let imm5 :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          16
                                                                                                                                          5)
                                                                                                                                      let U :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          14
                                                                                                                                          1)
                                                                                                                                      let ff :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          13
                                                                                                                                          1)
                                                                                                                                      let Pg :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          10
                                                                                                                                          3)
                                                                                                                                      let Zn :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          5
                                                                                                                                          5)
                                                                                                                                      let Zt :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          5)
                                                                                                                                      (decode_LDFF1SH_Z_P_AI_S
                                                                                                                                        msz
                                                                                                                                        imm5
                                                                                                                                        U
                                                                                                                                        ff
                                                                                                                                        Pg
                                                                                                                                        Zn
                                                                                                                                        Zt)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__1689 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 21)) == (0b10000101001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 15
                                                                                                                                                 13)) == (0b110#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__1688 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__1688 <b 1881) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__1689 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 1881
                                                                                                                                          let msz :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              23
                                                                                                                                              2)
                                                                                                                                          let imm5 :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              16
                                                                                                                                              5)
                                                                                                                                          let U :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              14
                                                                                                                                              1)
                                                                                                                                          let ff :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              13
                                                                                                                                              1)
                                                                                                                                          let Pg :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              10
                                                                                                                                              3)
                                                                                                                                          let Zn :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              5
                                                                                                                                              5)
                                                                                                                                          let Zt :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              0
                                                                                                                                              5)
                                                                                                                                          (decode_LD1W_Z_P_AI_S
                                                                                                                                            msz
                                                                                                                                            imm5
                                                                                                                                            U
                                                                                                                                            ff
                                                                                                                                            Pg
                                                                                                                                            Zn
                                                                                                                                            Zt)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__1691 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     21)) == (0b10000101001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     15
                                                                                                                                                     13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__1690 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__1690 <b 1882) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__1691 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 1882
                                                                                                                                              let msz :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  23
                                                                                                                                                  2)
                                                                                                                                              let imm5 :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  16
                                                                                                                                                  5)
                                                                                                                                              let U :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  14
                                                                                                                                                  1)
                                                                                                                                              let ff :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  13
                                                                                                                                                  1)
                                                                                                                                              let Pg :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  10
                                                                                                                                                  3)
                                                                                                                                              let Zn :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  5
                                                                                                                                                  5)
                                                                                                                                              let Zt :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  0
                                                                                                                                                  5)
                                                                                                                                              (decode_LDFF1W_Z_P_AI_S
                                                                                                                                                msz
                                                                                                                                                imm5
                                                                                                                                                U
                                                                                                                                                ff
                                                                                                                                                Pg
                                                                                                                                                Zn
                                                                                                                                                Zt)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__1693 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         31
                                                                                                                                                         22)) == (0b1000010001#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         15
                                                                                                                                                         13)) == (0b100#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__1692 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__1692 <b 1883) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__1693 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 1883
                                                                                                                                                  let dtypeh :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      23
                                                                                                                                                      2)
                                                                                                                                                  let imm6 :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      16
                                                                                                                                                      6)
                                                                                                                                                  let dtypel :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      13
                                                                                                                                                      2)
                                                                                                                                                  let Pg :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      10
                                                                                                                                                      3)
                                                                                                                                                  let Rn :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      5
                                                                                                                                                      5)
                                                                                                                                                  let Zt :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      0
                                                                                                                                                      5)
                                                                                                                                                  (decode_LD1RB_Z_P_BI_U8
                                                                                                                                                    dtypeh
                                                                                                                                                    imm6
                                                                                                                                                    dtypel
                                                                                                                                                    Pg
                                                                                                                                                    Rn
                                                                                                                                                    Zt)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__1695 ← (( do
                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             31
                                                                                                                                                             22)) == (0b1000010001#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             15
                                                                                                                                                             13)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__1694 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__1694 <b 1884) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__1695 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 1884
                                                                                                                                                      let dtypeh :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          23
                                                                                                                                                          2)
                                                                                                                                                      let imm6 :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          16
                                                                                                                                                          6)
                                                                                                                                                      let dtypel :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          13
                                                                                                                                                          2)
                                                                                                                                                      let Pg :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          10
                                                                                                                                                          3)
                                                                                                                                                      let Rn :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          5
                                                                                                                                                          5)
                                                                                                                                                      let Zt :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          0
                                                                                                                                                          5)
                                                                                                                                                      (decode_LD1RB_Z_P_BI_U16
                                                                                                                                                        dtypeh
                                                                                                                                                        imm6
                                                                                                                                                        dtypel
                                                                                                                                                        Pg
                                                                                                                                                        Rn
                                                                                                                                                        Zt)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__1697 ← (( do
                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 31
                                                                                                                                                                 22)) == (0b1000010001#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 15
                                                                                                                                                                 13)) == (0b110#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__1696 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__1696 <b 1885) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false)
                                                                                                                                                        )
                                                                                                                                                        :
                                                                                                                                                        SailM
                                                                                                                                                        Bool
                                                                                                                                                        )
                                                                                                                                                      if (w__1697 : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 1885
                                                                                                                                                          let dtypeh :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              23
                                                                                                                                                              2)
                                                                                                                                                          let imm6 :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              16
                                                                                                                                                              6)
                                                                                                                                                          let dtypel :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              13
                                                                                                                                                              2)
                                                                                                                                                          let Pg :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              10
                                                                                                                                                              3)
                                                                                                                                                          let Rn :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              5
                                                                                                                                                              5)
                                                                                                                                                          let Zt :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              0
                                                                                                                                                              5)
                                                                                                                                                          (decode_LD1RB_Z_P_BI_U32
                                                                                                                                                            dtypeh
                                                                                                                                                            imm6
                                                                                                                                                            dtypel
                                                                                                                                                            Pg
                                                                                                                                                            Rn
                                                                                                                                                            Zt)
                                                                                                                                                          (pure false))
                                                                                                                                                      else
                                                                                                                                                        (pure true))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
