import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0159
import ArmFull.Fn.M0160
import ArmFull.Fn.M0161
import ArmFull.Fn.M0261
import ArmFull.Fn.M0312
import ArmFull.Fn.M0313
import ArmFull.Fn.M0314
import ArmFull.Fn.M0315
import ArmFull.Fn.M0328
import ArmFull.Fn.M0329
import ArmFull.Fn.M0330
import ArmFull.Fn.M0331
import ArmFull.Fn.M0332
import ArmFull.Fn.M0333
import ArmFull.Fn.M0344
import ArmFull.Fn.M0346
import ArmFull.Fn.M0348
import ArmFull.Fn.M0350
import ArmFull.Fn.M0351
import ArmFull.Fn.M0352
import ArmFull.Fn.M0355
import ArmFull.Fn.M0358
import ArmFull.Fn.M0376
import ArmFull.Fn.M0377
import ArmFull.Fn.M0378
import ArmFull.Fn.M0379
import ArmFull.Fn.M0380
import ArmFull.Fn.M0381
import ArmFull.Fn.M0382
import ArmFull.Fn.M0383
import ArmFull.Fn.M0384
import ArmFull.Fn.M0385
import ArmFull.Fn.M0386
import ArmFull.Fn.M0391
import ArmFull.Fn.M0393
import ArmFull.Fn.M0427
import ArmFull.Fn.M0428
import ArmFull.Fn.M0430
import ArmFull.Fn.M1352
import ArmFull.Fn.M1358
import ArmFull.Fn.M1359
import ArmFull.Fn.M1364
import ArmFull.Fn.M1372
import ArmFull.Fn.M1373
import ArmFull.Fn.M1376
import ArmFull.Fn.M1377

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

/-- Type quantifiers: t : Int -/
def AArch64_AutoGen_SysRegRead__seg4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Bool := do
  if ((((((CRm == 0b1101#4) && (CRn == 0b1001#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b001#3)) : Bool)
  then
    (do
      (PMXEVTYPER_EL0_SysRegRead_822f8e38c465529c el op0 op1 CRn op2 CRm t)
      (pure false))
  else
    (do
      if ((((((CRm == 0b0010#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b001#3)) : Bool)
      then
        (do
          (MAIR2_EL1_SysRegRead_5817d7d1bdb094d0 el op0 op1 CRn op2 CRm t)
          (pure false))
      else
        (do
          if ((((((CRm == 0b0100#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b000#3)) : Bool)
          then
            (do
              (LORSA_EL1_SysRegRead_eff0a73c3cb651d8 el op0 op1 CRn op2 CRm t)
              (pure false))
          else
            (do
              if ((((((CRm == 0b0111#4) && (CRn == 0b0000#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
              then
                (do
                  (ID_AA64MMFR1_EL1_SysRegRead_8e0c46321a1a5a47 el op0 op1 CRn op2 CRm t)
                  (pure false))
              else
                (do
                  if ((((((CRm == 0b1100#4) && (CRn == 0b1001#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b011#3)) : Bool)
                  then
                    (do
                      (SPMOVSCLR_EL0_SysRegRead_f68ae6919a317d03 el op0 op1 CRn op2 CRm t)
                      (pure false))
                  else
                    (do
                      if ((((((CRm == 0b1111#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b111#3)) : Bool)
                      then
                        (do
                          (DBGWCR_EL1_SysRegRead_236e531d61e35213 el op0 op1 CRn op2 CRm t)
                          (pure false))
                      else
                        (do
                          if ((((((CRm == 0b1110#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b111#3)) : Bool)
                          then
                            (do
                              (DBGWCR_EL1_SysRegRead_9b436b8dcf826854 el op0 op1 CRn op2 CRm t)
                              (pure false))
                          else
                            (do
                              if ((((((CRm == 0b1101#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b111#3)) : Bool)
                              then
                                (do
                                  (DBGWCR_EL1_SysRegRead_0d4001a88a9206f8 el op0 op1 CRn op2 CRm t)
                                  (pure false))
                              else
                                (do
                                  if ((((((CRm == 0b1100#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b111#3)) : Bool)
                                  then
                                    (do
                                      (DBGWCR_EL1_SysRegRead_b7d3a0a1687ee605 el op0 op1 CRn op2 CRm
                                        t)
                                      (pure false))
                                  else
                                    (do
                                      if ((((((CRm == 0b1011#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b111#3)) : Bool)
                                      then
                                        (do
                                          (DBGWCR_EL1_SysRegRead_6ed96d96594172dd el op0 op1 CRn op2
                                            CRm t)
                                          (pure false))
                                      else
                                        (do
                                          if ((((((CRm == 0b1010#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b111#3)) : Bool)
                                          then
                                            (do
                                              (DBGWCR_EL1_SysRegRead_d6acb1282794050a el op0 op1 CRn
                                                op2 CRm t)
                                              (pure false))
                                          else
                                            (do
                                              if ((((((CRm == 0b1001#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b111#3)) : Bool)
                                              then
                                                (do
                                                  (DBGWCR_EL1_SysRegRead_732a44d59c35aeb3 el op0 op1
                                                    CRn op2 CRm t)
                                                  (pure false))
                                              else
                                                (do
                                                  if ((((((CRm == 0b1000#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b111#3)) : Bool)
                                                  then
                                                    (do
                                                      (DBGWCR_EL1_SysRegRead_2c1cc2102bf556aa el op0
                                                        op1 CRn op2 CRm t)
                                                      (pure false))
                                                  else
                                                    (do
                                                      if ((((((CRm == 0b0111#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b111#3)) : Bool)
                                                      then
                                                        (do
                                                          (DBGWCR_EL1_SysRegRead_7e97fa1e73481f2d el
                                                            op0 op1 CRn op2 CRm t)
                                                          (pure false))
                                                      else
                                                        (do
                                                          if ((((((CRm == 0b0110#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b111#3)) : Bool)
                                                          then
                                                            (do
                                                              (DBGWCR_EL1_SysRegRead_74bf5d2a6cfe195c
                                                                el op0 op1 CRn op2 CRm t)
                                                              (pure false))
                                                          else
                                                            (do
                                                              if ((((((CRm == 0b0101#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b111#3)) : Bool)
                                                              then
                                                                (do
                                                                  (DBGWCR_EL1_SysRegRead_81a0b83ef7c202d4
                                                                    el op0 op1 CRn op2 CRm t)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  if ((((((CRm == 0b0100#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b111#3)) : Bool)
                                                                  then
                                                                    (do
                                                                      (DBGWCR_EL1_SysRegRead_ab00b8f6b1bf63cc
                                                                        el op0 op1 CRn op2 CRm t)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      if ((((((CRm == 0b0011#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b111#3)) : Bool)
                                                                      then
                                                                        (do
                                                                          (DBGWCR_EL1_SysRegRead_d41ce14d142d5fc9
                                                                            el op0 op1 CRn op2 CRm t)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          if ((((((CRm == 0b0010#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b111#3)) : Bool)
                                                                          then
                                                                            (do
                                                                              (DBGWCR_EL1_SysRegRead_a0df5130cffc6ec3
                                                                                el op0 op1 CRn op2
                                                                                CRm t)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              if ((((((CRm == 0b0001#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b111#3)) : Bool)
                                                                              then
                                                                                (do
                                                                                  (DBGWCR_EL1_SysRegRead_782b8628944ba11a
                                                                                    el op0 op1 CRn
                                                                                    op2 CRm t)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  if ((((((CRm == 0b0000#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b111#3)) : Bool)
                                                                                  then
                                                                                    (do
                                                                                      (DBGWCR_EL1_SysRegRead_aae6422db875ace5
                                                                                        el op0 op1
                                                                                        CRn op2 CRm
                                                                                        t)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      if ((((((CRm == 0b0000#4) && (CRn == 0b1101#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b111#3)) : Bool)
                                                                                      then
                                                                                        (do
                                                                                          (SCXTNUM_EL2_SysRegRead_8bf0422effd0ab20
                                                                                            el op0
                                                                                            op1 CRn
                                                                                            op2 CRm
                                                                                            t)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          if ((((((CRm == 0b0000#4) && (CRn == 0b1101#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b111#3)) : Bool)
                                                                                          then
                                                                                            (do
                                                                                              (SCXTNUM_EL2_SysRegRead_af67262612e5c00e
                                                                                                el
                                                                                                op0
                                                                                                op1
                                                                                                CRn
                                                                                                op2
                                                                                                CRm
                                                                                                t)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              if ((((((CRm == 0b0010#4) && (CRn == 0b0101#4)) && (op0 == 0b11#2)) && (op1 == 0b110#3)) && (op2 == 0b000#3)) : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  (ESR_EL3_SysRegRead_ba1b08f3b6ea1fa7
                                                                                                    el
                                                                                                    op0
                                                                                                    op1
                                                                                                    CRn
                                                                                                    op2
                                                                                                    CRm
                                                                                                    t)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  if ((((((CRm == 0b1111#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      (PMEVTYPER_EL0_SysRegRead_82c0bc230c1e3204
                                                                                                        el
                                                                                                        op0
                                                                                                        op1
                                                                                                        CRn
                                                                                                        op2
                                                                                                        CRm
                                                                                                        t)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      if ((((((CRm == 0b1111#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          (PMEVTYPER_EL0_SysRegRead_6f9a48444f4b276b
                                                                                                            el
                                                                                                            op0
                                                                                                            op1
                                                                                                            CRn
                                                                                                            op2
                                                                                                            CRm
                                                                                                            t)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          if ((((((CRm == 0b1111#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              (PMEVTYPER_EL0_SysRegRead_3420cbf7b2d038f8
                                                                                                                el
                                                                                                                op0
                                                                                                                op1
                                                                                                                CRn
                                                                                                                op2
                                                                                                                CRm
                                                                                                                t)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              if ((((((CRm == 0b1111#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  (PMEVTYPER_EL0_SysRegRead_953a504769c668b0
                                                                                                                    el
                                                                                                                    op0
                                                                                                                    op1
                                                                                                                    CRn
                                                                                                                    op2
                                                                                                                    CRm
                                                                                                                    t)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  if ((((((CRm == 0b1111#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      (PMEVTYPER_EL0_SysRegRead_cd99afc01b24bf2b
                                                                                                                        el
                                                                                                                        op0
                                                                                                                        op1
                                                                                                                        CRn
                                                                                                                        op2
                                                                                                                        CRm
                                                                                                                        t)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      if ((((((CRm == 0b1111#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          (PMEVTYPER_EL0_SysRegRead_c8e002b2195e5a12
                                                                                                                            el
                                                                                                                            op0
                                                                                                                            op1
                                                                                                                            CRn
                                                                                                                            op2
                                                                                                                            CRm
                                                                                                                            t)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          if ((((((CRm == 0b1111#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              (PMEVTYPER_EL0_SysRegRead_74117943f83c7293
                                                                                                                                el
                                                                                                                                op0
                                                                                                                                op1
                                                                                                                                CRn
                                                                                                                                op2
                                                                                                                                CRm
                                                                                                                                t)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              if ((((((CRm == 0b1110#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  (PMEVTYPER_EL0_SysRegRead_13c3c0867de835a2
                                                                                                                                    el
                                                                                                                                    op0
                                                                                                                                    op1
                                                                                                                                    CRn
                                                                                                                                    op2
                                                                                                                                    CRm
                                                                                                                                    t)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  if ((((((CRm == 0b1110#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      (PMEVTYPER_EL0_SysRegRead_b06bc5007c474af3
                                                                                                                                        el
                                                                                                                                        op0
                                                                                                                                        op1
                                                                                                                                        CRn
                                                                                                                                        op2
                                                                                                                                        CRm
                                                                                                                                        t)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      if ((((((CRm == 0b1110#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          (PMEVTYPER_EL0_SysRegRead_187174725e559008
                                                                                                                                            el
                                                                                                                                            op0
                                                                                                                                            op1
                                                                                                                                            CRn
                                                                                                                                            op2
                                                                                                                                            CRm
                                                                                                                                            t)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          if ((((((CRm == 0b1110#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              (PMEVTYPER_EL0_SysRegRead_b63b7d8fea5e18df
                                                                                                                                                el
                                                                                                                                                op0
                                                                                                                                                op1
                                                                                                                                                CRn
                                                                                                                                                op2
                                                                                                                                                CRm
                                                                                                                                                t)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              if ((((((CRm == 0b1110#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  (PMEVTYPER_EL0_SysRegRead_c8e92c1375bb4b38
                                                                                                                                                    el
                                                                                                                                                    op0
                                                                                                                                                    op1
                                                                                                                                                    CRn
                                                                                                                                                    op2
                                                                                                                                                    CRm
                                                                                                                                                    t)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  if ((((((CRm == 0b1110#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      (PMEVTYPER_EL0_SysRegRead_161a91be0c63b6f4
                                                                                                                                                        el
                                                                                                                                                        op0
                                                                                                                                                        op1
                                                                                                                                                        CRn
                                                                                                                                                        op2
                                                                                                                                                        CRm
                                                                                                                                                        t)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      if ((((((CRm == 0b1110#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          (PMEVTYPER_EL0_SysRegRead_b777b07a1ab3a531
                                                                                                                                                            el
                                                                                                                                                            op0
                                                                                                                                                            op1
                                                                                                                                                            CRn
                                                                                                                                                            op2
                                                                                                                                                            CRm
                                                                                                                                                            t)
                                                                                                                                                          (pure false))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          if ((((((CRm == 0b1110#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              (PMEVTYPER_EL0_SysRegRead_6096f129eb2ac985
                                                                                                                                                                el
                                                                                                                                                                op0
                                                                                                                                                                op1
                                                                                                                                                                CRn
                                                                                                                                                                op2
                                                                                                                                                                CRm
                                                                                                                                                                t)
                                                                                                                                                              (pure false))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              if ((((((CRm == 0b1101#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  (PMEVTYPER_EL0_SysRegRead_d41d3960b7ebf0de
                                                                                                                                                                    el
                                                                                                                                                                    op0
                                                                                                                                                                    op1
                                                                                                                                                                    CRn
                                                                                                                                                                    op2
                                                                                                                                                                    CRm
                                                                                                                                                                    t)
                                                                                                                                                                  (pure false))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  if ((((((CRm == 0b1101#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      (PMEVTYPER_EL0_SysRegRead_14beb5e8e42eceb3
                                                                                                                                                                        el
                                                                                                                                                                        op0
                                                                                                                                                                        op1
                                                                                                                                                                        CRn
                                                                                                                                                                        op2
                                                                                                                                                                        CRm
                                                                                                                                                                        t)
                                                                                                                                                                      (pure false))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      if ((((((CRm == 0b1101#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (do
                                                                                                                                                                          (PMEVTYPER_EL0_SysRegRead_073a4fe6d2f5a921
                                                                                                                                                                            el
                                                                                                                                                                            op0
                                                                                                                                                                            op1
                                                                                                                                                                            CRn
                                                                                                                                                                            op2
                                                                                                                                                                            CRm
                                                                                                                                                                            t)
                                                                                                                                                                          (pure false))
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          if ((((((CRm == 0b1101#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                                                                                          then
                                                                                                                                                                            (do
                                                                                                                                                                              (PMEVTYPER_EL0_SysRegRead_4d7b8571d7d827fa
                                                                                                                                                                                el
                                                                                                                                                                                op0
                                                                                                                                                                                op1
                                                                                                                                                                                CRn
                                                                                                                                                                                op2
                                                                                                                                                                                CRm
                                                                                                                                                                                t)
                                                                                                                                                                              (pure false))
                                                                                                                                                                          else
                                                                                                                                                                            (do
                                                                                                                                                                              if ((((((CRm == 0b1101#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                              then
                                                                                                                                                                                (do
                                                                                                                                                                                  (PMEVTYPER_EL0_SysRegRead_50be283a37e4fd31
                                                                                                                                                                                    el
                                                                                                                                                                                    op0
                                                                                                                                                                                    op1
                                                                                                                                                                                    CRn
                                                                                                                                                                                    op2
                                                                                                                                                                                    CRm
                                                                                                                                                                                    t)
                                                                                                                                                                                  (pure false))
                                                                                                                                                                              else
                                                                                                                                                                                (do
                                                                                                                                                                                  if ((((((CRm == 0b1101#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                  then
                                                                                                                                                                                    (do
                                                                                                                                                                                      (PMEVTYPER_EL0_SysRegRead_1f37321b901f8989
                                                                                                                                                                                        el
                                                                                                                                                                                        op0
                                                                                                                                                                                        op1
                                                                                                                                                                                        CRn
                                                                                                                                                                                        op2
                                                                                                                                                                                        CRm
                                                                                                                                                                                        t)
                                                                                                                                                                                      (pure false))
                                                                                                                                                                                  else
                                                                                                                                                                                    (do
                                                                                                                                                                                      if ((((((CRm == 0b1101#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                      then
                                                                                                                                                                                        (do
                                                                                                                                                                                          (PMEVTYPER_EL0_SysRegRead_a6915f5d07275c6c
                                                                                                                                                                                            el
                                                                                                                                                                                            op0
                                                                                                                                                                                            op1
                                                                                                                                                                                            CRn
                                                                                                                                                                                            op2
                                                                                                                                                                                            CRm
                                                                                                                                                                                            t)
                                                                                                                                                                                          (pure false))
                                                                                                                                                                                      else
                                                                                                                                                                                        (do
                                                                                                                                                                                          if ((((((CRm == 0b1101#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                          then
                                                                                                                                                                                            (do
                                                                                                                                                                                              (PMEVTYPER_EL0_SysRegRead_1a04be91449acb40
                                                                                                                                                                                                el
                                                                                                                                                                                                op0
                                                                                                                                                                                                op1
                                                                                                                                                                                                CRn
                                                                                                                                                                                                op2
                                                                                                                                                                                                CRm
                                                                                                                                                                                                t)
                                                                                                                                                                                              (pure false))
                                                                                                                                                                                          else
                                                                                                                                                                                            (do
                                                                                                                                                                                              if ((((((CRm == 0b1100#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                                                                                              then
                                                                                                                                                                                                (do
                                                                                                                                                                                                  (PMEVTYPER_EL0_SysRegRead_59df350d04568b64
                                                                                                                                                                                                    el
                                                                                                                                                                                                    op0
                                                                                                                                                                                                    op1
                                                                                                                                                                                                    CRn
                                                                                                                                                                                                    op2
                                                                                                                                                                                                    CRm
                                                                                                                                                                                                    t)
                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                              else
                                                                                                                                                                                                (do
                                                                                                                                                                                                  if ((((((CRm == 0b1100#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                                                                                  then
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      (PMEVTYPER_EL0_SysRegRead_12c2ea6445066d74
                                                                                                                                                                                                        el
                                                                                                                                                                                                        op0
                                                                                                                                                                                                        op1
                                                                                                                                                                                                        CRn
                                                                                                                                                                                                        op2
                                                                                                                                                                                                        CRm
                                                                                                                                                                                                        t)
                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                  else
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      if ((((((CRm == 0b1100#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                      then
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          (PMEVTYPER_EL0_SysRegRead_264c590d45142978
                                                                                                                                                                                                            el
                                                                                                                                                                                                            op0
                                                                                                                                                                                                            op1
                                                                                                                                                                                                            CRn
                                                                                                                                                                                                            op2
                                                                                                                                                                                                            CRm
                                                                                                                                                                                                            t)
                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                      else
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          if ((((((CRm == 0b1100#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                                                                                                                          then
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              (PMEVTYPER_EL0_SysRegRead_1dbe5107f25be020
                                                                                                                                                                                                                el
                                                                                                                                                                                                                op0
                                                                                                                                                                                                                op1
                                                                                                                                                                                                                CRn
                                                                                                                                                                                                                op2
                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                t)
                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                          else
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              if ((((((CRm == 0b1100#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                                              then
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  (PMEVTYPER_EL0_SysRegRead_49df7d27e017454d
                                                                                                                                                                                                                    el
                                                                                                                                                                                                                    op0
                                                                                                                                                                                                                    op1
                                                                                                                                                                                                                    CRn
                                                                                                                                                                                                                    op2
                                                                                                                                                                                                                    CRm
                                                                                                                                                                                                                    t)
                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                              else
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  if ((((((CRm == 0b1100#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                  then
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      (PMEVTYPER_EL0_SysRegRead_c20edd6d6b9803a3
                                                                                                                                                                                                                        el
                                                                                                                                                                                                                        op0
                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                        CRn
                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                        CRm
                                                                                                                                                                                                                        t)
                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                  else
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      if ((((((CRm == 0b1100#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                      then
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          (PMEVTYPER_EL0_SysRegRead_b0eea7edf1a1fecf
                                                                                                                                                                                                                            el
                                                                                                                                                                                                                            op0
                                                                                                                                                                                                                            op1
                                                                                                                                                                                                                            CRn
                                                                                                                                                                                                                            op2
                                                                                                                                                                                                                            CRm
                                                                                                                                                                                                                            t)
                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                      else
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          if ((((((CRm == 0b1100#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                          then
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              (PMEVTYPER_EL0_SysRegRead_303aca4655281092
                                                                                                                                                                                                                                el
                                                                                                                                                                                                                                op0
                                                                                                                                                                                                                                op1
                                                                                                                                                                                                                                CRn
                                                                                                                                                                                                                                op2
                                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                                t)
                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                          else
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              if ((((((CRm == 0b0011#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  (CNTV_CTL_EL0_SysRegRead_23c5b36dc5cb110e
                                                                                                                                                                                                                                    el
                                                                                                                                                                                                                                    op0
                                                                                                                                                                                                                                    op1
                                                                                                                                                                                                                                    CRn
                                                                                                                                                                                                                                    op2
                                                                                                                                                                                                                                    CRm
                                                                                                                                                                                                                                    t)
                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  if ((((((CRm == 0b1101#4) && (CRn == 0b1001#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      (SPMIIDR_EL1_SysRegRead_895b44f480e2fb64
                                                                                                                                                                                                                                        el
                                                                                                                                                                                                                                        op0
                                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                                        CRn
                                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                                        CRm
                                                                                                                                                                                                                                        t)
                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      if ((((((CRm == 0b1110#4) && (CRn == 0b1001#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          (PMIAR_EL1_SysRegRead_8a45c86d25fdd6b8
                                                                                                                                                                                                                                            el
                                                                                                                                                                                                                                            op0
                                                                                                                                                                                                                                            op1
                                                                                                                                                                                                                                            CRn
                                                                                                                                                                                                                                            op2
                                                                                                                                                                                                                                            CRm
                                                                                                                                                                                                                                            t)
                                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          if ((((((CRm == 0b0000#4) && (CRn == 0b1101#4)) && (op0 == 0b11#2)) && (op1 == 0b110#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              (TPIDR_EL3_SysRegRead_165fa3219105298e
                                                                                                                                                                                                                                                el
                                                                                                                                                                                                                                                op0
                                                                                                                                                                                                                                                op1
                                                                                                                                                                                                                                                CRn
                                                                                                                                                                                                                                                op2
                                                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                                                t)
                                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              if ((((((CRm == 0b0010#4) && (CRn == 0b0001#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  (TRFCR_EL1_SysRegRead_346a67ae7b13428d
                                                                                                                                                                                                                                                    el
                                                                                                                                                                                                                                                    op0
                                                                                                                                                                                                                                                    op1
                                                                                                                                                                                                                                                    CRn
                                                                                                                                                                                                                                                    op2
                                                                                                                                                                                                                                                    CRm
                                                                                                                                                                                                                                                    t)
                                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  if ((((((CRm == 0b0001#4) && (CRn == 0b0000#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      (ID_MMFR0_EL1_SysRegRead_911dfac1545c3c44
                                                                                                                                                                                                                                                        el
                                                                                                                                                                                                                                                        op0
                                                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                                                        CRn
                                                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                                                        CRm
                                                                                                                                                                                                                                                        t)
                                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      if ((((((CRm == 0b0011#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          (OSDTRTX_EL1_SysRegRead_9df6f1b9434b173d
                                                                                                                                                                                                                                                            el
                                                                                                                                                                                                                                                            op0
                                                                                                                                                                                                                                                            op1
                                                                                                                                                                                                                                                            CRn
                                                                                                                                                                                                                                                            op2
                                                                                                                                                                                                                                                            CRm
                                                                                                                                                                                                                                                            t)
                                                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          if ((((((CRm == 0b0000#4) && (CRn == 0b0100#4)) && (op0 == 0b11#2)) && (op1 == 0b110#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              (ELR_EL3_SysRegRead_48156757f03c05da
                                                                                                                                                                                                                                                                el
                                                                                                                                                                                                                                                                op0
                                                                                                                                                                                                                                                                op1
                                                                                                                                                                                                                                                                CRn
                                                                                                                                                                                                                                                                op2
                                                                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                                                                t)
                                                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              if ((((((CRm == 0b1011#4) && (CRn == 0b1100#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  (ICH_VMCR_EL2_SysRegRead_7485c707cb4a586a
                                                                                                                                                                                                                                                                    el
                                                                                                                                                                                                                                                                    op0
                                                                                                                                                                                                                                                                    op1
                                                                                                                                                                                                                                                                    CRn
                                                                                                                                                                                                                                                                    op2
                                                                                                                                                                                                                                                                    CRm
                                                                                                                                                                                                                                                                    t)
                                                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0000#4) && (CRn == 0b0000#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      (VPIDR_EL2_SysRegRead_c419b4414b36ba2e
                                                                                                                                                                                                                                                                        el
                                                                                                                                                                                                                                                                        op0
                                                                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                                                                        CRn
                                                                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                                                                        CRm
                                                                                                                                                                                                                                                                        t)
                                                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0000#4) && (CRn == 0b0001#4)) && (op0 == 0b11#2)) && (op1 == 0b110#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          (ACTLR_EL3_SysRegRead_c20b5bca7bc57751
                                                                                                                                                                                                                                                                            el
                                                                                                                                                                                                                                                                            op0
                                                                                                                                                                                                                                                                            op1
                                                                                                                                                                                                                                                                            CRn
                                                                                                                                                                                                                                                                            op2
                                                                                                                                                                                                                                                                            CRm
                                                                                                                                                                                                                                                                            t)
                                                                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          if ((((((CRm == 0b1100#4) && (CRn == 0b1100#4)) && (op0 == 0b11#2)) && (op1 == 0b110#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              (ICC_CTLR_EL3_SysRegRead_7a137fb26d669941
                                                                                                                                                                                                                                                                                el
                                                                                                                                                                                                                                                                                op0
                                                                                                                                                                                                                                                                                op1
                                                                                                                                                                                                                                                                                CRn
                                                                                                                                                                                                                                                                                op2
                                                                                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                                                                                t)
                                                                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0000#4) && (CRn == 0b0001#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  (SCTLR_EL2_SysRegRead_e3c3d9b65d84cd42
                                                                                                                                                                                                                                                                                    el
                                                                                                                                                                                                                                                                                    op0
                                                                                                                                                                                                                                                                                    op1
                                                                                                                                                                                                                                                                                    CRn
                                                                                                                                                                                                                                                                                    op2
                                                                                                                                                                                                                                                                                    CRm
                                                                                                                                                                                                                                                                                    t)
                                                                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0011#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                      (AMAIR_EL2_SysRegRead_8a38edf51a31f5e0
                                                                                                                                                                                                                                                                                        el
                                                                                                                                                                                                                                                                                        op0
                                                                                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                                                                                        CRn
                                                                                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                                                                                        CRm
                                                                                                                                                                                                                                                                                        t)
                                                                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0011#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                          (AMAIR_EL2_SysRegRead_e7d62050e609b077
                                                                                                                                                                                                                                                                                            el
                                                                                                                                                                                                                                                                                            op0
                                                                                                                                                                                                                                                                                            op1
                                                                                                                                                                                                                                                                                            CRn
                                                                                                                                                                                                                                                                                            op2
                                                                                                                                                                                                                                                                                            CRm
                                                                                                                                                                                                                                                                                            t)
                                                                                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0101#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                              (CNTHPS_CVAL_EL2_SysRegRead_d2662865ff7936c3
                                                                                                                                                                                                                                                                                                el
                                                                                                                                                                                                                                                                                                op0
                                                                                                                                                                                                                                                                                                op1
                                                                                                                                                                                                                                                                                                CRn
                                                                                                                                                                                                                                                                                                op2
                                                                                                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                                                                                                t)
                                                                                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0001#4) && (CRn == 0b0001#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                  (OSLSR_EL1_SysRegRead_ee8639dd7aebdefe
                                                                                                                                                                                                                                                                                                    el
                                                                                                                                                                                                                                                                                                    op0
                                                                                                                                                                                                                                                                                                    op1
                                                                                                                                                                                                                                                                                                    CRn
                                                                                                                                                                                                                                                                                                    op2
                                                                                                                                                                                                                                                                                                    CRm
                                                                                                                                                                                                                                                                                                    t)
                                                                                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0000#4) && (CRn == 0b0110#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                      (FAR_EL1_SysRegRead_4ac11836ed369460
                                                                                                                                                                                                                                                                                                        el
                                                                                                                                                                                                                                                                                                        op0
                                                                                                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                                                                                                        CRn
                                                                                                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                                                                                                        CRm
                                                                                                                                                                                                                                                                                                        t)
                                                                                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0011#4) && (CRn == 0b0001#4)) && (op0 == 0b11#2)) && (op1 == 0b110#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                          (MDCR_EL3_SysRegRead_fa75e32e1a0e4d27
                                                                                                                                                                                                                                                                                                            el
                                                                                                                                                                                                                                                                                                            op0
                                                                                                                                                                                                                                                                                                            op1
                                                                                                                                                                                                                                                                                                            CRn
                                                                                                                                                                                                                                                                                                            op2
                                                                                                                                                                                                                                                                                                            CRm
                                                                                                                                                                                                                                                                                                            t)
                                                                                                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0011#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b110#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                              (AMAIR_EL3_SysRegRead_098fd5c15cd15cd8
                                                                                                                                                                                                                                                                                                                el
                                                                                                                                                                                                                                                                                                                op0
                                                                                                                                                                                                                                                                                                                op1
                                                                                                                                                                                                                                                                                                                CRn
                                                                                                                                                                                                                                                                                                                op2
                                                                                                                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                                                                                                                t)
                                                                                                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0000#4) && (CRn == 0b0001#4)) && (op0 == 0b11#2)) && (op1 == 0b110#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                  (SCTLR2_EL3_SysRegRead_87ae87d52be38631
                                                                                                                                                                                                                                                                                                                    el
                                                                                                                                                                                                                                                                                                                    op0
                                                                                                                                                                                                                                                                                                                    op1
                                                                                                                                                                                                                                                                                                                    CRn
                                                                                                                                                                                                                                                                                                                    op2
                                                                                                                                                                                                                                                                                                                    CRm
                                                                                                                                                                                                                                                                                                                    t)
                                                                                                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b1100#4) && (CRn == 0b1001#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                      (PMCNTENSET_EL0_SysRegRead_4d90af887d9c8c94
                                                                                                                                                                                                                                                                                                                        el
                                                                                                                                                                                                                                                                                                                        op0
                                                                                                                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                                                                                                                        CRn
                                                                                                                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                                                                                                                        CRm
                                                                                                                                                                                                                                                                                                                        t)
                                                                                                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b1001#4) && (CRn == 0b1100#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                          (ICC_SRE_EL2_SysRegRead_7b340e47907381fb
                                                                                                                                                                                                                                                                                                                            el
                                                                                                                                                                                                                                                                                                                            op0
                                                                                                                                                                                                                                                                                                                            op1
                                                                                                                                                                                                                                                                                                                            CRn
                                                                                                                                                                                                                                                                                                                            op2
                                                                                                                                                                                                                                                                                                                            CRm
                                                                                                                                                                                                                                                                                                                            t)
                                                                                                                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0010#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b111#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                              (CNTPS_CTL_EL1_SysRegRead_b28f26339dbc713f
                                                                                                                                                                                                                                                                                                                                el
                                                                                                                                                                                                                                                                                                                                op0
                                                                                                                                                                                                                                                                                                                                op1
                                                                                                                                                                                                                                                                                                                                CRn
                                                                                                                                                                                                                                                                                                                                op2
                                                                                                                                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                                                                                                                                t)
                                                                                                                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0000#4) && (CRn == 0b0011#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                  (DACR32_EL2_SysRegRead_7553854be98ecb11
                                                                                                                                                                                                                                                                                                                                    el
                                                                                                                                                                                                                                                                                                                                    op0
                                                                                                                                                                                                                                                                                                                                    op1
                                                                                                                                                                                                                                                                                                                                    CRn
                                                                                                                                                                                                                                                                                                                                    op2
                                                                                                                                                                                                                                                                                                                                    CRm
                                                                                                                                                                                                                                                                                                                                    t)
                                                                                                                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0000#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                      (CNTPCT_EL0_SysRegRead_30a0e264d583fe56
                                                                                                                                                                                                                                                                                                                                        el
                                                                                                                                                                                                                                                                                                                                        op0
                                                                                                                                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                                                                                                                                        CRn
                                                                                                                                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                                                                                                                                        CRm
                                                                                                                                                                                                                                                                                                                                        t)
                                                                                                                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0010#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                          (MAIR_EL2_SysRegRead_c37e0065b9939c9e
                                                                                                                                                                                                                                                                                                                                            el
                                                                                                                                                                                                                                                                                                                                            op0
                                                                                                                                                                                                                                                                                                                                            op1
                                                                                                                                                                                                                                                                                                                                            CRn
                                                                                                                                                                                                                                                                                                                                            op2
                                                                                                                                                                                                                                                                                                                                            CRm
                                                                                                                                                                                                                                                                                                                                            t)
                                                                                                                                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0100#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                              (LORC_EL1_SysRegRead_50b423e6e0102ba8
                                                                                                                                                                                                                                                                                                                                                el
                                                                                                                                                                                                                                                                                                                                                op0
                                                                                                                                                                                                                                                                                                                                                op1
                                                                                                                                                                                                                                                                                                                                                CRn
                                                                                                                                                                                                                                                                                                                                                op2
                                                                                                                                                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                                                                                                                                                t)
                                                                                                                                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0100#4) && (CRn == 0b0000#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                  (ID_AA64PFR2_EL1_SysRegRead_c98524f93c119d97
                                                                                                                                                                                                                                                                                                                                                    el
                                                                                                                                                                                                                                                                                                                                                    op0
                                                                                                                                                                                                                                                                                                                                                    op1
                                                                                                                                                                                                                                                                                                                                                    CRn
                                                                                                                                                                                                                                                                                                                                                    op2
                                                                                                                                                                                                                                                                                                                                                    CRm
                                                                                                                                                                                                                                                                                                                                                    t)
                                                                                                                                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0000#4) && (CRn == 0b1101#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                      (SCXTNUM_EL1_SysRegRead_32a07f15f90850b2
                                                                                                                                                                                                                                                                                                                                                        el
                                                                                                                                                                                                                                                                                                                                                        op0
                                                                                                                                                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                                                                                                                                                        CRn
                                                                                                                                                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                                                                                                                                                        CRm
                                                                                                                                                                                                                                                                                                                                                        t)
                                                                                                                                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                          (TCR_EL2_SysRegRead_424c76a4449d67b2
                                                                                                                                                                                                                                                                                                                                                            el
                                                                                                                                                                                                                                                                                                                                                            op0
                                                                                                                                                                                                                                                                                                                                                            op1
                                                                                                                                                                                                                                                                                                                                                            CRn
                                                                                                                                                                                                                                                                                                                                                            op2
                                                                                                                                                                                                                                                                                                                                                            CRm
                                                                                                                                                                                                                                                                                                                                                            t)
                                                                                                                                                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0000#4) && (CRn == 0b0000#4)) && (op0 == 0b11#2)) && (op1 == 0b001#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                              (CCSIDR2_EL1_SysRegRead_7161997c851583ee
                                                                                                                                                                                                                                                                                                                                                                el
                                                                                                                                                                                                                                                                                                                                                                op0
                                                                                                                                                                                                                                                                                                                                                                op1
                                                                                                                                                                                                                                                                                                                                                                CRn
                                                                                                                                                                                                                                                                                                                                                                op2
                                                                                                                                                                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                                                                                                                                                                t)
                                                                                                                                                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0000#4) && (CRn == 0b0000#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                  (CTR_EL0_SysRegRead_17103694dd49566e
                                                                                                                                                                                                                                                                                                                                                                    el
                                                                                                                                                                                                                                                                                                                                                                    op0
                                                                                                                                                                                                                                                                                                                                                                    op1
                                                                                                                                                                                                                                                                                                                                                                    CRn
                                                                                                                                                                                                                                                                                                                                                                    op2
                                                                                                                                                                                                                                                                                                                                                                    CRm
                                                                                                                                                                                                                                                                                                                                                                    t)
                                                                                                                                                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0011#4) && (CRn == 0b0100#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                      (SPSR_und_SysRegRead_ffbc14073ddb1072
                                                                                                                                                                                                                                                                                                                                                                        el
                                                                                                                                                                                                                                                                                                                                                                        op0
                                                                                                                                                                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                                                                                                                                                                        CRn
                                                                                                                                                                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                                                                                                                                                                        CRm
                                                                                                                                                                                                                                                                                                                                                                        t)
                                                                                                                                                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0110#4) && (CRn == 0b0000#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                          (ID_AA64ISAR2_EL1_SysRegRead_c585336ab0c39b5d
                                                                                                                                                                                                                                                                                                                                                                            el
                                                                                                                                                                                                                                                                                                                                                                            op0
                                                                                                                                                                                                                                                                                                                                                                            op1
                                                                                                                                                                                                                                                                                                                                                                            CRn
                                                                                                                                                                                                                                                                                                                                                                            op2
                                                                                                                                                                                                                                                                                                                                                                            CRm
                                                                                                                                                                                                                                                                                                                                                                            t)
                                                                                                                                                                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0010#4) && (CRn == 0b0100#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                                              (SSBS_SysRegRead_2e7b32f98c2852d5
                                                                                                                                                                                                                                                                                                                                                                                el
                                                                                                                                                                                                                                                                                                                                                                                op0
                                                                                                                                                                                                                                                                                                                                                                                op1
                                                                                                                                                                                                                                                                                                                                                                                CRn
                                                                                                                                                                                                                                                                                                                                                                                op2
                                                                                                                                                                                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                                                                                                                                                                                t)
                                                                                                                                                                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0001#4) && (CRn == 0b0001#4)) && (op0 == 0b11#2)) && (op1 == 0b110#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                                  (CPTR_EL3_SysRegRead_7b3995450955fa38
                                                                                                                                                                                                                                                                                                                                                                                    el
                                                                                                                                                                                                                                                                                                                                                                                    op0
                                                                                                                                                                                                                                                                                                                                                                                    op1
                                                                                                                                                                                                                                                                                                                                                                                    CRn
                                                                                                                                                                                                                                                                                                                                                                                    op2
                                                                                                                                                                                                                                                                                                                                                                                    CRm
                                                                                                                                                                                                                                                                                                                                                                                    t)
                                                                                                                                                                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0010#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                                      (S2POR_EL1_SysRegRead_e4b7b03dbe33ccaa
                                                                                                                                                                                                                                                                                                                                                                                        el
                                                                                                                                                                                                                                                                                                                                                                                        op0
                                                                                                                                                                                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                                                                                                                                                                                        CRn
                                                                                                                                                                                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                                                                                                                                                                                        CRm
                                                                                                                                                                                                                                                                                                                                                                                        t)
                                                                                                                                                                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                                                    (pure true)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
