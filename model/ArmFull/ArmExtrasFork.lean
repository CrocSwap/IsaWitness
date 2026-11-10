import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1

open Sail ArmFull

abbrev sign_extend {w : Nat} (x : BitVec w) (w' : Nat) := Sail.BitVec.signExtend x w'

def dec_str (x : Int) := x.repr
def hex_str (x : Int) := x.toHex

def putchar (_ : Int) : Unit := ()

def sleep_request (_ : Unit) : SailM Unit := pure ()
def wakeup_request (_ : Unit) : SailM Unit := pure ()

macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  first
  | grind
  | decide)
