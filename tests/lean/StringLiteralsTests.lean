module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std
namespace string_literals_tests

theorem empty_length : (toStr "").val.length = 0 := by
  rw [toStr_length]
  rfl

theorem ascii_length : (toStr "index out of bounds").val.length = 19 := by
  rw [toStr_length]
  rfl

theorem utf8_length : (toStr "位读取🙂").val.length = 13 := by
  rw [toStr_length]
  rfl

theorem nul_length : (toStr "a\x00b").val.length = 3 := by
  rw [toStr_length]
  rfl

#print axioms toStr_length
#print axioms empty_length
#print axioms ascii_length
#print axioms utf8_length
#print axioms nul_length
end string_literals_tests
