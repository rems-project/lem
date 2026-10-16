/- arc-14 re-mark, be:S1: the none-binder capture pin (see
   test_name_capture.lem). The avoid machinery renames constructor-named
   binders; these guards fail the BUILD if that defense ever regresses
   (a captured «none» pattern would flip both results). -/
import Test_name_capture

#guard cap_use (some (some 5)) == some 5
#guard cap_use (some none) == none
#guard cap_use none == none
#guard cap_shadow (some (some 5)) == none
#guard cap_shadow (some none) == none
