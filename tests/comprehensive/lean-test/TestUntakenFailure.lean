/- Driver for test_untaken_failure.lem (linksem 2026-09-28, B8/B9); run by the
   Makefile `lean-untaken-failure` target under LEAN_ABORT_ON_PANIC=1.
   No arguments: every failure branch is untaken, so the run must print
   `untaken: 0 z` and exit 0 (pre-fix: silent SIGABRT during module init).
   Argument `take`: `pick true` reaches `must_be_small 10`, which must abort
   loudly with its message. Argument `failstop`: leg 3; `twice`: leg 4 (below). -/
import Test_untaken_failure

def main (args : List String) : IO Unit := do
  -- leg 3 (audit item 2; D1(b) [USER 2026-09-30]): `failstop` first calls
  -- LemLib's `lemRequireAbortOnPanic`, which must REFUSE to run unless
  -- LEAN_ABORT_ON_PANIC is exactly 1 (3a unset, 3b "0"); with it set (3c)
  -- the reached failure fail-stops. Plant: removing this call makes 3a
  -- print the panic, continue and exit 0 (leg 3 FAILS).
  if args == ["failstop"] then lemRequireAbortOnPanic
  -- leg 4 (B8 on 4.32.2, review fix 2026-09-30): `twice` reaches
  -- `Assert_extra.fail` at two DIFFERENT runtime arguments, run WITHOUT
  -- LEAN_ABORT_ON_PANIC. With `never_extract` each reached failure panics
  -- (two PANIC lines, as OCaml raises each time); without it the closed term
  -- `@fail Char _` is extracted and lazily initialised once, and the second
  -- failure is SILENT (measured). Output goes to stderr, unbuffered, so the
  -- lines interleave with the panics.
  if args == ["twice"] then
    IO.eprintln s!"twice-1 {pick_char (args.length)}"
    IO.eprintln s!"twice-2 {pick_char (args.length + 1)}"
    return
  let take := args == ["take"] || args == ["failstop"]
  IO.println s!"untaken: {pick take} {pick_char 0}"
