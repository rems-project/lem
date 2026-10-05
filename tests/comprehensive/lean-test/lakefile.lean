import Lake
open Lake DSL

package LemComprehensiveTest where
  version := v!"0.1.0"
  moreLeanArgs := #["-DautoImplicit=false"]

require LemLib from "../../../lean-lib"

@[default_target]
lean_lib LemComprehensiveTest where
  srcDir := "."
  roots := #[
    `Test_case_arm_parsing, `Test_case_arm_parsing_auxiliary,
    `Test_cerberus_patterns, `Test_cerberus_patterns_auxiliary,
    `Test_classes, `Test_classes_auxiliary,
    `Test_cmp_threading, `Test_cmp_threading_auxiliary,  -- comparison dictionaries threaded through generic defs (linksem audit A1)
    `Test_collections, `Test_collections_auxiliary,
    `Test_comments, `Test_comments_auxiliary,  -- comments survive; layout sound (output-niceness S1)
    `Test_layout, `Test_layout_auxiliary,  -- long declarations broken over lines (output-niceness S3-A)
    `Test_text_fidelity, `Test_text_fidelity_auxiliary,  -- target_rep text intact through the passes (audit fixes)
    `TestTextFidelityHelper,  -- hand-written: `«a b»` for test_text_fidelity
    `Test_contextual_keywords, `Test_contextual_keywords_auxiliary,
    `Test_contextual_keywords_lemMeasureProofs,  -- hand-written proof of its measured declare's obligation (fuel-measure slice)
    `Test_cross_field_access,
    `Test_cross_field_access_import,
    `Test_cross_module, `Test_cross_module_auxiliary,
    `Test_cross_module_base, `Test_cross_module_base_auxiliary,
    `Test_cross_module_import, `Test_cross_module_import_auxiliary,
    `Test_cross_recup_base, `Test_cross_recup_base_auxiliary,
    `Test_cross_recup_import, `Test_cross_recup_import_auxiliary,
    `Test_derived_comparison, `Test_derived_comparison_auxiliary,
    `Test_derived_inhabited, `Test_derived_inhabited_auxiliary,
    `TestDerivedInhabitedCheck,  -- hand-written arc-8 S1 instance-shape checks
    `TestInstancePriorityCheck,  -- hand-written arc-14 B4 resolution probe (be:G1/sem:S2)
    `TestNameCaptureCheck,  -- arc-14 re-mark be:S1 none-binder pin
    `Test_deriving, `Test_deriving_auxiliary,
    `Test_either_maybe, `Test_either_maybe_auxiliary,
    `Test_expressions, `Test_expressions_auxiliary,
    `Test_integer_div, `Test_integer_div_auxiliary,
    `Test_if_bool_cond, `Test_if_bool_cond_auxiliary,  -- Bool if via lem_if where Lean`s if gets stuck (linksem B13)
    `Test_instance_priority, `Test_instance_priority_auxiliary,
    `Test_name_capture, `Test_name_capture_auxiliary,
    `Test_failwith_threading, `Test_failwith_threading_auxiliary,
    `TestFailwithThreadingCheck,  -- hand-written arc-8 S2 signature-shape checks
    `Test_fuel_measure, `Test_fuel_measure_auxiliary,  -- the auxiliary file carries the generated fuel_measure OBLIGATIONS (fuel-measure slice)
    `Test_fuel_measure_lemMeasureProofs,  -- hand-written proofs of those obligations (imported by the auxiliary file; the build fails without it)
    `Test_fuel_measure_types, `Test_fuel_measure_types_auxiliary,
    `Test_fuel_measure_tree, `Test_fuel_measure_tree_auxiliary,
    `Test_fuel_measure_tree_lemMeasureProofs,  -- hand-written proofs (nested inductive, foldl as written)
    `TestFuelMeasureImpl,  -- hand-written COMPUTABLE structural size of mtree (a measure over a user type)
    `TestFuelMeasureCheck,  -- hand-written fuel-measure kernel pins (decide/rfl through measured wrappers; consumers binder-free)
    `Test_fuel_measure_hyp, `Test_fuel_measure_hyp_auxiliary,  -- the `assuming` hypothesis form (measure-hypothesis slice): obligations with the `lemHyp` binder
    `Test_fuel_measure_hyp_lemMeasureProofs,  -- hand-written proofs USING the hypotheses (the build fails without it)
    `TestFuelMeasureHypImpl,  -- hand-written hypothesis predicate (`Ranked`), named in the declare
    `TestFuelMeasureHypCheck,  -- hand-written kernel pins (wrappers hypothesis-free; obligations applied with H; exhaustion outside H)
    `Test_lem_size, `Test_lem_size_auxiliary,  -- backend-derived size functions as fuel measures (D2-enablers slice)
    `Test_lem_size_lemMeasureProofs,  -- hand-written proofs of its obligations (the build fails without it)
    `TestLemSizeCheck,  -- hand-written derived-size kernel pins (decide through the sizes and the measured wrappers; #print axioms)
    `Test_fuel_param, `Test_fuel_param_auxiliary,
    `TestFuelConsumerImpl,  -- hand-written fuel_consumer implementation ([LemFuel])
    `TestFuelParamCheck,  -- hand-written fuel-parameter kernel pins (fuel-parameter arc)
    `TestFuelMonoExemplar,  -- hand-proved fuel-monotonicity exemplar (Route B: completion predicate; structural-declare slice)
    `Test_fuel_mutual_reader, `Test_fuel_mutual_reader_auxiliary,  -- fuel x reader x truly-mutual blocks (program-data-parameters S1.5, 2026-09-20); the auxiliary file carries the measured pair's obligations
    `Test_fuel_mutual_reader_lemMeasureProofs,  -- hand-written proofs of those obligations (reader binder before the parameters; the build fails without it)
    `TestFuelMutualReaderCheck,  -- hand-written kernel pins (signatures with the reader binder, _zero lemmas, fuel-parametricity, reader-decided values)
    `Test_function_tails, `Test_function_tails_auxiliary,  -- point-free `function` tails hoisted for measured/structural defs (tails-and-pmap-laws slice)
    `Test_function_tails_lemMeasureProofs,  -- hand-written proofs of its obligations (the build fails without it)
    `TestFunctionTailsCheck,  -- hand-written kernel pins (decide/rfl through the hoisted binders; the applied sentinel)
    `Test_functions, `Test_functions_auxiliary,
    `Test_fn_field_compare, `Test_fn_field_compare_auxiliary,  -- structural compare of function-field types (linksem audit A1)
    `Test_indreln, `Test_indreln_auxiliary,
    `Test_instances, `Test_instances_auxiliary,
    `Test_keywords, `Test_keywords_auxiliary,
    `Test_empty_list_ascription, `Test_empty_list_ascription_auxiliary,  -- empty list literals of closed type ascribed everywhere (review fix 2026-09-30, LOW c)
    `Test_long_if_chain, `Test_long_if_chain_auxiliary,  -- >96-arm else-if chains split into continuations (linksem B3)
    `Test_nested_abbrev, `Test_nested_abbrev_auxiliary,  -- abbreviations expanded in nested ctor args (linksem B4)
    `Test_lambda_let, `Test_lambda_let_auxiliary,  -- local lambda lets annotated (linksem B11)
    `Test_let_bindings, `Test_let_bindings_auxiliary,
    `Test_misc, `Test_misc_auxiliary,
    `Test_modules, `Test_modules_auxiliary,
    `Test_multiclause, `Test_multiclause_auxiliary,  -- multi-clause groups as Lean equations (TODO 39 pin)
    `Test_mutual_types, `Test_mutual_types_auxiliary,
    `Test_mutual_record_order, `Test_mutual_record_order_auxiliary,  -- mutual record literals in declaration order (linksem B7)
    `Test_mword, `Test_mword_auxiliary,
    `Test_numeric, `Test_numeric_auxiliary,
    `Test_patterns, `Test_patterns_auxiliary,
    `Test_instance_reader, `Test_instance_reader_auxiliary,  -- instance-implicit readers (instance-reader slice, 2026-10-05); the auxiliary file carries the measured ilen's obligation
    `Test_instance_reader_lemMeasureProofs,  -- hand-written proof of that obligation ([Sw] before the parameters; the build fails without it)
    `TestInstanceReaderImpl,  -- hand-written classes Sw/Md and the consumer implementations (they bind the class themselves)
    `TestInstanceReaderCheck,  -- hand-written signature pins (binder kind and order) and kernel rfl pins at concrete instances
    `Test_reader_consumer, `Test_reader_consumer_auxiliary,
    `TestReaderConsumerImpl,   -- hand-written consumer implementation (leading reader params)
    `TestReaderConsumerCheck,  -- hand-written reader_consumer pins (effect-retirement L1)
    `Test_reader_multi, `Test_reader_multi_auxiliary,
    `TestReaderMultiImpl,   -- hand-written three-reader consumer implementation (N-ary reader_seed slice, 2026-09-19)
    `TestReaderMultiCheck,  -- hand-written N-ary reader_seed pins (sorted-order binders; per-reader seed pickup; swap sensitivity)
    `Test_records, `Test_records_auxiliary,
    `Test_scope_shadowing, `Test_scope_shadowing_auxiliary,
    `Test_strings_chars, `Test_strings_chars_auxiliary,
    `Test_target_reps, `Test_target_reps_auxiliary,
    `Test_target_specific, `Test_target_specific_auxiliary,
    `Test_termination, `Test_termination_auxiliary,
    `Test_stress, `Test_stress_auxiliary,
    `Test_structural, `Test_structural_auxiliary,
    `TestStructuralCheck,  -- hand-written structural-declare kernel pins (decide/rfl through structural defs)
    `Test_supply, `Test_supply_auxiliary,
    `Test_supply_multi, `Test_supply_multi_auxiliary,
    `Test_symbolic_ops, `Test_symbolic_ops_auxiliary,  -- symbolic constant names via ascii_rep (linksem B1)
    `TestSupplyCheck,  -- hand-written supply draw-order/signature pins (effect-retirement L1)
    `Test_types_advanced, `Test_types_advanced_auxiliary,
    `Test_untaken_failure, `Test_untaken_failure_auxiliary,  -- untaken failure branches stay untaken (linksem B8/B9)
    `Test_tuple_inst_arity, `Test_tuple_inst_arity_auxiliary,  -- class instances at several tuple arities (linksem B14)
    `Test_tuple_let_once, `Test_tuple_let_once_auxiliary,
    `TupleLetTick,  -- hand-written m7 single-evaluation counter
    `Test_types_basic, `Test_types_basic_auxiliary,
    `Test_tyvar_collision, `Test_tyvar_collision_auxiliary,  -- type variables renamed on collision (backend-hardening item 3)
    `Test_wide_patterns, `Test_wide_patterns_auxiliary,  -- wide patterns generate in bounded time (backend-hardening item 5)
    `Test_vectors, `Test_vectors_auxiliary,
    `TestExtraImportHelper  -- hand-written helper for extra_import test
  ]

-- Arc-8 audit fix (auditor A F1): panic-path pin for the L_undefined
-- rendering (run by the Makefile `lean-panic` target under
-- LEAN_ABORT_ON_PANIC=1; must abort with the Incomplete Pattern message).
lean_exe «test-failwith-panic» where
  root := `TestFailwithThreadingPanic

-- Untaken failure branches are not evaluated at module init (linksem B8/B9);
-- run by the Makefile `lean-untaken-failure` target.
lean_exe «test-untaken-failure» where
  root := `TestUntakenFailure

lean_exe «test-tuple-let-once» where
  root := `TestTupleLetOnce

-- Effect-retirement L1: compiled-binary behavioral test of the supply
-- transform (draw sequencing, single evaluation, fuel/reader/multi
-- composition; suite phase lean-supply-draws).
lean_exe «test-supply-draws» where
  root := `TestSupplyDraws

-- Effect-retirement L1: compiled-binary behavioral test of
-- reader_consumer injection (lifted caller, HOF partial application,
-- reader_seed pickup; suite phase lean-reader-consumer).
lean_exe «test-reader-consumer» where
  root := `TestReaderConsumerExec

-- N-ary reader_seed (program-data-parameters S0.5, 2026-09-19):
-- compiled-binary behavioral test of the per-reader seed association
-- with three declared readers (sorted-order binders, seed pickup through
-- the consumer and through lifted callees, alpha/gamma swap
-- sensitivity, supply composition; suite phase lean-reader-multi).
lean_exe «test-reader-multi» where
  root := `TestReaderMultiExec

-- Fuel-parameter arc (2026-09-04): compiled-binary behavioral test of
-- the quantified fuel (two sufficient fuels agree; the declared sentinel
-- at an insufficient one; a callee starts from the full ambient; the
-- loud-exhaustion leg under LEAN_ABORT_ON_PANIC=1; suite phase
-- lean-fuel-param).
lean_exe «test-fuel-param» where
  root := `TestFuelParamExec

-- fuel x reader x truly-mutual blocks (program-data-parameters S1.5,
-- 2026-09-20): compiled-binary behavioral test that the reader value
-- reaches every member of a fuel'd mutual block, that sibling hops pass
-- the decremented counter, that a fuel'd callee starts from the full
-- ambient, and that the measured pair follows the reader (suite phase
-- lean-fuel-mutual-reader).
lean_exe «test-fuel-mutual-reader» where
  root := `TestFuelMutualReaderExec

-- Instance-implicit readers (instance-reader slice, 2026-10-05): compiled
-- binary that the runtime-chosen instance reaches every lifted definition
-- (transitive callee, consumer, seed def, fuel'd mutual block,
-- coexistence with an explicit reader and fuel; suite phase
-- lean-instance-reader).
lean_exe «test-instance-reader» where
  root := `TestInstanceReaderExec
