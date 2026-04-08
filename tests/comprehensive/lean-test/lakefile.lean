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
    `Test_cerberus_remaining, `Test_cerberus_remaining_auxiliary,
    `Test_classes, `Test_classes_auxiliary,
    `Test_collections, `Test_collections_auxiliary,
    `Test_cross_field_access,
    `Test_cross_field_access_import,
    `Test_cross_module, `Test_cross_module_auxiliary,
    `Test_cross_module_base, `Test_cross_module_base_auxiliary,
    `Test_cross_module_import, `Test_cross_module_import_auxiliary,
    `Test_cross_recup_base, `Test_cross_recup_base_auxiliary,
    `Test_cross_recup_import, `Test_cross_recup_import_auxiliary,
    `Test_deriving, `Test_deriving_auxiliary,
    `Test_either_maybe, `Test_either_maybe_auxiliary,
    `Test_expressions, `Test_expressions_auxiliary,
    `Test_indreln, `Test_indreln_auxiliary,
    `Test_instances, `Test_instances_auxiliary,
    `Test_keywords, `Test_keywords_auxiliary,
    `Test_let_bindings, `Test_let_bindings_auxiliary,
    `Test_modules, `Test_modules_auxiliary,
    `Test_mword, `Test_mword_auxiliary,
    `Test_patterns, `Test_patterns_auxiliary,
    `Test_records, `Test_records_auxiliary,
    `Test_scope_shadowing, `Test_scope_shadowing_auxiliary,
    `Test_strings_chars, `Test_strings_chars_auxiliary,
    `Test_target_reps, `Test_target_reps_auxiliary,
    `Test_target_specific, `Test_target_specific_auxiliary,
    `Test_termination, `Test_termination_auxiliary,
    `Test_vectors, `Test_vectors_auxiliary,
    `Test_beq_override  -- hand-written Lean test for BEq priority override
  ]
