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
    `Test_assertions, `Test_assertions_auxiliary,
    `Test_classes_advanced, `Test_classes_advanced_auxiliary,
    `Test_comments_whitespace, `Test_comments_whitespace_auxiliary,
    `Test_comprehensions, `Test_comprehensions_auxiliary,
    `Test_constructors, `Test_constructors_auxiliary,
    `Test_do_notation, `Test_do_notation_auxiliary,
    `Test_either_maybe, `Test_either_maybe_auxiliary,
    `Test_expressions_edge, `Test_expressions_edge_auxiliary,
    `Test_function_patterns, `Test_function_patterns_auxiliary,
    `Test_higher_order, `Test_higher_order_auxiliary,
    `Test_indreln, `Test_indreln_auxiliary,
    `Test_infix_ops, `Test_infix_ops_auxiliary,
    `Test_lean_reserved_words, `Test_lean_reserved_words_auxiliary,
    `Test_let_forms, `Test_let_forms_auxiliary,
    `Test_modules, `Test_modules_auxiliary,
    `Test_mutual_recursion, `Test_mutual_recursion_auxiliary,
    `Test_numeric_formats, `Test_numeric_formats_auxiliary,
    `Test_pattern_edge_cases, `Test_pattern_edge_cases_auxiliary,
    `Test_records_advanced, `Test_records_advanced_auxiliary,
    `Test_scope_shadowing, `Test_scope_shadowing_auxiliary,
    `Test_sets_maps, `Test_sets_maps_auxiliary,
    `Test_stress_large, `Test_stress_large_auxiliary,
    `Test_strings_chars, `Test_strings_chars_auxiliary,
    `Test_target_specific, `Test_target_specific_auxiliary,
    `Test_typ_args, `Test_typ_args_auxiliary,
    `Test_type_features, `Test_type_features_auxiliary,
    `Test_vectors, `Test_vectors_auxiliary,
    `Test_audit_regressions, `Test_audit_regressions_auxiliary,
    `Test_cross_module, `Test_cross_module_auxiliary,
    `Test_case_arm_nesting, `Test_case_arm_nesting_auxiliary,
    `Test_termination, `Test_termination_auxiliary,
    `Test_mword, `Test_mword_auxiliary,
    `Test_class_instance_constraints, `Test_class_instance_constraints_auxiliary,
    `Test_pattern_complex, `Test_pattern_complex_auxiliary,
    `Test_mutual_indreln, `Test_mutual_indreln_auxiliary,
    `Test_set_comprehension_advanced, `Test_set_comprehension_advanced_auxiliary,
    `Test_integer_arithmetic, `Test_integer_arithmetic_auxiliary,
    `Test_inline_target_rep, `Test_inline_target_rep_auxiliary,
    `Test_type_defs_advanced, `Test_type_defs_advanced_auxiliary,
    `Test_fun_and_function, `Test_fun_and_function_auxiliary,
    `Test_quantifiers_and_sets, `Test_quantifiers_and_sets_auxiliary,
    `Test_let_def_destructuring, `Test_let_def_destructuring_auxiliary,
    `Test_cross_module_base, `Test_cross_module_base_auxiliary,
    `Test_cross_module_import, `Test_cross_module_import_auxiliary,
    `Test_mutual_records, `Test_mutual_records_auxiliary,
    `Test_parameterized_instances, `Test_parameterized_instances_auxiliary,
    `Test_local_modules, `Test_local_modules_auxiliary,
    `Test_keyword_types, `Test_keyword_types_auxiliary,
    `Test_nested_match, `Test_nested_match_auxiliary,
    `Test_cerberus_patterns, `Test_cerberus_patterns_auxiliary,
    `Test_cerberus_remaining, `Test_cerberus_remaining_auxiliary,
    `Test_cross_recup_base, `Test_cross_recup_base_auxiliary,
    `Test_cross_recup_import, `Test_cross_recup_import_auxiliary,
    `Test_cross_field_access,
    `Test_cross_field_access_import,
    `Test_inline_theorem, `Test_inline_theorem_auxiliary,
    `Test_monadic_let, `Test_monadic_let_auxiliary,
    `Test_map_fold_mutual, `Test_map_fold_mutual_auxiliary,
    `Test_sorry_unit_match, `Test_sorry_unit_match_auxiliary,
    `Test_settype_unit, `Test_settype_unit_auxiliary,
    `Test_deriving_deep, `Test_deriving_deep_auxiliary
  ]
