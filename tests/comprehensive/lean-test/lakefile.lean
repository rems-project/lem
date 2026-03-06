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
    `Pervasives_extra,
    `Test_assertions, `Test_assertions_auxiliary,
    `Test_classes_advanced, `Test_classes_advanced_auxiliary,
    `Test_comments_whitespace, `Test_comments_whitespace_auxiliary,
    -- Test_comprehensions: expected failure (BEq instance synthesis)
    `Test_constructors, `Test_constructors_auxiliary,
    `Test_do_notation, `Test_do_notation_auxiliary,
    `Test_either_maybe, `Test_either_maybe_auxiliary,
    `Test_expressions_edge, `Test_expressions_edge_auxiliary,
    `Test_function_patterns, `Test_function_patterns_auxiliary,
    `Test_higher_order, `Test_higher_order_auxiliary,
    -- Test_indreln: expected failure (inductive relation syntax)
    `Test_infix_ops, `Test_infix_ops_auxiliary,
    `Test_lean_reserved_words, `Test_lean_reserved_words_auxiliary,
    `Test_let_forms, `Test_let_forms_auxiliary,
    `Test_modules, `Test_modules_auxiliary,
    `Test_mutual_recursion, `Test_mutual_recursion_auxiliary,
    `Test_numeric_formats, `Test_numeric_formats_auxiliary,
    `Test_pattern_edge_cases, `Test_pattern_edge_cases_auxiliary,
    `Test_records_advanced, `Test_records_advanced_auxiliary,
    `Test_scope_shadowing, `Test_scope_shadowing_auxiliary,
    -- Test_sets_maps: expected failure (setElemCompare)
    -- Test_stress_large: expected failure (BEq instance synthesis)
    `Test_strings_chars, `Test_strings_chars_auxiliary,
    `Test_target_specific, `Test_target_specific_auxiliary,
    `Test_type_features, `Test_type_features_auxiliary
  ]
