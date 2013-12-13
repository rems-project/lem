# Refactoring

- backend `lem` used for refactoring
- use command-line option `-lem`
- file `myfile.lem` translated to `myfile-processed.lem`
- compare files, modify `myfile-processed.lem`, when ready rename back to `myfile.lem`

## Types

    declare {lem} rename type nat = NAT
    declare lem target_rep type set 'a = `SET` 'a 'a
	
## Functions / Fields

    declare {lem} rename function my_fun = my_fun'
    declare lem target_rep function my_fun x y z = `my_fun'` (x, y) true z

Also possible `lem_transform`. However, better use `declare lem target_rep` instead of `lem_transform`. TODO: remove `lem_transform`

    let lem_transform my_fun x y z = other_existing_function y z 

## Modules

    declare {lem} rename module my_mod = my_mod_new_name


