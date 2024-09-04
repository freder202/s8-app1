########################################################################
## Author  :    Marc-Andre Tetrault
## Project :    Verification Primer
##
## Universite de Sherbrooke
########################################################################

# remove code coverage from checkers. Keep assertions and cover properties
deselect_coverage -bet -sysv_bind_modules

#
deselect_coverage -remove_empty_instances


#
set_implicit_block_scoring -off

#
set_toggle_portsonly

#
set_com
# consider using the nounconnect option

set_expr_coverable_operators -all
set_expr_coverable_operators -logical_not
set_expr_coverable_statements -all

# override default zero, where no coverage is collected.
set_covergroup -per_instance_default_one
