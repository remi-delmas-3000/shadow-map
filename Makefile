address_reuse:
	cbmc --pointer-check --signed-overflow-check --unsigned-overflow-check --conversion-check --undefined-shift-check --bounds-check --slice-formula address_reuse.c

address_reuse_full_width:
	cbmc -DFULL_WIDTH --pointer-check --signed-overflow-check --unsigned-overflow-check --conversion-check --undefined-shift-check --bounds-check --slice-formula address_reuse.c

nondet_init_bounded:
	cbmc -DSIZE=150 --slice-formula --pointer-check --pointer-overflow-check --signed-overflow-check --unsigned-overflow-check --conversion-check --bounds-check --malloc-may-fail --malloc-fail-null nondet_init.c

nondet_init_bounded_bug:
	cbmc -DSIZE=100 -DBUG=1 --slice-formula --pointer-check --pointer-overflow-check --signed-overflow-check --unsigned-overflow-check --conversion-check --bounds-check --malloc-may-fail --malloc-fail-null nondet_init.c

nondet_init_unbounded:
	cbmc -DUNBOUNDED --slice-formula --pointer-check --pointer-overflow-check --signed-overflow-check --unsigned-overflow-check --conversion-check --bounds-check --malloc-may-fail --malloc-fail-null nondet_init.c

nondet_init_unbounded_bug:
	cbmc -DUNBOUNDED -DBUG=1 --slice-formula --pointer-check --pointer-overflow-check --signed-overflow-check --unsigned-overflow-check --conversion-check --bounds-check --malloc-may-fail --malloc-fail-null nondet_init.c

shadow_struct:
	cbmc --pointer-check --signed-overflow-check --unsigned-overflow-check --conversion-check --undefined-shift-check --bounds-check --slice-formula shadow_struct.c
