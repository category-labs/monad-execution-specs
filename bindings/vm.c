#include <evmc/evmc.h>
#include <caml/alloc.h>
#include <caml/mlvalues.h>
#include <caml/callback.h>

void __caml_init() {
    static int once = 0;
    if (once == 0) {
        char* argv[] = {"ocaml_startup", NULL};
        caml_startup(argv);
        once = 1;
    }
}

void introspect(value val) {
    if (Is_block(val)) {
        printf("POINTER %p\n", (value*)(val));
    } else {
        printf("INTEGER %lx\n", Val_long(val));
    }
}

const struct evmc_vm* evmc_create() {
    __caml_init();
    static const struct evmc_vm* monad_vm = NULL;
    if (monad_vm == NULL) {
        uint64_t vm_int = Long_val((value)*caml_named_value("monad_vm"));
        monad_vm = (const struct evmc_vm*)vm_int;
    }
    return monad_vm;
}
