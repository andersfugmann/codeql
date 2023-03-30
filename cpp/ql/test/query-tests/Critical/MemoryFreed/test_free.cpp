void *malloc(int);
void free(void *);
bool condition();
void use(void*);
void *realloc(void*, unsigned long);
int strlen(char*);
int asprintf(char ** strp, const char * fmt, ...);


void* test_double_free1(int *a) {
    free(a); // GOOD
    a[5] = 5; // BAD
    *a = 5; // BAD
    free(a); // BAD
    a = (int*) malloc(8);
    free(a); // GOOD
    a = (int*) malloc(8);
    if (!a) free(a); // Noop
    return a; // GOOD [FALSE POSITIVE]
}

void test_double_free_aliasing(void *a, void* b) {
    free(a); // GOOD
    a = b;
    free(a); // GOOD
    free(b); // BAD [NOT DETECTED]
}

void test_dominance1(void *a) {
    free(a);
    if (condition()) free(a); // BAD
}

void test_dominance2(void *a) {
    free(a);
    if (condition()) a = malloc(10);
    if (condition()) free(a); // BAD
}

void test_post_dominance1(int *a)
{
    if (condition()) free(a); // GOOD
    if (condition()) a[2] = 5; // GOOD
    if (condition()) free(a); // GOOD
    a[2] = 5; // BAD
    free(a); // BAD
}

void test_post_dominance2(void *a) {
    if (condition()) free(a);
    free(a); // BAD
}

void test_post_dominance3(void *a) {
    if (condition()) free(a);
    a = malloc(10);
    free(a); // GOOD
}

void test_use_after_free6(int *a, int *b) {
    free(a);
    a=b;
    free(b);
    if (condition()) a[0] = 5; // BAD [NOT DETECTED]
}

void test_use_after_free7(int *a) {
    a[0] = 42;
    free(a);

    if (a[3]) { // BAD
        free(a); // BAD
    }
}

class A {
public:
    void f();
};

void test_new1() {
    A *a = new A();
    delete(a);
    a->f(); // BAD [NOT DETECTED]
    delete(a); // BAD [NOT DETECTED]
}

void test_dereference1(A *a) {
    a->f(); // GOOD
    free(a);
    a->f(); // BAD
}

void* use_after_free(void *a) {
    free(a);
    use(a); // BAD
    return a; // BAD
}

void test_realloc1(void *a) {
    free(a);
    void *b = realloc(a, sizeof(a)*3); // BAD
    free(a); // BAD
    free(b); // GOOD
}
void* test_realloc2(char *a) {
    void *b = realloc(a, strlen(a)+3); // GOOD

    // From the man page on return values from realloc and reallocarray:
    // "If these functions  fail, the original block is left untouched; it is not freed or moved."
    if (!b) {
        free(a); // GOOD
    }
    free(b); // GOOD
}

void test_realloc3(void *a) {
    void *b = realloc(a, 100);
    if (b) free(b); // GOOD
    if (!b) { // GOOD
        free(a); // GOOD
    }
}

void test_ptr_deref(void ** a) {
    free(*a);
    *a = malloc(10);
    free(*a); // GOOD
    free(*a); // BAD [NOT DETECTED]
    *a = malloc(10);
    free(a[0]); // GOOD
    free(a[1]); // GOOD
}

struct list {
    struct list *next;
    void* data;
};

void test_loop1(struct list ** list_ptr) {
    struct list *next;
    while (*list_ptr) { // GOOD
        free((*list_ptr)->data); // GOOD
        next = (*list_ptr)->next; // GOOD
        free(*list_ptr); // GOOD
        *list_ptr = next; // GOOD
    }
    free(list_ptr); // GOOD
}

void test_use_after_free8(struct list * a) {
    if (condition()) free(a);
    a->data = malloc(10); // BAD
    free(a); // BAD
}

void test_loop2(char ** a) {
    while (*a) { // GOOD
        free(*a); // GOOD
        a++;
    }
    free(a); // GOOD
}

void* test_realloc4() {
    void *a = 0;
    void *b = realloc(a, 10); // GOOD [FALSE POSITIVE]
    if (!b) { return a; } // GOOD
    return b;
}

void test_sizeof(int *a) {
    free(a);
    int x = sizeof(a[0]); // GOOD
}

void call_by_reference(char * &a);
int custom_alloc_func(char ** a);

void test_reassign(char *a) {
    free(a); // GOOD
    asprintf(&a, "Hello world"); // GOOD
    free(a); //GOOD
    call_by_reference(a); // GOOD
    free(a); // GOOD
    int v;
    if (v = custom_alloc_func(&a)) return;
    free(a); // GOOD
}

char* test_return1(char *a) {
    int ret = condition();
    if (!ret) free(a);
    return (ret ? a : 0); // GOOD [FALSE POSITIVE]
}

char* test_return2(char *a) {
    int ret = condition();
    if (!ret) free(a);
    if (ret) return a; // GOOD
    else return 0;
}

void test_condition1(char *a) {
    free(a);
    if (asprintf(&a, "Hello world") || condition());
    free(a); //GOOD
    if (condition() || asprintf(&a, "Hello world"));
    free(a); // BAD
}

void test_condition2(char *a) {
    free(a);
    if (condition()) a = (char*) malloc(10);
    else custom_alloc_func(&a);
    free(a); // GOOD
}

void* test_return1(void *a) {
    free(a);
    return a; // BAD
}

void MmFreePagesFromMdl(void*);
void ExFreePool(void*);
void test_ms_free(void * memory_descriptor_list) {
    MmFreePagesFromMdl(memory_descriptor_list); //GOOD
    ExFreePool(memory_descriptor_list); // GOOD
}


void deallocatingfunction(void *a) {
    free(a);
}

void* test_indirect_dealloc1(void *a) {
    deallocatingfunction(a);
    return a; // BAD
}

void maybe_deallocatingfunction(void *a) {
    if (condition()) free(a);
}

void* test_indirect_dealloc2(void *a) {
    maybe_deallocatingfunction(a);
    return a; // GOOD
}

void not_deallocatingfunction(void *a, void *b) {
    free(b);
}

void* test_indirect_dealloc3(void *a) {
    not_deallocatingfunction(a, 0);
    return a; // GOOD
}

void any_function(void *a) { }
void* test_indirect_dealloc4(void *a) {
    any_function(a);
    return a;
}

void indirect_dealloc1(void *a) {
    not_deallocatingfunction(a, 0);
    free(a); // GOOD
}

void reassign(void ** a);
void not_deallocating(void *a) {
    reassign(&a);
    free(a); // GOOD
}

void indirect_dealloc2(void *a) {
    not_deallocating(a);
    free(a); // GOOD
}

void deallocatingfunction2(void *a) {
    deallocatingfunction(a);
}
void test_indirect_dealloc5(void *a) {
    maybe_deallocatingfunction(a);
    deallocatingfunction2(a); // GOOD
    free(a); // BAD
}

void indirect_realloc(void *a) {
    realloc(a, 100);
}

void test_indirect_realloc(void *a) {
    indirect_realloc(a);
    free(a); // BAD [NOT DETECTED]
}

void indirect_free_by_reference(void * &a) {
    free(a);
    a = malloc(10);
}

void indirect_free_by_reference2(void *a) {
    indirect_free_by_reference(a);
    free(a); // GOOD
}
void test_indirect_free_by_reference(void *a) {
    indirect_free_by_reference2(a);
    free(a); // GOOD
}











