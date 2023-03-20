void *malloc(int);
void free(void *);
bool condition();
void use(void*);
void *realloc(void*, unsigned long);
int strlen(char*);

void test(int *a)
{
    free(a);
    a[2] = 5; // BAD
    free(a); // BAD
}

void test2(int *a)
{
    if (condition()) free(a); // GOOD 
    if (condition()) a[2] = 5; // GOOD
    if (condition()) free(a); // GOOD
    a[2] = 5; // BAD
    free(a); // BAD
}


void test_post_dominance1(void *a) {
    if (condition())
    {
        free(a);
    }
    // Post dominates the first free
    free(a); // BAD
}

void test_post_dominance2(void *a) {
    if (condition()) free(a);
    a = malloc(10);
    free(a); // GOOD
}

void test_dominance1(void *a) {
    free(a);
    if (condition()) free(a); // BAD    
}

void test_dominance2(void *a) {
    free(a);
    a = malloc(10);    
    if (condition()) free(a); // GOOD
    free(a); // BAD
}

void test_dominance3(void *a) {
    free(a);
    a = malloc(10);    
    free(a);
}

void test_dominance4(void *a, void* b) {
    free(a);
    a = malloc(10);    
    free(a); // GOOD
    a = malloc(10);
    free(a); // GOOD
    a = b;    
    free(a); // GOOD
    free(b); // BAD [NOT DETECTED]

}

void test_use_after_free1(int *a) {
    a[0] = 5; // GOOD
    *a = 5; // GOOD
    free(a); 
    a[0] = 5; // BAD
    *a = 5; // BAD
}

void test_use_after_free2(int *a) {
    if (condition()) free(a);
    a[0] = 5; // BAD
}

void test_use_after_free3(int* a) {
    free(a);
    if (condition()) a[0] = 5; // BAD
}

void test_use_after_free4(int *a, int *b) {
    free(a);
    a=b;
    if (condition()) a[0] = 5; // GOOD
}

void test_use_after_free5(int *a, int *b) {
    free(a);
    if (condition()) a = b;
    a[0] = 5; // BAD
    if (condition()) a[0] = 5; // BAD
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

void use_after_free(void *a) {
    free(a);
    use(a); // BAD
}

void test_realloc1(void *a) {
    free(a);
    a = realloc(a, 10); // BAD
    free(a); // GOOD
    void *b = realloc(a, 10); // BAD
    free(a); // BAD
    free(b); // GOOD
}

void test_realloc2(void *a) {
    free(a);
    void *b = realloc(a, sizeof(a)*3);
    free(a); // BAD
    free(b); // GOOD
}

void test_realloc3(char *a) {
    void *b = realloc(a, strlen(a)+3); // GOOD [FALSE POSITIVE]

    // From the man page on return values from realloc and reallocarray:
    // "If these functions  fail, the original block is left untouched; it is not freed or moved."
    if (!b) {
        free(a); // GOOD [FALSE POSITIVE]
    }
}

struct list {
    struct list *next;
    void* data;
};

void test_ptr_deref(void ** a) {
    free(*a);
    *a = malloc(10);
    free(*a); // GOOD [FALSE POSITIVE]
    free(*a); // BAD
}

void test_loop(struct list ** list_ptr) {
    struct list *next;
    while (*list_ptr) { // GOOD [FALSE POSITIVE]
        free((*list_ptr)->data);
        next = (*list_ptr)->next;
        free(*list_ptr);
        *list_ptr = next; // GOOD [FALSE POSITIVE]
    }
}

void* test_realloc4() {
    void *a = 0;
    void *b = realloc(a, 10);
    if (!b) { return a; } // GOOD [FALSE POSITIVE]
    return b;
}

void* test_alloc1() {
    void *a = 0;
    free(a);
    use(a); // GOOD [FALSE POSITIVE]
    return a; // GOOD [FALSE POSITIVE]
}
