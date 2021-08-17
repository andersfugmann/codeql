/** According to the c standard, i = i++ is unspecified, as the
    increment operation may occur before or after the
    assignment. This is also the case for prefix in/de-crement unary operator.
*/

void unspecified_use_of_unary_crement() {
    int i = 0;
    i = i++; // BAD
}

int post_increment(int i) {
    i = i + 5;
    return i;
}

void use_of_unary_crement_with_sequence_points() {
    int i = 0;
    i = post_increment(i++); // GOOD
}
