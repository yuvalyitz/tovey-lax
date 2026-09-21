*(3,4)-SAT* is satisfiability restricted to formulas in which every clause has exactly three
literals and every variable occurs at most four times. Tovey (1984) proved that it is
NP-hard. This submission states that theorem: every language in NP has a polynomial-time
many-one reduction to (3,4)-SAT, on the CNF encoding and the Turing machines of the
archive's Cook–Levin theorem.

The reduction is from unrestricted satisfiability. Every literal occurrence receives a
fresh variable; a clause is chained through link variables into clauses of at most three
literals; a cycle of implications forces the copies of one variable to agree; and every
short clause is filled with the negation of a fresh variable that Tovey's thirteen-clause
gadget forces to be true.

The correctness of the reduction is proved. Its polynomial running time is stated and not
proved: the one statement of this submission that remains open.
