
This is a lean implementation for the NP-hardness proof in
[Complexity and Algorithms for Unary Translocation Distance](https://arxiv.org/abs/2606.08412).

We only prove that the problem is NP-hard, but it can be proven that it
is strongly NP-hard by choosing B<sub>3</sub> sequences with numbers polynomial in
the length of the sequence ([Bose et al. 1960](https://www.cs.umd.edu/users/gasarch/COURSES/858/S13/BoseChowla.pdf),
[O’Bryant 2012](https://arxiv.org/pdf/math/0407117)) in function `get_b3`.
