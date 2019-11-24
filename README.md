# This is our README

This is a formalization of real numbers in Coq. Coq's standard library uses an axiomatic formalization. We instantiate one variant of it using two different approaches---Dedekind cut and Cauchy sequences.

Here is a list of modification that we made in the interface:
1. Req is the equivalence between real numbers. It does not have to be Coq's equality. Arithmetic operators are required to preserve this equality.
2. Trichotomous of real number ordering should not be computable.
3. The floor function from R to Z should not be computable.

# Developpers: Qinxiang Cao, Xiwei Wu, Litao Zhou, Zhixuan Hu, Likai Zou, Ke Wu, Zhang Cheng

