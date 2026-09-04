/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
comparator/PrintAxioms/Multiplicity.lean — axiom audit for the twelve multiplicity-aware
theorems:   lake build Solution.Multiplicity && lake env lean comparator/PrintAxioms/Multiplicity.lean
-/
import Solution.Multiplicity

#print axioms two_thirds_simple_on_critical_line
#print axioms two_thirds_simple_on_critical_line_cumulative
#print axioms five_sixths_distinct
#print axioms five_sixths_distinct_cumulative
#print axioms montgomery_taylor_simple_on_critical_line_mult
#print axioms montgomery_taylor_simple_on_critical_line_mult_cumulative
#print axioms montgomery_taylor_distinct_mult
#print axioms montgomery_taylor_distinct_mult_cumulative
#print axioms dirichlet_two_thirds_simple_on_critical_line
#print axioms dirichlet_five_sixths_distinct
#print axioms dirichlet_montgomery_taylor_simple_on_critical_line_mult
#print axioms dirichlet_montgomery_taylor_distinct_mult
