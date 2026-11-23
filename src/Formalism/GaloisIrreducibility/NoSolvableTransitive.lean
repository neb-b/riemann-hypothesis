module

public import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.Bundle0001
public import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.RestrictRoots
public import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.Bundle0002
public import Formalism.GaloisIrreducibility.Statement
public import Formalism.GaloisIrreducibility.NoSolvableOf
public import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.JordanPrime

@[expose] public section

namespace Formalism.GaloisIrreducibility

theorem lemmaA : LemmaA := lemmaAOf_statement orbit_subset_sum restrict_roots_to_subfield

theorem irred : Irred := irreducible_of_galois_conditions lemmaA
theorem permSubSumInv : PermSubSumInv := permutation_subset_sum_invariant

theorem primitiveOfPCycle : PrimitiveOfPCycle := primitive_of_p_cycle
theorem jordanPrime : JordanPrime := jordan_prime_cycle_theorem

theorem noSolvableTransitive : NoSolvableTransitive :=
  no_solvable_subgroup_of power_of_p_cycle primitive_of_p_cycle jordan_prime_cycle_theorem alternating_group_not_solvable

end Formalism.GaloisIrreducibility
