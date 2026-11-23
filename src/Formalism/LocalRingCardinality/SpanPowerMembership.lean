module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0004
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0005

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain

instance instFactExamplePrime : Fact T0.Prime := ⟨examplePrime_prime⟩

theorem exampleHost_type_primes_split : ∀ k, (placesOver H0.E (H0.g k)).ncard = Module.finrank ℚ H0.E := by
  refine g_split_of H0 (fun k => ?_)
  fin_cases k
  · show 413718278401 % (2 ^ (2 + 2) * 571 * 599) = 1; norm_num
  · show 603339156001 % (2 ^ (2 + 2) * 571 * 599) = 1; norm_num

theorem exampleHost_typeHypothesis : THyp H0 :=
  { cond := fun k => by
      fin_cases k
      · show 413718278401 % (2 ^ (2 + 2) * 571 * 599) = 1; norm_num
      · show 603339156001 % (2 ^ (2 + 2) * 571 * 599) = 1; norm_num
    bb := BB_disj0
    jac := fun k => by
      fin_cases k
      · exact ⟨by show (413718278401 : ℕ) ≠ 2; norm_num, by show jacobiSym (-599) 413718278401 = 1; norm_num⟩
      · exact ⟨by show (603339156001 : ℕ) ≠ 2; norm_num, by show jacobiSym (-599) 603339156001 = 1; norm_num⟩ }

theorem examplePrime_ne_split_primes : T0 ≠ H0.pde ∧ T0 ≠ H0.pde' :=
  ⟨by show T0 ≠ 751; norm_num [T0], by show T0 ≠ 991; norm_num [T0]⟩

def exampleRecord (G : LocalGap H0) : D7 :=
  exampleRecordOfData H0 T0 exampleHost_type_primes_split exampleHost_typeHypothesis examplePrime_mem_levelPrimes examplePrime_ne_split_primes π0O π0_mem_K π0_norm π0_cong G

theorem nonempty_D7_of_localGap (G : LocalGap H0) : Nonempty D7 := ⟨exampleRecord G⟩

theorem record_nonempty_of_localGap : Nonempty (LocalGap H0) → Nonempty D7 := fun ⟨G⟩ => nonempty_D7_of_localGap G

end Formalism.BasicNotions.Examples₂
