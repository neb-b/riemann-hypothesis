module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0028

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsValuedHeckeCharRamified
section
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.CMVal.Model

section General

variable {E : Type} [Field E] [NumberField E]

theorem IsCMType.bijective {I : Type} {φ : I → E →+* ℂ} (h : IsCMType φ) :
    Function.Bijective (fun i => InfinitePlace.mk (φ i)) := by
  refine ⟨fun i j hij => ?_, fun w => ?_⟩
  · obtain ⟨k, -, hk⟩ := h (φ j)
    have h1 : j = k := hk j (Or.inl rfl)
    have h2 : i = k := hk i (by
      rcases InfinitePlace.mk_eq_iff.1 hij with e | e
      · exact Or.inl e.symm
      · exact Or.inr e.symm)
    rw [h1, h2]
  · obtain ⟨i, hi, -⟩ := h w.embedding
    refine ⟨i, ?_⟩
    rcases hi with e | e
    · simp only [← e, InfinitePlace.mk_embedding]
    · have := congrArg InfinitePlace.mk e
      rw [InfinitePlace.mk_embedding, InfinitePlace.mk_conjugate_eq] at this
      exact this.symm

end General

section Integrality

end Integrality

section Symmetry

variable {E : Type} [Field E] [NumberField E]

end Symmetry

section Twist

variable {E : Type} [Field E] [NumberField E]

end Twist

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end CM

section Cyclotomic


end Cyclotomic

end GlobalTheory.CMVal.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.MemMixedTsub
section
noncomputable section

open WittVector Ideal Matrix

namespace GlobalTheory.Sandwich.Model

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

theorem xi_eq (ε : PreTilt O p) : xi ε = ReciprocityTheory.PGsh.Ainf.xi p O ε := rfl

theorem nu_eq (ε : PreTilt O p) : nu ε = ReciprocityTheory.PGsh.Ainf.nu p O ε := rfl

section Field

variable {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} [Algebra O C]
  (hv : v.Integers O) {ε : PreTilt O p}
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
include hv hε

theorem theta_mu : fontaineTheta O p (mu ε) = 0 := by
  rw [← xi_mul_nu, map_mul, xi_eq, ReciprocityTheory.PGsh.Ainf.theta_xi p O hv ε hε, zero_mul]

theorem mu_ne_zero : mu ε ≠ 0 := by
  intro h
  rw [← xi_mul_nu, mul_comm] at h
  have := ReciprocityTheory.PGsh.Ainf.xi_nzd p O hv ε hε _ h
  exact ReciprocityTheory.PGsh.Ainf.theta_nu p O hv ε hε (by rw [← nu_eq, this, map_zero])

omit hε [IsAlgClosed C] in
theorem isDomain_Ainf : IsDomain (Ainf p O) := by
  haveI : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p
  infer_instance

variable {h : ℕ} {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ] (D : Datum ε h Λ)

end Field

end GlobalTheory.Sandwich.Model
end
end

