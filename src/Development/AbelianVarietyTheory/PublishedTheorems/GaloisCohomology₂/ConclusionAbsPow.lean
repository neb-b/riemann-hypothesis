module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNeZeroMemJumpTypeTwo
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.HeckeGal.Model

namespace GlobalTheory.Published.CharAboveModel

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]

theorem absPow_isAlgPos (E : Type) [Field E] [NumberField E] (m : ℕ) :
    IsAlgPos (absPow E m) (fun _ => (m : ℤ)) := by
  classical
  intro k hk
  rw [(absPow_isAbsPow E m).2.2 k]
  have h1 : ∏ φ : E →+* ℂ, ((‖φ (k : E)‖ : ℝ) : ℂ) = ∏ φ : E →+* ℂ, φ (k : E) := by
    rw [← Finset.prod_fiberwise (s := Finset.univ) (g := InfinitePlace.mk),
      ← Finset.prod_fiberwise (s := Finset.univ) (g := InfinitePlace.mk) (f := fun φ : E →+* ℂ => φ (k : E))]
    refine Finset.prod_congr rfl fun w _ => ?_
    have e : (Finset.univ.filter fun φ : E →+* ℂ => InfinitePlace.mk φ = w) =
        {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
      ext φ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
      conv_lhs => rw [← InfinitePlace.mk_embedding w, InfinitePlace.mk_eq_iff]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (by rw [← h]; exact (star_star φ).symm)
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (by rw [h]; exact star_star _)
    rw [e]
    rcases w.isReal_or_isComplex with hw | hw
    · have hr := InfinitePlace.isReal_iff.mp hw
      rw [ComplexEmbedding.isReal_iff.mp hr]
      simp only [Finset.mem_singleton, Finset.insert_eq_of_mem, Finset.prod_singleton]
      have := hk hr.embedding
      rw [← ComplexEmbedding.IsReal.coe_embedding_apply hr, Complex.norm_real, Real.norm_eq_abs, abs_of_pos this]
    · have hn : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := fun h =>
        (InfinitePlace.isComplex_iff.mp hw) (ComplexEmbedding.isReal_iff.mpr h.symm)
      rw [Finset.prod_pair hn, Finset.prod_pair hn, ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj,
        Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast; ring
  simp only [Complex.ofReal_natCast, Complex.cpow_natCast, zpow_natCast]
  rw [Finset.prod_pow, Finset.prod_pow, h1]

theorem eq_cyc_pow [IsAlgClosure E Ω] {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) {ι : Qbar l ≃+* ℂ}
    {m : ℕ} {n : (E →+* ℂ) → ℤ} {μ : G E Ω →* (Qbar l)ˣ} (hμ : Continuous μ)
    (h : IsLAdicOf art ι (absPow E m) n μ) : μ = cyc E Ω l ^ m := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hc : Continuous (cyc E Ω l) :=
    (Continuous.units_map ((algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom).toMonoidHom
      ((continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp
        (continuous_subtype_val : Continuous fun z : ℤ_[l] => (z : ℚ_[l])))).comp (continuous_cycZ E Ω l)
  refine mul_inv_eq_one.1 (GlobalTheory.FrobDense.eq_one_of_frob E Ω art ha _ (μ * (cyc E Ω l ^ m)⁻¹)
    (hμ.mul (hc.pow m).inv) (Ideal.finite_factors h0).toFinset fun v hv A hA σ hσ => ?_)
  have hv' : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal := fun hm => hv (by
    rw [Set.Finite.mem_toFinset]; exact Ideal.dvd_span_singleton.mpr hm)
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one]
  refine Units.ext ?_
  rw [frob_abs E ha h hv' hA hσ, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, cyc_eq_map_cycZ, Units.coe_map,
    cycZ_of_isFrob hv' hA hσ]
  simp

section Loc

variable (P : LocPrime l) {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)


end Loc

end GlobalTheory.Published.CharAboveModel

end
