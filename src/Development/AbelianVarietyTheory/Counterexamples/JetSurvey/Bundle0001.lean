module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Counterexamples.JetSurvey.BalancedPairs
section
set_option autoImplicit false

namespace GlobalTheory.ChartJoints

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem emb_bar (H : Host E) (τ : E →+* ℂ) (a : 𝓞 E) :
    τ ((H.bar a : 𝓞 E) : E) = ComplexEmbedding.conjugate τ (a : E) := by
  rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]
  rfl

theorem balanced_pairs (H : Host E) {l : Level H} (c : Coeff l) {S : Type} [CommRing S] [Algebra c.F S]
    (τ τ' : E →+* ℂ) (v : S)
    (hv : ∀ a : 𝓞 E, algebraMap c.F S (embK c τ a) * v = algebraMap c.F S (embK c τ' (H.bar a)) * v)
    (hne : τ ≠ ComplexEmbedding.conjugate τ') : v = 0 := by
  have : ∃ a : 𝓞 E, embK c τ a ≠ embK c τ' (H.bar a) := by
    by_contra hcon
    push_neg at hcon
    apply hne
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
    ext a
    have := congrArg (fun z : c.F => (z : ℂ)) (hcon a)
    simp only [embK_coe] at this
    rw [emb_bar] at this
    exact this
  obtain ⟨a, ha⟩ := this
  have hu : IsUnit (algebraMap c.F S (embK c τ a - embK c τ' (H.bar a))) :=
    (IsUnit.mk0 _ (sub_ne_zero.2 ha)).map _
  apply hu.mul_left_cancel
  rw [map_sub, sub_mul, hv a, sub_self, mul_zero]

end GlobalTheory.ChartJoints
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.JetSurvey.UnimodularStandardLattice
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Survey.UnimodularStandardLattice

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

omit [IsCMField E] in
theorem mem_stdLat (v : Fin n → E) : v ∈ stdLat E n ↔ ∀ j, ∃ b : 𝓞 E, (b : E) = v j := by
  simp [stdLat, Submodule.mem_pi, Submodule.mem_one]

set_option autoImplicit false in
open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
private lemma mem_range_algebraMap_iff_isIntegral_int (x : E) :
    x ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact RingOfIntegers.isIntegral_coe y
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

set_option autoImplicit false in
open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
private lemma complexConj_mem_integers_iff (x : E) :
    IsCMField.complexConj E x ∈ (algebraMap (𝓞 E) E).range ↔
      x ∈ (algebraMap (𝓞 E) E).range := by
  rw [mem_range_algebraMap_iff_isIntegral_int, mem_range_algebraMap_iff_isIntegral_int]
  refine ⟨fun h => ?_, fun h => h.map (IsCMField.complexConj E)⟩
  simpa using h.map (IsCMField.complexConj E).symm


set_option autoImplicit false in
open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
theorem _root_.GlobalTheory.Survey.UnimodularStandardLattice.unimod_std :
    (⟨_root_.Formalism.L2.Pj.stdLat E n⟩ : _root_.Formalism.L2.Pj.GenLat E n).Unimod := by
  unfold _root_.Formalism.L2.Pj.GenLat.Unimod _root_.Formalism.L2.Pj.stdLat
  intro v
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one,
    ← RingHom.mem_range]
  constructor
  · intro hv w hw
    exact Subring.sum_mem _ fun j _ =>
      Subring.mul_mem _ ((complexConj_mem_integers_iff (v j)).2 (hv j)) (hw j)
  · intro h i
    have hs := h (Pi.single i 1) fun j => by
      rw [Pi.single_apply]
      split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at hs
    exact (complexConj_mem_integers_iff (v i)).1 hs


variable {H : Host E} {Dw : Datum H} {l : Level H}

end GlobalTheory.Survey.UnimodularStandardLattice
end
end

