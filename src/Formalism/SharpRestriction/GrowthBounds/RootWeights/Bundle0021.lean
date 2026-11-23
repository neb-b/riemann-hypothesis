module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0019
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.CommutatorTripleProductLeibniz
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0016
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0018
public import Lemmata.ClearingDenominators.UmonLeUzmon
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0012
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.ExistsHighestWeightVectorFindim
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0015
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0020
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.IntegralGeneratorsPreserveLattice
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.PropertySubmoduleWeightEntryComponent

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.DenominatorLemmaWithoutProjector
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

private theorem degreeZeroWeightsBounded_ellOf {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [CharZero K] [FiniteDimensional K V] {E : GLOps n K V} (hE : IsGLRep E) :
    DegreeZeroWeightsBounded E (ellOf E (⊤ : Submodule K V)) := by
  intro ν hsum hne a
  have hsplit : ν a + ∑ i ∈ Finset.univ.erase a, ν i = 0 := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ a)]; exact hsum
  have hell : (0 : ℤ) ≤ (ellOf E (⊤ : Submodule K V) : ℤ) := by positivity
  rw [abs_le]
  constructor
  · by_cases h0 : 0 ≤ ν a
    · linarith
    · push_neg at h0
      obtain ⟨b, hb, hbpos⟩ : ∃ b ∈ Finset.univ.erase a, 0 < ν b := by
        by_contra hc
        push_neg at hc
        have := Finset.sum_nonpos hc
        linarith
      have hba : b ≠ a := Finset.ne_of_mem_erase hb
      have := weight_difference_le_ell_of_rep hE ν hne b a hba (by linarith)
      linarith
  · by_cases h0 : ν a ≤ 0
    · linarith
    · push_neg at h0
      obtain ⟨b, hb, hbneg⟩ : ∃ b ∈ Finset.univ.erase a, ν b < 0 := by
        by_contra hc
        push_neg at hc
        have := Finset.sum_nonneg hc
        linarith
      have hab : a ≠ b := (Finset.ne_of_mem_erase hb).symm
      have := weight_difference_le_ell_of_rep hE ν hne a b hab (by linarith)
      linarith

private theorem degreeZeroWeightsBounded_linf {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [CharZero K] [FiniteDimensional K V] {E : GLOps n K V} (hE : IsGLRep E) :
    DegreeZeroWeightsBounded E (linf E (⊤ : Submodule K V)) := by
  intro ν hsum hne a
  have hmem : (ν a).natAbs ∈ {k | ∃ nu ∈ wtsOf E (⊤ : Submodule K V), (∑ b, nu b = 0) ∧
      ∃ b, k = (nu b).natAbs} :=
    ⟨ν, by simpa [wtsOf] using hne, hsum, a, rfl⟩
  have hbdd : BddAbove {k | ∃ nu ∈ wtsOf E (⊤ : Submodule K V), (∑ b, nu b = 0) ∧
      ∃ b, k = (nu b).natAbs} := by
    refine ⟨ellOf E (⊤ : Submodule K V), ?_⟩
    rintro k ⟨nu, hnu, hs, b, rfl⟩
    have hne' : weightSp E nu ≠ ⊥ := by simpa [wtsOf] using hnu
    have h := degreeZeroWeightsBounded_ellOf hE nu hs hne' b
    rw [Int.abs_eq_natAbs] at h
    exact_mod_cast h
  have hle : (ν a).natAbs ≤ linf E (⊤ : Submodule K V) := by
    unfold linf
    exact le_csSup hbdd hmem
  rw [Int.abs_eq_natAbs]
  exact_mod_cast hle

theorem linf_lemma_without_projector (D : Formalism.BasicNotions.D7) (h2 : adm2 D) : InvariantDenominatorLinftyBound := by
  intro p n' O _ _ _ S hG n V _ _ _ _ _ E hE M hM hMQ Inv hInv x hx
  haveI : CharZero (KK O) := dvr_fraction_field_charZero_prime S hG.prime
  rw [hMQ]
  exact invariant_projection_denominator_bound D h2 p O n V E hE M hM.1 Inv hInv _ _
    (fun c u hu0 hu => extremal_projector_properties hE c _ (degreeZeroWeightsBounded_linf hE) u hu0 hu)
    (fun c y hy => extremalProjector_denominator_bound S hG.prime hE hM.1 c _ y hy) x hx

theorem denominator_lemma_without_projector (D : Formalism.BasicNotions.D7) (h2 : adm2 D) : InvariantProjectionDenominator := by
  intro p n' O _ _ _ S hG n V _ _ _ _ _ E hE M hM hMQ Inv hInv x hx
  haveI : CharZero (KK O) := dvr_fraction_field_charZero_prime S hG.prime
  rw [hMQ]
  exact invariant_projection_denominator_bound D h2 p O n V E hE M hM.1 Inv hInv _ _
    (fun c u hu0 hu => extremal_projector_properties hE c _ (degreeZeroWeightsBounded_ellOf hE) u hu0 hu)
    (fun c y hy => extremalProjector_denominator_bound S hG.prime hE hM.1 c _ y hy) x hx

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.ExistsScalarMultipleMemDelta
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem delta_le_nabla {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V}
    (hK : v ∈ Nabla (O := O) E lam v) : Delta (O := O) E v ≤ NablaSub (O := O) E lam v := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨u', hu', rfl⟩ u hu
  have := hK (u * u') (Submonoid.mul_mem _ hu hu')
  simpa using this

theorem integral_enveloping_span_top {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v) :
    Submodule.span (KK O) {x | ∃ u ∈ UZmon E, x = u v} = ⊤ := by
  rw [eq_top_iff, ← hI.2.2.2]
  refine Submodule.span_mono ?_
  rintro x ⟨u, hu, rfl⟩
  exact ⟨u, enveloping_le_integral_enveloping E hu, rfl⟩

theorem nabla_to_delta_maps_fg [NeZero n] [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V}
    {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v)
    (hCR : ∀ W : Submodule (KK O) V, (∀ a b, ∀ x ∈ W, E a b x ∈ W) →
      ∃ W' : Submodule (KK O) V, IsCompl W W' ∧ ∀ a b, ∀ x ∈ W', E a b x ∈ W')
    {xi : V →ₗ[KK O] KK O} (h1 : xi v = 1)
    (h2 : ∀ w ∈ otherWts E lam, xi w = 0) (h3 : ∀ x, x - xi x • v ∈ otherWts E lam)
    (hK : v ∈ Nabla (O := O) E lam v) : (nablaToDeltaMaps (O := O) E lam v).FG := by
  refine lattice_fg_of_integral_functionals (O := O) (W := Module.End (KK O) V) _
    {φ | ∃ u ∈ UZmon E, ∃ u' ∈ UZmon E, φ = (xi ∘ₗ u) ∘ₗ LinearMap.applyₗ (u' v)} ?_ ?_
  · intro f hf
    have hz : ∀ u' ∈ UZmon E, f (u' v) = 0 := by
      intro u' hu'
      refine enveloping_coordinate_separates hI hCR h1 fun u hu => ?_
      have := hf _ ⟨u, hu, u', hu', rfl⟩
      simpa using this
    have hk : (⊤ : Submodule (KK O) V) ≤ LinearMap.ker f := by
      rw [← integral_enveloping_span_top hI]
      refine Submodule.span_le.2 ?_
      rintro x ⟨u, hu, rfl⟩
      exact hz u hu
    exact LinearMap.ext fun x => hk Submodule.mem_top
  · rintro φ ⟨u, hu, u', hu', rfl⟩ f hf
    have ha : u' v ∈ Nabla (O := O) E lam v := delta_le_nabla hK (Submodule.subset_span ⟨u', hu', rfl⟩)
    have hb : f (u' v) ∈ Nabla (O := O) E lam v := delta_le_nabla hK (hf _ ha)
    obtain ⟨c, hc⟩ := (mem_nabla_iff_coordinate_integral h1 h2 h3 _).1 hb u hu
    exact ⟨c, by simpa using hc⟩

theorem nabla_finitely_generated [NeZero n] [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V}
    {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v)
    (hCR : ∀ W : Submodule (KK O) V, (∀ a b, ∀ x ∈ W, E a b x ∈ W) →
      ∃ W' : Submodule (KK O) V, IsCompl W W' ∧ ∀ a b, ∀ x ∈ W', E a b x ∈ W')
    {xi : V →ₗ[KK O] KK O} (h1 : xi v = 1)
    (h2 : ∀ w ∈ otherWts E lam, xi w = 0) (h3 : ∀ x, x - xi x • v ∈ otherWts E lam) :
    (NablaSub (O := O) E lam v).FG := by
  refine lattice_fg_of_integral_functionals (O := O) (W := V) _ {φ | ∃ u ∈ UZmon E, φ = xi ∘ₗ u} ?_ ?_
  · intro x hx
    refine enveloping_coordinate_separates hI hCR h1 fun u hu => ?_
    have := hx _ ⟨u, hu, rfl⟩
    simpa using this
  · rintro φ ⟨u, hu, rfl⟩ x hx
    obtain ⟨c, hc⟩ := (mem_nabla_iff_coordinate_integral h1 h2 h3 _).1 hx u hu
    exact ⟨c, by simpa using hc⟩

theorem exists_scalar_multiple_mem_delta {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v) (y : V) :
    ∃ o : O, o ≠ 0 ∧ o • y ∈ Delta (O := O) E v := by
  first | exact Bl.ClearingDenominators.goal1 .. | (apply Bl.ClearingDenominators.goal1 <;> assumption) | (intros; apply Bl.ClearingDenominators.goal1 <;> assumption) | (apply @Bl.ClearingDenominators.goal1 <;> assumption) | (intros; apply @Bl.ClearingDenominators.goal1 <;> assumption) | (apply @Bl.ClearingDenominators.goal1 <;> first | assumption | infer_instance)

theorem nabla_to_delta_maps_span_top [NeZero n] [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V}
    {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v)
    (hfg : (NablaSub (O := O) E lam v).FG) : MQ (K := KK O) (nablaToDeltaMaps (O := O) E lam v) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro f _
  obtain ⟨G, hG⟩ := hfg
  choose o ho ho' using exists_scalar_multiple_mem_delta (O := O) hI
  set c : O := ∏ g ∈ G, o (f g) with hc
  have hc0 : c ≠ 0 := prod_ne_zero_iff.2 fun g _ => ho _
  have hmem : c • f ∈ nablaToDeltaMaps (O := O) E lam v := by
    intro x hx
    have hx' : x ∈ Submodule.span O (G : Set V) := hG ▸ hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem g hg =>
      rw [LinearMap.smul_apply, hc, ← mul_prod_erase G _ hg, mul_comm, mul_smul]
      exact Submodule.smul_mem _ _ (ho' _)
    | zero => simp
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy =>
      rw [← algebraMap_smul (KK O) r y, map_smul, algebraMap_smul]; exact Submodule.smul_mem _ _ hy
  have hc1 : algebraMap O (KK O) c ≠ 0 := by
    simpa using (IsFractionRing.injective O (KK O)).ne hc0
  have : f = (algebraMap O (KK O) c)⁻¹ • (c • f) := by
    rw [← algebraMap_smul (KK O) c f, smul_smul, inv_mul_cancel₀ hc1, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem coordinate_rank_one_mem_maps {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} {xi : V →ₗ[KK O] KK O} (h1 : xi v = 1)
    (h2 : ∀ w ∈ otherWts E lam, xi w = 0) (h3 : ∀ x, x - xi x • v ∈ otherWts E lam) :
    xi.smulRight v ∈ nablaToDeltaMaps (O := O) E lam v := by
  intro x hx
  obtain ⟨c, hc⟩ := (mem_nabla_iff_coordinate_integral h1 h2 h3 _).1 hx 1 (Submonoid.one_mem _)
  rw [Module.End.one_apply] at hc
  rw [LinearMap.smulRight_apply, hc, algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, Submonoid.one_mem _, rfl⟩)

end hw

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.IntegralPolynomialsEnvelopingStable
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem integral_formula_lattice_holds : AdmissibleDVRIntegralFormLatticesStable := by
  intro p n' O _ _ _ S0 hG
  have hV : ValuationProperties p O := valuation_properties_hold hG.prime S0
  have hchar := dvr_fraction_field_char_zero hG.prime S0
  exact ⟨hchar, fun n ι _ LL => ⟨fun S => integral_formula_stability_holds hG.prime hV n ι LL S,
    fun S => char_zero_stability_of_closure hG.prime hchar (fock_lattice_closure_holds hV) n ι LL S, fock_lattice_finite_spanning_holds hG.prime S0 hV n ι⟩⟩

theorem polynomial_isotypic_lattice_corollary (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h13 : IsotypicProjectorTheoremField D) : FilteredProjectorCorollaryField D :=
  polynomial_isotypic_lattice_of_parts D (complete_reducibility_of_semisimple D h2) contravariant_orthogonality_holds highest_weight_dominant_holds (subrep_restriction_of_reducibility (complete_reducibility_of_semisimple D h2)) polynomial_representation_holds integral_formula_lattice_holds h13

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.SubstitutionPreservesOfGenerators
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem coeff_weightComponent {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (nu : Fin n → ℤ) (F : MvPolynomial (ι × Fin n) R) (m : ι × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (weightComponent LL S nu F) m = if wtS LL S m = nu then AddMonoidAlgebra.coeff F m else 0 := by
  classical
  unfold weightComponent
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, MvPolynomial.mem_support_iff]
  by_cases h1 : wtS LL S m = nu <;> by_cases h2 : AddMonoidAlgebra.coeff F m = 0 <;> simp [h1, h2]

section bwd

variable {R : Type} [Field R] {ι : Type} [Fintype ι] (LL : Letters ι) {n : ℕ} (S : Set ι)
  {L : Type} [Field L] (φ : R →+* L) (W : Submodule R (MvPolynomial (ι × Fin n) R))

def scalarExtension : Submodule L (MvPolynomial (ι × Fin n) L) :=
  Submodule.span L ((MvPolynomial.map φ) '' (W : Set (MvPolynomial (ι × Fin n) R)))

def SubstitutionPreservesExtension (h h' : Matrix (Fin n) (Fin n) L) : Prop :=
  ∀ x ∈ scalarExtension φ W, matrixSubst LL S (RingHom.id L) h h' x ∈ scalarExtension φ W

theorem scalarExtension_monomial_weights (hGr : BinomialStableContainsComponents) (hW2 : ∀ a k, ∀ x ∈ W, binomPol R LL S a k x ∈ W) :
    ∀ z ∈ scalarExtension φ W, ∀ m ∈ z.support, wtS LL S m ∈ polWts LL S W := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    intro m hm
    have hm' : m ∈ w.support := MvPolynomial.support_map_subset φ w hm
    simp only [polWts, Set.mem_setOf_eq]
    refine ⟨weightComponent LL S (wtS LL S m) w, hGr R ι LL n S W hW2 w hw _, ?_, ?_⟩
    · intro h0
      have e := congrArg (AddMonoidAlgebra.coeff · m) h0
      rw [coeff_weightComponent, if_pos rfl, MvPolynomial.coeff_zero] at e
      exact (MvPolynomial.mem_support_iff.1 hm') e
    · intro m' hm''
      rw [MvPolynomial.mem_support_iff, coeff_weightComponent] at hm''
      by_contra hne
      exact hm'' (if_neg hne)
  | zero => intro m hm; simp at hm
  | add x y _ _ hx hy =>
    classical
    intro m hm
    rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
    · exact hx m h
    · exact hy m h
  | smul c x _ hx =>
    intro m hm
    exact hx m (MvPolynomial.support_smul hm)

end bwd

end Formalism.MainNotions.G.GLWeightTheory
end
end

