module

public import Mathlib
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.PolyCons
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Amb

variable {k : Type} [CommRing k]

theorem ringKrullDim_eq_one' [IsDomain k] [CharZero k] (hf : Module.Finite ℤ k) : ringKrullDim k = 1 := by
  have := hf
  have : Algebra.IsIntegral ℤ k := Algebra.IsIntegral.of_finite ℤ k
  have : Ring.DimensionLEOne k := Ring.DimensionLEOne.of_isIntegral (R := ℤ) k
  apply eq_of_le_of_not_lt
  · rw [← Nat.cast_one, ← Ring.krullDimLE_iff]
    infer_instance
  · intro h'
    have h'' : ringKrullDim k ≤ 0 := Order.le_of_lt_succ h'
    rw [← Nat.cast_zero, ← Ring.krullDimLE_iff] at h''
    have hk : IsField k := Ring.KrullDimLE.isField_of_isDomain
    exact Int.not_isField (isField_of_isIntegral_of_isField (R := ℤ) (S := k) Int.cast_injective hk)

theorem topologicalKrullDim_of_polyCovered' [IsDomain k] [IsNoetherianRing k] (hk : ringKrullDim k = 1)
    {X : Scheme.{0}} (f : X ⟶ Sp k) (d : ℕ) (h : PolyCovered f d) : topologicalKrullDim X = (d + 1 : ℕ) := by
  obtain ⟨ξ, -, hcov⟩ := h
  have hdim : ∀ (σ : Type) [Fintype σ], Fintype.card σ = d →
      topologicalKrullDim (Sp (MvPolynomial σ k)) = ((d + 1 : ℕ) : WithBot ℕ∞) := by
    intro σ _ hσ
    change topologicalKrullDim (PrimeSpectrum (MvPolynomial σ k)) = _
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, hk, Nat.card_eq_fintype_card, hσ, add_comm]
    norm_cast
  apply le_antisymm
  · unfold topologicalKrullDim
    rw [Order.krullDim_eq_iSup_coheight]
    refine iSup_le fun Z => ?_
    obtain ⟨x, hx⟩ := Z.isIrreducible.nonempty
    obtain ⟨σ, _, e, he, hσ, -, ⟨y, rfl⟩, -⟩ := hcov x
    haveI := he
    let Φ := TopologicalSpace.IrreducibleCloseds.orderIsoOfIsOpenEmbedding e e.isOpenEmbedding
    have hZ : TopologicalSpace.IrreducibleCloseds.map e e.isOpenEmbedding.continuous
        (Φ.symm ⟨Z, ⟨y, hx⟩⟩) = Z :=
      congrArg Subtype.val (Φ.apply_symm_apply ⟨Z, ⟨y, hx⟩⟩)
    rw [← hZ, e.isOpenEmbedding.coheight_map]
    have h1 := Order.coheight_le_krullDim (Φ.symm ⟨Z, ⟨y, hx⟩⟩)
    have h2 := hdim σ hσ
    unfold topologicalKrullDim at h2
    rw [h2] at h1
    exact h1
  · obtain ⟨σ, _, e, he, hσ, -, -, -⟩ := hcov ξ
    haveI := he
    rw [← hdim σ hσ]
    exact e.isOpenEmbedding.isInducing.topologicalKrullDim_le

theorem isIntegral_of_polyCovered' [IsDomain k] {X : Scheme.{0}} (f : X ⟶ Sp k) (d : ℕ) (h : PolyCovered f d) :
    IsIntegral X := by
  obtain ⟨ξ, -, hcov⟩ := h
  haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := by
    intro x
    obtain ⟨σ, _, e, he, -, -, ⟨y, rfl⟩, -⟩ := hcov x
    haveI := he
    exact isReduced_of_injective (e.stalkMap y).hom
      (asIso (e.stalkMap y)).commRingCatIsoToRingEquiv.injective
  haveI : IsReduced X := isReduced_of_isReduced_stalk X
  have hirr : ∀ x : X, ∃ R : Set X, IsOpen R ∧ IsIrreducible R ∧ x ∈ R ∧ ξ ∈ R := by
    intro x
    obtain ⟨σ, _, e, he, -, -, hx, hξ⟩ := hcov x
    haveI := he
    refine ⟨Set.range e, e.isOpenEmbedding.isOpen_range, ?_, hx, hξ⟩
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ (Sp (MvPolynomial σ k))).image _
      e.continuous.continuousOn
  haveI : IrreducibleSpace X := by
    refine (irreducibleSpace_def X).mpr ⟨⟨ξ, trivial⟩, ?_⟩
    rintro u v hu hv ⟨a, -, ha⟩ ⟨b, -, hb⟩
    obtain ⟨Ra, hRa, iRa, haRa, hξa⟩ := hirr a
    obtain ⟨Rb, hRb, iRb, hbRb, hξb⟩ := hirr b
    obtain ⟨p, hpa, hpu, hpb⟩ := iRa.2 u Rb hu hRb ⟨a, haRa, ha⟩ ⟨ξ, hξa, hξb⟩
    obtain ⟨q, -, ⟨hqu, -⟩, hqv⟩ :=
      iRb.2 (u ∩ Ra) v (hu.inter hRa) hv ⟨p, hpb, hpu, hpa⟩ ⟨b, hbRb, hb⟩
    exact ⟨q, trivial, hqu, hqv⟩
  exact isIntegral_of_irreducibleSpace_of_isReduced X

theorem polyCovered_pSpace' [IsDomain k] (N : ℕ) : PolyCovered (PSpace.str k N) N := by
  classical
  letI : GradedAlgebra (ProjSpace.grading k N) := MvPolynomial.gradedAlgebra
  have hX : ∀ i : Fin (N + 1), (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ≠ 0 :=
    fun i => MvPolynomial.X_ne_zero i
  let ξ0 : PSpace k N := (⟨⊥, by rw [HomogeneousIdeal.toIdeal_bot]; exact Ideal.isPrime_bot, fun hle => hX 0 (by
      have h0 : MvPolynomial.X 0 ∈ HomogeneousIdeal.irrelevant (ProjSpace.grading k N) := by
        rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply]
        exact DirectSum.decompose_of_mem_ne _ (ProjSpace.X_mem k N 0) one_ne_zero
      have h1 := hle h0
      change _ ∈ (⊥ : HomogeneousIdeal (ProjSpace.grading k N)).toIdeal at h1
      rwa [HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at h1)⟩ :
    ProjectiveSpectrum (ProjSpace.grading k N))
  have hmem : ∀ i, ξ0 ∈ ProjSpace.chart k N i := fun i =>
    (Proj.mem_basicOpen _ _ _).mpr fun h => hX i (by
      change _ ∈ (⊥ : HomogeneousIdeal (ProjSpace.grading k N)).toIdeal at h
      rwa [HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at h)
  have hspec : ∀ z : PSpace k N, ξ0 ⤳ z := fun z =>
    specializes_iff_mem_closure.mpr
      ((ProjectiveSpectrum.le_iff_mem_closure (𝒜 := ProjSpace.grading k N)
        (ξ0 : ProjectiveSpectrum (ProjSpace.grading k N)) (z : ProjectiveSpectrum (ProjSpace.grading k N))).mp
      (show (⊥ : HomogeneousIdeal (ProjSpace.grading k N)) ≤ z.asHomogeneousIdeal from bot_le))
  have hr : ∀ i, ξ0 ∈ Set.range (ProjSpace.chartι k N i) := fun i => by
    have := hmem i
    rw [← ProjSpace.opensRange_chartι] at this
    exact this
  obtain ⟨η, hη⟩ := hr 0
  let w : Sp (MvPolynomial {j : Fin (N + 1) // j ≠ 0} k) := ⟨⊥, Ideal.isPrime_bot⟩
  have hηw : η ⤳ w := by
    have h1 : ProjSpace.chartι k N 0 η ⤳ ProjSpace.chartι k N 0 w := by
      rw [hη]
      exact hspec _
    exact (ProjSpace.chartι k N 0).isOpenEmbedding.isInducing.specializes_iff.mp h1
  have hηbot : η.asIdeal = ⊥ := le_bot_iff.mp ((PrimeSpectrum.le_iff_specializes _ _).mpr hηw)
  refine ⟨ξ0, fun y => ?_, fun x => ?_⟩
  · have hs : PSpace.str k N ξ0 = (spMap MvPolynomial.C) η := by
      rw [← hη, ← ProjSpace.chartι_str k N 0]
      rfl
    rw [hs]
    refine (PrimeSpectrum.le_iff_specializes _ _).mp ?_
    change Ideal.comap (MvPolynomial.C : k →+* MvPolynomial {j : Fin (N + 1) // j ≠ 0} k) η.asIdeal ≤ y.asIdeal
    intro a ha
    rw [Ideal.mem_comap, hηbot, Ideal.mem_bot, MvPolynomial.C_eq_zero] at ha
    rw [ha]
    exact zero_mem _
  · obtain ⟨i, hi⟩ := ProjSpace.exists_mem_chart k N x
    refine ⟨{j : Fin (N + 1) // j ≠ i}, inferInstance, ProjSpace.chartι k N i, inferInstance, ?_,
      ProjSpace.chartι_str k N i, ?_, hr i⟩
    · simp
    · rw [← ProjSpace.opensRange_chartι] at hi
      exact hi

end GlobalTheory.Amb
end
end

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.PolyPb
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

namespace GlobalTheory.Amb

variable {k : Type} [CommRing k]

def sumTensEquiv (σ τ : Type) : MvPolynomial (τ ⊕ σ) k ≃+* MvPolynomial σ k ⊗[k] MvPolynomial τ k :=
  (MvPolynomial.sumAlgEquiv k τ σ).toRingEquiv.trans
    (MvPolynomial.algebraTensorAlgEquiv (σ := τ) k (MvPolynomial σ k)).symm.toRingEquiv

theorem sumTensEquiv_C (σ τ : Type) (r : k) :
    sumTensEquiv σ τ (MvPolynomial.C r) = algebraMap k (MvPolynomial σ k ⊗[k] MvPolynomial τ k) r := by
  have h1 : (MvPolynomial.sumAlgEquiv k τ σ) (MvPolynomial.C r) = MvPolynomial.C (MvPolynomial.C r) := by
    rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
    rfl
  have h2 : (MvPolynomial.C (MvPolynomial.C r) : MvPolynomial τ (MvPolynomial σ k)) =
      MvPolynomial.monomial 0 (MvPolynomial.C r) := rfl
  show (MvPolynomial.algebraTensorAlgEquiv (σ := τ) k (MvPolynomial σ k)).symm
    ((MvPolynomial.sumAlgEquiv k τ σ) (MvPolynomial.C r)) = _
  rw [h1, h2, MvPolynomial.algebraTensorAlgEquiv_symm_monomial, Algebra.TensorProduct.algebraMap_apply]
  rfl

variable {X Y : Scheme.{0}} (f : X ⟶ Sp k) (g : Y ⟶ Sp k) {σ τ : Type}

def prodChart (e : Sp (MvPolynomial σ k) ⟶ X) (e' : Sp (MvPolynomial τ k) ⟶ Y)
    (he : e ≫ f = spMap (MvPolynomial.C : k →+* MvPolynomial σ k))
    (he' : e' ≫ g = spMap (MvPolynomial.C : k →+* MvPolynomial τ k)) :
    Sp (MvPolynomial (τ ⊕ σ) k) ⟶ pullback f g :=
  spMap (sumTensEquiv σ τ).symm.toRingHom ≫ (pullbackSpecIso k (MvPolynomial σ k) (MvPolynomial τ k)).inv ≫
    pullback.map _ _ f g e e' (𝟙 _) (by rw [Category.comp_id, he]; rfl) (by rw [Category.comp_id, he']; rfl)

variable {f g} {e : Sp (MvPolynomial σ k) ⟶ X} {e' : Sp (MvPolynomial τ k) ⟶ Y}
  {he : e ≫ f = spMap (MvPolynomial.C : k →+* MvPolynomial σ k)}
  {he' : e' ≫ g = spMap (MvPolynomial.C : k →+* MvPolynomial τ k)}

theorem isOpenImmersion_prodChart [IsOpenImmersion e] [IsOpenImmersion e'] :
    IsOpenImmersion (prodChart f g e e' he he') := by
  unfold prodChart
  have : IsIso (CommRingCat.ofHom (sumTensEquiv (k := k) σ τ).symm.toRingHom) :=
    (sumTensEquiv (k := k) σ τ).symm.toCommRingCatIso.isIso_hom
  have : IsIso (spMap (sumTensEquiv (k := k) σ τ).symm.toRingHom) := inferInstanceAs (IsIso (Spec.map _))
  have : IsOpenImmersion (pullback.map (Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial σ k))))
      (Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial τ k)))) f g e e' (𝟙 _)
      (by rw [Category.comp_id, he]; rfl) (by rw [Category.comp_id, he']; rfl)) :=
    Scheme.pullback_map_isOpenImmersion _ _ _ _ _ _ _ _ _
  infer_instance

theorem prodChart_str : prodChart f g e e' he he' ≫ (pullback.fst f g ≫ f) =
    spMap (MvPolynomial.C : k →+* MvPolynomial (τ ⊕ σ) k) := by
  unfold prodChart
  rw [Category.assoc, Category.assoc, pullback.lift_fst_assoc, Category.assoc, he,
    pullbackSpecIso_inv_fst_assoc]
  unfold spMap
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext1
  refine RingHom.ext fun r => ?_
  change (sumTensEquiv (k := k) σ τ).symm (Algebra.TensorProduct.includeLeftRingHom (MvPolynomial.C r)) = MvPolynomial.C r
  rw [RingEquiv.symm_apply_eq, sumTensEquiv_C]
  rfl

theorem range_prodChart : Set.range (prodChart f g e e' he he') =
    pullback.fst f g ⁻¹' Set.range e ∩ pullback.snd f g ⁻¹' Set.range e' := by
  have e₁ : Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial σ k))) ≫ 𝟙 (Sp k) = e ≫ f := by
    rw [Category.comp_id, he]; rfl
  have e₂ : Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial τ k))) ≫ 𝟙 (Sp k) = e' ≫ g := by
    rw [Category.comp_id, he']; rfl
  have hr := Scheme.Pullback.range_map _ _ f g e e' (𝟙 _) e₁ e₂
  have : IsIso (CommRingCat.ofHom (sumTensEquiv (k := k) σ τ).symm.toRingHom) :=
    (sumTensEquiv (k := k) σ τ).symm.toCommRingCatIso.isIso_hom
  have : IsIso (spMap (sumTensEquiv (k := k) σ τ).symm.toRingHom) := inferInstanceAs (IsIso (Spec.map _))
  let a := spMap (sumTensEquiv (k := k) σ τ).symm.toRingHom ≫
    (pullbackSpecIso k (MvPolynomial σ k) (MvPolynomial τ k)).inv
  have ha : Function.Surjective a := (inferInstance : Surjective a).surj
  have hc : prodChart f g e e' he he' = a ≫ pullback.map _ _ f g e e' (𝟙 _) e₁ e₂ := by
    simp only [prodChart, a, Category.assoc]
  rw [hc, ← hr]
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨a t, (Scheme.Hom.comp_apply a _ t).symm⟩
  · rintro ⟨u, rfl⟩
    obtain ⟨t, rfl⟩ := ha u
    exact ⟨t, Scheme.Hom.comp_apply a _ t⟩

theorem polyCovered_pullback' {X Y : Scheme.{0}} (f : X ⟶ Sp k) (g : Y ⟶ Sp k) (a b : ℕ) (hf : PolyCovered f a)
    (hg : PolyCovered g b) : PolyCovered (pullback.fst f g ≫ f) (a + b) := by
  obtain ⟨ξ, hξ, hX⟩ := hf
  obtain ⟨η, hη, hY⟩ := hg
  have heq : f ξ = g η := ((hξ (g η)).antisymm (hη (f ξ))).eq
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback ξ η heq
  refine ⟨z, fun y => ?_, fun x => ?_⟩
  · rw [Scheme.Hom.comp_apply, hz1]
    exact hξ y
  · obtain ⟨σ, _, e, he1, he2, he3, hxe, hξe⟩ := hX (pullback.fst f g x)
    obtain ⟨τ, _, e', he1', he2', he3', hxe', hηe'⟩ := hY (pullback.snd f g x)
    refine ⟨τ ⊕ σ, inferInstance, prodChart f g e e' he3 he3', isOpenImmersion_prodChart, ?_, prodChart_str, ?_, ?_⟩
    · rw [Fintype.card_sum, he2, he2', add_comm]
    · rw [range_prodChart]
      exact ⟨hxe, hxe'⟩
    · rw [range_prodChart]
      refine ⟨?_, ?_⟩
      · show pullback.fst f g z ∈ Set.range e
        rw [hz1]; exact hξe
      · show pullback.snd f g z ∈ Set.range e'
        rw [hz2]; exact hηe'

end GlobalTheory.Amb
end
end

