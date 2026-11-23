module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0539
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsImageHeightUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurePreservingRotBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1581
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1631
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceBigCellLocalUnitaryDecomposition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2089
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealPullbackLocallyGenerated
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IdealPull

theorem germ_appLE {X Y : Scheme.{0}} (t : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (hV : V ≤ t ⁻¹ᵁ U)
    (y : Y) (hy : y ∈ V) (a : Γ(X, U)) :
    (Y.presheaf.germ V y hy).hom ((t.appLE U V hV).hom a) =
      (t.stalkMap y).hom ((X.presheaf.germ U (t y) (show t y ∈ U from hV hy)).hom a) := by
  show (Y.presheaf.germ V y hy).hom (resG Y hV ((t.app U).hom a)) = _
  rw [germ_resG]
  exact (Scheme.Hom.germ_stalkMap_apply t U y _ a).symm

theorem regAt_and_unitAt_div_gen : ∀ (Y₀ Y₁ : Scheme.{0}) [IsIntegral Y₁] (t : Y₁ ⟶ Y₀) (I : Y₀.IdealSheafData) (y : Y₁) (U : Y₀.Opens) (hx : t y ∈ U) (n : ℕ) (b : Fin n → Γ(Y₀, U)), (∀ (k : Fin n) (W : Y₀.affineOpens) (h : W.1 ≤ U), resG Y₀ h (b k) ∈ I.ideal W) → (∀ (W : Y₀.affineOpens) (hxW : t y ∈ W.1) (a : Γ(Y₀, W.1)), a ∈ I.ideal W → Y₀.presheaf.germ W.1 (t y) hxW a ∈ Ideal.span (Set.range fun k => Y₀.presheaf.germ U (t y) hx (b k))) → ∀ (U' : Y₁.affineOpens) (f : Γ(Y₁, U'.1)) (hyU' : y ∈ U'.1), fnOf U'.1 (gen_mem hyU') f ≠ 0 → (I.comap t).ideal U' = Ideal.span {f} → ∀ (V : Y₁.Opens) (hV : V ≤ t ⁻¹ᵁ U) (hyV : y ∈ V), (∀ k, RegAt y (fnOf V (gen_mem hyV) (t.appLE U V hV (b k)) / fnOf U'.1 (gen_mem hyU') f)) ∧ ∃ k, UnitAt y (fnOf V (gen_mem hyV) (t.appLE U V hV (b k)) / fnOf U'.1 (gen_mem hyU') f) := by
  intro Y₀ Y₁ _ t I y U hx n b hb hgerm U' f hyU' hf0 hU' V hV hyV
  obtain ⟨_, ⟨W, hWa, rfl⟩, hxW, hWU⟩ := Y₀.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  have hWU' : W ≤ U := hWU
  obtain ⟨_, ⟨V₀, hV₀a, rfl⟩, hyV₀, hV₀le⟩ := Y₁.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ U'.1 ⊓ t ⁻¹ᵁ W from ⟨hyU', hxW⟩) (U'.1 ⊓ t ⁻¹ᵁ W).isOpen
  have hV₀U' : V₀ ≤ U'.1 := fun z hz => (hV₀le hz).1
  have hV₀W : V₀ ≤ t ⁻¹ᵁ W := fun z hz => (hV₀le hz).2
  let R := Y₁.presheaf.stalk y
  let g : R := (Y₁.presheaf.germ U'.1 y hyU').hom f
  let β : Fin n → R := fun k => (t.stalkMap y).hom ((Y₀.presheaf.germ U (t y) hx).hom (b k))
  have hI1 : (I.comap t).ideal ⟨V₀, hV₀a⟩ = Ideal.span {resG Y₁ hV₀U' f} := by
    rw [← (I.comap t).map_ideal (U := ⟨V₀, hV₀a⟩) (V := U') hV₀U', hU', Ideal.map_span,
      Set.image_singleton]
    rfl
  have hI2 := GlobalTheory.Principalise.comapIdealAffine I t ⟨W, hWa⟩ ⟨V₀, hV₀a⟩ hV₀W
  have hgf : (Y₁.presheaf.germ V₀ y hyV₀).hom (resG Y₁ hV₀U' f) = g := germ_resG _ _ _ _
  have hc : ∀ k, ∃ c : R, β k = c * g := by
    intro k
    have hmem : (t.appLE W V₀ hV₀W).hom (resG Y₀ hWU' (b k)) ∈ (I.comap t).ideal ⟨V₀, hV₀a⟩ := by
      rw [hI2]; exact Ideal.mem_map_of_mem _ (hb k ⟨W, hWa⟩ hWU')
    rw [hI1, Ideal.mem_span_singleton'] at hmem
    obtain ⟨c, hc⟩ := hmem
    refine ⟨(Y₁.presheaf.germ V₀ y hyV₀).hom c, ?_⟩
    have := congrArg (Y₁.presheaf.germ V₀ y hyV₀).hom hc
    rw [map_mul, hgf, germ_appLE, germ_resG] at this
    exact this.symm
  choose c hcβ using hc
  have hgmem : g ∈ Ideal.span (Set.range β) := by
    have hmem : resG Y₁ hV₀U' f ∈ (I.comap t).ideal ⟨V₀, hV₀a⟩ := by
      rw [hI1]; exact Ideal.mem_span_singleton_self _
    rw [hI2] at hmem
    have h2 := Ideal.mem_map_of_mem (Y₁.presheaf.germ V₀ y hyV₀).hom hmem
    rw [hgf, Ideal.map_map] at h2
    refine (Ideal.map_le_iff_le_comap.2 ?_) h2
    intro a ha
    rw [Ideal.mem_comap, RingHom.comp_apply, germ_appLE]
    have h3 := Ideal.mem_map_of_mem (t.stalkMap y).hom (hgerm ⟨W, hWa⟩ hxW a ha)
    rw [Ideal.map_span, ← Set.range_comp] at h3
    exact h3
  have hfK : algebraMap R Y₁.functionField g = fnOf U'.1 (gen_mem hyU') f := algebraMap_germ hyU' f
  have hg0 : g ≠ 0 := fun h => hf0 (by rw [← hfK, h, map_zero])
  have hFk : ∀ k, fnOf V (gen_mem hyV) (t.appLE U V hV (b k)) / fnOf U'.1 (gen_mem hyU') f =
      algebraMap R Y₁.functionField (c k) := by
    intro k
    rw [← algebraMap_germ hyV, ← hfK, germ_appLE]
    change algebraMap R _ (β k) / _ = _
    rw [hcβ k, map_mul, mul_div_assoc, div_self (hfK ▸ hf0), mul_one]
  refine ⟨fun k => hFk k ▸ ⟨c k, rfl⟩, ?_⟩
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hgmem
  have hsum : ∑ k, e k * c k = 1 := by
    have : (∑ k, e k * c k) * g = 1 * g := by
      rw [one_mul, Finset.sum_mul]
      conv_rhs => rw [← he]
      exact Finset.sum_congr rfl fun k _ => by rw [hcβ k, smul_eq_mul, mul_assoc]
    exact mul_right_cancel₀ hg0 this
  obtain ⟨k, hk⟩ : ∃ k, IsUnit (c k) := by
    by_contra hcon
    push_neg at hcon
    have : (1 : R) ∈ IsLocalRing.maximalIdeal R := hsum ▸ Ideal.sum_mem _ fun k _ =>
      Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hcon k))
    exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal R).ne_top this
  exact ⟨k, c k, hk, (hFk k).symm⟩

end GlobalTheory.IdealPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageHeightAddLogNonneg
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace GlobalTheory.ImageHeightNonneg

theorem IsImageHeight.neg_log_le {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] {Nm : (K →+* ℂ) → V → ℝ} {L : Submodule (𝓞 K) V}
    {ev : V →ₗ[K] Ω} {d n : ℕ} {w : Fin n → V} {abelian₂ h : ℝ} (hs : Submodule.span K (L : Set V) = ⊤)
    (hw : Submodule.span (𝓞 K) (Set.range w) = L) (hle : ∀ i σ, Nm σ (w i) ≤ abelian₂) (hh : IsImageHeight Nm L ev d h) :
    0 ≤ h + Real.log abelian₂ := by
  obtain ⟨N, n', b, w', A, δ, f, hF, hf, e⟩ := hh
  have hF' : IsFrame Nm L b (Matrix.of fun j k => b.repr (w k) j) A := by
    refine ⟨?_, ?_, hF.herm, hF.conj, hF.norm⟩
    · simp only [Matrix.of_apply, Module.Basis.sum_repr]; exact hw
    · have h1 : Submodule.span K (Set.range w) = ⊤ := by rw [← hs, ← hw, Submodule.span_span_of_tower]
      have h2 := congrArg (Submodule.map b.equivFun.toLinearMap) h1
      rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, LinearEquiv.range] at h2
      exact h2
  have h1 := GlobalTheory.ImageHeightUnique.formHeight_linSubst hF hF' δ f
  rw [Module.Basis.toMatrix_self, GlobalTheory.HeightUnique.linSubst_one] at h1
  obtain ⟨y, hy, -⟩ := hf.exists_point
  obtain ⟨j, -⟩ := Function.ne_iff.1 hy
  have h2 := GlobalTheory.FormHtLower.formHeight_ge (Λ := abelian₂) (Fin.pos j) hF'.full hF'.herm
    (fun k σ => (hF.norm σ (w k)).trans_le (hle k σ)) hf.ne_zero hf.homog
  rw [h1, ← e] at h2
  have hpos : (0 : ℝ) < ((d : ℝ) + 1) * δ := mul_pos (by positivity) (Nat.cast_pos.2 hf.pos)
  refine nonneg_of_mul_nonneg_right (a := ((d : ℝ) + 1) * δ) ?_ hpos
  push_cast at h2
  linarith

theorem imageHeight_add_log_nonneg (K V Ω : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ)
    (L : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (d n : ℕ) (w : Fin n → V) (abelian₂ : ℝ) (hG : HasGram Nm)
    (hc : ∀ σ x, Nm ((starRingEnd ℂ).comp σ) x = Nm σ x) (hs : Submodule.span K (L : Set V) = ⊤)
    (hw : IsShortGen Nm L w abelian₂) (hd : 0 < imageDeg ev d) : 0 ≤ imageHeight Nm L ev d + Real.log abelian₂ := by
  have hL : Submodule.span (𝓞 K) (Set.range w) = L :=
    le_antisymm (Submodule.span_le.2 fun x hx => (hw.gen x).2 (Submodule.subset_span hx))
      fun x hx => Submodule.span_le_restrictScalars ℤ (𝓞 K) _ ((hw.gen x).1 hx)
  have hK : ∀ σ : K →+* ℂ, (starRingEnd ℂ).comp σ ≠ σ := fun σ h =>
    IsTotallyComplex.complexEmbedding_not_isReal σ h
  exact IsImageHeight.neg_log_le hs hL hw.le (isImageHeight_imageHeight (exists_isImageHeight_iff.2
    ⟨exists_isFrame hK hc hG (hL ▸ Submodule.fg_span (Set.finite_range _)) hs, hd⟩))

end GlobalTheory.ImageHeightNonneg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImplocusOpenClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section
namespace GlobalTheory.LevCover

theorem implocus_open_closed : ∀ (Y : Scheme.{0}) (Z : Over Y) (P Q : ∀ T : Over Y, (T ⟶ Z) → Prop), IsFinite Z.hom → Etale Z.hom → GlobalTheory.LevCover.ClopenCond Z P → GlobalTheory.LevCover.ClopenCond Z Q → ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ (∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ W ↔ ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom → ∀ z : T ⟶ Z, P T z → Q T z) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y), Set.range x.base ⊆ W ↔ ∀ z : Over.mk x ⟶ Z, P _ z → Q _ z := by
  intro Y Z P Q hfin het hP hQ
  obtain ⟨U, hUc, HU⟩ := hP
  obtain ⟨V, hVc, HV⟩ := hQ
  let B : Set Z.left := (U : Set Z.left) \ V
  have hBo : IsOpen B := U.isOpen.sdiff hVc
  have hBc : IsClosed B := hUc.sdiff V.isOpen
  have c1 : ∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ (Z.hom.base '' B)ᶜ ↔
      ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom → ∀ z : T ⟶ Z, P T z → Q T z := by
    intro Tb t
    constructor
    · intro hW T σ hσ z hPz
      rw [HU] at hPz
      rw [HV]
      rintro _ ⟨w, rfl⟩
      by_contra hv
      have hb : z.left.base w ∈ B := ⟨hPz ⟨w, rfl⟩, hv⟩
      apply hW ⟨σ.base w, rfl⟩
      refine ⟨_, hb, ?_⟩
      rw [← Scheme.Hom.comp_apply, Over.w z, ← hσ, Scheme.Hom.comp_apply]
    · intro H
      rintro _ ⟨τ, rfl⟩ ⟨u, hu, hτ⟩
      obtain ⟨p, hp1, hp2⟩ := Scheme.Pullback.exists_preimage_pullback τ u hτ.symm
      let O : (pullback t Z.hom).Opens := (pullback.snd t Z.hom) ⁻¹ᵁ ⟨B, hBo⟩
      let T : Over Y := Over.mk (O.ι ≫ pullback.fst t Z.hom ≫ t)
      let z : T ⟶ Z := Over.homMk (O.ι ≫ pullback.snd t Z.hom) (by simp [T, pullback.condition])
      have hmem : ∀ w, O.ι.base w ∈ (O : Set _) := fun w => by
        rw [← Scheme.Opens.range_ι O]; exact ⟨w, rfl⟩
      have hPz : P T z := by
        rw [HU]
        rintro _ ⟨w, rfl⟩
        exact (hmem w).1
      have hQz := H T (O.ι ≫ pullback.fst t Z.hom) (Category.assoc _ _ _) z hPz
      rw [HV] at hQz
      have hpO : p ∈ Set.range O.ι.base := by
        rw [Scheme.Opens.range_ι O]
        show (pullback.snd t Z.hom).base p ∈ B
        rw [hp2]; exact hu
      obtain ⟨w, hw⟩ := hpO
      apply hu.2
      have := hQz ⟨w, rfl⟩
      simpa [z, Scheme.Hom.comp_apply, hw, hp2] using this
  refine ⟨(Z.hom.base '' B)ᶜ, (Z.hom.isClosedMap _ hBc).isOpen_compl,
    (Z.hom.isOpenMap _ hBo).isClosed_compl, c1, ?_⟩
  intro k _ _ x
  constructor
  · intro hW z hPz
    exact (c1 (Sp k) x).1 hW (Over.mk x) (𝟙 _) (Category.id_comp _) z hPz
  · intro H
    rintro _ ⟨s, rfl⟩ ⟨u, hu, hs⟩
    let Bo : Z.left.Opens := ⟨B, hBo⟩
    haveI : IsClosedImmersion Bo.ι := .of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hBc)
    have huB : u ∈ Set.range Bo.ι.base := by rw [Scheme.Opens.range_ι]; exact hu
    obtain ⟨v, hv⟩ := huB
    obtain ⟨w, hw⟩ := GlobalTheory.LevCover.exists_lift_geom (Bo.ι ≫ Z.hom) x (by
      rintro _ ⟨s', rfl⟩
      refine ⟨v, ?_⟩
      rw [Subsingleton.elim s' s, Scheme.Hom.comp_apply, hv, hs])
    let z : Over.mk x ⟶ Z := Over.homMk (w ≫ Bo.ι) (by simpa using hw)
    have hPz : P _ z := by
      rw [HU]
      rintro _ ⟨y, rfl⟩
      have : (Bo.ι.base (w.base y)) ∈ (Bo : Set Z.left) := by
        rw [← Scheme.Opens.range_ι Bo]; exact ⟨_, rfl⟩
      exact this.1
    have hQz := H z hPz
    rw [HV] at hQz
    let y0 : Sp k := (⊥ : PrimeSpectrum k)
    have h1 : (Bo.ι.base (w.base y0)) ∈ (Bo : Set Z.left) := by
      rw [← Scheme.Opens.range_ι Bo]; exact ⟨_, rfl⟩
    exact h1.2 (hQz ⟨y0, rfl⟩)

end GlobalTheory.LevCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsExtraTail
section
noncomputable section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.FactorAndSection

theorem exists_factor {R K A : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing A] (φ : R →+* A) (hφ : φ.IsIntegral) (ψ : A →+* K)
    (h : ψ.comp φ = algebraMap R K) : ∃ χ : A →+* R, (algebraMap R K).comp χ = ψ ∧ χ.comp φ = RingHom.id R := by
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hmem : ∀ a : A, ψ a ∈ (algebraMap R K).range := by
    intro a
    have h1 : (ψ.comp φ).IsIntegralElem (ψ a) := (hφ a).map ψ
    rw [h] at h1
    exact (IsIntegrallyClosed.isIntegral_iff (R := R) (K := K)).1 h1
  let e : R ≃+* (algebraMap R K).range := RingEquiv.ofBijective (algebraMap R K).rangeRestrict
    ⟨fun a b hab => hinj (congrArg Subtype.val hab), (algebraMap R K).rangeRestrict_surjective⟩
  have he : ∀ z : (algebraMap R K).range, algebraMap R K (e.symm z) = z.1 := fun z =>
    congrArg Subtype.val (e.apply_symm_apply z)
  have h1 : (algebraMap R K).comp (e.symm.toRingHom.comp (ψ.codRestrict _ hmem)) = ψ := by
    ext a
    exact he _
  refine ⟨e.symm.toRingHom.comp (ψ.codRestrict _ hmem), h1, ?_⟩
  ext r
  apply hinj
  have h2 := congrArg (fun f : A →+* K => f (φ r)) h1
  have h3 := congrArg (fun f : R →+* K => f r) h
  exact h2.trans h3

theorem exists_section {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] {Z : Scheme.{0}} (p : Z ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) [IsFinite p]
    (y : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K ⟶ Z) (hy : y ≫ p = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K)) :
    ∃ x : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Z,
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K) ≫ x = y ∧ x ≫ p = 𝟙 (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) := by
  haveI : IsAffine Z := isAffine_of_isAffineHom p
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Z.isoSpec.inv ≫ p)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (y ≫ Z.isoSpec.hom)
  have hfin : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have hint : φ.hom.IsIntegral := ((IsFinite.SpecMap_iff φ).1 hfin).to_isIntegral
  have hc : φ ≫ ψ = CommRingCat.ofHom (algebraMap R K) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hψ, Category.assoc, Iso.hom_inv_id_assoc, hy]
  obtain ⟨χ, h1, h2⟩ := exists_factor (R := R) (K := K) φ.hom hint ψ.hom (congrArg CommRingCat.Hom.hom hc)
  have h1' : CommRingCat.ofHom χ ≫ CommRingCat.ofHom (algebraMap R K) = ψ := CommRingCat.hom_ext h1
  have h2' : φ ≫ CommRingCat.ofHom χ = 𝟙 _ := CommRingCat.hom_ext h2
  refine ⟨Spec.map (CommRingCat.ofHom χ) ≫ Z.isoSpec.inv, ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, h1', hψ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · rw [Category.assoc, ← hφ, ← Spec.map_comp, h2', Spec.map_id]

end GlobalTheory.FactorAndSection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceBigCellStabiliserOfLocalRingBigCellLem
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertBigCell

theorem exists_bigCell : (∀ {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) O), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A B C D : Matrix (Fin n) (Fin n) O), IsUnit (Matrix.fromBlocks A B C D).det →
      (Matrix.fromBlocks A B C D)ᵀ * Matrix.fromBlocks 0 S S 0 * (Matrix.fromBlocks A B C D).map c =
        Matrix.fromBlocks 0 S S 0 →
      ∃ X : Matrix (Fin n) (Fin n) O, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det) →
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
      ∃ p ∈ GlobalTheory.DblVac.KD σ W v, p ∈ GlobalTheory.DblVac.PDiag σ W ∧ p * g ∈ GlobalTheory.DblVac.KD σ W v ∧ GlobalTheory.DblVac.BigCell W v (p * g) := by
  intro H F E _ _ _ _ _ σ B d W r s hB hW v w hw g hg
  obtain ⟨hinj, -, -, -, -, -, -⟩ := GlobalTheory.T.inertCompletionToAdeles_properties σ hw
  obtain ⟨gmul, gone, ginj, gat, gsurj, gvec⟩ := GlobalTheory.T.adelicMatrixGluedAtInertPlace_properties hw (ι := Fin d ⊕ Fin d)
  obtain ⟨gmul', gone', -, -, -, gvec'⟩ := GlobalTheory.T.adelicMatrixGluedAtInertPlace_properties hw (ι := Fin d)
  obtain ⟨hJ, -, -⟩ := GlobalTheory.T.adelicMatrix_trivial_off_inertPlace_unitary_at_place σ hw (ι := Fin d ⊕ Fin d)
  obtain ⟨-, hdiag, hhalfblk⟩ := GlobalTheory.T.adelicMatrix_trivial_off_inertPlace_unitary_at_place σ hw (ι := Fin d)
  obtain ⟨b, δ, hb, hδ, hint, hdet, hdetinv⟩ := GlobalTheory.T.exists_unimodular_frame_inertPlace σ B W r s hB hW hw
  obtain ⟨cc, cO, h2, calg⟩ := GlobalTheory.T.inertCompletionConjugation_properties σ B hB hw
  have hlat := GlobalTheory.T.mem_adelicLatticeAtFinitePlace_iff_inert hw W

  have hvec : ∀ x : Fin d → w.adicCompletion E,
      (fun i => iotaW hw (x i)) ∈ GlobalTheory.InertSph.latAt W v ↔ InLat (w.adicCompletionIntegers E) b x := by
    intro x
    rw [hlat]
    constructor
    · rintro ⟨u, hu, he⟩
      have hxu : x = u := funext fun i => hinj (congrFun he i)
      subst hxu
      exact (hb x).1 hu
    · intro hx
      exact ⟨x, (hb x).2 hx, rfl⟩
  have hvec2 : ∀ x : Fin d ⊕ Fin d → w.adicCompletion E,
      (fun i => iotaW hw (x i)) ∈ GlobalTheory.DblVac.latD W v ↔ InLat2 (w.adicCompletionIntegers E) b x := by
    intro x
    exact and_congr (hvec (x ∘ Sum.inl)) (hvec (x ∘ Sum.inr))
  have hsurj2 : ∀ z ∈ GlobalTheory.DblVac.latD W v, ∃ x : Fin d ⊕ Fin d → w.adicCompletion E,
      z = fun i => iotaW hw (x i) := by
    rintro z ⟨h1, h2⟩
    obtain ⟨x1, -, e1⟩ := (hlat _).1 h1
    obtain ⟨x2, -, e2⟩ := (hlat _).1 h2
    refine ⟨Sum.elim x1 x2, funext fun i => ?_⟩
    rcases i with i | i
    · exact congrFun e1 i
    · exact congrFun e2 i

  have hpres : ∀ P : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (w.adicCompletion E),
      (∀ x, InLat2 (w.adicCompletionIntegers E) b x → InLat2 (w.adicCompletionIntegers E) b (P *ᵥ x)) →
      ∀ z ∈ GlobalTheory.DblVac.latD W v, glueW hw P *ᵥ z ∈ GlobalTheory.DblVac.latD W v := by
    intro P hP z hz
    obtain ⟨x, rfl⟩ := hsurj2 z hz
    rw [gvec]
    exact (hvec2 _).2 (hP x ((hvec2 x).1 hz))
  have hpres' : ∀ P : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (w.adicCompletion E),
      (∀ z ∈ GlobalTheory.DblVac.latD W v, glueW hw P *ᵥ z ∈ GlobalTheory.DblVac.latD W v) →
      ∀ x, InLat2 (w.adicCompletionIntegers E) b x → InLat2 (w.adicCompletionIntegers E) b (P *ᵥ x) := by
    intro P hP x hx
    have := hP _ ((hvec2 x).2 hx)
    rw [gvec] at this
    exact (hvec2 _).1 this

  have e1 : incM F (dbl W.J) = dbl (incM F W.J) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [incM, dbl]
  have e2 : (dbl W.J).map (algebraMap E (w.adicCompletion E)) = dbl (W.J.map (algebraMap E (w.adicCompletion E))) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [dbl]
  have hskew : (W.J.map (algebraMap E (w.adicCompletion E)))ᵀ =
      -(W.J.map (algebraMap E (w.adicCompletion E))).map (conjW σ hw) := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.neg_apply, calg, hW.skew j i, map_neg, neg_neg]
  have h2ne : (2 : w.adicCompletion E) ≠ 0 := by
    have h := (algebraMap E (w.adicCompletion E)).injective.ne (two_ne_zero : (2 : E) ≠ 0)
    rw [show (2 : w.adicCompletion E) = algebraMap E (w.adicCompletion E) 2 from (map_ofNat _ 2).symm]
    exact h

  obtain ⟨hgat, hglat⟩ := hg
  have hgg : GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.matD g⁻¹ = 1 := Units.mul_inv g.1
  have hgg' : GlobalTheory.DblVac.matD g⁻¹ * GlobalTheory.DblVac.matD g = 1 := Units.inv_mul g.1
  have hginvat : At (evFin F v) (GlobalTheory.DblVac.matD g⁻¹ - 1) := by
    intro u hu
    have e : GlobalTheory.DblVac.matD g⁻¹ - 1 = -(GlobalTheory.DblVac.matD g⁻¹ * (GlobalTheory.DblVac.matD g - 1)) := by
      rw [Matrix.mul_sub, hgg', Matrix.mul_one, neg_sub]
    rw [e, smul_neg, ← Matrix.mul_smul, hgat u hu, Matrix.mul_zero, neg_zero]
  obtain ⟨P, hP⟩ := gsurj _ hgat
  obtain ⟨Q, hQ⟩ := gsurj _ hginvat
  have hPQ : P * Q = 1 := ginj (by rw [gmul, hP, hQ, gone]; exact hgg)
  have hU : Pᵀ * dbl (W.J.map (algebraMap E (w.adicCompletion E))) * P.map (conjW σ hw) =
      dbl (W.J.map (algebraMap E (w.adicCompletion E))) := by
    rw [← e2]
    apply (hJ (dbl W.J) P).1
    rw [hP, e1]
    exact g.2
  have hPlat : ∀ z, InLat2 (w.adicCompletionIntegers E) b z →
      InLat2 (w.adicCompletionIntegers E) b (P *ᵥ z) ∧ InLat2 (w.adicCompletionIntegers E) b (Q *ᵥ z) :=
    fun z hz => ⟨hpres' P (fun y hy => by rw [hP]; exact (hglat y hy).1) z hz,
      hpres' Q (fun y hy => by rw [hQ]; exact (hglat y hy).2) z hz⟩

  obtain ⟨P0, P0', hPP, hP0U, hP0d, hP0lat, N, hN, hNlat⟩ :=
    _root_.GlobalTheory.InertCellLocal.bigCell_local_step H (w.adicCompletionIntegers E) (conjW σ hw) cc cO h2 h2ne
      (W.J.map (algebraMap E (w.adicCompletion E))) hskew b δ hδ hint hdet hdetinv P Q hPQ hU hPlat

  let u : GL (Fin d ⊕ Fin d) (AE F E) :=
    ⟨glueW hw P0, glueW hw P0', by rw [← gmul, hPP, gone], by
      have hPP' : P0' * P0 = 1 := mul_eq_one_comm.mp hPP
      rw [← gmul, hPP', gone]⟩
  have hu : u ∈ UG (cA σ) (dbl (incM F W.J)) := by
    show (glueW hw P0)ᵀ * dbl (incM F W.J) * (glueW hw P0).map (cA σ) = dbl (incM F W.J)
    rw [← e1]
    apply (hJ (dbl W.J) P0).2
    rw [e2]
    exact hP0U
  let p : GlobalTheory.DblVac.UD σ W := ⟨u, hu⟩
  have hp : GlobalTheory.DblVac.matD p = glueW hw P0 := rfl
  have hp' : GlobalTheory.DblVac.matD p⁻¹ = glueW hw P0' := rfl
  have hmul : ∀ a c : GlobalTheory.DblVac.UD σ W, GlobalTheory.DblVac.matD (a * c) = GlobalTheory.DblVac.matD a * GlobalTheory.DblVac.matD c :=
    fun _ _ => rfl
  have hpl : ∀ z ∈ GlobalTheory.DblVac.latD W v, GlobalTheory.DblVac.matD p *ᵥ z ∈ GlobalTheory.DblVac.latD W v :=
    hpres P0 (fun x hx => (hP0lat x hx).1)
  have hpl' : ∀ z ∈ GlobalTheory.DblVac.latD W v, GlobalTheory.DblVac.matD p⁻¹ *ᵥ z ∈ GlobalTheory.DblVac.latD W v :=
    hpres P0' (fun x hx => (hP0lat x hx).2)
  have hpg : GlobalTheory.DblVac.matD (p * g) = glueW hw (P0 * P) := by
    rw [gmul, hP]
    rfl
  refine ⟨p, ⟨?_, fun z hz => ⟨hpl z hz, hpl' z hz⟩⟩, ⟨1, ?_⟩, ⟨?_, fun z hz => ⟨?_, ?_⟩⟩, ?_⟩
  · rw [hp]
    exact gat P0
  · rw [hp]
    refine (hdiag P0 hP0d).trans ?_
    exact (Matrix.mul_one _).symm
  · rw [hpg]
    exact gat _
  · rw [hmul, ← Matrix.mulVec_mulVec]
    exact hpl _ (hglat z hz).1
  · rw [mul_inv_rev, hmul, ← Matrix.mulVec_mulVec]
    exact (hglat _ (hpl' z hz)).2
  ·
    refine ⟨glueW hw N, ?_, ?_⟩
    · have hd : GlobalTheory.DblVac.diagonalBlockOfMatrix (p * g) = glueW hw ((2 : w.adicCompletion E)⁻¹ •
          ((P0 * P).toBlocks₁₁ + (P0 * P).toBlocks₁₂ + (P0 * P).toBlocks₂₁ + (P0 * P).toBlocks₂₂)) := by
        unfold GlobalTheory.DblVac.diagonalBlockOfMatrix
        rw [hpg]
        exact hhalfblk _
      rw [hd, ← gmul', hN, gone']
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := (hlat z).1 hz
      rw [gvec']
      exact (hvec _).2 (hNlat x ((hb x).1 hx))

end GlobalTheory.InertBigCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeGenericFibreInjectiveDomainMapStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAbelianScheme_genericFibre_injective_domain_map : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R'), Function.Injective ρ → ∀ (G : Over (Sp R)) [GrpObj G], IsAbelianScheme ((Over.pullback (jK R)).obj G) → IsAbelianScheme ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)) := by
  first | exact @GlobalTheory.Desc.isAbelianScheme_generic_of_injective | exact GlobalTheory.Desc.isAbelianScheme_generic_of_injective | (intros; apply GlobalTheory.Desc.isAbelianScheme_generic_of_injective <;> assumption)
end

