module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0571
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0589
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0014
public import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockCharactersCrystallineOfRules
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0495
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0468
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0090
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfClosedMembershipLimit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleBasisLimitLatticeTower
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0534
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0565
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0588

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowDvdGaloisComparisonMatrix
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem pow_dvd_map_of_smul_eq {A D W : Type} [CommRing A] [CommRing D] [CommRing W] {n : Type} [Fintype n]
    [DecidableEq n] (i : A →+* D) (hi : Function.Injective i) (j : A →+* W) (t t' : A) (N l k : ℕ)
    (M Y y : Matrix n n A) (ε : Matrix n n D) (h : i t ^ N • M.map i = i t' ^ N • (Y.map i * ε))
    (hy : y.map i = (l : D) ^ k • ε) (ht : IsUnit (j t')) (hY : IsUnit (Y.map j)) (a b : n) :
    (l : W) ^ k ∣ j (y a b) := by
  have h1 : ((l : A) ^ k * t ^ N) • M = t' ^ N • (Y * y) := by
    apply Matrix.map_injective hi
    change (((l : A) ^ k * t ^ N) • M).map i = (t' ^ N • (Y * y)).map i
    have e1 : (((l : A) ^ k * t ^ N) • M).map i = (l : D) ^ k • (i t ^ N • M.map i) := by
      ext p q; simp [mul_assoc]
    have e2 : (t' ^ N • (Y * y)).map i = i t' ^ N • (Y.map i * y.map i) := by
      rw [← Matrix.map_mul]; ext p q; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow]
    rw [e1, e2, h, hy, Matrix.mul_smul, smul_comm]
  have h2 : (l : W) ^ k • (j t ^ N • M.map j) = j t' ^ N • (Y.map j * y.map j) := by
    have e := congrArg (fun Z : Matrix n n A => Z.map j) h1
    rw [← Matrix.map_mul]
    ext p q
    have := congrFun (congrFun e p) q
    simpa only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast, mul_assoc]
      using this
  obtain ⟨u, hu⟩ := hY
  obtain ⟨v, hv⟩ := ht.pow N
  have h3 : y.map j = (l : W) ^ k • ((↑v⁻¹ : W) • ((↑u⁻¹ : Matrix n n W) * (j t ^ N • M.map j))) := by
    rw [smul_comm, ← Matrix.mul_smul, h2, ← hu, ← hv, Matrix.mul_smul, ← mul_assoc, Units.inv_mul, one_mul,
      smul_smul, Units.inv_mul, one_smul]
  exact ⟨_, congrFun (congrFun h3 a) b⟩

theorem pow_dvd_of_rel_gal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → (∀ g, IsUnit (ρ g)) → ∀ (g : ↥(GK K)) (ε : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)), ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι) ε → ∀ (k : ℕ) (y : Matrix (Fin d) (Fin d) (Ainf l)), y.map bk.iA = ((l : ℕ) : bk.DA bk.ρ₀) ^ k • ε → ∀ i j, ((l : ℕ) : Ainf l) ^ k ∣ y i j := by
  intro l _ K bk d ρ τ s ht hτ _ g ε hε k y hy i j
  obtain ⟨ι, ⟨tb⟩⟩ := _root_.GlobalTheory.BSP.AinfTopBasis.main l K bk
  obtain ⟨-, hu, hsat⟩ := _root_.GlobalTheory.BSP.isUnit_inclW_per_and_saturated l K bk τ hτ
  exact hsat k _ (pow_dvd_map_of_smul_eq bk.iA (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk (Ainf l) bk.ev ι tb).1 (inclW l) τ _ s.N l k
    _ ht.Y y ε (GlobalTheory.T.rel_galois_comparison_matrix l K bk d ρ τ s ht hτ g ε hε) hy (hu g) ht.unit i j)

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageMapLatticeEquiv
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem avg_equiv : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (G' : Type) [AddCommGroup G'] [TopologicalSpace G'] [IsTopologicalAddGroup G'] [LocallyCompactSpace G'] [SecondCountableTopology G'] [T2Space G'] (Γ : AddSubgroup G) (Γ' : AddSubgroup G'), IsCoLat Γ → IsCoLat Γ' → ∀ e : G ≃ₜ+ G', (∀ x, e x ∈ Γ' ↔ x ∈ Γ) → ∀ Φ : G' → ℂ, Per Γ' Φ → avg Γ (fun x => Φ (e x)) = avg Γ' Φ := by
  intro G _ _ _ _ _ _ G' _ _ _ _ _ _ Γ Γ' hΓ hΓ' e he Φ hΦ
  letI mG : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  letI mG' : MeasurableSpace G' := borel G'
  haveI : BorelSpace G' := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := _root_.GlobalTheory.CuspGeneric.exists_fundamentalDomain_mass_one G Γ hΓ
  let f : G ≃ᵐ G' := e.toHomeomorph.toMeasurableEquiv
  haveI := hμ
  have hμ' : (μ.map f).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  let eΓ : Γ' ≃ Γ :=
    { toFun := fun g => ⟨e.symm g, (he _).1 (by simpa using g.2)⟩
      invFun := fun x => ⟨e x, (he x).2 x.2⟩
      left_inv := fun g => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }
  have hqmp : Measure.QuasiMeasurePreserving f.toEquiv.symm (μ.map f) μ :=
    MeasurePreserving.quasiMeasurePreserving ⟨f.symm.measurable, f.map_symm_map⟩
  have h𝓕' : IsAddFundamentalDomain Γ' (f '' 𝓕) (μ.map f) := by
    refine h𝓕.image_of_equiv f.toEquiv hqmp eΓ fun g x => ?_
    show e (e.symm (g : G') + x) = (g : G') + e x
    rw [map_add (f := _), ContinuousAddEquiv.apply_symm_apply]
  have hm : (μ.map f) (f '' 𝓕) = 1 := by
    rw [MeasurableEquiv.map_apply, Set.preimage_image_eq _ f.injective, h1]
  have hΦ' : Per Γ (fun x => Φ (e x)) :=
    ⟨hΦ.1.comp e.continuous, fun γ hγ x => by show Φ (e (γ + x)) = Φ (e x); rw [map_add (f := _)]; exact hΦ.2 _ ((he γ).2 hγ) _⟩
  have A := (_root_.GlobalTheory.CuspGeneric.setIntegral_eq_mass_mul_avg G' Γ' hΓ' (μ.map f) (f '' 𝓕) hμ' h𝓕' Φ hΦ).2.2.2
  have B := (_root_.GlobalTheory.CuspGeneric.setIntegral_eq_mass_mul_avg G Γ hΓ μ 𝓕 hμ h𝓕 _ hΦ').2.2.2
  rw [hm] at A
  rw [h1] at B
  simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul] at A B
  rw [← A, ← B, f.measurableEmbedding.setIntegral_map, Set.preimage_image_eq _ f.injective]
  rfl

end GlobalTheory.CuspGeneric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageProdFubini
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

section Prod

variable {G₁ : Type} [AddCommGroup G₁] [TopologicalSpace G₁] [IsTopologicalAddGroup G₁]
  {G₂ : Type} [AddCommGroup G₂] [TopologicalSpace G₂] [IsTopologicalAddGroup G₂]

theorem isCoLat_prod {Γ₁ : AddSubgroup G₁} {Γ₂ : AddSubgroup G₂} (h₁ : IsCoLat Γ₁) (h₂ : IsCoLat Γ₂) :
    IsCoLat (Γ₁.prod Γ₂) := by
  obtain ⟨d₁, K₁, hK₁, c₁⟩ := h₁
  obtain ⟨d₂, K₂, hK₂, c₂⟩ := h₂
  refine ⟨?_, K₁ ×ˢ K₂, hK₁.prod hK₂, fun z => ?_⟩
  · refine DiscreteTopology.of_continuous_injective
      (f := fun z : Γ₁.prod Γ₂ => ((⟨z.1.1, (AddSubgroup.mem_prod.1 z.2).1⟩ : Γ₁),
        (⟨z.1.2, (AddSubgroup.mem_prod.1 z.2).2⟩ : Γ₂))) ?_ ?_
    · exact ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
    · intro a b h
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      exact Subtype.ext (Prod.ext h.1 h.2)
  · obtain ⟨γ₁, hγ₁, e₁⟩ := c₁ z.1
    obtain ⟨γ₂, hγ₂, e₂⟩ := c₂ z.2
    exact ⟨(γ₁, γ₂), AddSubgroup.mem_prod.2 ⟨hγ₁, hγ₂⟩, ⟨e₁, e₂⟩⟩

end Prod

section FD

open Pointwise

variable {G₁ : Type} [AddCommGroup G₁] [MeasurableSpace G₁]
  {G₂ : Type} [AddCommGroup G₂] [MeasurableSpace G₂]

theorem vadd_prod_set {Γ₁ : AddSubgroup G₁} {Γ₂ : AddSubgroup G₂} (g : Γ₁.prod Γ₂) (A : Set G₁) (B : Set G₂) :
    g +ᵥ (A ×ˢ B) = ((g : G₁ × G₂).1 +ᵥ A) ×ˢ ((g : G₁ × G₂).2 +ᵥ B) := by
  ext ⟨x, y⟩
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_prod]
  rfl

theorem isAddFundamentalDomain_prod {Γ₁ : AddSubgroup G₁} {Γ₂ : AddSubgroup G₂} {μ₁ : Measure G₁} {μ₂ : Measure G₂}
    [SFinite μ₁] [SFinite μ₂] {𝓕₁ : Set G₁} {𝓕₂ : Set G₂}
    (h₁ : IsAddFundamentalDomain Γ₁ 𝓕₁ μ₁) (h₂ : IsAddFundamentalDomain Γ₂ 𝓕₂ μ₂) :
    IsAddFundamentalDomain (Γ₁.prod Γ₂) (𝓕₁ ×ˢ 𝓕₂) (μ₁.prod μ₂) := by
  refine ⟨h₁.nullMeasurableSet.prod h₂.nullMeasurableSet, ?_, ?_⟩
  · have a₁ : ∀ᵐ z ∂μ₁.prod μ₂, ∃ γ : Γ₁, γ +ᵥ z.1 ∈ 𝓕₁ := Measure.quasiMeasurePreserving_fst.ae h₁.ae_covers
    have a₂ : ∀ᵐ z ∂μ₁.prod μ₂, ∃ γ : Γ₂, γ +ᵥ z.2 ∈ 𝓕₂ := Measure.quasiMeasurePreserving_snd.ae h₂.ae_covers
    filter_upwards [a₁, a₂] with z ⟨γ₁, e₁⟩ ⟨γ₂, e₂⟩
    exact ⟨⟨((γ₁ : G₁), (γ₂ : G₂)), AddSubgroup.mem_prod.2 ⟨γ₁.2, γ₂.2⟩⟩, ⟨e₁, e₂⟩⟩
  · intro g g' hne
    change μ₁.prod μ₂ ((g +ᵥ (𝓕₁ ×ˢ 𝓕₂)) ∩ (g' +ᵥ (𝓕₁ ×ˢ 𝓕₂))) = 0
    rw [vadd_prod_set, vadd_prod_set, Set.prod_inter_prod, Measure.prod_prod]
    by_cases e : (g : G₁ × G₂).1 = (g' : G₁ × G₂).1
    · have e2 : (g : G₁ × G₂).2 ≠ (g' : G₁ × G₂).2 := fun e2 => hne (Subtype.ext (Prod.ext e e2))
      have := h₂.aedisjoint (i := ⟨(g : G₁ × G₂).2, (AddSubgroup.mem_prod.1 g.2).2⟩)
        (j := ⟨(g' : G₁ × G₂).2, (AddSubgroup.mem_prod.1 g'.2).2⟩) (fun h => e2 (congrArg Subtype.val h))
      rw [show μ₂ (((g : G₁ × G₂).2 +ᵥ 𝓕₂) ∩ ((g' : G₁ × G₂).2 +ᵥ 𝓕₂)) = 0 from this, mul_zero]
    · have := h₁.aedisjoint (i := ⟨(g : G₁ × G₂).1, (AddSubgroup.mem_prod.1 g.2).1⟩)
        (j := ⟨(g' : G₁ × G₂).1, (AddSubgroup.mem_prod.1 g'.2).1⟩) (fun h => e (congrArg Subtype.val h))
      rw [show μ₁ (((g : G₁ × G₂).1 +ᵥ 𝓕₁) ∩ ((g' : G₁ × G₂).1 +ᵥ 𝓕₁)) = 0 from this, zero_mul]

end FD

section Main

theorem avg_prod (G₁ : Type) [AddCommGroup G₁] [TopologicalSpace G₁] [IsTopologicalAddGroup G₁]
    [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁]
    (G₂ : Type) [AddCommGroup G₂] [TopologicalSpace G₂] [IsTopologicalAddGroup G₂]
    [LocallyCompactSpace G₂] [SecondCountableTopology G₂] [T2Space G₂]
    (Γ₁ : AddSubgroup G₁) (Γ₂ : AddSubgroup G₂) (h₁ : IsCoLat Γ₁) (h₂ : IsCoLat Γ₂)
    (Φ : G₁ × G₂ → ℂ) (hΦ : Per (Γ₁.prod Γ₂) Φ) :
    avg (Γ₁.prod Γ₂) Φ = avg Γ₁ (fun x => avg Γ₂ (fun y => Φ (x, y))) := by
  letI m₁ : MeasurableSpace G₁ := borel G₁
  haveI : BorelSpace G₁ := ⟨rfl⟩
  letI m₂ : MeasurableSpace G₂ := borel G₂
  haveI : BorelSpace G₂ := ⟨rfl⟩
  have e₁ : ∃ p : Measure G₁ × Set G₁, p.1.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ₁ p.2 p.1 ∧ p.1 p.2 = 1 := by
    obtain ⟨μ, F, a, b, c⟩ := _root_.GlobalTheory.CuspGeneric.exists_fundamentalDomain_mass_one G₁ Γ₁ h₁
    exact ⟨(μ, F), a, b, c⟩
  have e₂ : ∃ p : Measure G₂ × Set G₂, p.1.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ₂ p.2 p.1 ∧ p.1 p.2 = 1 := by
    obtain ⟨μ, F, a, b, c⟩ := _root_.GlobalTheory.CuspGeneric.exists_fundamentalDomain_mass_one G₂ Γ₂ h₂
    exact ⟨(μ, F), a, b, c⟩
  have A₁ : ∀ Ψ : G₁ → ℂ, avg Γ₁ Ψ = ∫ x in e₁.choose.2, Ψ x ∂e₁.choose.1 := fun Ψ => dif_pos e₁
  have A₂ : ∀ Ψ : G₂ → ℂ, avg Γ₂ Ψ = ∫ y in e₂.choose.2, Ψ y ∂e₂.choose.1 := fun Ψ => dif_pos e₂
  obtain ⟨H₁, F₁, M₁⟩ := e₁.choose_spec
  obtain ⟨H₂, F₂, M₂⟩ := e₂.choose_spec
  set μ₁ := e₁.choose.1
  set 𝓕₁ := e₁.choose.2
  set μ₂ := e₂.choose.1
  set 𝓕₂ := e₂.choose.2
  have hFD : IsAddFundamentalDomain (Γ₁.prod Γ₂) (𝓕₁ ×ˢ 𝓕₂) (μ₁.prod μ₂) := isAddFundamentalDomain_prod F₁ F₂
  have hM : μ₁.prod μ₂ (𝓕₁ ×ˢ 𝓕₂) = 1 := by rw [Measure.prod_prod, M₁, M₂, one_mul]
  obtain ⟨-, -, hI, hE⟩ := _root_.GlobalTheory.CuspGeneric.setIntegral_eq_mass_mul_avg (G₁ × G₂) (Γ₁.prod Γ₂) (isCoLat_prod h₁ h₂) (μ₁.prod μ₂) (𝓕₁ ×ˢ 𝓕₂)
    inferInstance hFD Φ hΦ
  rw [hM, ENNReal.toReal_one, Complex.ofReal_one, one_mul] at hE
  rw [← hE, setIntegral_prod _ hI, A₁]
  simp only [A₂]

end Main

end GlobalTheory.CuspGeneric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageTranslateInvariant
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem avg_add_right (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G) (hΓ : IsCoLat Γ) (Φ : G → ℂ) (hΦ : Per Γ Φ) (y : G) :
    avg Γ (fun x => Φ (x + y)) = avg Γ Φ := by
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := _root_.GlobalTheory.CuspGeneric.exists_fundamentalDomain_mass_one G Γ hΓ
  have hΨ : Per Γ (fun x => Φ (x + y)) :=
    ⟨hΦ.1.comp (continuous_add_const y), fun γ hγ x => by simp only [add_assoc, hΦ.2 γ hγ]⟩

  have hpres : MeasurePreserving (fun x : G => x - y) μ μ := by
    simpa [sub_eq_add_neg] using measurePreserving_add_right μ (-y)
  have h𝓕' : IsAddFundamentalDomain Γ ((fun x : G => x - y) ⁻¹' 𝓕) μ :=
    h𝓕.preimage_of_equiv hpres.quasiMeasurePreserving (e := id) Function.bijective_id (fun γ x => by
      simp only [id, AddSubgroup.vadd_def, vadd_eq_add]; abel)
  have hm' : μ ((fun x : G => x - y) ⁻¹' 𝓕) = 1 := by
    rw [hpres.measure_preimage h𝓕.nullMeasurableSet, h1]
  have hA := (_root_.GlobalTheory.CuspGeneric.setIntegral_eq_mass_mul_avg G Γ hΓ μ 𝓕 hμ h𝓕 _ hΨ).2.2.2
  have hB := (_root_.GlobalTheory.CuspGeneric.setIntegral_eq_mass_mul_avg G Γ hΓ μ _ hμ h𝓕' Φ hΦ).2.2.2
  rw [h1] at hA
  rw [hm'] at hB
  simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul] at hA hB
  rw [← hA, ← hB]
  have hpres2 : MeasurePreserving (fun x : G => x + y) μ μ := measurePreserving_add_right μ y
  have hemb : MeasurableEmbedding (fun x : G => x + y) := (MeasurableEquiv.addRight y).measurableEmbedding
  have := hpres2.setIntegral_preimage_emb hemb Φ ((fun x : G => x - y) ⁻¹' 𝓕)
  rw [← this]
  have hs : (fun x : G => x + y) ⁻¹' ((fun x : G => x - y) ⁻¹' 𝓕) = 𝓕 := by
    ext x; simp
  rw [hs]

end GlobalTheory.CuspGeneric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionAtGoodPoints
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.RestPtAssembly

theorem chiRat_isCrys (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (c : ℕ) (h1 : 1 ≤ c)
    (h2 : c ≤ D.R.t) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c))) := by
  have h0 := ((GlobalTheory.BlockCrys.chiRatioCrysAt D i w hw) c h1 h2).2
  have hM : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (chiRatO D.nd i c))) := by
    refine GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv _ (LinearEquiv.funUnique (Fin 1) _ _).symm
      (fun g x => ?_) h0
    funext a
    rw [Subsingleton.elim a 0]
    have e1 : Br.loc D.nbr i w hw (chiRatO D.nd i c) g 0 0 =
        ((Br.locChi D.nbr i w hw (GlobalTheory.IndefiniteRowSideFullHecke.BlockCharactersCrystallineNonGaloisCusps.chiRatio D i c) g : (Br.LL D.nbr i w hw)ˣ) :
          Br.LL D.nbr i w hw) := by
      change (D.nbr i w hw).toLL (chiRatO D.nd i c (decS D.nd w (Br.iota D.nbr i w hw g)) 0 0) =
        (D.nbr i w hw).toLL ((GlobalTheory.IndefiniteRowSideFullHecke.BlockCharactersCrystallineNonGaloisCusps.chiRatio D i c (decS D.nd w (Br.iota D.nbr i w hw g)) :
          (D.nd.O i)ˣ) : D.nd.O i)
      rw [GlobalTheory.IndefiniteRowSideFullHecke.BlockCharactersCrystallineNonGaloisCusps.chiRatO_apply]
    change _ = (Br.loc D.nbr i w hw (chiRatO D.nd i c) g).mulVec (fun _ => x) 0
    rw [Matrix.mulVec, dotProduct, Fin.sum_univ_one, e1]
    rfl
  exact GlobalTheory.CrysCoef.isCrys_inclusion _ (D.loc (D.nd.l i)) _ _ _ C.le _ _ hM

end GlobalTheory.RestPtAssembly

end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SaturatedAinfLatticeFreeOverBreuilKisin
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000

namespace GlobalTheory.BKLim.SatLat

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (T0 V V' : Matrix (Fin d) (Fin d) (WCb l)) (Y1 : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit T0 → (∀ i j, V i j ∈ bk.OE) → (∀ i j, V' i j ∈ bk.OE) → V * V' = 1 → Y1.map (inclW l) = inclW l τ ^ N • (T0 * V) → ∃ (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Wm Wm' : Matrix (Fin d) (Fin d) (WCb l)), IsUnit (Y.map (inclW l)) ∧ (∀ i j, Wm i j ∈ bk.OE) ∧ (∀ i j, Wm' i j ∈ bk.OE) ∧ Wm * Wm' = 1 ∧ Y.map (inclW l) = inclW l τ ^ N • (T0 * Wm) ∧ ∀ y : Fin d → Ainf l, (∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (fun i => inclW l (y i)) = inclW l τ ^ N • (T0 *ᵥ w)) → ∃ c : Fin d → bk.S, y = Y *ᵥ fun a => bk.ev (c a) := by
  intro l _ K bk τ hτ d N T0 V V' Y1 hT0 hV hV' hVV' hY1
  classical
  obtain ⟨htu, -, -, -⟩ := _root_.GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ
  have hOEcl := _root_.GlobalTheory.OEStable.main l K bk
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin d) (Fin d) (WCb l), M = inclW l τ ^ N • T0 := ⟨_, rfl⟩
  have hMu : IsUnit M.det := by
    rw [hM, Matrix.det_smul]
    exact ((htu.pow N).pow _).mul ((Matrix.isUnit_iff_isUnit_det T0).1 hT0)
  have hMM : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hMu
  have hMM' : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hMu
  have hVu : IsUnit V.det := by
    have h : V.det * V'.det = 1 := by rw [← Matrix.det_mul, hVV', Matrix.det_one]
    exact ⟨⟨V.det, V'.det, h, by rw [mul_comm]; exact h⟩, rfl⟩
  let ι : (Fin d → Ainf l) → (Fin d → WCb l) := fun y a => inclW l (y a)
  have hιmul : ∀ (A : Matrix (Fin d) (Fin d) (Ainf l)) (v : Fin d → Ainf l),
      ι (A *ᵥ v) = A.map (inclW l) *ᵥ ι v := by
    intro A v; funext i; simp [ι, Matrix.mulVec, dotProduct, map_sum]
  have hevW : ∀ s : bk.S, bk.evW s ∈ bk.OE := fun s n => ⟨0, s, 0, by simp⟩
  have hevWι : ∀ c : Fin d → bk.S, ι (fun a => bk.ev (c a)) = fun a => bk.evW (c a) := fun c => rfl
  let mem : (Fin d → Ainf l) → Prop := fun y => ∀ i, (M⁻¹ *ᵥ ι y) i ∈ bk.OE
  have hY1M : Y1.map (inclW l) = M * V := by rw [hY1, hM, Matrix.smul_mul]
  have hmemV : ∀ c : Fin d → bk.S, mem (Y1 *ᵥ fun a => bk.ev (c a)) := by
    intro c i
    show (M⁻¹ *ᵥ ι (Y1 *ᵥ fun a => bk.ev (c a))) i ∈ bk.OE
    rw [hιmul, hevWι, hY1M, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hMM', Matrix.one_mul]
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hV i j) (hevW _)
  obtain ⟨Y, hYu, hYmem⟩ := _root_.GlobalTheory.BSP.saturated_module_free l K bk d mem
    (fun i => by
      show (M⁻¹ *ᵥ ι 0) i ∈ bk.OE
      have : ι 0 = 0 := by funext a; simp [ι]
      rw [this, Matrix.mulVec_zero]; exact Subring.zero_mem _)
    (fun y z hy hz i => by
      show (M⁻¹ *ᵥ ι (y + z)) i ∈ bk.OE
      have : ι (y + z) = ι y + ι z := by funext a; simp [ι]
      rw [this, Matrix.mulVec_add]; exact Subring.add_mem _ (hy i) (hz i))
    (fun c y hy i => by
      show (M⁻¹ *ᵥ ι (fun a => bk.ev c * y a)) i ∈ bk.OE
      have : ι (fun a => bk.ev c * y a) = bk.evW c • ι y := by funext a; simp [ι, BK.evW]
      rw [this, Matrix.mulVec_smul]; exact Subring.mul_mem _ (hevW c) (hy i))
    (fun y hy i => by
      have h : (M⁻¹ *ᵥ ι (fun a => (l : Ainf l) * y a)) i ∈ bk.OE := hy i
      have : ι (fun a => (l : Ainf l) * y a) = ((l : ℕ) : WCb l) • ι y := by funext a; simp [ι]
      rw [this, Matrix.mulVec_smul] at h
      exact hOEcl.1 _ h)
    (fun y hy _ z hz i => by
      refine hOEcl.2.1 _ fun n => ⟨_, hy n i, ?_⟩
      rw [← Pi.sub_apply, ← Matrix.mulVec_sub]
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.dvd_sum fun j _ => Dvd.dvd.mul_left ?_ _
      have := map_dvd (inclW l) (hz n j)
      simpa [ι, map_sub, map_pow, map_natCast] using this)
    Y1 M (by rw [hY1M, Matrix.det_mul]; exact (hMu.mul hVu).ne_zero)
    ((Matrix.isUnit_iff_isUnit_det M).2 hMu) hmemV
    (fun y hy => by
      refine ⟨M⁻¹ *ᵥ ι y, hy, ?_⟩
      show ι y = M *ᵥ (M⁻¹ *ᵥ ι y)
      rw [Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec])
  obtain ⟨Wm, hWm⟩ : ∃ Wm : Matrix (Fin d) (Fin d) (WCb l), Wm = M⁻¹ * Y.map (inclW l) := ⟨_, rfl⟩
  have hYWm : Y.map (inclW l) = M * Wm := by rw [hWm, ← Matrix.mul_assoc, hMM, Matrix.one_mul]
  have hcol : ∀ (A : Matrix (Fin d) (Fin d) (Ainf l)) (j : Fin d),
      (A *ᵥ fun a => bk.ev ((Pi.single j (1 : bk.S) : Fin d → bk.S) a)) = fun i => A i j := by
    intro A j; funext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hWmOE : ∀ i j, Wm i j ∈ bk.OE := by
    intro i j
    have h : (M⁻¹ *ᵥ ι (fun a => Y a j)) i ∈ bk.OE := (hYmem (fun a => Y a j)).2 ⟨Pi.single j (1 : bk.S), (hcol Y j).symm⟩ i
    rw [hWm]
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, ι] using h
  have hC : ∀ j, ∃ c : Fin d → bk.S, (fun i => Y1 i j) = Y *ᵥ fun a => bk.ev (c a) := fun j =>
    (hYmem _).1 (by rw [← hcol Y1 j]; exact hmemV _)
  choose c hc using hC
  obtain ⟨Cw, hCw⟩ : ∃ Cw : Matrix (Fin d) (Fin d) (WCb l), Cw = Matrix.of fun a j => bk.evW (c j a) := ⟨_, rfl⟩
  have hVW : V = Wm * Cw := by
    have h1 : Y1.map (inclW l) = Y.map (inclW l) * Cw := by
      refine Matrix.ext fun i j => ?_
      have := congrArg (fun v => inclW l (v i)) (hc j)
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, hCw, BK.evW, map_sum] using this
    rw [hY1M, hYWm, Matrix.mul_assoc] at h1
    have h2 := congrArg (HMul.hMul M⁻¹) h1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hMM', Matrix.one_mul, Matrix.one_mul] at h2
    exact h2
  refine ⟨Y, Wm, Cw * V', hYu, hWmOE, ?_, ?_, ?_, ?_⟩
  · intro i j
    simp only [Matrix.mul_apply, hCw, Matrix.of_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hevW _) (hV' k j)
  · rw [← Matrix.mul_assoc, ← hVW, hVV']
  · rw [hYWm, hM, Matrix.smul_mul]
  · rintro y ⟨w, hw, hyw⟩
    refine (hYmem y).1 ?_
    intro i
    have : ι y = M *ᵥ w := by
      rw [hM]; refine hyw.trans ?_; funext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    show (M⁻¹ *ᵥ ι y) i ∈ bk.OE
    rw [this, Matrix.mulVec_mulVec, hMM', Matrix.one_mulVec]; exact hw i

end GlobalTheory.BKLim.SatLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableDiscCoefficientRecurrenceStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistable_disc_coefficient_recurrence : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ), ∀ (ι : Type) (TB : TopBasis bk.ev bk.J ι) (j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → ∀ (cD : ι → (bk.DA bk.ρ₀ →+ bk.DS bk.ρ₀)), (∀ i a, cD i (bk.iA a) = toDisc l (X : bk.S) bk.ρ₀ (TB.c i a)) → (∀ i x y, cD i (j x * y) = x * cD i y) → (∀ y, HasSum (fun i => j (cD i y) * bk.iA (TB.b i)) y) → (∀ i y, ‖cD i y‖ ≤ ‖y‖) → ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → ∀ (i₁ : ι) (a b : Fin d), HasSum (fun i => Φ ((s.W * (s.W'.map (cD i)).map j) a b) * bk.iS (TB.c i₁ (WittVector.frobenius (TB.b i)))) (bk.iS bk.E ^ (2 * s.N) * (s.W * (s.W'.map (cD i₁)).map j) a b) := by
  first | exact @GlobalTheory.BSP.wseed_coeff_recurrence | exact GlobalTheory.BSP.wseed_coeff_recurrence | (intros; apply GlobalTheory.BSP.wseed_coeff_recurrence <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodFrameIsDeRhamStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistablePeriodFrame_isDeRham : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ) (N : ℕ) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y.map (inclW l) = inclW l τ ^ s.N • F.T → IsUnit Z → (∀ i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → s.W * Z.map i = Y.map bk.iA) → (∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → G (bk.iS bk.E) ^ s.N • (s.X.map bk.iS * Z.map i * (F.ε g).map bk.iA) = bk.iS bk.E ^ s.N • (s.κ g * (s.X.map bk.iS * Z.map i).map G)) → F.IsDR := by
  first | (exact @GlobalTheory.BKLim.WDR.frame_isDR) | (exact GlobalTheory.BKLim.WDR.frame_isDR) | (intros; apply GlobalTheory.BKLim.WDR.frame_isDR  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodsBreuilKisinGaloisStableStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistablePeriods_breuilKisin_galoisStable : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ) (N : ℕ) (F : Pre bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y.map (inclW l) = inclW l τ ^ s.N • F.T → IsUnit Z → (∀ i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → s.W * Z.map i = Y.map bk.iA) → ∃ F₀ : Frame bk N d ρ, F₀.toPre = F ∧ ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → G (bk.iS bk.E) ^ s.N • (s.X.map bk.iS * Z.map i * (F₀.ε g).map bk.iA) = bk.iS bk.E ^ s.N • (s.κ g * (s.X.map bk.iS * Z.map i).map G) := by
  first | (exact @GlobalTheory.BKLim.GalStab.galois_stable) | (exact GlobalTheory.BKLim.GalStab.galois_stable) | (intros; apply GlobalTheory.BKLim.GalStab.galois_stable  <;> assumption)
end

