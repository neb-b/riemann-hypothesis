module

public import Mathlib
public import GroundTheory.GlobalFields.SplittingFromInequality.Decomposition
public import GroundTheory.GlobalFields.TateThesis.TateMain

@[expose] public section

-- bundled from GroundTheory.GlobalFields.TateThesis.ChebotarevFrobenius
section
namespace GroundTheory.Global

open NumberField IsDedekindDomain IntermediateField
open scoped Pointwise

noncomputable section

section Unique

variable {F L : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
  [IsGalois F L]

theorem arithFrobAt_eq_of_isArithFrobAt (w : HeightOneSpectrum (𝓞 L))
    (he : w.asIdeal.ramificationIdx (𝓞 F) = 1) {τ : Gal(L/F)}
    (hτ : IsArithFrobAt (𝓞 F) τ w.asIdeal) : arithFrobAt (𝓞 F) Gal(L/F) w.asIdeal = τ := by
  have : IsGaloisGroup Gal(L/F) (𝓞 F) (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ F L
  have hmem := (IsArithFrobAt.arithFrobAt (𝓞 F) Gal(L/F) w.asIdeal).mul_inv_mem_inertia hτ
  have hcard : Nat.card (w.asIdeal.inertia Gal(L/F)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (w.asIdeal.under (𝓞 F)) w.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx _ w.asIdeal Gal(L/F)]
    exact he
  rw [Subgroup.card_eq_one.mp hcard, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  exact hmem

theorem ramificationIdx_smul (τ : Gal(L/F)) (w : HeightOneSpectrum (𝓞 L)) :
    (τ • w).asIdeal.ramificationIdx (𝓞 F) = w.asIdeal.ramificationIdx (𝓞 F) := by
  have : IsGaloisGroup Gal(L/F) (𝓞 F) (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ F L
  have : (τ • w).asIdeal.LiesOver (AdeleBaseChange.below (K := F) w).asIdeal :=
    (AdeleBaseChange.below_eq_iff _ _).1 (below_smul τ w)
  exact Ideal.ramificationIdx_eq_of_isGaloisGroup (AdeleBaseChange.below (K := F) w).asIdeal
    (τ • w).asIdeal w.asIdeal Gal(L/F)

theorem arithFrobAt_smul (τ : Gal(L/F)) (w : HeightOneSpectrum (𝓞 L))
    (he : w.asIdeal.ramificationIdx (𝓞 F) = 1) :
    arithFrobAt (𝓞 F) Gal(L/F) (τ • w).asIdeal =
      τ * arithFrobAt (𝓞 F) Gal(L/F) w.asIdeal * τ⁻¹ :=
  arithFrobAt_eq_of_isArithFrobAt (τ • w) (by rw [ramificationIdx_smul, he])
    ((IsArithFrobAt.arithFrobAt (𝓞 F) Gal(L/F) w.asIdeal).conj τ)

end Unique

section Tower

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem isArithFrobAt_restrictScalars_iff (E : IntermediateField K L) (w : HeightOneSpectrum (𝓞 L))
    (hf : (w.asIdeal.under (𝓞 E)).inertiaDeg (𝓞 K) = 1) (τ : Gal(L/E)) :
    IsArithFrobAt (𝓞 K) (τ.restrictScalars K) w.asIdeal ↔ IsArithFrobAt (𝓞 E) τ w.asIdeal := by
  have hcard : Nat.card (𝓞 K ⧸ w.asIdeal.under (𝓞 K)) =
      Nat.card (𝓞 E ⧸ w.asIdeal.under (𝓞 E)) := by
    have h := Ideal.absNorm_pow_inertiaDeg ((w.asIdeal.under (𝓞 E)).under (𝓞 K))
      (w.asIdeal.under (𝓞 E))
    rw [hf, pow_one, Ideal.under_under] at h
    rw [← Submodule.cardQuot_apply, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
      ← Ideal.absNorm_apply, h]
  change (∀ x, _ - x ^ Nat.card (𝓞 K ⧸ w.asIdeal.under (𝓞 K)) ∈ w.asIdeal) ↔
    (∀ x, _ - x ^ Nat.card (𝓞 E ⧸ w.asIdeal.under (𝓞 E)) ∈ w.asIdeal)
  rw [hcard]
  rfl

variable [IsGalois K L]

theorem eq_of_under_eq_of_le_stabilizer (H : Subgroup Gal(L/K)) (w w' : HeightOneSpectrum (𝓞 L))
    (hH : H ≤ MulAction.stabilizer Gal(L/K) w.asIdeal)
    (h : w'.asIdeal.under (𝓞 (fixedField H)) = w.asIdeal.under (𝓞 (fixedField H))) : w' = w := by
  have : IsGaloisGroup Gal(L/fixedField H) (𝓞 (fixedField H)) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing _ _ _ (fixedField H) L
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 (fixedField H)) (𝓞 L)
    Gal(L/fixedField H) w.asIdeal w'.asIdeal h.symm
  have hgH : g.restrictScalars K ∈ H := by
    have h1 : g.restrictScalars K ∈ fixingSubgroup (fixedField H) :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx ↦ g.commutes ⟨x, hx⟩
    rwa [fixingSubgroup_fixedField] at h1
  have hs := hH hgH
  rw [MulAction.mem_stabilizer_iff] at hs
  refine HeightOneSpectrum.ext ?_
  rw [hg]
  exact hs

end Tower

end

end GroundTheory.Global
end

-- bundled from GroundTheory.GlobalFields.TateThesis.TateMainUnique
section
open NumberField Topology Filter Complex Set
open scoped NumberField.AdeleRing

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

theorem eqOn_of_differentiableOn_of_eq_globalZeta {F : 𝔸[K] → ℂ} {χ : HeckeCharacter K}
    {S : Set ℂ} (hS : S.Finite) (hSre : ∀ z ∈ S, z.re ≤ 1) {G H : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G Sᶜ) (hH : DifferentiableOn ℂ H Sᶜ)
    (hGZ : ∀ s : ℂ, 1 < s.re → G s = globalZeta F χ s)
    (hHZ : ∀ s : ℂ, 1 < s.re → H s = globalZeta F χ s) : EqOn G H Sᶜ := by
  have hopen : IsOpen Sᶜ := hS.isClosed.isOpen_compl
  have hU : IsPreconnected Sᶜ :=
    (hS.countable.isConnected_compl_of_one_lt_rank (by simp)).isPreconnected
  have h2 : (2 : ℂ) ∈ Sᶜ := fun h ↦ by
    have := hSre 2 h
    norm_num at this
  have heq : G =ᶠ[𝓝 (2 : ℂ)] H :=
    Filter.eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)) fun s hs ↦ (hGZ s hs).trans (hHZ s hs).symm
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (hG.analyticOnNhd hopen)
    (hH.analyticOnNhd hopen) hU h2 heq

theorem eq_tateZeta_of_differentiable {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K)
    {χ : HeckeCharacter K} (hχ : ∃ v : normOneSubgroup K, χ.toIdele (v : IdeleGroup K) ≠ 1)
    {G : ℂ → ℂ} (hG : Differentiable ℂ G) (hGZ : ∀ s : ℂ, 1 < s.re → G s = globalZeta F χ s) :
    G = tateZeta F χ := by
  have h := eqOn_of_differentiableOn_of_eq_globalZeta (S := ∅) finite_empty (by simp)
    hG.differentiableOn (differentiable_tateZeta hF hχ).differentiableOn hGZ
    fun s hs ↦ tateZeta_eq_globalZeta hF χ hs
  funext s
  exact h (by simp)

theorem eqOn_tateZeta_of_differentiableOn {χ : HeckeCharacter K} {τ : ℝ}
    (hτ : ∀ x : IdeleGroup K, (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I))
    {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K) {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G {-((τ : ℂ) * I), 1 - (τ : ℂ) * I}ᶜ)
    (hGZ : ∀ s : ℂ, 1 < s.re → G s = globalZeta F χ s) :
    EqOn G (tateZeta F χ) {-((τ : ℂ) * I), 1 - (τ : ℂ) * I}ᶜ := by
  refine eqOn_of_differentiableOn_of_eq_globalZeta (toFinite _) ?_ hG ?_ hGZ
    fun s hs ↦ tateZeta_eq_globalZeta hF χ hs
  · intro z hz
    rcases hz with rfl | rfl <;> simp
  · intro s hs
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hs
    exact (differentiableAt_tateZeta hτ hF hs.1 hs.2).differentiableWithinAt

end

end GroundTheory.Global
end

