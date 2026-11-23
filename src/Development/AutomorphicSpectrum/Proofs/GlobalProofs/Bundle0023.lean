module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0022
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0021
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Formalism.RealPlaceAnalysis.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsShintaniConeDomain
section
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

theorem exists_coneDomain : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    ∃ (ι : Type) (_ : Fintype ι) (r : ι → ℕ) (v : ∀ c, Fin (r c) → F), IsConeDomain 𝔣 r v := by
  intro F _ _ _ 𝔣 h𝔣
  classical
  obtain ⟨M, hM⟩ := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Balance.balance F 𝔣 h𝔣
  obtain ⟨κ, _, b, hbpos, hbcov⟩ := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Gens.exists_totPos_basis F M
  obtain ⟨R, hR0, hR⟩ := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.bounded_ratio_on_basis_cone F b hbpos

  obtain ⟨σ₁⟩ : Nonempty (F →+* ℝ) := by
    have w : InfinitePlace F := Classical.choice inferInstance
    exact ⟨w.embedding_of_isReal (IsTotallyReal.isReal w)⟩

  let G := ↥(congSubgroup 𝔣)
  let φ : G →* F := ((algebraMap (𝓞 F) F : 𝓞 F →+* F) : 𝓞 F →* F).comp ((Units.coeHom (𝓞 F)).comp (congSubgroup 𝔣).subtype)
  have hφ : ∀ g : G, φ g = (((g : (𝓞 F)ˣ) : 𝓞 F) : F) := fun g => rfl
  have hgpos : ∀ g : G, TotPos F (φ g) := fun g => g.2.2
  let f : G →* ℝ := (σ₁ : F →* ℝ).comp φ
  have hf : ∀ g : G, f g = σ₁ (φ g) := fun g => rfl
  have hfpos : ∀ g, 0 < f g := fun g => hgpos g σ₁
  have hφinj : Function.Injective φ := by
    intro g g' h
    apply Subtype.ext
    apply Units.ext
    exact RingOfIntegers.coe_injective h
  have hfinj : Function.Injective f := fun g g' h => hφinj (σ₁.injective h)
  let D : Set F := {x | ∀ i, 0 < b.repr x i}

  have hDpos : ∀ x ∈ D, TotPos F x := by
    intro x hx σ
    have hk : Nonempty κ := b.index_nonempty
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr x, map_sum]
    refine Finset.sum_pos (fun i _ => ?_) Finset.univ_nonempty
    rw [Rat.smul_def, map_mul, map_ratCast]
    exact mul_pos (by exact_mod_cast hx i) (hbpos i σ)
  have hfin : {g : G | ∃ x ∈ D, φ g * x ∈ D}.Finite := by
    have hfin0 := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.finite_totPos_units_bounded_ratio F (R * R)
    refine Set.Finite.of_finite_image (f := fun g : G => (g : (𝓞 F)ˣ)) (hfin0.subset ?_) (Subtype.val_injective.injOn)
    rintro _ ⟨g, ⟨x, hx, hgx⟩, rfl⟩
    refine ⟨hgpos g, fun σ τ => ?_⟩
    have h1 := hR _ hgx σ τ
    have h2 := hR x hx τ σ
    have hxσ := hDpos x hx σ
    have hgτ := hgpos g τ
    rw [map_mul, map_mul] at h1
    have h3 : σ (φ g) * σ x ≤ (R * R * τ (φ g)) * σ x := by
      calc σ (φ g) * σ x ≤ R * (τ (φ g) * τ x) := h1
        _ ≤ R * (τ (φ g) * (R * σ x)) := by gcongr
        _ = _ := by ring
    exact le_of_mul_le_mul_right h3 hxσ
  let E : Set F := {y ∈ D | ∀ g' : G, f g' < 1 → φ g' * y ∉ D}
  let T := {g : G | ∃ x ∈ D, φ g * x ∈ D}
  let Λ : Set (F →ₗ[ℚ] ℚ) := (fun p : G × κ => (b.coord p.2).comp (LinearMap.mulLeft ℚ (φ p.1))) '' (T ×ˢ Set.univ)
  have hΛ : Λ.Finite := (hfin.prod Set.finite_univ).image _
  have hsign : ∀ (p q : ℚ), SignType.sign p = SignType.sign q → 0 < p → 0 < q := by
    intro p q h hp
    rw [sign_pos hp] at h
    exact sign_eq_one_iff.mp h.symm
  have htile : Tile ((posCone F : ConvexCone ℚ F) : Set F) (fun _ => True) E := by
    refine _root_.GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.SignTiles.tile_of_signs (posCone F) b hbpos Λ hΛ E (fun x hx => hx.1) ?_
    intro x y hx hy hs hxE
    refine ⟨hy, fun g' hg' hyD => ?_⟩
    refine hxE.2 g' hg' ?_
    have hgT : g' ∈ T := ⟨y, hy, hyD⟩
    intro i
    have := hs _ ⟨(g', i), ⟨hgT, trivial⟩, rfl⟩
    simp only [LinearMap.comp_apply, Module.Basis.coord_apply, LinearMap.mulLeft_apply] at this
    exact hsign _ _ this.symm (hyD i)
  have h0 : (0 : F) ∉ E := by
    intro h
    have := hDpos 0 h.1 σ₁
    simp at this
  obtain ⟨ι, hι, r, v, hr, hli, hvP, hsub, hun⟩ := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.tile_family_closed _ _ E htile h0
  refine ⟨ι, hι, r, v, hr, hli, hvP, ?_⟩
  intro x hx

  obtain ⟨u, hu, hub⟩ := hM x hx
  have hxD : ∃ g : G, φ g * x ∈ D := by
    refine ⟨⟨u, hu⟩, hbcov _ ?_ hub⟩
    intro σ
    rw [map_mul]
    exact mul_pos (hu.2 σ) (hx σ)
  obtain ⟨g, hg, hguniq⟩ := _root_.GlobalTheory.CompanionTheory.SiegelKlingen.exists_unique_minimal_translate φ f hfpos hfinj D hfin x hxD
  obtain ⟨c, hc, hcuniq⟩ := hun _ hg
  refine ⟨(⟨g.1, g.2⟩, c), hc, ?_⟩
  rintro ⟨⟨u', hu'⟩, c'⟩ hp
  have hp' : φ ⟨u', hu'⟩ * x ∈ openCone (v c') := hp
  have hg' : (⟨u', hu'⟩ : G) = g := hguniq _ (hsub c' hp')
  have hc' : c' = c := by
    apply hcuniq
    rw [← hg']
    exact hp'
  subst hc'
  have := congrArg Subtype.val hg'
  simp only at this
  simp [this]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ShintaniValuesNegativeIntegersRationalStatement
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_difference_cone_bound : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ), (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ (B R : ℕ) (cs : List (Fin r)) (β : ι → ℕ),
  ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, ‖s‖ ≤ R → -(B : ℝ) ≤ s.re → ∀ x : Fin r → ℝ, (∀ i, 0 ≤ x i) →
    ‖DLR cs (Fr a b s β) x‖ ≤ C * sizeE x ^ ((Fintype.card ι : ℤ) * (B : ℤ) - ∑ j, (β j : ℤ) - (cs.length : ℤ)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DiffDecay.diff_bound | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DiffDecay.diff_bound | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DiffDecay.diff_bound <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SkewOfCommute
section
open Matrix Formalism.REAL
open GlobalTheory.SmoothGlob (lieSet)

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.KStable

variable {n : ℕ} {ε : Fin n → Bool}

theorem skew_of_commute {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieSet ε) (hc : X * Jm ε = Jm ε * X) :
    Xᴴ = -X := by
  have h : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  have h1 : Xᴴ * Jm ε = -(X * Jm ε) := by
    rw [hc]; exact eq_neg_of_add_eq_zero_left h
  calc Xᴴ = Xᴴ * (Jm ε * Jm ε) := by rw [Formalism.REAL.Jm_mul_self, Matrix.mul_one]
    _ = (Xᴴ * Jm ε) * Jm ε := by rw [Matrix.mul_assoc]
    _ = -(X * (Jm ε * Jm ε)) := by rw [h1, Matrix.neg_mul, Matrix.mul_assoc]
    _ = -X := by rw [Formalism.REAL.Jm_mul_self, Matrix.mul_one]

theorem exp_mem_Kset {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieSet ε) (hc : X * Jm ε = Jm ε * X) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Kset ε := by
  have hs := skew_of_commute hX hc
  constructor
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose,
      Matrix.conjTranspose_smul, hs]
    have hneg : star t • -X = -(t • X) := by simp
    have hcm : Commute (t • X) (-(t • X)) := (Commute.refl _).neg_right
    rw [hneg, ← Matrix.exp_add_of_commute _ _ hcm]
    simp
  · exact ((show Commute X (Jm ε) from hc).smul_left t).exp_left

end GlobalTheory.CompanionTheory.Hypotheses₂.KStable

end
end

