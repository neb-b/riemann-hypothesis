module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0321
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0110
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSStageUnconditional
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0330

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoupledTameInertiaGenerator
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting
noncomputable section

open GlobalTheory.TameCoupledEx in
theorem GlobalTheory.TameCoupledEx.exists_coupled_of (hK : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → Nonempty (IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g)) (hL : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ∀ (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (m : ℕ), 0 < m → ¬ g ∣ m → ∀ c : Formalism.CyclotomicNorms.Fbar g, c ^ m = 1 → ∃ μ : Ω, μ ^ m = 1 ∧ redThrough A κ μ = c) (hS : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ((g : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 → ∀ (m : ℕ), 0 < m → ¬ g ∣ m → ∀ Y μ : Ω, Y ^ m = ((g : ℕ) : Ω) → μ ^ m = 1 → ∃ σ ∈ Ine (F := E) A, σ Y = μ * Y) (hW : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ∀ τ ∈ Ine (F := E) A, (∀ d, 0 < d → ∃ y : Ω, y ^ (g ^ d - 1) = ((g : ℕ) : Ω) ∧ A.valuation (τ y / y - 1) < 1) → ∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ((g : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 → ∀ ζ : ℕ → Formalism.CyclotomicNorms.Fbar g, IsGenSys ζ → ∃ κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g, ∃ σ ∈ Ine (F := E) A, TameGenAt A σ ∧ TameCoupled A κ σ ζ := by
  intro E Ω _ _ _ _ _ A v hA g _ hg hg2 ζ hζ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : IsGalois E Ω := {}
  have hgp : g.Prime := Fact.out
  have hgv : A.valuation ((g : ℕ) : Ω) < 1 := val_g_lt A v hA hg
  have hg0 : ((g : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.2 hgp.ne_zero
  obtain ⟨κ⟩ := hK E Ω A v hA g hg
  let D : ℕ → ℕ := fun n => (n + 1).factorial
  have hDpos : ∀ n, 0 < D n := fun n => Nat.factorial_pos _
  have hNpos : ∀ d, 0 < d → 0 < g ^ d - 1 := fun d hd => pow_sub_one_pos hgp hd
  have hgN : ∀ d, 0 < d → ¬ g ∣ g ^ d - 1 := fun d hd => not_dvd_pow_sub_one hgp hd
  have hroot : ∀ n, ∃ r : Ω, r ^ (g ^ D n - 1) = ((g : ℕ) : Ω) := fun n =>
    IsAlgClosed.exists_pow_nat_eq _ (hNpos _ (hDpos n))
  choose r hr using hroot
  have hDdvd : ∀ n, D n ∣ D (n + 1) := fun n => Nat.factorial_dvd_factorial (by omega)
  have hdD : ∀ d, 0 < d → d ∣ D d := fun d hd => Nat.dvd_factorial hd (by omega)
  have hmem : ∀ (σ : G E Ω) {N : ℕ} {y : Ω}, 0 < N → y ^ N = ((g : ℕ) : Ω) → σ y / y ∈ A :=
    fun σ N y hN hy => tameQuot_mem A σ hN hg0 hy
  have hcl : ∀ (x : Ω) (P : Ω → Prop), IsClosed {τ : G E Ω | P (τ x)} := fun x P =>
    ReciprocityTheory.Gal.isClosed_setOf_apply x P
  let T : ℕ → Set (G E Ω) := fun n =>
    (Ine (F := E) A : Set (G E Ω)) ∩ {σ | redThrough A κ (σ (r n) / r n) = ζ (D n)}
  obtain ⟨σ, hσ⟩ : (⋂ n, T n).Nonempty := by
    refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T ?_ ?_ ?_ ?_
    · rintro n σ ⟨hI, hv⟩
      refine ⟨hI, ?_⟩
      show redThrough A κ (σ (r n) / r n) = ζ (D n)
      have hv' : redThrough A κ (σ (r (n + 1)) / r (n + 1)) = ζ (D (n + 1)) := hv
      rw [ratio_descent hgp hgv hI (hDpos n) (hDdvd n) (hr n) (hr (n + 1)),
        redThrough_pow A κ (hmem σ (hNpos _ (hDpos _)) (hr (n + 1))), hv']
      exact (hζ (D n) (hDpos n)).2 (D (n + 1)) (hDdvd n) (hDpos (n + 1))
    · intro n
      have hc : ζ (D n) ^ (g ^ D n - 1) = 1 := by
        rw [← (hζ _ (hDpos n)).1]; exact pow_orderOf_eq_one _
      obtain ⟨μ, hμ, hμc⟩ := hL E Ω A v hA g hg κ _ (hNpos _ (hDpos n)) (hgN _ (hDpos n)) _ hc
      obtain ⟨σ, hσI, hσr⟩ := hS E Ω A v hA g hg hg2 _ (hNpos _ (hDpos n)) (hgN _ (hDpos n)) (r n) μ (hr n) hμ
      refine ⟨σ, hσI, ?_⟩
      show redThrough A κ (σ (r n) / r n) = ζ (D n)
      have hr0 : r n ≠ 0 := ne_zero_of_pow_eq hgp (hNpos _ (hDpos n)) (hr n)
      rw [hσr, mul_div_cancel_right₀ _ hr0, hμc]
    · exact ((ReciprocityTheory.Gal.isClosed_Ine A).inter (hcl (r 0) (fun t => redThrough A κ (t / r 0) = ζ (D 0)))).isCompact
    · intro n
      exact (ReciprocityTheory.Gal.isClosed_Ine A).inter (hcl (r n) (fun t => redThrough A κ (t / r n) = ζ (D n)))
  simp only [Set.mem_iInter] at hσ
  have hσI : σ ∈ Ine (F := E) A := (hσ 0).1
  have hσv : ∀ n, redThrough A κ (σ (r n) / r n) = ζ (D n) := fun n => (hσ n).2
  refine ⟨κ, σ, hσI, ⟨hσI, ?_⟩, ?_⟩
  · intro τ hτ
    have hτI : τ ∈ Ine (F := E) A := hτ
    let Z : Set (G E Ω) := closure (Subgroup.zpowers σ : Set (G E Ω))
    have hZI : Z ⊆ Ine (F := E) A := closure_minimal (fun x hx => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx; exact zpow_mem hσI k) (ReciprocityTheory.Gal.isClosed_Ine A)
    let U : ℕ → Set (G E Ω) := fun n =>
      Z ∩ {h | redThrough A κ (h (r n) / r n) = redThrough A κ (τ (r n) / r n)}
    obtain ⟨h, hh⟩ : (⋂ n, U n).Nonempty := by
      refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed U ?_ ?_ ?_ ?_
      · rintro n x ⟨hxZ, hx⟩
        refine ⟨hxZ, ?_⟩
        show redThrough A κ (x (r n) / r n) = redThrough A κ (τ (r n) / r n)
        have hx' : redThrough A κ (x (r (n + 1)) / r (n + 1)) = redThrough A κ (τ (r (n + 1)) / r (n + 1)) := hx
        rw [ratio_descent hgp hgv (hZI hxZ) (hDpos n) (hDdvd n) (hr n) (hr (n + 1)),
          ratio_descent hgp hgv hτI (hDpos n) (hDdvd n) (hr n) (hr (n + 1)),
          redThrough_pow A κ (hmem x (hNpos _ (hDpos _)) (hr (n + 1))),
          redThrough_pow A κ (hmem τ (hNpos _ (hDpos _)) (hr (n + 1))), hx']
      · intro n
        have hN := hNpos _ (hDpos n)
        haveI : NeZero (g ^ D n - 1) := ⟨hN.ne'⟩
        have hprim : IsPrimitiveRoot (ζ (D n)) (g ^ D n - 1) := (hζ _ (hDpos n)).1 ▸ IsPrimitiveRoot.orderOf _
        have hc : (redThrough A κ (τ (r n) / r n)) ^ (g ^ D n - 1) = 1 := by
          rw [← redThrough_pow A κ (hmem τ hN (hr n)), tameQuot_pow τ hg0 (hr n), redThrough_one]
        obtain ⟨j, -, hj⟩ := hprim.eq_pow_of_pow_eq_one hc
        refine ⟨σ ^ j, subset_closure (Subgroup.mem_zpowers_iff.2 ⟨(j : ℤ), by simp⟩), ?_⟩
        show redThrough A κ ((σ ^ j) (r n) / r n) = _
        rw [ratio_pow hgp hgv hσI hN (hgN _ (hDpos n)) (hr n), redThrough_pow A κ (hmem σ hN (hr n)), hσv n, hj]
      · exact (isClosed_closure.inter (hcl (r 0)
          (fun t => redThrough A κ (t / r 0) = redThrough A κ (τ (r 0) / r 0)))).isCompact
      · intro n
        exact isClosed_closure.inter (hcl (r n)
          (fun t => redThrough A κ (t / r n) = redThrough A κ (τ (r n) / r n)))
    simp only [Set.mem_iInter] at hh
    have hhZ : h ∈ Z := (hh 0).1
    have hhI := hZI hhZ
    have hhv : ∀ n, redThrough A κ (h (r n) / r n) = redThrough A κ (τ (r n) / r n) := fun n => (hh n).2
    have hρI : h⁻¹ * τ ∈ Ine (F := E) A := mul_mem (inv_mem hhI) hτI
    have hρW : ∀ y : Ω, y ≠ 0 → A.valuation ((h⁻¹ * τ) y / y - 1) < 1 := by
      refine hW E Ω A v hA g hg _ hρI ?_
      intro d hd
      have hN := hNpos _ (hDpos d)
      refine ⟨r d ^ ((g ^ D d - 1) / (g ^ d - 1)), root_down (hdD d hd) (hr d), ?_⟩
      apply val_sub_one_lt_of_red κ (hmem _ (hNpos _ hd) (root_down (hdD d hd) (hr d)))
      rw [ratio_descent hgp hgv hρI hd (hdD d hd) (root_down (hdD d hd) (hr d)) (hr d),
        redThrough_pow A κ (hmem _ hN (hr d))]
      have e1 : (h * (h⁻¹ * τ)) (r d) / r d = (h (r d) / r d) * ((h⁻¹ * τ) (r d) / r d) :=
        ratio_mul hgp hgv hhI _ hN (hgN _ (hDpos d)) (hr d)
      rw [mul_inv_cancel_left] at e1
      have e2 := congrArg (redThrough A κ) e1
      rw [redThrough_mul A κ (hmem h hN (hr d)) (hmem _ hN (hr d)), ← hhv d] at e2
      have hne : redThrough A κ (h (r d) / r d) ≠ 0 := by
        intro h0
        have : (redThrough A κ (h (r d) / r d)) ^ (g ^ D d - 1) = 1 := by
          rw [← redThrough_pow A κ (hmem h hN (hr d)), tameQuot_pow h hg0 (hr d), redThrough_one]
        rw [h0, zero_pow hN.ne'] at this
        exact zero_ne_one this
      have e3 : redThrough A κ ((h⁻¹ * τ) (r d) / r d) = 1 :=
        (mul_eq_left₀ hne).1 e2.symm
      rw [e3, one_pow]
    set C : Subgroup (G E Ω) :=
      Subgroup.closure (insert σ {σ' : G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ' y / y - 1) < 1}) with hC
    have h1 : h ∈ C.topologicalClosure := by
      refine closure_mono ?_ hhZ
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact zpow_mem (Subgroup.subset_closure (Set.mem_insert _ _) : σ ∈ C) k
    have h2 : h⁻¹ * τ ∈ C := Subgroup.subset_closure (Set.mem_insert_of_mem _ hρW)
    have h3 := C.topologicalClosure.mul_mem h1 (C.le_topologicalClosure h2)
    rw [mul_inv_cancel_left] at h3
    exact h3
  · intro d hd y hy
    rw [ratio_descent hgp hgv hσI hd (hdD d hd) hy (hr d),
      redThrough_pow A κ (hmem σ (hNpos _ (hDpos d)) (hr d)), hσv d]
    exact (hζ d hd).2 (D d) (hdD d hd) (hDpos d)

theorem GlobalTheory.TameCoupledEx.exists_coupled_tame_generator : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ((g : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 → ∀ ζ : ℕ → Formalism.CyclotomicNorms.Fbar g, IsGenSys ζ → ∃ κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g, ∃ σ ∈ Ine (F := E) A, TameGenAt A σ ∧ TameCoupled A κ σ ζ :=
  GlobalTheory.TameCoupledEx.exists_coupled_of GlobalTheory.T.residue_field_over_place_alg_closure GlobalTheory.T.exists_rootOfUnity_lift_from_residueField GlobalTheory.T.tame_kummer_inertia_surjective GlobalTheory.T.inertia_wild_of_trivial_tame_characters
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisRepOfCuspidal
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting.TwistAny

open Formalism.L2.NR

theorem exists_isRepOf_tw : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE), GalEx D → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (π : D.naut.CG D.R.r), D.naut.csd π → D.naut.ralg π → ∃ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (Qbar l), IsRepOf D l ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2) ρ := by
  intro hGA D cf jE A hGal l _ ι π hc hr
  obtain ⟨ρ₁, c1, ss1, f1⟩ := hGal l ι D.R.r (Formalism.L2.NR.one_le_r D) π hc hr
  obtain ⟨n, hn⟩ := (GlobalTheory.Mem.CharAlg.isAlg_even_odd D.R D.host).2 cf.eta cf.isEta.inf D.R.t D.R.t_odd
  obtain ⟨art, ha⟩ := hGA D.host.E D.nd.Om
  obtain ⟨μ, hμc, hμ⟩ := ha.exists_isLAdicOf ι (GlobalTheory.HeckeGal.isAlgPos_of_isAlg hn)
  refine ⟨Formalism.MainNotions.SumRepresentations.At.twGL ρ₁ μ, ?_, GlobalTheory.TwistLG.isSSRep_twGL _ _ ss1, ?_⟩
  · simp only [GlobalTheory.TwistLG.twGL_val]
    exact (Units.continuous_val.comp hμc).smul c1
  have hfin := placesOver_finite D.host.E l (Fact.out : l.Prime).ne_zero
  filter_upwards [f1, D.naut.locG_unr_ae π, hfin.compl_mem_cofinite] with w hw1 hu hwl
  intro B σ hB hσ
  have hwl' : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := hwl
  have hue : D.naut.unr (D.naut.locG D.naut.etaTinv w) := (D.naut.etaTinv_def w).1
  have hU := (A.chr.unr_iff _ w).1 hue
  have hf := A.chr.frob _ w hU
  rw [A.chr.etaTinv] at hf hU
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow D.host.E (-(D.R.t : ℝ) / 2)
  have hψu : (cf.eta⁻¹ * GlobalTheory.HeckeGal.Model.absPow D.host.E (-(D.R.t : ℝ) / 2)).UnrAt w := by
    intro x hx
    change (cf.eta⁻¹).loc w x * (GlobalTheory.HeckeGal.Model.absPow D.host.E
      (-(D.R.t : ℝ) / 2)).loc w x = 1
    rw [hU x hx, hν.1 w x hx, one_mul]
  have hμv := hμ.frob_unr ha (Or.inl hwl') hψu hB hσ
  set u : ℂ := (((cf.eta⁻¹ * GlobalTheory.HeckeGal.Model.absPow D.host.E (-(D.R.t : ℝ) / 2)).val w : ℂˣ) : ℂ)⁻¹ with hu_def
  have hu1 : D.naut.frobEig (D.naut.lpTw (D.naut.locG D.naut.etaTinv w) (-(D.R.t : ℝ) / 2)) = {u} := by
    rw [D.naut.frobEig_tw _ _ hue, hf, Multiset.map_singleton]
    congr 1
    rw [hu_def, HChar.val_mul, HChar.val_inv, Units.val_mul, hν.2.1 w]
    have hn' : (Ideal.absNorm w.asIdeal : ℕ) = normV w := by
      simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [hn', mul_inv, Units.val_inv_eq_inv_val, Complex.cpow_neg, inv_inv]
  have hχu : ι ((μ σ : (Qbar l)ˣ) : Qbar l) = u := by
    rw [hμv, map_inv₀, ι.apply_symm_apply]
  have h1 := hw1 B σ hB hσ
  rw [GlobalTheory.TwistLG.twGL_val, ← Matrix.charpoly_map, GlobalTheory.ParamRep.map_smul_matrix,
    GlobalTheory.ParamRep.galPol_twist D.nd D.naut π hu u hu1]
  have h2 : ((((ρ₁ σ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).map ι.toRingHom)).charpoly =
      ((D.naut.frobEig (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2))).map fun α => X - C α).prod := by
    rw [Matrix.charpoly_map]; exact h1
  have h3 := GlobalTheory.ParamRep.charpoly_smul_of_prod _ u _ h2
  have hχu' : ι.toRingHom ((μ σ : (Qbar l)ˣ) : Qbar l) = u := hχu
  rw [hχu']
  exact h3

end GlobalTheory.HeightCounting.TwistAny
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSStageLoc
section
noncomputable section

namespace GlobalTheory.Mem.SProv

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.EX GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

theorem delv_pos (s : Scale) (cD : ℝ) : (0 : ℚ) < (Delv s cD : ℚ) := by
  have h : 0 < s.x ^ cD := Real.rpow_pos_of_pos (lt_trans one_pos s.one_lt_alt) _
  exact_mod_cast Nat.ceil_pos.2 h

theorem code_of_over (K : Ctx) (B : Pre) (h : K.Over B) :
    ∃ letter : B.Word → Fin (B.R.k - 2) → Bool, Function.Injective letter ∧
      (∀ (w : B.Word) (τ : Tau B.R) (l : ℕ) (h : l + 1 < B.R.k - 1),
        (B.hcW w τ).v ⟨l, by omega⟩ - (B.hcW w τ).v ⟨l + 1, h⟩ = 4 * (Delv K.s K.cD : ℚ)) ∧
      ∀ (w : B.Word) (τ : Tau B.R) (l : ℕ) (h : l < B.R.k - 2),
        (B.hcW w τ).u ⟨l + 1, by omega⟩ =
          (B.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then (Delv K.s K.cD : ℚ) else 0) := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := h
  refine ⟨K.c, K.ok.inj, fun w τ l h => ?_, K.ok.code⟩
  have h' : l + 1 < K.P.R.k - 1 := h
  have a := (K.ok.hc w).1 τ ⟨l, by omega⟩
  have b := (K.ok.hc w).1 τ ⟨l + 1, h'⟩
  have e : K.P.R.k - 2 - l = K.P.R.k - 2 - (l + 1) + 1 := by omega
  show (K.P.hcW w τ).v ⟨l, _⟩ - (K.P.hcW w τ).v ⟨l + 1, h'⟩ = _
  rw [a, b]
  simp only [e]
  push_cast
  ring

theorem exists_split (B : Pre) (p : HeightOneSpectrum (𝓞 B.host.F)) (L : LocAt B.host.F B.host.E B.conjF p) :
    ∃ s : Option (SplitAt L.Fp L.Ep L.cj (resChar p)),
      (s.isSome ↔ resChar p ∈ ({B.host.g 0, B.host.g 1} : Finset ℕ)) := by
  letI := B.host.cmStar
  by_cases h : resChar p ∈ ({B.host.g 0, B.host.g 1} : Finset ℕ)
  · have hk : ∃ k, resChar p = B.host.g k := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h <;> exact ⟨_, h⟩
    obtain ⟨k, hk⟩ := hk
    obtain ⟨S⟩ := GlobalTheory.LocSplit.nonempty_splitAt B.host.F B.host.E B.conjF B.sp.cm.deg2 (SpectralModel.conjF_ne B) p L
      (by rw [hk, SpectralModel.ncard_primesOver _ _ (B.host.g_prime k), B.g_split])
    exact ⟨some S, by simpa using h⟩
  · exact ⟨none, by simp [h]⟩

theorem exists_sStage_loc (K : Ctx) (B : Base) (C : Cols B) (W : RowsRest B C) (cd : CDHaar) (h : K.Over B.toPre)
    (h2 : SpectralModel.ColsPos C) (h3 : W.Drows ≤ W.Dall)
    (L : ∀ p : HeightOneSpectrum (𝓞 B.host.F), LocAt B.host.F B.host.E B.toPre.conjF p) :
    ∃ S : SStage B C W, S.s.Del = (Delv K.s K.cD : ℚ) ∧ S.s.cdScale = Vol.trueScale cd ∧
      (∀ τ, S.dsig τ = Vol.trueDsig B.R (B.hc τ)) ∧
      ∀ p, ∃ s, S.s.atP p = { L p with split := s } := by
  obtain ⟨letter, hl, hg, hu⟩ := code_of_over K B.toPre h
  obtain ⟨S, hd, -⟩ := SpectralModel.exists_sStage W ⟨_, letter, delv_pos K.s K.cD, hl, hg, hu⟩ h2 h3
    (fun τ => Vol.trueDsig B.R (B.hc τ)) (fun τ => (Vol.lamSH_isHCParam_and_trueDsig_pos B.R (B.hc τ)).2) (fun _ => 0)
  choose sp hsp using fun p => exists_split B.toPre p (L p)
  exact ⟨{ S with
      s := { S.s with
        cdScale := Vol.trueScale cd
        cdScale_pos := Vol.trueScale_pos cd
        Del := (Delv K.s K.cD : ℚ)
        Del_pos := delv_pos K.s K.cD
        cloud_gap := hg
        letter := letter
        letter_inj := hl
        u_letter := hu
        atP := fun p => { L p with split := sp p } }
      s_split := hsp
      s_HH := S.s_HH
      s_Cu := S.s_Cu
      s_PlF := S.s_PlF
      s_Cu_isom := S.s_Cu_isom
      sEE := S.sEE },
    rfl, rfl, fun τ => congrFun hd τ, fun p => ⟨sp p, rfl⟩⟩

end GlobalTheory.Mem.SProv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpecialisationCoefficientSpaceToDualWeyl
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.SpecFactor

open MvPolynomial

variable {K : Type} [Field K] {ι : Type} [DecidableEq ι] {n : ℕ}

noncomputable def specAt (τ₀ : ι) (y : ι × Fin n × Fin n → K) :
    Formalism.L2.DIV.Pol K ι n →ₐ[K] MvPolynomial (Fin n × Fin n) K :=
  MvPolynomial.aeval fun v => if v.1 = τ₀ then MvPolynomial.X v.2 else MvPolynomial.C (y v)

theorem eval_specAt (τ₀ : ι) (y : ι × Fin n × Fin n → K) (z : Fin n × Fin n → K) (w : Formalism.L2.DIV.Pol K ι n) :
    MvPolynomial.eval z (specAt τ₀ y w) =
      MvPolynomial.eval (fun v => if v.1 = τ₀ then z v.2 else y v) w := by
  have h : (MvPolynomial.eval z).comp (specAt τ₀ y).toRingHom =
      MvPolynomial.eval (fun v : ι × Fin n × Fin n => if v.1 = τ₀ then z v.2 else y v) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [specAt]
    · intro v
      by_cases hv : v.1 = τ₀ <;> simp [specAt, hv]
  exact congrArg (fun f : Formalism.L2.DIV.Pol K ι n →+* K => f w) h

theorem exists_specAt_ne [Infinite K] (τ₀ : ι) (w : Formalism.L2.DIV.Pol K ι n) (hw : w ≠ 0) :
    ∃ y, specAt τ₀ y w ≠ 0 := by
  by_contra h
  push_neg at h
  apply hw
  apply MvPolynomial.funext
  intro z
  have := congrArg (MvPolynomial.eval (fun v : Fin n × Fin n => z (τ₀, v))) (h z)
  rw [eval_specAt, map_zero] at this
  rw [map_zero, ← this]
  congr 2
  funext v
  split_ifs with hv
  · obtain ⟨a, b⟩ := v; simp only at hv; subst hv; rfl
  · rfl

theorem specAt_blockEmb (τ₀ : ι) (y : ι × Fin n × Fin n → K) (τ : ι) (F : MvPolynomial (Fin n × Fin n) K) :
    specAt τ₀ y (Formalism.GradedWeylDivisibility.blockEmb K τ F) =
      if τ = τ₀ then F else MvPolynomial.C (MvPolynomial.eval (fun v => y (τ, v)) F) := by
  unfold specAt Formalism.GradedWeylDivisibility.blockEmb
  rw [MvPolynomial.aeval_rename]
  split_ifs with h
  · subst h
    simp only [Function.comp_def, if_true]
    exact MvPolynomial.aeval_X_left_apply F
  · simp only [Function.comp_def, h, if_false]
    have hh : (MvPolynomial.aeval (R := K) fun x : Fin n × Fin n => (MvPolynomial.C (y (τ, x)) : MvPolynomial (Fin n × Fin n) K)).toRingHom =
        MvPolynomial.C.comp (MvPolynomial.eval fun v => y (τ, v)) := by
      apply MvPolynomial.ringHom_ext
      · intro r; simp
      · intro v; simp
    exact congrArg (fun f : MvPolynomial (Fin n × Fin n) K →+* MvPolynomial (Fin n × Fin n) K => f F) hh

end GlobalTheory.SpecFactor

namespace GlobalTheory.SpecFactor

open MvPolynomial

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}

theorem specAt_mem (lam : ι → DomWeight n) (τ₀ : ι) (y : ι × Fin n × Fin n → K) (P : Formalism.L2.DIV.Pol K ι n)
    (hP : P ∈ Formalism.L2.DIV.VV K lam) : specAt τ₀ y P ∈ nablaSq K n (lam τ₀) := by
  unfold Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat at hP
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    rw [map_prod]
    simp only [specAt_blockEmb]
    rw [Fintype.prod_eq_mul_prod_compl τ₀, if_pos rfl, mul_comm]
    have : ∏ i ∈ ({τ₀}ᶜ : Finset ι), (if i = τ₀ then F i else
        MvPolynomial.C (MvPolynomial.eval (fun v => y (i, v)) (F i))) =
        MvPolynomial.C (∏ i ∈ ({τ₀}ᶜ : Finset ι), MvPolynomial.eval (fun v => y (i, v)) (F i)) := by
      rw [map_prod]
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [if_neg (by simpa using hi)]
    rw [this, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (hF τ₀)
  | zero => simp
  | add x z _ _ hx hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hz
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem specAt_blockAct (τ₀ : ι) (y : ι × Fin n × Fin n → K) (M : Matrix (Fin n) (Fin n) K)
    (P : Formalism.L2.DIV.Pol K ι n) :
    specAt τ₀ y (Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then M else 1) P) =
      Formalism.GradedWeylDivisibility.rowAct K M (specAt τ₀ y P) := by
  have h : (specAt τ₀ y).comp (Formalism.GradedWeylDivisibility.blockAct K (n := n) (fun τ => if τ = τ₀ then M else 1)) =
      (Formalism.GradedWeylDivisibility.rowAct K M).comp (specAt τ₀ y) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨τ, a, b⟩
    by_cases hτ : τ = τ₀
    · subst hτ
      simp [specAt, Formalism.GradedWeylDivisibility.blockAct, Formalism.GradedWeylDivisibility.rowAct]
    · set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, Formalism.GradedWeylDivisibility.blockAct, specAt, MvPolynomial.aeval_X, hτ, if_false, map_sum, map_mul,
        MvPolynomial.aeval_C, Matrix.one_apply]
      rw [Finset.sum_eq_single a]
      · simp [hτ]
      · intro c _ hc; simp [Ne.symm hc]
      · simp
  exact congrArg (fun f : Formalism.L2.DIV.Pol K ι n →ₐ[K] MvPolynomial (Fin n × Fin n) K => f P) h

end GlobalTheory.SpecFactor

theorem GlobalTheory.specialise_factor : ∀ (K : Type) [Field K] [Infinite K] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (lam : ι → DomWeight n) (τ₀ : ι) (w : Formalism.L2.DIV.Pol K ι n), w ∈ Formalism.L2.DIV.VV K lam → w ≠ 0 →
    ∃ φ : Formalism.L2.DIV.Pol K ι n →ₗ[K] MvPolynomial (Fin n × Fin n) K, φ w ≠ 0 ∧
      (∀ P ∈ Formalism.L2.DIV.VV K lam, φ P ∈ nablaSq K n (lam τ₀)) ∧
      ∀ (M : Matrix (Fin n) (Fin n) K) (P : Formalism.L2.DIV.Pol K ι n),
        φ (Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then M else 1) P) = Formalism.GradedWeylDivisibility.rowAct K M (φ P) := by
  intro K _ _ n ι _ _ lam τ₀ w _ hw
  obtain ⟨y, hy⟩ := GlobalTheory.SpecFactor.exists_specAt_ne τ₀ w hw
  exact ⟨(GlobalTheory.SpecFactor.specAt τ₀ y).toLinearMap, hy,
    fun P hP => GlobalTheory.SpecFactor.specAt_mem lam τ₀ y P hP,
    fun M P => GlobalTheory.SpecFactor.specAt_blockAct τ₀ y M P⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSphericalEigensystemFirstLiftBaseLevelStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sphericalEigensystem_firstLift_baseLevel : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ π : D.what₂.FT, ∃ c, HasEig R F Y π c := by
  first | exact @GlobalTheory.Mem.R3.EigEx.exists_hasEig | exact GlobalTheory.Mem.R3.EigEx.exists_hasEig | (intros; apply GlobalTheory.Mem.R3.EigEx.exists_hasEig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FcLargeOfSup
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top

theorem fc_large_of_sup {C : FC} {K K' : TransportedAlt} {CH : ℝ} (h : C.Large (K.sup K') CH) : C.Large K CH ∧ C.Large K' CH :=
  ⟨⟨fun c hc => (le_max_left _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_left _ _).trans (h.2.2.1 c hc),
      fun c hc => (le_max_left _ _).trans (h.2.2.2 c hc)⟩,
    ⟨fun c hc => (le_max_right _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_right _ _).trans (h.2.2.1 c hc),
      fun c hc => (le_max_right _ _).trans (h.2.2.2 c hc)⟩⟩

theorem Ev.mono {p q : Ctx → Prop} (h : ∀ K, p K → q K) (hp : Ev p) : Ev q := by
  obtain ⟨a, ha, hp⟩ := hp
  refine ⟨a, ha, fun e C8 he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 he hle h52 h8
  refine ⟨K, fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 hL
  refine ⟨a1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD hcD
  refine ⟨a2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch hch
  exact ⟨a3, fun X h1 h2 h3 h4 hx => h X (ha3 X h1 h2 h3 h4 hx)⟩

theorem large₂.and {K : Ctx} {p q : ∀ B : Base, Fr B.toPre → TwDat B → Prop} (hp : large₂ K p) (hq : large₂ K q) :
    large₂ K fun B f T => p B f T ∧ q B f T :=
  large₂.inter hp hq

theorem large₂.mono {K : Ctx} {p q : ∀ B : Base, Fr B.toPre → TwDat B → Prop}
    (h : ∀ B f T, K.Over B.toPre → p B f T → q B f T) (hp : large₂ K p) : large₂ K q :=
  large₂.imp hp h

end GlobalTheory.Mem.Top
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeComparisonUnitAtFrobeniusEqDeltaStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeComparisonUnitAtFrobenius_eq_delta : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (b : Bool) (P : PlE D.host), P ∉ T.S0 i →
    ∀ σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ →
    cHkT D T i b P = Units.map (algebraMap (T.O0 i) (T.O i)).toMonoidHom
      (if b then T.delta i σ else (T.delta i σ)⁻¹) := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.cHkT_eq_of_isFrob | exact GlobalTheory.HeightCounting.FormsStep.cHkT_eq_of_isFrob | (intros; apply GlobalTheory.HeightCounting.FormsStep.cHkT_eq_of_isFrob <;> assumption)
end

