module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0080
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionRegularLocalRing
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0092
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0007
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterAlgRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RationalRelationInChartIdeal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.ChartDehom

theorem den_mul_algebraMap {F : Type} [Field F] [CharZero F] (q : ℚ) :
    (q.den : F) * algebraMap ℚ F q = (q.num : F) := by
  have hd : (q.den : F) ≠ 0 := by exact_mod_cast q.den_nz
  rw [eq_ratCast, Rat.cast_def]
  field_simp

theorem exists_homog {K : Type} [Fintype K] {J : K → Type} {Ω : Type} [Field Ω] [CharZero Ω]
    (y : (Σ k, J k) → Ω) (c : (k : K) → J k) (hy : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {Q : Type} [CommRing Q] (ρ : MvPolynomial (Σ k, J k) ℤ →+* Q)
    (τ : MvPolynomial (Σ k, J k) ℚ →+* Q)
    (hρ : ∀ k, ρ (X ⟨k, c k⟩) = 1) (hX : ∀ p, ρ (X p) = τ (X p))
    (hQ : ∀ q : ℚ, (q.den : Q) * τ (MvPolynomial.C q) = (q.num : Q))
    (G : MvPolynomial (Σ k, J k) ℚ) :
    ∃ (N : ℤ) (D : K → ℕ) (H : MvPolynomial (Σ k, J k) ℤ), N ≠ 0 ∧
      mConeMap y H = MvPolynomial.C (N : Ω) *
        (∏ k, (MvPolynomial.C (y ⟨k, c k⟩) * X k : MvPolynomial K Ω) ^ D k) *
        MvPolynomial.C (aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) G) ∧
      ρ H = (N : Q) * τ G := by
  classical
  set u : (Σ k, J k) → Ω := fun p => y p / y ⟨p.1, c p.1⟩ with hu
  set w : K → MvPolynomial K Ω := fun k => MvPolynomial.C (y ⟨k, c k⟩) * X k with hw
  let M : (K → ℕ) → MvPolynomial (Σ k, J k) ℤ := fun D => ∏ k, X ⟨k, c k⟩ ^ D k
  have hXc : ∀ p, mConeMap y (X p) = MvPolynomial.C (y p) * X p.1 := by
    intro p; simp [mConeMap]
  have hMc : ∀ D, mConeMap y (M D) = ∏ k, w k ^ D k := by
    intro D
    simp only [M, map_prod, map_pow, hXc, hw]
  have hMρ : ∀ D, ρ (M D) = 1 := by
    intro D
    simp only [M, map_prod, map_pow, hρ, one_pow, Finset.prod_const_one]
  have hW : ∀ D E : K → ℕ, (∏ k, w k ^ D k) * ∏ k, w k ^ E k = ∏ k, w k ^ (D + E) k := by
    intro D E
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  have hS : ∀ a, ∏ k, w k ^ (Pi.single a 1 : K → ℕ) k = w a := by
    intro a
    rw [Finset.prod_eq_single a (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
    simp
  have hCc : ∀ n : ℤ, mConeMap y (MvPolynomial.C n) = MvPolynomial.C (n : Ω) := by
    intro n
    have h := (mConeMap y).commutes n
    simpa [MvPolynomial.algebraMap_eq] using h
  have hCρ : ∀ n : ℤ, ρ (MvPolynomial.C n) = (n : Q) := fun n =>
    eq_intCast (ρ.comp MvPolynomial.C) n
  induction G using MvPolynomial.induction_on with
  | C q =>
    refine ⟨q.den, 0, MvPolynomial.C q.num, by exact_mod_cast q.den_nz, ?_, ?_⟩
    · rw [hCc, aeval_C]
      simp only [Pi.zero_apply, pow_zero, Finset.prod_const_one]
      rw [_root_.mul_one, ← map_mul]
      congr 1
      have := den_mul_algebraMap (F := Ω) q
      push_cast
      exact this.symm
    · rw [hCρ]
      have := hQ q
      push_cast
      exact this.symm
  | add f g hf hg =>
    obtain ⟨N₁, D₁, H₁, h₁, c₁, r₁⟩ := hf
    obtain ⟨N₂, D₂, H₂, h₂, c₂, r₂⟩ := hg
    refine ⟨N₁ * N₂, D₁ + D₂,
      MvPolynomial.C N₂ * H₁ * M D₂ + MvPolynomial.C N₁ * H₂ * M D₁, mul_ne_zero h₁ h₂, ?_, ?_⟩
    · rw [map_add (f := _), map_mul, map_mul, map_mul, map_mul, c₁, c₂, hMc, hMc, hCc, hCc, ← hW, map_add (f := _),
        map_add]
      push_cast
      rw [MvPolynomial.C_mul]
      ring
    · rw [map_add (f := _), map_mul, map_mul, map_mul, map_mul, r₁, r₂, hMρ, hMρ, hCρ, hCρ, map_add (f := _)]
      push_cast
      ring
  | mul_X f p hf =>
    obtain ⟨N, D, H, h, c₁, r₁⟩ := hf
    refine ⟨N, D + Pi.single p.1 1, H * X p, h, ?_, ?_⟩
    · have hp : MvPolynomial.C (y p) * X p.1 = MvPolynomial.C (u p) * w p.1 := by
        rw [hw]
        simp only
        rw [← _root_.mul_assoc, ← MvPolynomial.C_mul, hu]
        simp only
        rw [div_mul_cancel₀ _ (hy p.1)]
      rw [map_mul, c₁, hXc, hp, ← hW, hS, map_mul, aeval_X, MvPolynomial.C_mul]
      ring
    · rw [map_mul, map_mul, r₁, hX]
      ring

theorem map_mem_chartIdeal : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, J k) → Ω) (c : (k : K) → J k), (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ G : MvPolynomial (Σ k, J k) ℚ,
    aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) G = (0 : Ω) →
    map (algebraMap ℚ ℂ) G ∈ ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c := by
  intro K _ J _ Ω _ _ y c hy G hG
  classical
  set A : Ideal (MvPolynomial (Σ k, J k) ℂ) :=
    Ideal.span (Set.range fun k => (X ⟨k, c k⟩ - 1 : MvPolynomial (Σ k, J k) ℂ)) with hA
  let π := Ideal.Quotient.mk A
  let ρ : MvPolynomial (Σ k, J k) ℤ →+* (MvPolynomial (Σ k, J k) ℂ ⧸ A) :=
    π.comp (MvPolynomial.map (Int.castRingHom ℂ))
  let τ : MvPolynomial (Σ k, J k) ℚ →+* (MvPolynomial (Σ k, J k) ℂ ⧸ A) :=
    π.comp (MvPolynomial.map (algebraMap ℚ ℂ))
  have hρ : ∀ k, ρ (X ⟨k, c k⟩) = 1 := by
    intro k
    have h : π (X ⟨k, c k⟩) = π 1 :=
      Ideal.Quotient.eq.mpr (Ideal.subset_span ⟨k, rfl⟩)
    simpa [ρ] using h
  have hX : ∀ p, ρ (X p) = τ (X p) := by
    intro p
    simp [ρ, τ]
  have hQ : ∀ q : ℚ, (q.den : MvPolynomial (Σ k, J k) ℂ ⧸ A) * τ (MvPolynomial.C q) =
      (q.num : MvPolynomial (Σ k, J k) ℂ ⧸ A) := by
    intro q
    have h := congrArg (fun a : ℂ => π (MvPolynomial.C a)) (den_mul_algebraMap (F := ℂ) q)
    simpa [τ] using h
  obtain ⟨N, D, H, hN, hc, hr⟩ := exists_homog y c hy ρ τ hρ hX hQ G
  have hHP : H ∈ mCoordIdeal y := by
    rw [mCoordIdeal, RingHom.mem_ker, hc, hG]
    simp
  have h1 : MvPolynomial.map (Int.castRingHom ℂ) H ∈ pC (mCoordIdeal y) :=
    Ideal.subset_span ⟨H, hHP, rfl⟩
  have h2 : MvPolynomial.map (Int.castRingHom ℂ) H -
      MvPolynomial.C (N : ℂ) * MvPolynomial.map (algebraMap ℚ ℂ) G ∈ A := by
    refine Ideal.Quotient.eq.mp ?_
    have : π (MvPolynomial.C (N : ℂ)) = (N : MvPolynomial (Σ k, J k) ℂ ⧸ A) := by simp
    rw [map_mul, this]
    exact hr
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have h3 : MvPolynomial.C (N : ℂ) * MvPolynomial.map (algebraMap ℚ ℂ) G ∈
      ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c := by
    have ha : MvPolynomial.map (Int.castRingHom ℂ) H ∈
        ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c := Ideal.mem_sup_left h1
    have hb : MvPolynomial.map (Int.castRingHom ℂ) H -
        MvPolynomial.C (N : ℂ) * MvPolynomial.map (algebraMap ℚ ℂ) G ∈
        ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c := Ideal.mem_sup_right h2
    simpa using Ideal.sub_mem _ ha hb
  have h4 := Ideal.mul_mem_left _ (MvPolynomial.C (N : ℂ)⁻¹) h3
  rwa [← _root_.mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ hN', MvPolynomial.C_1, _root_.one_mul] at h4

end GlobalTheory.CompanionTheory.Ar.ChartDehom
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularLocalChartCoords
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.ChartParams

theorem eval_unren_eq_zero {σ : Type} [Fintype σ] (Q : Ideal (MvPolynomial σ ℂ))
    (v : Fin (Fintype.card σ) → ℂ)
    (hv : v ∈ ReciprocityTheory.AnForm.R.zeroSet (Q.map (ReciprocityTheory.AnForm.R.renR σ : MvPolynomial σ ℂ →+* _))) :
    ∀ f ∈ Q, eval (fun q => v (Fintype.equivFin σ q)) f = 0 := by
  intro f hf
  have h1 := hv (ReciprocityTheory.AnForm.R.renC σ f) (Ideal.mem_map_of_mem _ hf)
  have h2 := ReciprocityTheory.AnForm.R.eval_renC (fun q => v (Fintype.equivFin σ q)) f
  have h3 : ReciprocityTheory.AnForm.R.renPt (fun q => v (Fintype.equivFin σ q)) = v := by
    funext j; simp [ReciprocityTheory.AnForm.R.renPt]
  rw [h3, h1] at h2
  exact h2.symm

theorem analyticOnNhd_rescale {σ : Type} {n m : ℕ} (e : σ ≃ Fin m) (g : (Fin n → ℂ) → Fin m → ℂ)
    (V : Set (Fin n → ℂ)) (hg : AnalyticOnNhd ℂ g V) (ε : ℝ) (hεV : Metric.ball 0 ε ⊆ V) (hε : 0 < ε) :
    ∀ t ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ q, AnalyticAt ℂ (fun s => g ((ε : ℂ) • s) (e q)) t := by
  intro t ht q
  have hmem : (ε : ℂ) • t ∈ V := by
    apply hεV
    rw [mem_ball_zero_iff] at ht ⊢
    rw [norm_smul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    nlinarith
  have h1 : AnalyticAt ℂ (fun s : Fin n → ℂ => (ε : ℂ) • s) t :=
    ((ε : ℂ) • ContinuousLinearMap.id ℂ (Fin n → ℂ)).analyticAt t
  have h2 : AnalyticAt ℂ (fun s => g ((ε : ℂ) • s)) t :=
    AnalyticAt.comp (f := fun s : Fin n → ℂ => (ε : ℂ) • s) (hg _ hmem) h1
  exact (analyticAt_pi_iff (f := fun l s => g ((ε : ℂ) • s) l)).mp h2 (e q)

theorem eq_zero_of_fderiv_eq_zero {σ : Type} [Fintype σ] {n m : ℕ} (e : σ ≃ Fin m)
    (r : Fin n → MvPolynomial (Fin m) ℂ) (gm : (Fin n → ℂ) → σ → ℂ) (ε : ℂ) (hε : ε ≠ 0)
    (t : Fin n → ℂ) (hgm : DifferentiableAt ℂ gm t)
    (hr : ∀ᶠ s in nhds t, ReciprocityTheory.AnForm.R.evalFam r (fun j => gm s (e.symm j)) = ε • s)
    (v : Fin n → ℂ) (hv : fderiv ℂ gm t v = 0) : v = 0 := by
  let R : (σ → ℂ) → Fin n → ℂ := fun y i => eval (fun j => y (e.symm j)) (r i)
  have hR : DifferentiableAt ℂ R (gm t) := by
    have han : AnalyticAt ℂ R (gm t) := by
      rw [analyticAt_pi_iff]
      intro i
      refine ReciprocityTheory.AnForm.R.analyticAt_eval_of_pi
        (f := fun (y : σ → ℂ) (j : Fin m) => y (e.symm j)) (fun l => ?_) (r i)
      exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) (e.symm l)).analyticAt _
    exact han.differentiableAt
  have hc : HasFDerivAt (R ∘ gm) ((fderiv ℂ R (gm t)).comp (fderiv ℂ gm t)) t :=
    hR.hasFDerivAt.comp t hgm.hasFDerivAt
  have hs : HasFDerivAt (R ∘ gm) (ε • ContinuousLinearMap.id ℂ (Fin n → ℂ)) t := by
    have h0 : HasFDerivAt (fun s : Fin n → ℂ => ε • s)
        (ε • ContinuousLinearMap.id ℂ (Fin n → ℂ)) t :=
      (hasFDerivAt_id t).const_smul ε
    exact h0.congr_of_eventuallyEq hr
  have heq := hc.unique hs
  have h1 := congrArg (fun L => L v) heq
  simp only [ContinuousLinearMap.comp_apply, hv, map_zero, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply] at h1
  exact (smul_eq_zero.mp h1.symm).resolve_left hε

theorem sncChart_of_regular_parameters : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J))
    (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC P)) (n : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (c : (k : K) → J k)
    (w : (Σ k, J k) → ℂ), w ∈ mcPts P → (∀ k, w ⟨k, c k⟩ ≠ 0) →
    ∀ (a : ℕ) (r : Fin n → MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ)
      (h : MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ)
      [IsRegularLocalRing (ReciprocityTheory.AnForm.R.locRing (Cmp.SncRes.ideal (pC P) c)
        (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w)))],
    ringKrullDim (ReciprocityTheory.AnForm.R.locRing (Cmp.SncRes.ideal (pC P) c)
      (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w))) = n → a ≤ n →
    Ideal.span (Set.range fun i => algebraMap _ (ReciprocityTheory.AnForm.R.locRing (Cmp.SncRes.ideal (pC P) c)
      (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w))) (r i)) =
      Ideal.map (algebraMap _ (ReciprocityTheory.AnForm.R.locRing (Cmp.SncRes.ideal (pC P) c)
        (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w))))
        (ReciprocityTheory.AnForm.R.ptIdeal (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w))) →
    (∀ i, eval (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w)) (r i) = 0) →
    eval (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w)) h ≠ 0 →
    (∀ v ∈ ReciprocityTheory.AnForm.R.zeroSet (Cmp.SncRes.ideal (pC P) c), eval v h ≠ 0 →
      ((fun q => v (Fintype.equivFin (Σ k, J k) q)) ∈ Bd ↔ ∃ i : Fin n, (i : ℕ) < a ∧ eval v (r i) = 0)) →
    ∃ (χ : SncChart P n Bd) (O : Set ((Σ k, J k) → ℂ)), IsOpen O ∧ w ∈ O ∧
      ∀ z ∈ O ∩ mcPts P, ∃ t : Fin n → ℂ, ‖t‖ ≤ 1 / 2 ∧ ∃ c' : K → ℂ, (∀ k, c' k ≠ 0) ∧
        z = torusSmul c' (χ.γ t) := by
  intro K _ J _ P hP n Bd c w hw hwc a r h _ hdim haN hspan hr0 hh0 hbd
  classical
  set I := Cmp.SncRes.ideal (pC P) c with hI
  set p := ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w) with hp
  have hcone : ∀ z, z ∈ mcPts P → (∀ k, z ⟨k, c k⟩ ≠ 0) →
      ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c z) ∈ ReciprocityTheory.AnForm.R.zeroSet I := by
    intro z hz hzc
    have h1 := (ReciprocityTheory.AnForm.R.mem_conePts_iff_chartIdeal hP c z hzc).1
      ((mem_mcPts_iff_conePts_pC P z).1 hz)
    exact ReciprocityTheory.AnForm.R.renPt_zero _ _ h1
  have hpz : p ∈ ReciprocityTheory.AnForm.R.zeroSet I := hcone w hw hwc
  obtain ⟨U, V, g, hU, hpU, hV, hg, hbij, hrg⟩ :=
    ReciprocityTheory.AnForm.R.exists_holo_coords I p n hdim r hspan

  have hsolve : ∀ v ∈ U ∩ ReciprocityTheory.AnForm.R.zeroSet I,
      ReciprocityTheory.AnForm.R.evalFam r v ∈ V ∧ g (ReciprocityTheory.AnForm.R.evalFam r v) = v := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := hbij.surjOn hv
    rw [hrg u hu]
    exact ⟨hu, rfl⟩
  have hr0' : ReciprocityTheory.AnForm.R.evalFam r p = 0 := funext hr0
  obtain ⟨h0V, hg0⟩ := hsolve p ⟨hpU, hpz⟩
  rw [hr0'] at h0V hg0

  have hcont0 : ContinuousAt g 0 := (hg 0 h0V).continuousAt
  have hnear : ∀ᶠ u in nhds (0 : Fin n → ℂ), u ∈ V ∧ eval (g u) h ≠ 0 := by
    have hVn : ∀ᶠ u in nhds (0 : Fin n → ℂ), u ∈ V := hV.mem_nhds h0V
    refine hVn.and ?_
    have hc : ContinuousAt (fun u => eval (g u) h) 0 :=
      (MvPolynomial.continuous_eval h).continuousAt.comp hcont0
    refine hc.eventually_ne ?_
    rw [hg0]; exact hh0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hnear
  have hεV : Metric.ball (0 : Fin n → ℂ) ε ⊆ V := fun u hu => (hball u hu).1
  have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have hsc : ∀ t ∈ Metric.ball (0 : Fin n → ℂ) 1, (ε : ℂ) • t ∈ Metric.ball (0 : Fin n → ℂ) ε := by
    intro t ht
    rw [mem_ball_zero_iff] at ht ⊢
    rw [norm_smul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    nlinarith
  let e := Fintype.equivFin (Σ k, J k)
  let gm : (Fin n → ℂ) → (Σ k, J k) → ℂ := fun t q => g ((ε : ℂ) • t) (e q)

  have hzs : ∀ t ∈ Metric.ball (0 : Fin n → ℂ) 1, g ((ε : ℂ) • t) ∈ ReciprocityTheory.AnForm.R.zeroSet I :=
    fun t ht => (hbij.mapsTo (hεV (hsc t ht))).2
  have hchart : ∀ t ∈ Metric.ball (0 : Fin n → ℂ) 1,
      gm t ∈ ReciprocityTheory.AnForm.R.conePts (pC P) ∧ ∀ k, gm t ⟨k, c k⟩ = 1 := by
    intro t ht
    have h1 := ReciprocityTheory.AnForm.R.conePts_of_chartIdeal hP c (gm t)
      (eval_unren_eq_zero _ _ (hzs t ht))
    exact ⟨h1.1, h1.2.1⟩
  have hcoord : ∀ t ∈ Metric.ball (0 : Fin n → ℂ) 1,
      ReciprocityTheory.AnForm.R.evalFam r (g ((ε : ℂ) • t)) = (ε : ℂ) • t :=
    fun t ht => hrg _ (hεV (hsc t ht))
  have han : AnalyticOnNhd ℂ gm (Metric.ball 0 1) := fun t ht =>
    AnalyticAt.pi (f := fun q s => g ((ε : ℂ) • s) (e q))
      (analyticOnNhd_rescale e g V hg ε hεV hε t ht)
  refine ⟨SncChart.mk gm a haN han ?_ ?_ ?_ ?_, {z | (∀ k, z ⟨k, c k⟩ ≠ 0) ∧
              ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c z) ∈ U ∧
              ‖ReciprocityTheory.AnForm.R.evalFam r (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c z))‖ < ε / 2},
            ?_, ⟨hwc, hpU, ?_⟩, ?_⟩
  · exact fun t ht => (mem_mcPts_iff_conePts_pC P _).2 (hchart t ht).1
  · intro t ht v ⟨c', hc'⟩
    have hdiff : DifferentiableAt ℂ gm t := (han t ht).differentiableAt
    have hcomp : ∀ k, c' k = 0 := by
      intro k
      have h1 := congrFun hc' ⟨k, c k⟩
      have h2 : (fun s => gm s ⟨k, c k⟩) =ᶠ[nhds t] fun _ => (1 : ℂ) := by
        filter_upwards [Metric.isOpen_ball.mem_nhds ht] with s hs using (hchart s hs).2 k
      have h3 : HasFDerivAt (fun s => gm s ⟨k, c k⟩)
          ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) ⟨k, c k⟩).comp
            (fderiv ℂ gm t)) t :=
        (hasFDerivAt_pi'.1 hdiff.hasFDerivAt) ⟨k, c k⟩
      have h4 := h3.unique ((hasFDerivAt_const (1 : ℂ) t).congr_of_eventuallyEq h2)
      have h5 := congrArg (fun L => L v) h4
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
        ContinuousLinearMap.zero_apply] at h5
      rw [h1] at h5
      simpa [torusSmul, (hchart t ht).2 k] using h5
    have hzero : fderiv ℂ gm t v = 0 := by
      rw [hc']; funext q; simp [torusSmul, hcomp q.1]
    refine eq_zero_of_fderiv_eq_zero e r gm (ε : ℂ) hεc t hdiff ?_ v hzero
    filter_upwards [Metric.isOpen_ball.mem_nhds ht] with s hs
    have : (fun j => gm s (e.symm j)) = g ((ε : ℂ) • s) := by
      funext j; simp [gm]
    rw [this]
    exact hcoord s hs
  · intro t ht t' ht' c' hc' he
    have hone : ∀ k, c' k = 1 := by
      intro k
      have h1 := congrFun he ⟨k, c k⟩
      simpa [torusSmul, (hchart t ht).2 k, (hchart t' ht').2 k] using h1.symm
    have hgg : g ((ε : ℂ) • t) = g ((ε : ℂ) • t') := by
      funext j
      have h1 := congrFun he (e.symm j)
      simpa [gm, torusSmul, hone] using h1
    have h2 := (hcoord t ht).symm.trans ((congrArg _ hgg).trans (hcoord t' ht'))
    exact smul_right_injective _ hεc h2
  · intro t ht
    have h1 := hbd (g ((ε : ℂ) • t)) (hzs t ht) (hball _ (hsc t ht)).2
    refine h1.trans ?_
    have h2 : ∀ i, eval (g ((ε : ℂ) • t)) (r i) = (ε : ℂ) * t i := fun i =>
      congrFun (hcoord t ht) i
    simp only [h2, mul_eq_zero, hεc, false_or]
  · have hA : IsOpen {z : (Σ k, J k) → ℂ | ∀ k, z ⟨k, c k⟩ ≠ 0} := by
      have : {z : (Σ k, J k) → ℂ | ∀ k, z ⟨k, c k⟩ ≠ 0} = ⋂ k, {z | z ⟨k, c k⟩ ≠ 0} := by
        ext z; simp
      rw [this]
      exact isOpen_iInter_of_finite fun k => isOpen_ne_fun (continuous_apply _) continuous_const
    have hf : ContinuousOn (fun z : (Σ k, J k) → ℂ =>
        ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c z))
        {z : (Σ k, J k) → ℂ | ∀ k, z ⟨k, c k⟩ ≠ 0} := by
      refine continuousOn_pi.2 fun j => ?_
      simp only [ReciprocityTheory.AnForm.R.renPt, ReciprocityTheory.AnForm.R.affCoord, Function.comp_apply]
      exact (continuous_apply _).continuousOn.div (continuous_apply _).continuousOn
        fun z hz => hz _
    have hev : Continuous (ReciprocityTheory.AnForm.R.evalFam r) :=
      continuous_pi fun l => MvPolynomial.continuous_eval (p := r l)
    have hT : IsOpen (U ∩ ReciprocityTheory.AnForm.R.evalFam r ⁻¹' {u | ‖u‖ < ε / 2}) :=
      hU.inter (isOpen_lt continuous_norm continuous_const |>.preimage hev)
    have := hf.isOpen_inter_preimage hA hT
    exact this
  · show ‖ReciprocityTheory.AnForm.R.evalFam r p‖ < ε / 2
    rw [hr0', norm_zero]; positivity
  · rintro z ⟨⟨hzc, hzU, hzn⟩, hzm⟩
    obtain ⟨hv1, hv2⟩ := hsolve _ ⟨hzU, hcone z hzm hzc⟩
    set v := ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c z) with hv
    set u := ReciprocityTheory.AnForm.R.evalFam r v with hu
    refine ⟨(ε : ℂ)⁻¹ • u, ?_, fun k => z ⟨k, c k⟩, hzc, ?_⟩
    · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
      rw [inv_mul_le_iff₀ hε]
      linarith
    · funext q
      show z q = z ⟨q.1, c q.1⟩ * g ((ε : ℂ) • (ε : ℂ)⁻¹ • u) (e q)
      rw [smul_inv_smul₀ hεc, hv2]
      have hvq : v (e q) = ReciprocityTheory.AnForm.R.affCoord c z q := by
        show ReciprocityTheory.AnForm.R.affCoord c z (e.symm (e q)) = _
        rw [Equiv.symm_apply_apply]
      rw [hvq]
      simp only [ReciprocityTheory.AnForm.R.affCoord]
      rw [mul_div_cancel₀ _ (hzc q.1)]

end GlobalTheory.CompanionTheory.Ar.ChartParams
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularValuesInAdjoinedField
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncRes

theorem valR_mem_adjoin_of_affine {Ω : Type} [Field Ω] [CharZero Ω] {X : Scheme.{0}} (ξ : Sp Ω ⟶ X)
    {W₀ : X.Opens} (hW₀ : IsAffineOpen W₀) (h₀ : ⊤ ≤ ξ ⁻¹ᵁ W₀) (A : Subalgebra ℚ Ω)
    (hA : Set.range (valMap ξ W₀ h₀).hom = A) {O : X.Opens} (hO : ⊤ ≤ ξ ⁻¹ᵁ O) (t : Γ(X, O)) :
    valR ξ O t ∈ IntermediateField.adjoin ℚ (A : Set Ω) := by
  have hmem : ∀ a : Γ(X, W₀), valR ξ W₀ a ∈ IntermediateField.adjoin ℚ (A : Set Ω) := fun a => by
    apply IntermediateField.subset_adjoin
    rw [valR_eq ξ W₀ h₀, ← hA]
    exact ⟨a, rfl⟩
  let z : Sp Ω := IsLocalRing.closedPoint Ω
  obtain ⟨b, hbO, hxb⟩ := hW₀.exists_basicOpen_le (V := O) ⟨ξ z, hO trivial⟩ (h₀ trivial)
  have hD : ⊤ ≤ ξ ⁻¹ᵁ X.basicOpen b := fun y _ => by
    rw [Subsingleton.elim y z]
    exact hxb
  have hloc := hW₀.isLocalization_basicOpen b
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers b)
    ((X.presheaf.map (homOfLE hbO).op).hom t)
  have hres : ∀ c : Γ(X, W₀), valR ξ (X.basicOpen b) (algebraMap Γ(X, W₀) Γ(X, X.basicOpen b) c) =
      valR ξ W₀ c := fun c => valR_res ξ (X.basicOpen_le b) hD c
  have hv := congrArg (valR ξ (X.basicOpen b)) h
  simp only at hv
  rw [valR_mul ξ _ hD, valR_res ξ hbO hD, hres, hres, valR_pow ξ _ h₀] at hv
  have hunit : valR ξ W₀ b ≠ 0 := ((le_preimage_basicOpen_iff ξ h₀ b).1 hD).ne_zero
  have e : valR ξ O t = valR ξ W₀ a / valR ξ W₀ b ^ n := by
    rw [eq_div_iff (pow_ne_zero n hunit)]
    exact hv
  rw [e]
  exact div_mem (hmem a) (pow_mem (hmem b) n)

theorem valR_appIso_inv {C : Type} [CommRing C] {X Y : Scheme.{0}} (r : Y ⟶ X) [IsOpenImmersion r] (y : Sp C ⟶ Y)
    (V : Y.Opens) (h : ⊤ ≤ y ⁻¹ᵁ V) (t : Γ(Y, V)) :
    valR (y ≫ r) (r ''ᵁ V) ((r.appIso V).inv.hom t) = valR y V t := by
  rw [← valR_appLE y r (r.preimage_image_eq V).ge h, ← Scheme.Hom.appIso_hom']
  congr 1
  exact congrArg (fun φ => φ.hom t) (r.appIso V).inv_hom_id

theorem valR_mem_adjoin_of_modification : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X X' : Scheme.{0}) (ξ : Sp Ω ⟶ X) [IsDominant ξ] [IsReduced X] (f : X' ⟶ X) (U : X.Opens) [IsIso (f ∣_ U)] (ζ : Sp Ω ⟶ X') (hζ : ζ ≫ f = ξ) (hU : ⊤ ≤ ζ ⁻¹ᵁ (f ⁻¹ᵁ U)) (W₀ : X.Opens) (hW₀ : IsAffineOpen W₀) (h₀ : ⊤ ≤ ξ ⁻¹ᵁ W₀) (A : Subalgebra ℚ Ω) (hA : Set.range (valMap ξ W₀ h₀).hom = A) (W' : X'.Opens) (h' : ⊤ ≤ ζ ⁻¹ᵁ W') (s : Γ(X', W')), valR ζ W' s ∈ IntermediateField.adjoin ℚ (A : Set Ω) := by
  intro Ω _ _ X X' ξ _ _ f U _ ζ hζ hU W₀ hW₀ h₀ A hA W' h' s
  haveI : IsOpenImmersion ((f ⁻¹ᵁ U).ι ≫ f) := by
    rw [← morphismRestrict_ι]
    infer_instance
  have hr : Set.range ζ ⊆ Set.range (f ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    exact hU (Set.mem_univ y)
  let y : Sp Ω ⟶ (f ⁻¹ᵁ U).toScheme := IsOpenImmersion.lift (f ⁻¹ᵁ U).ι ζ hr
  have hy : y ≫ (f ⁻¹ᵁ U).ι = ζ := IsOpenImmersion.lift_fac _ _ _
  have hyr : y ≫ ((f ⁻¹ᵁ U).ι ≫ f) = ξ := by rw [← Category.assoc, hy, hζ]
  have hV : ⊤ ≤ y ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ⁻¹ᵁ W') := fun z hz => by
    have : z ∈ ζ ⁻¹ᵁ W' := h' hz
    rw [← hy] at this
    exact this
  have e1 : valR ζ W' s = valR y _ (((f ⁻¹ᵁ U).ι.app W').hom s) := by
    conv_lhs => rw [← hy]
    exact valR_comp y _ W' s
  rw [e1, ← valR_appIso_inv ((f ⁻¹ᵁ U).ι ≫ f) y _ hV]
  subst hyr
  exact valR_mem_adjoin_of_affine _ hW₀ h₀ A hA (fun z hz => ((( (f ⁻¹ᵁ U).ι ≫ f).preimage_image_eq _).ge (hV hz) : _)) _

end GlobalTheory.CompanionTheory.Ar.SncRes
end
end

