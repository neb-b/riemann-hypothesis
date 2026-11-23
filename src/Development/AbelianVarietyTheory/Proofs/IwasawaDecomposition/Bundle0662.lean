module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0606
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0506
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0622
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0618
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0616
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0636
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0647
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0648
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0655
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0629
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0658
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0637
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0424
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0639
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0640
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0341
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeakCharInertPartRealAdelicDataTransport
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
public import Formalism.SharpRestriction.GrowthBounds.BaseLevels.LvSite

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactDualLinearFormFlagDegreePointClass
section
namespace GlobalTheory.GrassTop
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

theorem add_mul_pred_div_two : ∀ (a b : ℕ), (a + b) * (a + b - 1) / 2 = a * (a - 1) / 2 + b * (b - 1) / 2 + a * b := by
  have g : ∀ n : ℕ, (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n := by
    intro n
    rw [Nat.add_sub_cancel]
    cases n with
    | zero => simp
    | succ k =>
      rw [Nat.add_sub_cancel, show (k + 1 + 1) * (k + 1) = (k + 1) * k + 2 * (k + 1) by ring,
        Nat.add_mul_div_left _ _ (by norm_num)]
  intro a b
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← add_assoc, g (a + b), g b, ih]; ring

theorem pointPoly_isWeightedHomogeneous : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), IsWeightedHomogeneous Prod.snd (pointPoly H Dw) (Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q)) := by
  intro E _ _ _ H Dw
  unfold pointPoly
  have hs : Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q) = ∑ τ : GlobalTheory.AllWt.Psi H, Dw.p * Dw.q := by simp
  rw [hs]
  apply IsWeightedHomogeneous.prod
  intro τ _
  have hm : Dw.mult τ.1 = Dw.p := by simp [Datum.mult, τ.2]
  rw [hm, show Dw.p + Dw.q - Dw.p = Dw.q by omega]
  have h1 : IsWeightedHomogeneous (Prod.snd : (E →+* ℂ) × ℕ → ℕ)
      (C ((-1 : ℝ) ^ Dw.p) * X (τ.1, Dw.p) : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) Dw.p := by
    simpa using (isWeightedHomogeneous_C (Prod.snd : (E →+* ℂ) × ℕ → ℕ) ((-1 : ℝ) ^ Dw.p)).mul
      (isWeightedHomogeneous_X ℝ (Prod.snd : (E →+* ℂ) × ℕ → ℕ) (τ.1, Dw.p))
  simpa [mul_comm] using h1.pow Dw.q

theorem antisymm_isHomogeneous : ∀ {ι : Type} [Fintype ι] {m : ι → ℕ} (P : MvPolynomial (Root m) ℝ) (d : ℕ), P.IsHomogeneous d → (antisymm P).IsHomogeneous d := by
  intro ι _ m P d h
  unfold GlobalTheory.GoodMetric.antisymm
  apply IsHomogeneous.sum
  intro w _
  have h1 := h.rename_isHomogeneous (f := fun x : Root m => (⟨x.fst, (w x.fst) x.snd⟩ : Root m))
  have h2 := (mem_homogeneousSubmodule _ _).mpr h1
  exact (mem_homogeneousSubmodule _ _).mp (Submodule.smul_of_tower_mem _ _ h2)

theorem intGr_sub {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (A B : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) : intGr H Dw (A - B) = intGr H Dw A - intGr H Dw B := by
  unfold intGr Formalism.DegreeFormula.degFl
  simp only [map_sub, sub_mul, coeff_sub, mul_sub, Finset.sum_sub_distrib, sub_div]

theorem intGr_C_mul {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (c : ℝ) (A : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) : intGr H Dw (C c * A) = c * intGr H Dw A := by
  unfold intGr Formalism.DegreeFormula.degFl
  have hc : rho H Dw (C c) = C c := by
    simpa [MvPolynomial.algebraMap_eq] using (rho H Dw).commutes c
  have hc0 : chernRoots Dw.mult (C c) = C c := by
    simpa [MvPolynomial.algebraMap_eq] using (chernRoots Dw.mult).commutes c
  simp only [map_mul, hc0, hc, mul_assoc, coeff_C_mul]
  rw [mul_div_assoc']
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => by ring

theorem intGr_of_chernRoots_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (Dw : Datum H) (A : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) (h : chernRoots Dw.mult A = 0) :
    intGr H Dw A = 0 := by
  unfold intGr Formalism.DegreeFormula.degFl
  simp [h]

theorem grass_top : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (la : GlobalTheory.AllWt.Weight Dw) (R : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) (n D : ℕ) (L : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ), D = Fintype.card (GlobalTheory.AllWt.Psi H) * ((Dw.p + Dw.q) * (Dw.p + Dw.q - 1) / 2) → antisymm ((∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) ^ D) = chernRoots Dw.mult R * rootDiscr Dw.mult → (∀ (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) (d : ℕ), MvPolynomial.IsWeightedHomogeneous (Prod.snd : (E →+* ℂ) × ℕ → ℕ) Q d → d ≠ n → L Q = 0) → (∀ (τ : E →+* ℂ) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), L ((MvPolynomial.X (τ, 0) - 1) * Q) = 0) → (∀ (τ : E →+* ℂ) (k : ℕ) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), Dw.mult τ < k → L (MvPolynomial.X (τ, k) * Q) = 0) → (∀ (τ : GlobalTheory.AllWt.Psi H) (k : ℕ) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), 1 ≤ k → L ((∑ a ∈ Finset.range (k + 1), MvPolynomial.C ((-1 : ℝ) ^ (k - a)) * MvPolynomial.X (τ.1, a) * MvPolynomial.X (conjEmb τ.1, k - a)) * Q) = 0) → L R = Formalism.DegreeFormula.flagDeg (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (fun τ i => (la τ i : ℝ)) * L (pointPoly H Dw) := by
  intro E _ _ _ H Dw la R n D L hD hR hdeg hJ0 hJk hrel

  have hL : ∀ Q ∈ relIdeal H Dw, L Q = 0 := by
    intro Q hQ
    have key : ∀ a, L (Q * a) = 0 := by
      refine Submodule.span_induction (p := fun x _ => ∀ a, L (x * a) = 0) ?_ ?_ ?_ ?_ hQ
      · rintro x ((⟨τ, rfl⟩ | ⟨τ, k, hk, rfl⟩) | ⟨τ, k, hk, rfl⟩) a
        · exact hJ0 τ a
        · exact hJk τ k a hk
        · exact hrel τ k a hk
      · intro a; simp
      · intro x y _ _ hx hy a; rw [add_mul, map_add (f := _), hx, hy, add_zero]
      · intro b x _ hx a; rw [smul_eq_mul, mul_comm b x, mul_assoc]; exact hx _
    simpa using key 1
  have hker : ∀ Q, chernRoots Dw.mult Q = 0 → L Q = 0 := by
    intro Q hQ
    apply hL
    refine Ideal.span_mono ?_ (_root_.GlobalTheory.GrassKernel.mem_span_of_chernRoots_eq_zero Dw.mult Q hQ)
    exact Set.subset_union_left
  set e := Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q) with he
  set δ := Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * (Dw.p - 1) / 2 + Dw.q * (Dw.q - 1) / 2) with hδ

  have hRh : (chernRoots Dw.mult R).IsHomogeneous e := by
    refine GlobalTheory.T.isHomogeneous_of_mul_isHomogeneous_of_ne_zero_right _ _ e δ (by apply GlobalTheory.GoodMetric.rootDiscr_ne_zero) (_root_.GlobalTheory.GrassTop.rootDiscr_isHomogeneous H Dw) ?_
    rw [← hR]
    have hed : e + δ = D := by
      rw [hD, he, hδ, add_mul_pred_div_two]; ring
    rw [hed]
    apply antisymm_isHomogeneous
    have hlin : (∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) *
        MvPolynomial.X x).IsHomogeneous 1 :=
      IsHomogeneous.sum _ _ _ fun x _ => isHomogeneous_C_mul_X _ _
    simpa using hlin.pow D
  set Re := weightedHomogeneousComponent (Prod.snd : (E →+* ℂ) × ℕ → ℕ) e R with hRe
  have hReW : IsWeightedHomogeneous (Prod.snd : (E →+* ℂ) × ℕ → ℕ) Re e :=
    weightedHomogeneousComponent_isWeightedHomogeneous _ _
  have hrest : chernRoots Dw.mult (R - Re) = 0 := by
    have hc : ∀ d, homogeneousComponent d (chernRoots Dw.mult (R - Re)) = 0 := by
      intro d
      rw [_root_.GlobalTheory.GrassComp.homogeneousComponent_chernRoots, map_sub]
      by_cases hd : d = e
      · rw [hd, hReW.weightedHomogeneousComponent_same]
        simp [hRe]
      · rw [map_sub, ← _root_.GlobalTheory.GrassComp.homogeneousComponent_chernRoots, homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hRh), if_neg hd,
          weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hReW), if_neg hd,
          map_zero, sub_zero]
    rw [← sum_homogeneousComponent (chernRoots Dw.mult (R - Re))]
    exact Finset.sum_eq_zero fun d _ => hc d
  have hLR : L R = L Re := by
    have := hker _ hrest
    rw [map_sub, sub_eq_zero] at this
    exact this
  have hIR : intGr H Dw R = intGr H Dw Re := by
    have := intGr_of_chernRoots_eq_zero H Dw _ hrest
    rw [intGr_sub, sub_eq_zero] at this
    exact this
  by_cases hn : n = e
  · obtain ⟨c, hc⟩ := _root_.GlobalTheory.GrassTopDim.top_eq_smul_point H Dw Re hReW
    have h1 := hL _ hc
    rw [map_sub, sub_eq_zero, C_mul', map_smul, smul_eq_mul] at h1
    have h2 := _root_.GlobalTheory.GrassTop.intGr_eq_zero_of_mem_relIdeal H Dw _ hc
    rw [intGr_sub, intGr_C_mul, _root_.GlobalTheory.GrassTop.intGr_pointPoly, mul_one, sub_eq_zero] at h2
    rw [hLR, h1, ← h2, ← hIR, _root_.GlobalTheory.GrassTop.intGr_eq_flagDeg H Dw la R D hD hR]
  · have h1 : L Re = 0 := hdeg Re e hReW (Ne.symm hn)
    have h2 : L (pointPoly H Dw) = 0 := hdeg _ e (pointPoly_isWeightedHomogeneous H Dw) (Ne.symm hn)
    rw [hLR, h1, h2, mul_zero]

end GlobalTheory.GrassTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRiemannFormPeriodChartGenericFibre
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh.PerChart

theorem hermForm_pull' {g g' : ℕ} (M : Matrix (Fin g') (Fin g) ℂ) (Hm : Matrix (Fin g') (Fin g') ℂ) (z w : Fin g → ℂ) :
    hermForm (Mᵀ * Hm * Mᵀᴴ) z w = hermForm Hm (M *ᵥ z) (M *ᵥ w) := by
  have : Mᵀᴴ *ᵥ (star w) = star (M *ᵥ w) := by
    rw [Matrix.star_mulVec, ← Matrix.mulVec_transpose]
    rfl
  rw [hermForm, hermForm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, this, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

theorem exists_logExp_eq (n a : ℕ) (z : Fin n → ℂ) (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1)
    (hnz : ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) : ∃ s ∈ logDom n a, logExp a s = z := by
  refine ⟨fun k => if (k : ℕ) < a then Complex.log (z k) else z k, fun k => ?_, funext fun k => ?_⟩
  · have hk1 : ‖z k‖ < 1 := (pi_norm_lt_iff one_pos).1 (mem_ball_zero_iff.1 hz) k
    by_cases hk : (k : ℕ) < a
    · simp only [hk, if_true]
      rw [Complex.log_re]
      exact Real.log_neg (norm_pos_iff.2 (hnz k hk)) hk1
    · simp only [hk, if_false]
      exact hk1
  · by_cases hk : (k : ℕ) < a
    · simp only [logExp, hk, if_true]
      exact Complex.exp_log (hnz k hk)
    · simp only [logExp, hk, if_false]

theorem exists_riemann_period_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ x₀ : GlobalTheory.CxPts (genStr T.Z) σ, ∃ (n a : ℕ) (ha : a ≤ n) (g rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (ch₀ : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g) (d : ℝ), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B ∧ IsExpChart ch₀ ex ∧ x₀ ∈ ch₀.source ∧ ch₀ x₀ = 0 ∧ Fintype.card ((Σ τ : E →+* ℂ, Fin (Dw.mult τ))) = g ∧ 0 < d ∧ (∀ x ∈ ch₀.source, Inner x ↔ ∀ i : Fin a, ch₀ x (Fin.castLE ha i) ≠ 0) ∧ ∀ x ∈ ch₀.source, Inner x → ((((d : ℝ) : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹).IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm (((d : ℝ) : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹) u u).re) ∧ (∀ v w : Fin g → ℂ, ex x v = 1 → ex x w = 1 → ∃ m : ℤ, (hermForm (((d : ℝ) : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹) v w).im = m) ∧ ∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → ex x v = 1 → ex x w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm (((d : ℝ) : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹) v w).im : ℂ) / k) → GlobalTheory.UU.CubWeil T.Z.t.cub k (ex x ((k : ℂ)⁻¹ • v)) (ex x ((k : ℂ)⁻¹ • w)) (unitOn ζ)) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T σ U hσ hU x₀
  obtain ⟨n, a₁, g, r₀, e, ex, ζ, hx₀, he0, hEC, hbd, hsurj, hζan, hζli, hζK, hζB, hζC, hζstd⟩ :=
    _root_.GlobalTheory.ShFam.Hor.LogCh.exists_framed_chart E H Dw l Xo c O β Y T σ x₀
  have hEC' := hEC
  obtain ⟨htarget, hholE, hsymmHol, hadd, hjoint, htan⟩ := hEC'
  let a := min a₁ n
  have ha : a ≤ n := min_le_right _ _
  have hka : ∀ k : Fin n, ((k : ℕ) < a ↔ (k : ℕ) < a₁) := fun k => by
    simp only [a, lt_min_iff, k.isLt, and_true]
  have hsymm : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, e.symm z ∈ e.source := fun z hz =>
    e.map_target (by rw [htarget]; exact hz)
  have hExpAt : ∀ x ∈ e.source, IsExpAt T.Z.t (x.1 ≫ genι T.Z) (ex x) := fun x hx =>
    ⟨hadd x hx, (htan x hx).1, (htan x hx).2⟩
  have hzero : ∀ x ∈ e.source, ex x 0 = 1 := fun x hx => by
    have := hadd x hx 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hHol : IsHolTo (Metric.ball (0 : Fin n → ℂ) 1 ×ˢ Set.univ)
      (fun zw : (Fin n → ℂ) × (Fin g → ℂ) => (ex (e.symm zw.1) zw.2).left) := htarget ▸ hjoint
  have hslice : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, IsHolTo Set.univ (fun w => (ex (e.symm z) w).left) :=
    fun z hz => by
      have := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun w : Fin g → ℂ => (z, w)) hHol isOpen_univ
        ((differentiableOn_const z).prodMk differentiableOn_id) fun w _ => Set.mk_mem_prod hz (Set.mem_univ w)
      dsimp only at this
      exact this
  have h0 : e.symm 0 = x₀ := by rw [← he0]; exact e.left_inv hx₀
  have hmem0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  have hinner : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → Inner (e.symm z) :=
    fun z hz hnz => (hbd _ (hsymm z hz)).2 fun k hk => by
      rw [e.right_inv (by rw [htarget]; exact hz)]
      exact hnz k ((hka k).2 hk)
  let K : (Fin n → ℂ) → Set (Fin g → ℂ) := fun z => {w | ex (e.symm z) w = 1}
  let Pair : ℕ → (Fin n → ℂ) → (Fin g → ℂ) → (Fin g → ℂ) → ℂˣ → Prop := fun N z v w c =>
    GlobalTheory.UU.CubWeil T.Z.t.cub N (ex (e.symm z) ((N : ℂ)⁻¹ • v)) (ex (e.symm z) ((N : ℂ)⁻¹ • w)) (unitOn c)
  have hLF : IsLatFam (Metric.ball 0 1) K :=
    _root_.GlobalTheory.ShFam.Hor.LogCh.isLatFam_ker E H T.Z.X T.Z.t n g (Metric.ball 0 1) (fun z => (e.symm z).1 ≫ genι T.Z) (fun z => ex (e.symm z))
      Metric.isOpen_ball hHol fun z hz => hExpAt _ (hsymm z hz)
  have hB0 : IsLatBasis (K 0) (ζ 0) := by
    show IsLatBasis {w | ex (e.symm 0) w = 1} (ζ 0)
    rw [h0]
    exact hζB
  have hP1 : ∀ N z v w c c', Pair N z v w c → Pair N z v w c' → c = c' := fun N z v w c c' h h' =>
    unitOn_injective (h.unique h')
  have hP2 : ∀ (m N : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → Fin n → ℂ) (v w : (Fin m → ℂ) → Fin g → ℂ)
      (c : ℂˣ) (b₀ b₁ : Fin m → ℂ), 0 < N → IsOpen B → _root_.IsPreconnected B → DifferentiableOn ℂ φ B →
      Set.MapsTo φ B (Metric.ball 0 1) → DifferentiableOn ℂ v B → DifferentiableOn ℂ w B →
      (∀ b ∈ B, v b ∈ K (φ b) ∧ w b ∈ K (φ b)) → b₀ ∈ B → b₁ ∈ B →
      Pair N (φ b₀) (v b₀) (w b₀) c → Pair N (φ b₁) (v b₁) (w b₁) c := by
    intro m N B φ v w c b₀ b₁ hN hB hBc hφ hφm hv hw hK hb₀ hb₁ h
    have h1 := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun b => (φ b, (N : ℂ)⁻¹ • v b)) hHol hB
      (hφ.prodMk ((differentiableOn_const ((N : ℂ)⁻¹)).smul hv)) fun b hb => Set.mk_mem_prod (hφm hb) (Set.mem_univ _)
    have h2 := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun b => (φ b, (N : ℂ)⁻¹ • w b)) hHol hB
      (hφ.prodMk ((differentiableOn_const ((N : ℂ)⁻¹)).smul hw)) fun b hb => Set.mk_mem_prod (hφm hb) (Set.mem_univ _)
    dsimp only at h1 h2
    exact _root_.GlobalTheory.TorsionPairFam.cubWeil_const_of_isHolTo T.Z.X T.Z.t.G T.Z.t.PP T.Z.t.cub m N B (fun b => (e.symm (φ b)).1 ≫ genι T.Z)
      (fun b => ex (e.symm (φ b)) ((N : ℂ)⁻¹ • v b)) (fun b => ex (e.symm (φ b)) ((N : ℂ)⁻¹ • w b)) c b₀ b₁ hN hB hBc
      h1 h2
      (fun b hb => ⟨pow_eq_one_of_map _ (hadd _ (hsymm _ (hφm hb))) (hzero _ (hsymm _ (hφm hb))) hN (hK b hb).1,
        pow_eq_one_of_map _ (hadd _ (hsymm _ (hφm hb))) (hzero _ (hsymm _ (hφm hb))) hN (hK b hb).2⟩) hb₀ hb₁ h
  have hP3 : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) →
      ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧
        Submodule.span ℝ (K z) = ⊤ ∧ (∀ v ∈ K z, ∀ w ∈ K z, ∃ m : ℤ, (hermForm Hm v w).im = m) ∧
        ∀ (N : ℕ) (v w : Fin g → ℂ), 0 < N → v ∈ K z → w ∈ K z →
          Pair N z v w (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / N))
            (Complex.exp_ne_zero _)) := by
    intro z hz hnz
    obtain ⟨-, Hm, hH, hpos, hspan, hint, hw⟩ := GlobalTheory.ShFam.Hor.LogCh.kernel_lattice_of_isUnf E H Dw l Xo c O β T.Z σ U hσ hU g (e.symm z) (ex (e.symm z))
      (hinner z hz hnz) (hExpAt _ (hsymm z hz)) (hslice z hz)
    exact ⟨Hm, hH, hpos, hspan, fun v hv w hw' => hint v w hv hw', fun N v w hN hv hw' => hw N v w _ hN hv hw' rfl⟩
  have hP4 : ∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧
      ∀ u u' : Fin r₀ → ℤ, (fun j => (u j : ZMod N)) ∈ S → Pair N 0 (∑ j, u j • ζ 0 j) (∑ j, u' j • ζ 0 j) 1 := by
    intro N hN
    have hsl : IsHolTo Set.univ (fun w => (ex x₀ w).left) := by
      have := hslice 0 hmem0
      rw [h0] at this
      exact this
    obtain ⟨Tt, hT1, hT2, hTc⟩ := _root_.GlobalTheory.exists_toric_torsion_cubWeil_one_of_exp E H T.Z.X T.Z.t (x₀.1 ≫ genι T.Z) g N (ex x₀) hN (hExpAt x₀ hx₀) hsurj hsl
    obtain ⟨S, hSc, hS⟩ := _root_.GlobalTheory.ShFam.Hor.LogCh.exp_lattice_torsion_count _ g r₀ N (ex x₀) (ζ 0) Tt hN (hadd x₀ hx₀) hsurj hζB hT1 hTc
    refine ⟨S, hSc, fun u u' hu => ?_⟩
    show GlobalTheory.UU.CubWeil T.Z.t.cub N (ex (e.symm 0) ((N : ℂ)⁻¹ • ∑ j, u j • ζ 0 j))
      (ex (e.symm 0) ((N : ℂ)⁻¹ • ∑ j, u' j • ζ 0 j)) (unitOn 1)
    rw [h0, unitOn_one]
    exact hT2 _ (hS u hu) _ (pow_eq_one_of_map _ (hadd x₀ hx₀) (hzero x₀ hx₀) hN ((hζB.2 _).2 ⟨u', rfl⟩))
  obtain ⟨r, lam, M, hc, hs, -, hMv, hrad⟩ :=
    GlobalTheory.ShFam.Hor.LogCh.ConstForm.constForm n a g r₀ K ζ Pair hLF hζan hζli hζK hB0 hζC hζstd hP1 hP2 hP3 hP4
  have hM' : ∀ s ∈ logDom n a, ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧
      (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧
      ∀ s' ∈ logDom n a, logExp a s' = logExp a s → ∀ i j, (hermForm Hm (lam s' i) (lam s' j)).im = M i j := by
    intro s hsD
    have hz1 : logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
      rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos]
      intro k
      have hk := hsD k
      by_cases h : (k : ℕ) < a
      · simp only [h, if_true] at hk
        simp only [logExp, h, if_true, Complex.norm_exp]
        exact Real.exp_lt_one_iff.2 hk
      · simp only [h, if_false] at hk
        simpa only [logExp, h, if_false] using hk
    have hnz : ∀ k : Fin n, (k : ℕ) < a → logExp a s k ≠ 0 := fun k hk => by
      simp only [logExp, hk, if_true]
      exact Complex.exp_ne_zero _
    obtain ⟨Hm, hH, hpos, -, hint, hw⟩ := hP3 _ hz1 hnz
    refine ⟨Hm, hH, hpos, fun s' hs' he => hMv s' hs' Hm ?_ ?_⟩
    · rw [he]; exact hint
    · rw [he]; exact hw
  obtain ⟨rk, τ₀, B, P, ρ, d, hρ, hρ1, hd, hPC, hPd, hPu, hrel⟩ :=
    _root_.GlobalTheory.ShFam.Hor.LogCh.exists_periodChart_of_latFam n a g r₀ r ha K ζ lam M hLF hζan hζli hζK hB0 hζstd hc hs hM' hrad
  obtain ⟨ch, hch, hchs, hchρ⟩ := GlobalTheory.ShFam.Hor.LogCh.isExpChart_rescale E H Dw l Xo c O β T.Z σ n g e ex P ρ hEC hρ hρ1 hPd hPu
  have hρ0 : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hρ.ne'
  have hcard : Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) = g := by
    let z₁ : Fin n → ℂ := fun _ => (1 / 2 : ℂ)
    have hz₁ : z₁ ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
      rw [mem_ball_zero_iff]
      refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 fun k => ?_) (by norm_num)
      simp [z₁]
    exact (GlobalTheory.ShFam.Hor.LogCh.kernel_lattice_of_isUnf E H Dw l Xo c O β T.Z σ U hσ hU g (e.symm z₁) (ex (e.symm z₁))
      (hinner z₁ hz₁ fun k _ => by simp [z₁]) (hExpAt _ (hsymm z₁ hz₁)) (hslice z₁ hz₁)).1
  have hex : ∀ x ∈ ch.source, ∀ k, e x k = (ρ : ℂ) * ch x k := fun x hx k => by
    rw [hchρ x hx]
    simp [Complex.real_smul]
  have hx₀ch : x₀ ∈ ch.source := (hchs x₀).2 ⟨hx₀, by rw [he0]; exact Metric.mem_ball_self hρ⟩
  refine ⟨n, a, ha, g, rk, τ₀, B, ch, fun x v => ex x (P (e x) *ᵥ v), d, hPC, hch, hx₀ch, ?_, hcard, hd, ?_, ?_⟩
  · funext k
    have := hex x₀ hx₀ch k
    rw [he0] at this
    exact ((mul_eq_zero.1 this.symm).resolve_left hρ0)
  · intro x hx
    have hxe := ((hchs x).1 hx).1
    rw [hbd x hxe]
    constructor
    · intro h i hi
      apply h (Fin.castLE ha i) ((hka _).1 (by simp))
      rw [hex x hx, hi, mul_zero]
    · intro h k hk hk0
      apply h ⟨k, (hka k).2 hk⟩
      rw [hex x hx] at hk0
      exact (mul_eq_zero.1 hk0).resolve_left hρ0
  · intro x hx hin
    have hxe := ((hchs x).1 hx).1
    have hzb := ((hchs x).1 hx).2
    have hz1 : e x ∈ Metric.ball (0 : Fin n → ℂ) 1 := by rw [← htarget]; exact e.map_source hxe
    have hnz : ∀ k : Fin n, (k : ℕ) < a → e x k ≠ 0 := fun k hk =>
      (hbd x hxe).1 hin k ((hka k).1 hk)
    obtain ⟨s, hsD, hsz⟩ := exists_logExp_eq n a (e x) hz1 hnz
    have hsl : IsHolTo Set.univ (fun w => (ex x w).left) := by
      have := hslice (e x) hz1
      rw [e.left_inv hxe] at this
      exact this
    obtain ⟨-, Hm, hH, hpos, -, hint, hweil⟩ :=
      GlobalTheory.ShFam.Hor.LogCh.kernel_lattice_of_isUnf E H Dw l Xo c O β T.Z σ U hσ hU g x (ex x) hin (hExpAt x hxe) hsl
    have hKz : ∀ w, w ∈ K (logExp a s) ↔ ex x w = 1 := fun w => by
      rw [hsz]
      show ex (e.symm (e x)) w = 1 ↔ _
      rw [e.left_inv hxe]
    have hlamrel := hMv s hsD Hm (fun v hv w hw => hint v w ((hKz v).1 hv) ((hKz w).1 hw))
      (fun N v w hN hv hw => by
        show GlobalTheory.UU.CubWeil T.Z.t.cub N (ex (e.symm (logExp a s)) ((N : ℂ)⁻¹ • v))
          (ex (e.symm (logExp a s)) ((N : ℂ)⁻¹ • w)) _
        rw [hsz, e.left_inv hxe]
        exact hweil N v w _ hN ((hKz v).1 hv) ((hKz w).1 hw) rfl)
    have key := hrel s hsD (hsz ▸ hzb) Hm hlamrel
    have hchx : ρ⁻¹ • e x = ch x := by rw [hchρ x hx, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]
    rw [hsz, hchx] at key
    rw [← key]
    have hPinj : Function.Injective (P (e x)).mulVec :=
      Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (hPu _ hzb))
    refine ⟨Matrix.isHermitian_mul_mul_conjTranspose _ hH, fun u hu => ?_, fun v w hv hw => ?_,
      fun k v w ζ' hk hv hw hζ' => ?_⟩
    · rw [hermForm_pull']
      exact hpos _ (fun h0' => hu (hPinj (by rw [h0', Matrix.mulVec_zero])))
    · rw [hermForm_pull']
      exact hint _ _ hv hw
    · rw [hermForm_pull'] at hζ'
      have e1 : ∀ u : Fin g → ℂ, P (e x) *ᵥ ((k : ℂ)⁻¹ • u) = (k : ℂ)⁻¹ • (P (e x) *ᵥ u) := fun u =>
        Matrix.mulVec_smul _ _ _
      show GlobalTheory.UU.CubWeil T.Z.t.cub k (ex x (P (e x) *ᵥ ((k : ℂ)⁻¹ • v))) (ex x (P (e x) *ᵥ ((k : ℂ)⁻¹ • w))) (unitOn ζ')
      rw [e1, e1]
      exact hweil k _ _ ζ' hk hv hw hζ'

end GlobalTheory.ShFam.Hor.LogCh.PerChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionToLocalLanglandsA
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

noncomputable section

namespace GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

def nOfLay {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P)
    (L : Lay0 (Dof x)) (hZ : L.ZOk) (hE : L.EtaOk) : NStage B w.C (P.q.W x.o.η x.o.hη) :=
  { loc := L.loc, locA := L.locA, locT := L.locT, nd := L.nd, ntw := L.ntw, naut := L.naut, nbc := L.nbc, nexp := L.nexp,
    ntypes := L.ntypes, nStage_trivialCharacter_compat := L.nStage_trivialCharacter_compat, nStage_trivialCharacter_coeff_eq := L.nStage_trivialCharacter_coeff_eq, nth := L.nth, nbr := L.nbr, nbr_ind := L.nbr_ind,
    self_good := L.self_good, ntwbr := L.ntwbr, ntwbr_ind := L.ntwbr_ind, loc_tie := L.loc_tie, bc_tie := L.bc_tie,
    rbar_tie := L.rbar_tie, mtpar_tie := L.mtpar_tie, Z_tie := hZ.1, Zgood_tie := hZ.2, etaJ_tie := hE }

theorem exists_pq_sel (B : Base) {px : PreX B.toPre} (I : ColIn B px) (hI : I.Ok) :
    ∃ Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield B.host.E)) → PlE B.host,
      (∀ v, NG.OverPl (Pq v) v) ∧ Set.range Pq = Set.range I.sel :=
  ⟨I.sel, fun v => hI.sel_ok v, rfl⟩

end GlobalTheory.HeightCounting.Up

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepTiesD
section
noncomputable section

namespace GlobalTheory.Mem.Top.KerOne.CertEq

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.ChartsLv Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
  (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
  {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}


set_option maxHeartbeats 4000000 in
def StepTiesD {i : ℕ} (hi : i + 1 ≤ D.R.m) (Fo : FormsIn M (i + 1) hi) (S : StepD X0 u w hg Fo) (c : LatCmp D) : Prop :=
  (∀ (β : Fo.Ch) (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal)
    (x : GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] w'.adicCompletion D.host.F)),
    x ∈ UPts D.sp.cm.sig (D.sp.X (i + 1)).gram (w'.adicCompletion D.host.F) →
    (∀ a b, (((frB X0 u w hg S.B w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom) x * frB X0 u w hg S.B w' h : GL (Fin (D.sp.X (i + 1)).rank) _) :
        Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈ w'.adicCompletionIntegers D.host.F) →
    (∀ a b, ((((frB X0 u w hg S.B w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom) x * frB X0 u w hg S.B w' h)⁻¹ : GL (Fin (D.sp.X (i + 1)).rank) _) :
        Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈ w'.adicCompletionIntegers D.host.F) →
    x ∈ ulocOf Fo β w') ∧
  (∀ (β : Fo.Ch) (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal)
    (x : GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] w'.adicCompletion D.host.F)), x ∈ ulocOf Fo β w' →
    (∀ a b, (((frB X0 u w hg S.B w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom) x * frB X0 u w hg S.B w' h : GL (Fin (D.sp.X (i + 1)).rank) _) :
        Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈ w'.adicCompletionIntegers D.host.F) ∧
    (∀ a b, ((((frB X0 u w hg S.B w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom) x * frB X0 u w hg S.B w' h)⁻¹ : GL (Fin (D.sp.X (i + 1)).rank) _) :
        Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈ w'.adicCompletionIntegers D.host.F)) ∧
  (∀ w' ∈ Fo.bad, ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∉ w'.asIdeal) ∧
  cT (sigD D : D.host.E →+* D.host.E) (reGL (rankN D (i + 1) hi) D.host.E S.B).1 * gramN D (i + 1) hi *
    (reGL (rankN D (i + 1) hi) D.host.E S.B).1 = 1 ∧
  (∀ β, UnitCharacterChartCompatibility hi (Fo.K β).lev (c.embW u w hg) (S.ψ β)) ∧
  (∀ β cl, ∃ r : D.what₂.LL, D.what₂.embLL r = ((Fo.tw β).ch ((Fo.K β).y cl) : ℂ)) ∧
  Fo.okW w ∧
  ¬ D.what₂.places.resChar w ∣ Fo.T

end GlobalTheory.Mem.Top.KerOne.CertEq

end
end

