module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0207
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TraceBound
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0040
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0043
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.DiscreteSeriesGKMapValuesEqGeneralisedCoefficien
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.AutSpace GlobalTheory.TypeSum GlobalTheory.TypeSum.GrowthAtPlace Formalism.REAL

namespace GlobalTheory.TypeSum.GKCoef


open CoefLow in
theorem values_eq_coef : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (τ : D.what₂.Tau), IsInfFam (D := D) θ → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)) (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool)
      (P : Matrix (Fin V.rank) (Fin V.rank) ℂ) (T : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ →ₗ[ℂ] (GA D V → ℂ)),
    Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ → IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = gramAt D V τ →
    GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ ε σ P T →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ) (x : GA D V), ∃ ℓ : H →ₗ[ℂ] ℂ,
      Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ ℓ ∧ SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ (v : H) ∧
      ∀ y ∈ UJset ε, T v (x * atTau θ V τ (P⁻¹ * y * P)) = ℓ (σ y v) := by
  classical
  intro D θ V τ hθ hHC hCW H _ _ σ lam ε P T _ hDS hP h hT v x
  haveI : CompleteSpace H := hDS.1
  have hstd := std_of_isDS hHC hDS
  have hσ := hstd.1
  obtain ⟨N, hN⟩ := GlobalTheory.TypeSum.GKCoef.exists_growth_exponent θ V τ hθ hHC H σ lam ε P T hDS hP h hT x
  let F : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ → Mx V.rank → ℂ := fun w y => T w (x * atTau θ V τ (P⁻¹ * y * P))
  let f : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ →ₗ[ℂ] Bd (Unit × UJset ε) :=
    { toFun := fun w => mkBd (fun i => F w i.2.1 / wt N i.2.1) (by
        obtain ⟨C, hC⟩ := hN w
        refine ⟨C, fun i => ?_⟩
        rw [norm_div, norm_wt, div_le_iff₀ (wt_pos _ _)]
        exact hC _ i.2.2)
      map_add' := fun v w => by ext i; simp [mkBd, F, add_div]; rfl
      map_smul' := fun c v => by ext i; simp [mkBd, F, mul_div_assoc] }
  obtain ⟨T₀, hT₀'⟩ := LinearMap.exists_extend f
  have hT₀ : ∀ (w : H) (hw : IsKFin ε σ w) (i : Unit × UJset ε),
      T₀ w i = F ⟨w, mem_kFin_iff.2 hw⟩ i.2.1 / wt N i.2.1 := fun w hw i => by
    have : T₀ w = f ⟨w, mem_kFin_iff.2 hw⟩ := LinearMap.congr_fun hT₀' ⟨w, mem_kFin_iff.2 hw⟩
    rw [this]; rfl
  let wcomp (c : (Unit × UJset ε) → ℂ) (B : ℝ) (hB0 : 0 ≤ B)
      (hB : ∀ i, ‖c i‖ ≤ B) (φ : (Unit × UJset ε) → (Unit × UJset ε)) :
      Bd (Unit × UJset ε) →L[ℂ] Bd (Unit × UJset ε) :=
    LinearMap.mkContinuous
      { toFun := fun F => mkBd (fun i => c i * F (φ i)) ⟨_, wcomp_le hB φ F⟩
        map_add' := fun F G => by ext i; simp [mkBd, mul_add]; rfl
        map_smul' := fun a F => by ext i; simp [mkBd]; ring } B
      fun F => lp.norm_le_of_forall_le (by positivity) (wcomp_le hB φ F)
  let rt (h : Mx V.rank) : Bd (Unit × UJset ε) →L[ℂ] Bd (Unit × UJset ε) :=
    if hh : h ∈ UJset ε then
      wcomp (fun i => (wt N (i.2.1 * h) : ℂ) / wt N i.2.1) (wt N h) (wt_pos N h).le
        (fun i => by
          rw [norm_div, norm_wt, norm_wt, div_le_iff₀' (wt_pos _ _)]
          exact wt_mul_le _ _ _) fun i => (i.1, ⟨i.2.1 * h, mul_mem_UJ i.2.2 hh⟩)
    else 0
  have rt_apply {h : Mx V.rank} (hh : h ∈ UJset ε) (F : Bd (Unit × UJset ε)) (i : Unit × UJset ε) :
      rt h F i = (wt N (i.2.1 * h) : ℂ) / wt N i.2.1 * F (i.1, ⟨i.2.1 * h, mul_mem_UJ i.2.2 hh⟩) := by
    simp only [rt, dif_pos hh]
    rfl
  have modRep_rt : ModRep ε rt := by
    refine ⟨?_, fun a ha b hb => ?_, 1, N, fun g hg => ?_⟩
    · ext F i
      rw [rt_apply (one_mem_UJ ε)]
      simp [div_self (wt_ne _ _)]
    · ext F i
      rw [ContinuousLinearMap.comp_apply, rt_apply (mul_mem_UJ ha hb), rt_apply ha, rt_apply hb]
      simp only [mul_assoc]
      have := wt_ne N (i.2.1 * a)
      field_simp
    · simp only [rt, dif_pos hg, one_mul]
      dsimp only [wcomp]
      exact LinearMap.mkContinuous_norm_le _ (wt_pos N g).le _
  have key : ∀ (w : H) (hw : IsKFin ε σ w), ∀ y ∈ UJset ε, ∀ i : Unit × UJset ε,
      rt y (T₀ w) i = F ⟨w, mem_kFin_iff.2 hw⟩ (i.2.1 * y) / wt N i.2.1 := by
    intro w hw y hy i
    rw [rt_apply hy, hT₀ w hw]
    have := wt_ne N (i.2.1 * y)
    field_simp

  have hder : ∀ (w : H) (hw : IsKFin ε σ w) {X : Mx V.rank} (hX : X ∈ lieSet ε) {g : Mx V.rank} (hg : g ∈ UJset ε)
      (s : ℝ), HasDerivAt (fun t : ℝ => F ⟨w, mem_kFin_iff.2 hw⟩ (g * NormedSpace.exp (t • X)))
        (F ⟨dRep σ X w, mem_kFin_iff.2 (isKFin_dRep _ ε H σ hstd w hw X hX)⟩ (g * NormedSpace.exp (s • X))) s := by
    intro w hw X hX g hg s
    have hs := mul_mem_UJ hg (exp_mem_UJ hX s)
    have h1 := hasDerivAt_map hθ hP h hT ⟨w, mem_kFin_iff.2 hw⟩
      ⟨dRep σ X w, mem_kFin_iff.2 (isKFin_dRep _ ε H σ hstd w hw X hX)⟩ hX (hstd.2.2.1 w hw) rfl x hs
    have h2 := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact h1)
    refine HasDerivAt.congr_of_eventuallyEq h2 (Filter.Eventually.of_forall fun t => ?_)
    show F _ _ = F _ _
    simp only [F]
    rw [mul_assoc g (NormedSpace.exp (s • X)), ← exp_add_smul, add_sub_cancel]
  obtain ⟨T', hT1, hT2, S, C, hS, hC⟩ := GlobalTheory.TypeSum.casselmanWallach_banach hCW V.rank ε H σ hstd _ _
    modRep_rt T₀
    (fun k hk w hw => by
      ext i
      rw [key w hw k (K_le_UJ hk), hT₀ _ (isKFin_translate hw hk)]
      congr 1
      exact map_K hθ hP h hT hk _ _ rfl x i.2.2)
    (fun X hX w hw => by
      have hw1 := isKFin_dRep _ ε H σ hstd w hw X hX
      have hw2 := isKFin_dRep _ ε H σ hstd _ hw1 X hX
      obtain ⟨C2, hC2⟩ := hN ⟨_, mem_kFin_iff.2 hw2⟩
      obtain ⟨B, hB⟩ := ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).bddAbove_image
        ((continuous_wt N).comp (continuous_exp_smul X)).continuousOn)
      refine hasDerivAt_of_sq (K := |C2| * |B|) fun t ht => lp.norm_le_of_forall_le (by positivity) fun i => ?_
      have e : (t • T₀ (dRep σ X w)) i = t • T₀ (dRep σ X w) i := rfl
      rw [lp.coeFn_sub, lp.coeFn_sub, Pi.sub_apply, Pi.sub_apply, e, key w hw _ (exp_mem_UJ hX _),
        key w hw _ (exp_mem_UJ hX _), hT₀ _ hw1, zero_smul, NormedSpace.exp_zero, mul_one,
        ← smul_div_assoc, ← sub_div, ← sub_div, norm_div, norm_wt, div_le_iff₀ (wt_pos _ _)]
      have tb := taylor_two (hder w hw hX i.2.2) (hder _ hw1 hX i.2.2) (K := |C2| * |B| * wt N i.2.1)
        (fun s hs => by
          refine (hC2 _ (mul_mem_UJ i.2.2 (exp_mem_UJ hX s))).trans ?_
          have w1 := wt_mul_le N i.2.1 (NormedSpace.exp (s • X))
          have w2 : wt N (NormedSpace.exp (s • X)) ≤ |B| := (hB ⟨s, abs_le.1 hs, rfl⟩).trans (le_abs_self B)
          have w3 := wt_pos N i.2.1
          have w4 := wt_pos N (i.2.1 * NormedSpace.exp (s • X))
          change C2 * wt N _ ≤ _
          calc C2 * wt N (i.2.1 * NormedSpace.exp (s • X)) ≤ |C2| * (wt N i.2.1 * |B|) :=
                mul_le_mul (le_abs_self _) (w1.trans (mul_le_mul_of_nonneg_left w2 w3.le)) w4.le (abs_nonneg _)
            _ = _ := by ring) ht
      simp only [zero_smul, NormedSpace.exp_zero, mul_one] at tb
      calc _ ≤ |C2| * |B| * wt N i.2.1 * t ^ 2 := tb
        _ = _ := by ring)
  let ℓ : H →ₗ[ℂ] ℂ :=
    { toFun := fun w => wt N (1 : Mx V.rank) * T' w ((), ⟨1, one_mem_UJ ε⟩)
      map_add' := fun a b => by simp [mul_add]
      map_smul' := fun c a => by simp; ring }
  have hvK : IsKFin ε σ (v : H) := mem_kFin_iff.1 v.2
  refine ⟨ℓ, ⟨S, wt N (1 : Mx V.rank) * |C|, hS, fun w hw => ?_⟩, hstd.2.2.1 _ hvK, fun y hy => ?_⟩
  · change ‖(wt N (1 : Mx V.rank) : ℂ) * T' w ((), ⟨1, one_mem_UJ ε⟩)‖ ≤ _
    rw [norm_mul, norm_wt, mul_assoc]
    refine mul_le_mul_of_nonneg_left ((apply_le _ _).trans ((hC w hw).trans ?_)) (wt_pos _ _).le
    exact mul_le_mul_of_nonneg_right (le_abs_self C) (sobNorm_nonneg _ _ _)
  · change _ = (wt N (1 : Mx V.rank) : ℂ) * T' (σ y v) ((), ⟨1, one_mem_UJ ε⟩)
    rw [hT2 y hy _ (hstd.2.2.1 _ hvK), hT1 _ hvK, key _ hvK y hy]
    have := wt_ne N (1 : Mx V.rank)
    simp only [one_mul, F]
    field_simp

end GlobalTheory.TypeSum.GKCoef

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCommonGrowthExponentGKDiscreteSeries
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.TypeSum.CoefRep

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem norm_sum_list_le {p : ℕ} (ℓ : Fin p → (H →ₗ[ℂ] ℂ)) (x : Fin p → H) (y : Mx n) :
    ∀ L : List (ℂ × List (Mx n)),
      ‖∑ j, ℓ j (σ y ((L.map fun u => u.1 • Dw σ u.2 (x j)).sum))‖ ≤
        (L.map fun u => ‖u.1‖ * ‖∑ j, ℓ j (σ y (Dw σ u.2 (x j)))‖).sum
  | [] => by simp
  | u :: L => by
    simp only [List.map_cons, List.sum_cons, map_add (f := _), map_smul, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    refine (norm_add_le _ _).trans (add_le_add (le_of_eq (norm_mul _ _)) (norm_sum_list_le ℓ x y L))

theorem exists_rewrite : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ N : ℕ,
    ∃ S : List (List (Mx n)), Words (lieSet ε) S ∧ ∃ (m : List (List (Mx n)) → ℕ) (A : List (List (Mx n)) → ℝ),
    ∀ (p : ℕ) (ℓ : Fin p → (H →ₗ[ℂ] ℂ)) (x : Fin p → H), (∀ j, Sobolev₂ (lieSet ε) σ (ℓ j)) →
    (∀ j, IsKFin ε σ (x j)) → ∀ B : ℕ → ℝ,
    (∀ k (w : List (Mx n)), w.length ≤ k → (∀ X ∈ w, X ∈ lieSet ε ∧ Xᴴ = -X ∧ hs X ≤ 1) →
      ∀ y ∈ UJset ε, ‖∑ j, ℓ j (σ y (Dw σ w (x j)))‖ ≤ B k * (1 + hs y) ^ N) →
    ∃ (q : ℕ) (ℓ' : Fin q → (H →ₗ[ℂ] ℂ)) (x' : Fin q → H) (c : Fin q → ℝ),
      (∀ i, Sm ε σ (x' i)) ∧ (∀ i, 0 ≤ c i) ∧ (∀ i w, Sm ε σ w → ‖ℓ' i w‖ ≤ c i * sobNorm σ S w) ∧
      (∀ S', Words (lieSet ε) S' → ∑ i, c i * sobNorm σ S' (x' i) ≤ A S' * B (m S')) ∧
      ∀ y ∈ UJset ε, ∑ j, ℓ j (σ y (x j)) = ∑ i, ℓ' i (σ y (x' i)) := by
  intro _hHC hCW n ε H _ _ _ σ hstd N
  have hσ := hstd.1
  have hcb : CoefBound ε σ := GlobalTheory.TypeSum.coefBound_of_casselmanWallach hCW n ε H σ hstd
  obtain ⟨S, C, hS, hC, hM2⟩ := GlobalTheory.TypeSum.coefBound_two_finSum n ε H σ hstd hcb N
  obtain ⟨d, X, hX, hL1⟩ := GlobalTheory.TypeSum.TraceBound.trace_bound n ε H σ hstd
  have hL1' : ∀ T : List (List (Mx n)), ∃ (r : ℕ) (A : ℝ), Words (lieSet ε) T → ∀ (q : ℕ) (e : Fin q → H)
      (μ : Fin q → ℝ), Orthonormal ℂ e → (∀ i, IsKFin ε σ (e i)) → (∀ i, 1 ≤ μ i) →
      (∀ i, onePlusCas σ X (e i) = (μ i : ℂ) • e i) → ∑ i, sobNorm σ T (e i) ^ 2 / μ i ^ r ≤ A := by
    intro T
    by_cases hT : Words (lieSet ε) T
    · obtain ⟨r, A, h⟩ := hL1 T hT
      exact ⟨r, A, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hT⟩
  choose r A hrA using hL1'
  have hXl : ∀ i, X i ∈ lieSet ε := fun i => (hX i).1
  refine ⟨S, hS, fun S' => 2 * r (S ++ S'), fun S' => C * (1 + (d : ℝ)) ^ r (S ++ S') * max 0 (A (S ++ S')), ?_⟩
  intro p ℓ x hℓ hx B hB
  have hB0 : ∀ k, 0 ≤ B k := fun k => by
    have h := hB k [] (Nat.zero_le _) (by simp) 1 (one_mem_UJ ε)
    have hp : (0 : ℝ) < (1 + hs (1 : Mx n)) ^ N := pow_pos (by linarith [hs_nonneg (1 : Mx n)]) _
    exact (mul_nonneg_iff_of_pos_right hp).1 ((norm_nonneg _).trans h)
  obtain ⟨q, e, μ, he, heK, hμ, heig, hexp⟩ :=
    GlobalTheory.TypeSum.EigenSpan.exists_orthonormal_eigen n ε H σ hstd d X (fun i => ⟨(hX i).1, (hX i).2.1⟩) p x hx
  have heS : ∀ i, Sm ε σ (e i) := fun i => hstd.2.2.1 _ (heK i)
  have hxS : ∀ j, Sm ε σ (x j) := fun j => hstd.2.2.1 _ (hx j)
  have hμ0 : ∀ i (t : ℕ), 0 < μ i ^ t := fun i t => pow_pos (by linarith [hμ i]) t
  have hd0 : (0 : ℝ) ≤ 1 + (d : ℝ) := by positivity
  have key : ∀ (t : ℕ) (i : Fin q) (w : H), Sm ε σ w →
      ‖∑ j, ⟪e i, x j⟫_ℂ * ℓ j w‖ ≤
        C * ((1 + (d : ℝ)) ^ t * B (2 * t)) * sobNorm σ S (e i) * sobNorm σ S w / μ i ^ t := by
    intro t i w hw
    obtain ⟨L, hL1, hL2, hL3⟩ := GlobalTheory.TypeSum.caspow_expand n ε H σ hσ d X hXl t
    have hxt : ∀ j, Sm ε σ ((onePlusCas σ X)^[t] (x j)) := fun j => sm_iterate_onePlusCas hσ hXl (hxS j) t
    have hM : 0 ≤ (1 + (d : ℝ)) ^ t * B (2 * t) := mul_nonneg (pow_nonneg hd0 _) (hB0 _)
    have hgrow : ∀ y ∈ UJset ε, ‖∑ j, ℓ j (σ y ((onePlusCas σ X)^[t] (x j)))‖ ≤
        (1 + (d : ℝ)) ^ t * B (2 * t) * (1 + hs y) ^ N := by
      intro y hy
      have e1 : ∀ j, (onePlusCas σ X)^[t] (x j) = (L.map fun u => u.1 • Dw σ u.2 (x j)).sum :=
        fun j => hL3 _ (hxS j)
      simp only [e1]
      refine (norm_sum_list_le ℓ x y L).trans ?_
      have hw0 : 0 ≤ B (2 * t) * (1 + hs y) ^ N :=
        mul_nonneg (hB0 _) (pow_nonneg (by linarith [hs_nonneg y]) _)
      calc (L.map fun u => ‖u.1‖ * ‖∑ j, ℓ j (σ y (Dw σ u.2 (x j)))‖).sum
          ≤ (L.map fun u => ‖u.1‖ * (B (2 * t) * (1 + hs y) ^ N)).sum := by
            refine List.sum_le_sum fun u hu => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            refine hB (2 * t) u.2 (hL1 u hu).1 (fun Y hY => ?_) y hy
            obtain ⟨i, rfl⟩ := (hL1 u hu).2 Y hY
            exact hX i
        _ = (L.map fun u => ‖u.1‖).sum * (B (2 * t) * (1 + hs y) ^ N) := List.sum_map_mul_right _ _ _
        _ ≤ (1 + (d : ℝ)) ^ t * (B (2 * t) * (1 + hs y) ^ N) := mul_le_mul_of_nonneg_right hL2 hw0
        _ = _ := by ring
    have h2 := hM2 p ℓ _ hℓ hxt _ hM hgrow (e i) w (heS i) hw
    have e2 : ∀ j, ⟪e i, (onePlusCas σ X)^[t] (x j)⟫_ℂ = ((μ i : ℂ) ^ t) * ⟪e i, x j⟫_ℂ := fun j => by
      rw [inner_iterate_onePlusCas hσ hXl (heS i) (hxS j),
        iterate_onePlusCas_of_eq hσ hXl (heS i) (heig i), inner_smul_left]
      congr 1
      rw [← Complex.ofReal_pow, Complex.conj_ofReal]
    simp only [e2, mul_assoc, ← Finset.mul_sum] at h2
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith [hμ i])] at h2
    rw [le_div_iff₀ (hμ0 i t)]
    have hc := mul_comm (‖∑ j, ⟪e i, x j⟫_ℂ * ℓ j w‖) (μ i ^ t)
    linarith
  have hterm : ∀ (i : Fin q) (t : ℕ), 0 ≤ C * ((1 + (d : ℝ)) ^ t * B (2 * t)) * sobNorm σ S (e i) / μ i ^ t :=
    fun i t => div_nonneg (mul_nonneg (mul_nonneg hC (mul_nonneg (pow_nonneg hd0 _) (hB0 _)))
      (sobNorm_nonneg σ S _)) (hμ0 i t).le
  have hbdd : ∀ i : Fin q, BddBelow (Set.range fun t : ℕ =>
      C * ((1 + (d : ℝ)) ^ t * B (2 * t)) * sobNorm σ S (e i) / μ i ^ t) :=
    fun i => ⟨0, by rintro _ ⟨t, rfl⟩; exact hterm i t⟩
  refine ⟨q, fun i => ∑ j, ⟪e i, x j⟫_ℂ • ℓ j, e,
    fun i => ⨅ t : ℕ, C * ((1 + (d : ℝ)) ^ t * B (2 * t)) * sobNorm σ S (e i) / μ i ^ t,
    heS, fun i => le_ciInf fun t => hterm i t, ?_, ?_, ?_⟩
  · intro i w hw
    have e3 : (∑ j, ⟪e i, x j⟫_ℂ • ℓ j) w = ∑ j, ⟪e i, x j⟫_ℂ * ℓ j w := by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [e3, mul_comm, Real.mul_iInf_of_nonneg (sobNorm_nonneg σ S w)]
    refine le_ciInf fun t => (key t i w hw).trans (le_of_eq ?_)
    ring
  · intro S' hS'
    have hW : Words (lieSet ε) (S ++ S') := words_append hS hS'
    have hA := hrA (S ++ S') hW q e μ he heK hμ heig
    set r₀ := r (S ++ S')
    have hK0 : 0 ≤ C * ((1 + (d : ℝ)) ^ r₀ * B (2 * r₀)) :=
      mul_nonneg hC (mul_nonneg (pow_nonneg hd0 _) (hB0 _))
    calc ∑ i, (⨅ t : ℕ, C * ((1 + (d : ℝ)) ^ t * B (2 * t)) * sobNorm σ S (e i) / μ i ^ t) * sobNorm σ S' (e i)
        ≤ ∑ i, C * ((1 + (d : ℝ)) ^ r₀ * B (2 * r₀)) * sobNorm σ S (e i) / μ i ^ r₀ * sobNorm σ S' (e i) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (ciInf_le (hbdd i) r₀) (sobNorm_nonneg σ S' _)
      _ ≤ ∑ i, C * ((1 + (d : ℝ)) ^ r₀ * B (2 * r₀)) * (sobNorm σ (S ++ S') (e i) ^ 2 / μ i ^ r₀) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have a0 := sobNorm_nonneg σ S (e i)
          have b0 := sobNorm_nonneg σ S' (e i)
          have hab : sobNorm σ S (e i) * sobNorm σ S' (e i) ≤ sobNorm σ (S ++ S') (e i) ^ 2 := by
            rw [sobNorm_append]; nlinarith
          have hm := hμ0 i r₀
          calc C * ((1 + (d : ℝ)) ^ r₀ * B (2 * r₀)) * sobNorm σ S (e i) / μ i ^ r₀ * sobNorm σ S' (e i)
              = C * ((1 + (d : ℝ)) ^ r₀ * B (2 * r₀)) * (sobNorm σ S (e i) * sobNorm σ S' (e i) / μ i ^ r₀) := by
                ring
            _ ≤ _ := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hab hm.le) hK0
      _ = C * ((1 + (d : ℝ)) ^ r₀ * B (2 * r₀)) * ∑ i, sobNorm σ (S ++ S') (e i) ^ 2 / μ i ^ r₀ := by
          rw [Finset.mul_sum]
      _ ≤ C * ((1 + (d : ℝ)) ^ r₀ * B (2 * r₀)) * max 0 (A (S ++ S')) :=
          mul_le_mul_of_nonneg_left (hA.trans (le_max_right _ _)) hK0
      _ = C * (1 + (d : ℝ)) ^ r (S ++ S') * max 0 (A (S ++ S')) * B (2 * r (S ++ S')) := by ring
  · intro y _
    have h1 : ∀ j, ℓ j (σ y (x j)) = ∑ i, ⟪e i, x j⟫_ℂ * ℓ j (σ y (e i)) := fun j => by
      conv_lhs => rw [hexp j]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, smul_eq_mul]
    simp only [h1, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    exact Finset.sum_comm

end GlobalTheory.TypeSum.CoefRep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.HilbertSchmidtCompactUnitarySubOneLeFourMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

namespace GlobalTheory.HsLe

theorem hs_toMK_sub_one_le {n : ℕ} (ε : Fin n → Bool) (k : KG ε) :
    Formalism.REAL.hs (toMK k - 1) ≤ 4 * (n : ℝ) := by
  have hu : toMK k ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := k.2.1
  have hcol : ∀ j : Fin n, ∑ i, ‖toMK k i j‖ ^ 2 = 1 := by
    intro j
    have hm : star (toMK k) * toMK k = 1 := Matrix.mem_unitaryGroup_iff'.1 hu
    have h1 : (star (toMK k) * toMK k) j j = (1 : Matrix (Fin n) (Fin n) ℂ) j j := by rw [hm]
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
    have h2 : ((∑ i, ‖toMK k i j‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← h1]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.star_apply, ← Complex.conj_mul']
      rfl
    exact_mod_cast h2
  have hsum : ∑ i, ∑ j, ‖toMK k i j‖ ^ 2 = (n : ℝ) := by
    rw [Finset.sum_comm]
    simp [hcol]
  have hone : ∑ i : Fin n, ∑ j : Fin n, ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 = (n : ℝ) := by
    have : ∀ i j : Fin n, ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 = if i = j then 1 else 0 := by
      intro i j
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    simp only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  have key : ∀ a b : ℂ, ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    intro a b
    have h := norm_sub_le a b
    nlinarith [norm_nonneg (a - b), norm_nonneg a, norm_nonneg b, sq_nonneg (‖a‖ - ‖b‖)]
  unfold Formalism.REAL.hs
  calc ∑ i, ∑ j, ‖(toMK k - 1) i j‖ ^ 2
      ≤ ∑ i, ∑ j, (2 * ‖toMK k i j‖ ^ 2 + 2 * ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [Matrix.sub_apply]
        exact key _ _
    _ = 2 * ∑ i, ∑ j, ‖toMK k i j‖ ^ 2 + 2 * ∑ i : Fin n, ∑ j : Fin n, ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ = 4 * (n : ℝ) := by rw [hsum, hone]; ring

end GlobalTheory.HsLe
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.IInfLeOfCombBound
section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.RunJoin

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

theorem iInf_le_of_combBound {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hjm : D.R.m ≤ j)
    {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPJ h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (cb : ℝ)
    (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ)
    (hspan : @Submodule.span (𝓞 (recB h.toLawsCore).KO) _ _ _ (WeightFamilies.Prov.modOC (recB h.toLawsCore) j wL)
      (Set.range G.w) = (recPJ h j hj).WWc S.sW wL)
    (hX : CombBound G S cb nus) :
    ∀ la, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la, (⨅ k, v (G.w k).1) ≤ (nus la : EReal) := by
  rintro la _ ⟨y0, rfl⟩
  obtain ⟨y, hy⟩ := pt_realise h j hj la y0
  have hv : ∀ w (F : (recB h.toLawsCore).Cusp j w),
      (recPJ h j hj).vAt la y ((recPJ h j hj).inc w F) = vAtV y0 F.1 := fun w F => by
    rw [recPJ_vAt_inc, hy]
  have hd : (recPJ h j hj).depth S.sW wL la y = ⨅ k, vAtV y0 (G.w k).1 := by
    unfold PJ.depth
    rw [← hspan, iInf_span_eq (X := recPJ h j hj) G.w la ((recPJ h j hj).vAt la y)
      ((recPJ h j hj).vAt_zero la y) ((recPJ h j hj).vAt_add la y) ((recPJ h j hj).vAt_smul la y)
      (fun _ ha => vAdd_int_nonneg la ha)]
    simp only [hv]
  have h1 := (hX la y).2 hjm
  rw [hd] at h1
  exact h1

theorem combAlg_of_tiedW : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (ka wL wF : WeightFamilies.Wt D j) (S : Scal (recB h.toLawsCore)) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (G : GlobalFamilyData (recPJ h j hj) ka wL wF) (c Gc Prw : ℝ), G.TiedW S Gc Prw → CombBound G S c nus → (j < D.R.m → CombAlg (T.Q.Xo j) T.Q.c (fun k => (G.w k).1) G.et.1 nus (c / (2 * (G.iet : ℝ)))) ∧ (j = D.R.m → ∀ la, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la, (⨅ k, v (G.w k).1) ≤ (nus la : EReal)) := by
  intro D T h j hj ka wL wF S nus G c Gc Prw hW hX
  exact ⟨fun hjm => combAlg_of_combBound h j hj hjm G S c nus hW.1 hX,
    fun hjm => iInf_le_of_combBound h j hj hjm.ge G S c nus hW.1 hX⟩

end GlobalTheory.RunJoin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.PairingConvolutionSwapStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory GlobalTheory.KFourier

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_star_mul_convolution_eq_integral_swap : ∀ {n : ℕ} (ε : Fin n → Bool) (e q g : KG ε → ℂ), Continuous e → Continuous q → Continuous g → ∫ k', star (q k') * ∫ k, e k * g (k' * k) ∂(muK ε) ∂(muK ε) = ∫ y, g y * ∫ x, e x * star (q (y * x⁻¹)) ∂(muK ε) ∂(muK ε) := by
  first | exact @GlobalTheory.KFourier.pairing_convolution_swap | exact GlobalTheory.KFourier.pairing_convolution_swap | (intros; apply GlobalTheory.KFourier.pairing_convolution_swap <;> assumption)
end

