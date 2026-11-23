module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0073
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0051
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0068
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0052
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0055
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0066
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0057
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0072
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0070
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0069

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.CoeffEqZeroOfForallEvalEqZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

theorem exists_shift_coeff (N : ℕ) (a : ℂ) :
    ∃ K : Fin N → Fin N → ℂ, ∀ (c : Fin N → ℂ) (t : ℂ),
      ∑ j : Fin N, c j * (t + a) ^ (j : ℕ) =
        ∑ i : Fin N, (∑ j : Fin N, c j * K i j) * t ^ (i : ℕ) := by
  refine ⟨fun i j => a ^ ((j : ℕ) - i) * ((j : ℕ).choose i : ℂ), fun c t => ?_⟩
  have hj : ∀ j : Fin N, (t + a) ^ (j : ℕ) =
      ∑ i : Fin N, t ^ (i : ℕ) * (a ^ ((j : ℕ) - i) * ((j : ℕ).choose i : ℂ)) := by
    intro j
    have hr := Fin.sum_univ_eq_sum_range (fun i => t ^ i * (a ^ ((j : ℕ) - i) * ((j : ℕ).choose i : ℂ))) N
    rw [hr, add_pow]
    rw [← Finset.sum_subset (Finset.range_subset_range.2 (show (j : ℕ) + 1 ≤ N by omega))]
    · exact Finset.sum_congr rfl fun i _ => by ring
    · intro i _ hi
      simp only [Finset.mem_range, not_lt] at hi
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
  simp_rw [hj, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem exists_monic_shift_coeff (N : ℕ) (a : ℂ) :
    ∃ (K₀ : Fin N → ℂ) (K : Fin N → Fin N → ℂ), ∀ (c : Fin N → ℂ) (t : ℂ),
      (t + a) ^ N + ∑ j : Fin N, c j * (t + a) ^ (j : ℕ) =
        t ^ N + ∑ i : Fin N, (K₀ i + ∑ j : Fin N, c j * K i j) * t ^ (i : ℕ) := by
  obtain ⟨K, hK⟩ := exists_shift_coeff N a
  refine ⟨fun i => a ^ (N - (i : ℕ)) * (N.choose i : ℂ), K, fun c t => ?_⟩
  have hr := Fin.sum_univ_eq_sum_range (fun i => a ^ (N - i) * (N.choose i : ℂ) * t ^ i) N
  rw [hK, add_pow, Finset.sum_range_succ]
  simp only [add_mul, Finset.sum_add_distrib, hr, Nat.sub_self, pow_zero, Nat.choose_self,
    Nat.cast_one, mul_one]
  have : ∑ x ∈ Finset.range N, t ^ x * a ^ (N - x) * (N.choose x : ℂ) =
      ∑ x ∈ Finset.range N, a ^ (N - x) * (N.choose x : ℂ) * t ^ x :=
    Finset.sum_congr rfl fun _ _ => by ring
  rw [this]
  ring

theorem coeff_eq_zero_of_forall_eval_eq_zero {N : ℕ} (e : Fin N → ℂ)
    (he : ∀ t : ℂ, ∑ i : Fin N, e i * t ^ (i : ℕ) = 0) (i : Fin N) : e i = 0 := by
  classical
  have hp : (∑ j : Fin N, Polynomial.C (e j) * Polynomial.X ^ (j : ℕ)) = 0 :=
    Polynomial.funext fun t => by simpa [Polynomial.eval_finsetSum] using he t
  have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p i) hp
  simpa [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Fin.val_inj] using this

theorem analyticAt_coord {ι : Type} [Fintype ι] (i : ι) (z : ι → ℂ) :
    AnalyticAt ℂ (fun w : ι → ℂ => w i) z :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i).analyticAt z

theorem weierstrassDivision_in_coordinate (h : WeierstrassPolynomialDivision.Statement)
    {σ : Type} [Fintype σ] [DecidableEq σ] (k : σ) (d : ℕ) (y₀ : Fin d → ℂ) (u₀ : σ → ℂ) (N : ℕ)
    (b : Fin N → (Fin d → ℂ) → ℂ) (f : (Fin d → ℂ) × (σ → ℂ) → ℂ)
    (hb : ∀ j, AnalyticAt ℂ (b j) y₀)
    (hG : ∀ T : ℂ, T ^ N + ∑ j, b j y₀ * T ^ (j : ℕ) = (T - u₀ k) ^ N)
    (hf : AnalyticAt ℂ f (y₀, u₀)) :
    ∃ (q : (Fin d → ℂ) × (σ → ℂ) → ℂ) (e : Fin N → (Fin d → ℂ) × ({m // m ≠ k} → ℂ) → ℂ),
      AnalyticAt ℂ q (y₀, u₀) ∧ (∀ i, AnalyticAt ℂ (e i) (y₀, fun m => u₀ m)) ∧
      ∀ᶠ x in 𝓝 (y₀, u₀), f x = q x * (x.2 k ^ N + ∑ j, b j x.1 * x.2 k ^ (j : ℕ)) +
        ∑ i, e i (x.1, fun m => x.2 m) * x.2 k ^ (i : ℕ) := by
  obtain ⟨K₀, K, hK⟩ := exists_monic_shift_coeff N (u₀ k)
  obtain ⟨K', hK'⟩ := exists_shift_coeff N (-u₀ k)

  let ι : σ → Option (Fin d ⊕ {m // m ≠ k}) := fun m =>
    if hm : m = k then none else some (Sum.inr ⟨m, hm⟩)

  let φ : (Option (Fin d ⊕ {m // m ≠ k}) → ℂ) → (Fin d → ℂ) × (σ → ℂ) := fun z =>
    (fun i => y₀ i + z (some (Sum.inl i)), fun m => u₀ m + z (ι m))

  let ψ' : (Fin d → ℂ) × ({m // m ≠ k} → ℂ) → (Fin d ⊕ {m // m ≠ k} → ℂ) := fun x' l =>
    Sum.elim (fun i => x'.1 i - y₀ i) (fun m => x'.2 m - u₀ m) l
  let ψ : (Fin d → ℂ) × (σ → ℂ) → (Option (Fin d ⊕ {m // m ≠ k}) → ℂ) := fun x o =>
    Option.elim o (x.2 k - u₀ k) (ψ' (x.1, fun m => x.2 m))

  let c : Fin N → (Fin d ⊕ {m // m ≠ k} → ℂ) → ℂ := fun i w =>
    K₀ i + ∑ j, b j (fun l => y₀ l + w (Sum.inl l)) * K i j
  have hc_an : ∀ i, AnalyticAt ℂ (c i) 0 := by
    intro i
    have hy : AnalyticAt ℂ (fun w : Fin d ⊕ {m // m ≠ k} → ℂ => fun l => y₀ l + w (Sum.inl l)) 0 :=
      AnalyticAt.pi (f := fun l (w : Fin d ⊕ {m // m ≠ k} → ℂ) => y₀ l + w (Sum.inl l)) fun l =>
        analyticAt_const.add (analyticAt_coord (Sum.inl l) 0)
    have hb' : ∀ j, AnalyticAt ℂ (fun w : Fin d ⊕ {m // m ≠ k} → ℂ => b j (fun l => y₀ l + w (Sum.inl l))) 0 := by
      intro j
      refine (hb j).comp_of_eq hy ?_
      funext l; simp
    exact analyticAt_const.add (Finset.analyticAt_fun_sum _ fun j _ => (hb' j).fun_mul analyticAt_const)
  have hc0 : ∀ i, c i 0 = 0 := by
    refine coeff_eq_zero_of_forall_eval_eq_zero (fun i => c i 0) fun t => ?_
    have h1 := hK (fun j => b j y₀) t
    have h2 := hG (t + u₀ k)
    have hy : (fun l => y₀ l + (0 : Fin d ⊕ {m // m ≠ k} → ℂ) (Sum.inl l)) = y₀ := by funext l; simp
    simp only [c, hy]
    rw [add_sub_cancel_right] at h2
    linear_combination h1.symm.trans h2
  have hφ : AnalyticAt ℂ φ 0 :=
    (AnalyticAt.pi (f := fun i (z : Option (Fin d ⊕ {m // m ≠ k}) → ℂ) => y₀ i + z (some (Sum.inl i))) fun i =>
      analyticAt_const.add (analyticAt_coord _ 0)).prod
    (AnalyticAt.pi (f := fun m (z : Option (Fin d ⊕ {m // m ≠ k}) → ℂ) => u₀ m + z (ι m)) fun m => analyticAt_const.add (analyticAt_coord _ 0))
  have hφ0 : φ 0 = (y₀, u₀) := by
    simp [φ]
  have hφψ : ∀ x, φ (ψ x) = x := by
    intro x
    refine Prod.ext (funext fun i => ?_) (funext fun m => ?_)
    · simp [φ, ψ, ψ']
    · by_cases hm : m = k
      · subst hm; simp [φ, ψ, ι]
      · simp [φ, ψ, ψ', ι, hm]
  have hψ' : AnalyticAt ℂ ψ' (y₀, fun m => u₀ m) := by
    rw [analyticAt_pi_iff]
    intro l
    cases l with
    | inl i => exact ((analyticAt_coord i _).comp analyticAt_fst).sub analyticAt_const
    | inr m => exact ((analyticAt_coord m _).comp analyticAt_snd).sub analyticAt_const
  have hψ'0 : ψ' (y₀, fun m => u₀ m) = 0 := by
    funext l; cases l <;> simp [ψ']
  have hπ : AnalyticAt ℂ (fun x : (Fin d → ℂ) × (σ → ℂ) => (x.1, fun m : {m // m ≠ k} => x.2 m)) (y₀, u₀) :=
    analyticAt_fst.prod (AnalyticAt.pi (f := fun (m : {m // m ≠ k}) (x : (Fin d → ℂ) × (σ → ℂ)) => x.2 m) fun m =>
      (analyticAt_coord _ _).comp analyticAt_snd)
  have hψ : AnalyticAt ℂ ψ (y₀, u₀) := by
    rw [analyticAt_pi_iff]
    intro o
    cases o with
    | none => exact ((analyticAt_coord k _).comp analyticAt_snd).sub analyticAt_const
    | some l => exact (analyticAt_coord l _).comp (hψ'.comp_of_eq hπ rfl)
  have hψ0 : ψ (y₀, u₀) = 0 := by
    funext o; cases o with
    | none => simp [ψ]
    | some l => simp only [ψ, Option.elim_some]; exact congrFun hψ'0 l
  have hg : AnalyticAt ℂ (f ∘ φ) 0 := hf.comp_of_eq hφ hφ0
  obtain ⟨q, a, hq, ha, hev⟩ := h _ N c (f ∘ φ) hc_an hc0 hg
  refine ⟨q ∘ ψ, fun i x' => ∑ j, a j (ψ' x') * K' i j, hq.comp_of_eq hψ hψ0, fun i => ?_, ?_⟩
  · exact Finset.analyticAt_fun_sum _ fun j _ => ((ha j).comp_of_eq hψ' hψ'0).fun_mul analyticAt_const
  · have ht : Tendsto ψ (𝓝 (y₀, u₀)) (𝓝 0) := hψ0 ▸ hψ.continuousAt.tendsto
    filter_upwards [ht.eventually hev] with x hx
    rw [Function.comp_apply, hφψ] at hx
    rw [hx]
    have hy : (fun l => y₀ l + ψ x (some (Sum.inl l))) = x.1 := by funext l; simp [ψ, ψ']
    have hc' : ∀ i, c i (fun l => ψ x (some l)) = K₀ i + ∑ j, b j x.1 * K i j := by
      intro i; simp only [c]; rw [hy]
    have h1 := hK (fun j => b j x.1) (x.2 k - u₀ k)
    rw [sub_add_cancel] at h1
    have hn : ψ x none = x.2 k - u₀ k := rfl
    have hw : weierstrassPolynomial c (ψ x) = x.2 k ^ N + ∑ j, b j x.1 * x.2 k ^ (j : ℕ) := by
      unfold weierstrassPolynomial
      simp only [hc', hn]
      exact h1.symm
    have hr := hK' (fun j => a j (ψ' (x.1, fun m => x.2 m))) (x.2 k)
    rw [← sub_eq_add_neg] at hr
    rw [hw, Function.comp_apply, ← hr]
    rfl

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchProperAtPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

theorem BranchProperAtPoint.proof (hrim : BranchAwayFromRim.Statement) :
    BranchProperAtPoint.Statement := by
  intro n k J u p x m γ hJ hdim hu hcov hdisj b s hs hsx P hP
  obtain ⟨ε₀, hε₀, ρ, hρ, hrimb⟩ := hrim n k J u p x m γ hJ hdim hu hcov hdisj b
  obtain ⟨P', hP'P, hP'o, hsP'⟩ := mem_nhds_iff.mp hP
  set K : Set (Fin k → ℂ) := Metric.closedBall 0 ρ \ P' with hK
  have hKc : IsCompact K := (isCompact_closedBall 0 ρ).diff hP'o
  have hKD : K ⊆ Metric.ball 0 (γ b).radius := fun τ hτ =>
    mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hτ.1) hρ)
  have hcont : ContinuousOn (γ b).toFun K := (γ b).differentiableOn.continuousOn.mono hKD
  have hxK : x ∉ (γ b).toFun '' K := by
    rintro ⟨τ, hτK, hτx⟩
    have hτs : τ = s := (γ b).injOn (hKD hτK) hs (hτx.trans hsx.symm)
    exact hτK.2 (hτs ▸ hsP')
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.isOpen_iff.mp (hKc.image_of_continuousOn hcont).isClosed.isOpen_compl x hxK
  refine ⟨min ε₀ δ, lt_min hε₀ hδ, fun τ hτ hfτ => ?_⟩
  have h1 : ‖τ‖ ≤ ρ := hrimb τ hτ (Metric.ball_subset_ball (min_le_left _ _) hfτ)
  by_contra hτP
  have hτK : τ ∈ K := ⟨mem_closedBall_zero_iff.mpr h1, fun h => hτP (hP'P h)⟩
  exact hball (Metric.ball_subset_ball (min_le_right _ _) hfτ) ⟨τ, hτK, rfl⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchSheetAE
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

namespace BranchSheetAE

variable {d : ℕ}

theorem volume_preimage_null {G : Set (Fin d → ℂ)} {F : (Fin d → ℂ) → Fin d → ℂ} (hG : IsOpen G)
    (hF : DifferentiableOn ℂ F G) (hdet : ∀ w ∈ G, (ReciprocityTheory.AnForm.A.jacC F w).det ≠ 0)
    {N : Set (Fin d → ℂ)} (hN : volume N = 0) :
    volume {t | t ∈ G ∧ F t ∈ N} = 0 := by
  have hFa := SheetOnlyNull.analyticOnNhd_of_differentiableOn hG hF
  have hequiv : ∀ w ∈ G, ∃ e : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ),
      HasStrictFDerivAt F (e : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) w := by
    intro w hw
    have hinj : Function.Injective (fderiv ℂ F w) :=
      (SheetOnlyNull.injective_iff_det_ne_zero _).2 (by rw [← ReciprocityTheory.AnForm.A.det_jacC]; exact hdet w hw)
    refine ⟨(LinearEquiv.ofInjectiveEndo _ hinj).toContinuousLinearEquiv, ?_⟩
    exact (hFa w hw).hasStrictFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)
  apply measure_null_of_locally_null
  rintro x ⟨hxG, -⟩
  obtain ⟨e, he⟩ := hequiv x hxG
  set φ := he.toOpenPartialHomeomorph F with hφdef
  have hφ : ∀ w, φ w = F w := fun w => by rw [hφdef, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
  have hsymd : DifferentiableOn ℝ φ.symm (φ.target ∩ φ.symm ⁻¹' G) := by
    rintro z ⟨hzT, hzG⟩
    obtain ⟨e', he'⟩ := hequiv _ hzG
    have hd : HasFDerivAt φ.symm _ z :=
      φ.hasFDerivAt_symm hzT (f' := e') (by
        have : (φ : (Fin d → ℂ) → Fin d → ℂ) = F := funext hφ
        rw [this]; exact he'.hasFDerivAt)
    exact (hd.differentiableAt.restrictScalars ℝ).differentiableWithinAt
  refine ⟨{t | t ∈ G ∧ F t ∈ N} ∩ φ.source,
    inter_mem_nhdsWithin _ (φ.open_source.mem_nhds he.mem_toOpenPartialHomeomorph_source), ?_⟩
  refine measure_mono_null ?_ (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    (μ := volume) (hsymd.mono Set.inter_subset_left) (measure_mono_null Set.inter_subset_right hN))
  rintro t ⟨⟨htG, htN⟩, hts⟩
  refine ⟨φ t, ⟨⟨φ.map_source hts, ?_⟩, ?_⟩, φ.left_inv hts⟩
  · show φ.symm (φ t) ∈ G
    rw [φ.left_inv hts]; exact htG
  · rw [hφ]; exact htN

end BranchSheetAE

theorem BranchSheetAE.proof (h₁ : IndefiniteRowSideFullHecke.ComplexSets.RankDeficientFibreInfinite.Statement)
    (h₂ : ComplexSets.FibreBound.Statement) (h₃ : DiscriminantSheetCover.Statement) :
    BranchSheetAE.Statement := by
  intro n d J A p γ hJ hdim hA
  set Δ := Metric.ball (0 : Fin d → ℂ) γ.radius with hΔ
  set τ : (Fin d → ℂ) → Fin d → ℂ := fun t => A *ᵥ γ.toFun t with hτdef
  have hΔo : IsOpen Δ := Metric.isOpen_ball
  have hτd : DifferentiableOn ℂ τ Δ := SheetOnlyNull.differentiableOn_mulVec A γ.differentiableOn
  have hdeta := SheetOnlyNull.analyticOnNhd_det_jacC hΔo hτd
  have hne : ∃ z ∈ Δ, (ReciprocityTheory.AnForm.A.jacC τ z).det ≠ 0 := by
    by_contra hall
    push Not at hall
    obtain ⟨y, hy⟩ := h₁ d d Δ τ hΔo ⟨0, Metric.mem_ball_self γ.radius_pos⟩ hτd fun v hv hinj =>
      (SheetOnlyNull.injective_iff_det_ne_zero _).1 hinj
        (by rw [← ReciprocityTheory.AnForm.A.det_jacC]; exact hall v hv)
    have hinf : (γ.toFun '' {t | t ∈ Δ ∧ τ t = y}).Infinite :=
      (Set.infinite_image_iff (γ.injOn.mono fun t (ht : t ∈ {t | t ∈ Δ ∧ τ t = y}) => ht.1)).2 hy
    refine hinf ((h₂ n d J A hJ hdim hA y).2.1.subset ?_)
    rintro _ ⟨t, ⟨htΔ, hty⟩, rfl⟩
    exact ⟨γ.mapsTo htΔ, hty⟩
  have hZ := ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd hΔo (convex_ball _ _).isPreconnected
    hdeta hne
  obtain ⟨P, U, D, N, s, -, hUD, -, -, hnull, hfib⟩ := h₃ n d J A hJ hdim hA
  set G := Δ ∩ (fun t => (ReciprocityTheory.AnForm.A.jacC τ t).det) ⁻¹' {0}ᶜ with hGdef
  have hG : IsOpen G := hdeta.continuousOn.isOpen_inter_preimage hΔo isOpen_compl_singleton
  have hS := BranchSheetAE.volume_preimage_null hG (hτd.mono Set.inter_subset_left)
    (fun w hw => hw.2) hnull
  rw [ae_restrict_iff' hΔo.measurableSet, ae_iff]
  refine measure_mono_null ?_ (measure_union_null hZ hS)
  intro t ht
  simp only [Set.mem_ofPred_eq, Classical.not_imp] at ht
  obtain ⟨htΔ, hno⟩ := ht
  by_cases hdt : (ReciprocityTheory.AnForm.A.jacC τ t).det = 0
  · exact Or.inl ⟨htΔ, hdt⟩
  refine Or.inr ⟨⟨htΔ, hdt⟩, fun hD => hno ?_⟩
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hD
  obtain ⟨hfibk, -, hsh⟩ := hfib k (τ t) ((hUD k).2.2.1 hk)
  have hmem : γ.toFun t ∈ fibre J A (τ t) := ⟨γ.mapsTo htΔ, rfl⟩
  rw [hfibk] at hmem
  obtain ⟨j, hj⟩ := hmem
  exact ⟨s k j, hj ▸ hsh j⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PChartMassCompare
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

open scoped ENNReal

noncomputable section

theorem ChartMassCompare.proof (h1 : SheetComass.Statement) (h2 : SheetAreaCompare.Statement) :
    ChartMassCompare.Statement := by
  intro n d J A φ R hJ hdim hA hφ
  obtain ⟨C, hC⟩ := h1 n d J A φ R hφ
  obtain ⟨c, hc, hca⟩ := h2 n d J A
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set B := Metric.closedBall (0 : Fin n → ℂ) R
  refine ⟨ENNReal.ofReal C' * c, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hc, fun g hg => ?_⟩
  set gB := B.indicator g with hgBdef
  have hgB : Measurable gB := hg.indicator measurableSet_closedBall

  have hpt : ∀ y, chartAbsDens J A gB φ y ≤
      C' * sheetSum J A (fun x s => |gB x| * sheetJac s (A *ᵥ x)) y := by
    intro y
    have hfin := (ComplexSets.FibreBound.proof n d J A hJ hdim hA y).2.1
    unfold chartAbsDens sheetSum
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun x hx => ?_
    have hxf : x ∈ fibre J A y := hfin.mem_toFinset.mp hx
    split_ifs with hs
    · dsimp only
      rw [← hxf.2]
      by_cases hxB : x ∈ B
      · have hb := hC x ⟨hxf.1, hxB⟩ _ hs.choose_spec
        rw [abs_mul]
        calc |gB x| * |ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ hs.choose) (A *ᵥ x)|
            ≤ |gB x| * (C' * sheetJac hs.choose (A *ᵥ x)) :=
              mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
                (sheetJac_nonneg _ _))) (abs_nonneg _)
          _ = C' * (|gB x| * sheetJac hs.choose (A *ᵥ x)) := by ring
      · simp [gB, hxB]
    · simp
  have hnn : ∀ y, 0 ≤ chartAbsDens J A gB φ y := fun y =>
    finsum_nonneg fun x => finsum_nonneg fun _ => by split_ifs; exacts [abs_nonneg _, le_rfl]
  calc ∫⁻ y, ‖chartAbsDens J A gB φ y‖ₑ
      ≤ ∫⁻ y, ENNReal.ofReal C' * ‖sheetSum J A (fun x s => |gB x| * sheetJac s (A *ᵥ x)) y‖ₑ := by
        refine lintegral_mono fun y => ?_
        rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_of_nonneg (hnn y),
          ← ENNReal.ofReal_mul hC'0]
        exact ENNReal.ofReal_le_ofReal ((hpt y).trans
          (mul_le_mul_of_nonneg_left (le_abs_self _) hC'0))
    _ = ENNReal.ofReal C' * ∫⁻ y, ‖sheetSum J A (fun x s => |gB x| * sheetJac s (A *ᵥ x)) y‖ₑ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C' * (c * ∫⁻ z in zeroSetEuc J, ‖gB (WithLp.ofLp z)‖ₑ
          ∂(μH[((2 * d : ℕ) : ℝ)])) := by gcongr; exact hca gB hgB
    _ = ENNReal.ofReal C' * c * ∫⁻ z in zeroSetEuc J ∩ {z | WithLp.ofLp z ∈ B},
          ‖g (WithLp.ofLp z)‖ₑ ∂(μH[((2 * d : ℕ) : ℝ)]) := by
        have hT : MeasurableSet {z : EuclideanSpace ℂ (Fin n) | WithLp.ofLp z ∈ B} :=
          measurableSet_closedBall.preimage (PiLp.continuous_ofLp 2 _).measurable
        have hfun : (fun z : EuclideanSpace ℂ (Fin n) => ‖gB (WithLp.ofLp z)‖ₑ) =
            {z : EuclideanSpace ℂ (Fin n) | WithLp.ofLp z ∈ B}.indicator
              (fun z => ‖g (WithLp.ofLp z)‖ₑ) := by
          ext z
          by_cases hz : WithLp.ofLp z ∈ B <;> simp [gB, hz, Set.indicator]
        rw [hfun, lintegral_indicator hT, Measure.restrict_restrict hT, Set.inter_comm, mul_assoc]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOff
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

theorem abs_finsum_le_finsum_abs {α : Type*} (f : α → ℝ) : |∑ᶠ i, f i| ≤ ∑ᶠ i, |f i| := by
  by_cases h : (Function.support f).Finite
  · have hs : Function.support (fun i => |f i|) ⊆ ↑h.toFinset := by
      intro i hi
      simpa using hi
    rw [finsum_eq_sum_of_support_subset (s := h.toFinset) f (by rw [Set.Finite.coe_toFinset]),
      finsum_eq_sum_of_support_subset _ hs]
    exact Finset.abs_sum_le_sum_abs _ _
  · rw [finsum_of_infinite_support h, abs_zero]
    exact finsum_nonneg fun i => abs_nonneg _

variable {n d : ℕ}

theorem abs_chartDens_le (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) :
    |chartDens J A f φ y| ≤ chartAbsDens J A f φ y := by
  classical
  refine (abs_finsum_le_finsum_abs _).trans (le_of_eq (finsum_congr fun x => ?_))
  rw [finsum_eq_if, finsum_eq_if]
  split_ifs <;> simp

theorem chartAbsDens_nonneg (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) :
    0 ≤ chartAbsDens J A f φ y :=
  finsum_nonneg fun _ => finsum_nonneg fun _ => by split_ifs <;> positivity

theorem CutOff.proof (hS : CutOffShape.Statement) (hT : CutOffTube.Statement)
    (hG : CutOffGradient.Statement) : CutOff.Statement := by
  obtain ⟨K, hK⟩ := hG
  intro n d J A P hJ hdim hA hP
  have hA' : ContDiff ℝ ∞ fun x : Fin n → ℂ => A *ᵥ x :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).contDiff.restrict_scalars ℝ
  have hc : Continuous fun x : Fin n → ℂ => ‖eval (A *ᵥ x) P‖ ^ 2 :=
    ((MvPolynomial.continuous_eval P).comp hA'.continuous).norm.pow 2
  have key : ∀ T : (Fin (d + 1) → ℂ) → ℝ, Integrable T → ∀ (k : ℕ) (F : (Fin (d + 1) → ℂ) → ℝ),
      (∀ y, ‖F y‖ ≤ K / ((k : ℝ) + 1) * T y) → ‖∫ y, F y‖ ≤ K / ((k : ℝ) + 1) * ∫ y, T y :=
    fun T hTi k F hF => (norm_integral_le_of_norm_le (hTi.const_mul _)
      (Eventually.of_forall hF)).trans_eq (integral_const_mul _ _)
  have lim : ∀ c : ℝ, Tendsto (fun k : ℕ => K / ((k : ℝ) + 1) * c) atTop (𝓝 0) := fun c => by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul K).mul_const c
    rw [mul_zero, zero_mul] at h
    exact h.congr fun k => by ring
  refine ⟨logLogCutAlong A P, fun k => ((hS _ P).1 k).1.comp hA', fun k x => ((hS _ P).1 k).2.1 _,
    fun k => ⟨{x | ‖eval (A *ᵥ x) P‖ ^ 2 < cutLevel k}, isOpen_lt hc continuous_const, fun x hx => ?_,
      fun x hx => ((hS _ P).1 k).2.2 _ hx.1⟩, fun x _ hx => (hS _ P).2 _ hx, fun R => ?_,
    fun R φ hφ => ?_⟩
  · have hx0 : eval (A *ᵥ x) P = 0 := hx
    show ‖eval (A *ᵥ x) P‖ ^ 2 < cutLevel k
    rw [hx0, norm_zero, zero_pow two_ne_zero]
    exact (cutLevel_mem k).1
  · have hTi := hT n d J A P R (fun _ => euclPot) hJ hdim hA hP
      fun _ => smoothNear_of_contDiff (contDiff_euclPot n)
    have hl := (lim (∫ y, tubeDens J A P R (fun _ => euclPot) y)).const_mul 2
    rw [mul_zero] at hl
    refine squeeze_zero_norm (fun k => ?_) hl
    have h := hK n d J A P R (fun _ => euclPot) k
    refine (norm_sub_le _ _).trans ?_
    rw [two_mul]
    exact add_le_add (key _ hTi k _ fun y => (abs_chartDens_le _ _ _ _ y).trans (h y hJ hdim hA).2.1)
      (key _ hTi k _ fun y => (abs_chartDens_le _ _ _ _ y).trans (h y hJ hdim hA).2.2)
  · refine squeeze_zero_norm (fun k => key _ (hT n d J A P R φ hJ hdim hA hP hφ) k _ fun y => ?_)
      (lim _)
    rw [Real.norm_of_nonneg (chartAbsDens_nonneg _ _ _ _ y)]
    exact (hK n d J A P R φ k y hJ hdim hA).1

end

end GroundTheory.Heights₂.Heights
end

