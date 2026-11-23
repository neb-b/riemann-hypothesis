module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsTwOps
section
open UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Geo.Cs UpperTheory.V.Lit.Dr
open scoped ContDiff

private theorem tp_contDiffOn {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ F] {Y : Set V} (hY : IsOpen Y) (A : V →L[ℝ] V) (B : F →L[ℝ] F)
    (hA : ∀ p ∈ Y, A p ∈ Y) {q : ℕ} {w : V → V [⋀^Fin q]→L[ℝ] F} (hw : ContDiffOn ℝ ∞ w Y) :
    ContDiffOn ℝ ∞ (tp A B w) Y := by
  intro z hz
  apply ContDiffAt.contDiffWithinAt
  refine altSmooth _ _ _ q _ z fun v => ?_
  have h1 : ContDiffAt ℝ ∞ (fun y : V => w (A y)) z :=
    (hw.contDiffAt (hY.mem_nhds (hA z hz))).comp z A.contDiff.contDiffAt
  have h2 : ContDiffAt ℝ ∞ (fun y : V => w (A y) fun i => A (v i)) z :=
    (ContinuousAlternatingMap.apply ℝ V F (fun i => A (v i))).contDiff.contDiffAt.comp z h1
  exact B.contDiff.contDiffAt.comp z h2

private theorem twOps_abs {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ F] {Y : Set V} (hY : IsOpen Y) (A A' : V →L[ℝ] V) (B : F →L[ℝ] F)
    (hA : ∀ p ∈ Y, A p ∈ Y) (hA' : ∀ p ∈ Y, A' p ∈ Y) (h1 : ∀ p, A (A' p) = p) (h2 : ∀ p, A' (A p) = p)
    {W : V → V} (hW : IsField Y W) :
    IsField Y (fun p => A' (W (A p))) ∧ (∀ t p, flow (fun p => A' (W (A p))) t p = A' (flow W t (A p))) ∧
    ∀ q : ℕ, (∀ w : V → V [⋀^Fin q]→L[ℝ] F, ∀ p ∈ Y,
        tp A B (pb (flow W 1) w) p = pb (flow (fun p => A' (W (A p))) 1) (tp A B w) p) ∧
      ∀ w : V → V [⋀^Fin (q + 1)]→L[ℝ] F, ContDiffOn ℝ ∞ w Y → ∀ p ∈ Y,
        tp A B (hom W w) p = hom (fun p => A' (W (A p))) (tp A B w) p := by
  have hf : ∀ t p, flow (fun p => A' (W (A p))) t p = A' (flow W t (A p)) := fun t p => by
    simp only [flow, map_add (f := _), map_smul, h2]
  have hZ : IsField Y (fun p => A' (W (A p))) :=
    ⟨A'.contDiff.comp_contDiffOn (hW.1.comp A.contDiff.contDiffOn hA), fun p hp t ht => by
      rw [hf]; exact hA' _ (hW.2 _ (hA p hp) t ht)⟩
  refine ⟨hZ, hf, fun q => ?_⟩
  have nat := pbNat V F Y hY A' B W _ hW hZ hA' (fun p _ => by simp only [h1]) q
  have rel : ∀ (n : ℕ) (w : V → V [⋀^Fin n]→L[ℝ] F), ∀ p ∈ Y, ∀ v : Fin n → V,
      tp A B w (A' p) (fun i => A' (v i)) = B (w p v) := fun n w p _ v => by
    simp only [tp_apply, h1]
  refine ⟨fun w p hp => ?_, fun w hw p hp => ?_⟩
  · refine ContinuousAlternatingMap.ext fun v => ?_
    have := nat.1 _ _ (rel q w) 1 ⟨zero_le_one, le_rfl⟩ _ (hA p hp) (fun i => A (v i))
    simp only [h2] at this
    exact this.symm
  · refine ContinuousAlternatingMap.ext fun v => ?_
    have := (nat.2 _ _ (rel (q + 1) w)).2 hw (tp_contDiffOn hY A B hA hw) _ (hA p hp) (fun i => A (v i))
    simp only [h2] at this
    exact this.symm

theorem UpperTheory.V.Lit.Geo.Cs.twOps :
    UpperTheory.V.Lit.Geo.Cs.TwOps := by
  intro E _ _ _ a ho U Ξ W hW g x
  have h1 : ∀ p : HV E a, sand g (sand g⁻¹ p) = p := fun p => by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  have h2 : ∀ p : HV E a, sand g⁻¹ (sand g p) = p := fun p => by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
  obtain ⟨k1, k2, k3⟩ := twOps_abs ho (sand g) (sand g⁻¹) (mulVecL (Ξ.mat g⁻¹)) (fun p hp => sand_mem_cone g hp)
    (fun p hp => sand_mem_cone g⁻¹ hp) h1 h2 (hW.field (QuotientGroup.mk x))
  refine ⟨k1, k2, fun q => ?_⟩
  have app := omApply _ _ _ _ (geo ho U Ξ) W hW q
  refine ⟨fun w => ⟨tp_contDiffOn ho _ _ (fun p hp => sand_mem_cone g hp) (w.2 _).1, fun p hp => ?_⟩, fun w p hp => ?_⟩
  · refine Eq.trans ?_ ((k3 q).1 (w.1 _) p hp)
    refine ContinuousAlternatingMap.ext fun v => ?_
    rw [Tw, tp_apply, tp_apply, app.1 w _ _ (sand_mem_cone g hp)]
  · refine Eq.trans ?_ ((k3 q).2 (w.1 _) (w.2 _).1 p hp)
    refine ContinuousAlternatingMap.ext fun v => ?_
    rw [Tw, tp_apply, tp_apply, app.2 w _ _ (sand_mem_cone g hp)]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfAdjInt
section
open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.Pf.adjInt :
    UpperTheory.V.Lit.Geo.Pf.AdjInt := by
  intro E _ _ _ a μ _ Ξ r χ G htw hadm X x y hx hy hs
  have hint : ∀ u v, Pf.TwInv χ u → Pf.TwInv χ v → Pf.Cs (Pf.pt χ G u v) → Pf.QInt μ (Pf.pt χ G u v) :=
    fun u v hu hv hc =>
      have hC := (Pf.ptInv E a χ _ G u v).2.1 hu hv
      (Pf.bddInt E a μ _ hC (Pf.csBdd E a _ hC (.inl hc))).1
  refine (fun (h : _ ∧ _) (h3 : _ ∧ _ → _) => ⟨h.1, h.2, h3 h⟩) ⟨?_, ?_⟩ ?_
  · exact hint _ _ hx (Pf.twLie E a Ξ r χ htw _ y hy).1
      (hs.elim (fun h => Pf.cs_pt_left χ G _ h)
        fun h => Pf.cs_pt_right χ G _ (Pf.csTens E a Ξ r _ y h).1)
  · exact hint _ _ (Pf.twLie E a Ξ r χ htw _ x hx).2 hy
      (hs.elim (fun h => Pf.cs_pt_left χ G _ (Pf.csTens E a Ξ r _ x h).2)
        fun h => Pf.cs_pt_right χ G _ h)
  rintro ⟨h1, h2⟩
  obtain ⟨θ, hθ, hd⟩ := Pf.ptDiv E a Ξ r χ G htw hadm x y
  have hS := (Pf.ptInv E a χ _ G x y).2.2 θ hθ hx hy
  have hc : Pf.Cs θ.1 := by
    rw [show θ.1 = _ from funext hθ]
    exact hs.elim (fun h => Pf.cs_pt_left χ G _ h) fun h => Pf.cs_pt_right χ G _ h
  have h0 := fun Y => Pf.stokesFn E a μ θ Y hS hc
  refine sub_eq_zero.1 ?_
  unfold Pf.qint at h0 ⊢
  rw [← MeasureTheory.integral_sub h1 h2]
  simp only [← hd X]
  exact h0 _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullHomBd
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo

private theorem norm_hom_le {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (W : V → V) {q : ℕ} (w : V → V [⋀^Fin (q + 1)]→L[ℝ] F) (p : V) (v : Fin q → V) (A : F →L[ℝ] F) (K : ℝ)
    (hc : ContinuousOn (fun t => hk W t w p) (Set.Icc 0 1))
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖A (hk W t w p v)‖ ≤ K) : ‖A (hom W w p v)‖ ≤ K := by
  have hi : IntervalIntegrable (fun t => hk W t w p) MeasureTheory.volume 0 1 :=
    hc.intervalIntegrable_of_Icc zero_le_one
  have e := (A.comp (ContinuousAlternatingMap.apply ℝ V F v)).intervalIntegral_comp_comm hi
  have e' : A (hom W w p v) = ∫ t in (0 : ℝ)..1, A (hk W t w p v) := e.symm
  rw [e']
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := K)
    (f := fun t => A (hk W t w p v)) fun t ht => hb t (by
      rw [Set.uIoc_of_le zero_le_one] at ht
      exact Set.Ioc_subset_Icc_self ht)
  simpa using this

theorem UpperTheory.V.Lit.Geo.homBd :
    HomBd := by
  intro E _ _ _ a ho U Ξ Y C hY W hW q
  obtain ⟨B₁, hB₁, h₁⟩ := corrBd E a U Ξ C (q + 1)
  obtain ⟨B₂, hB₂, h₂⟩ := fieldDer E a U Y C hY
  obtain ⟨B₃, hB₃, h₃⟩ := fieldBd E a U Y C hY W hW
  obtain ⟨hfl, hfe⟩ := fieldFlow E a ho U Ξ Y C hY W hW
  refine ⟨B₁ * B₂ * (B₃ * 2) ^ q, by positivity, fun α α' w hα hw hw' g M hM hb X => ?_⟩
  obtain ⟨y, x, hyx⟩ : ∃ (y : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)),
      (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1 = infGL E a y * finGL E a x :=
    ⟨_, _, (infGL_mul_finGL _).symm⟩
  have hYg : Y (infGL E a y * finGL E a x) = Y g := by
    obtain ⟨t, ht⟩ := (retrFacts E a).1 g
    have := hY.left 1 t g
    rw [map_one, one_mul] at this
    rw [← hyx, ht, this]
  have hp : sand y (hOne E a) ∈ (geo ho U Ξ).Y := ⟨y, rfl⟩
  have e1 := hw' y x X
  rw [(omApply _ _ _ _ (geo ho U Ξ) W hfl q).2 w _ _ hp] at e1
  have e2 : ev (α' X) (infGL E a y * finGL E a x) = mulVecL (Ξ.mat y⁻¹)
      (hom (W (x : GL (Fin a) (Af E) ⧸ U)) (w.1 (x : GL (Fin a) (Af E) ⧸ U)) (sand y (hOne E a))
        fun i => (2 : ℝ) • sand y (hv (X i))) := by
    rw [e1, mulVecL_apply, Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]
  rw [hyx, e2]
  refine norm_hom_le _ _ _ _ _ _
    ((hkSmooth _ _ _ (geo ho U Ξ).isOpen _ (hfl.field _) q _ (w.2 _).1).2.2.1 _ hp) fun t ht => ?_
  have ht' : |t| ≤ 1 := abs_le.2 ⟨by linarith [ht.1], ht.2⟩
  obtain ⟨h, hh, hC, hC'⟩ := hY.root g t ht'
  choose v' hv' hv'' using h₃ y x t ht'
  have key := h₁ α w.1 hα hw g y h x M hyx hC hC' hM (hb t ht h hh)
    (Matrix.vecCons (hv (Y g)) fun i => v' ((2 : ℝ) • hv (X i)))
  have e3 : (Matrix.vecCons (W (x : GL (Fin a) (Af E) ⧸ U) (sand y (hOne E a))) fun i =>
      fderiv ℝ (flow (W (x : GL (Fin a) (Af E) ⧸ U)) t) (sand y (hOne E a)) ((2 : ℝ) • sand y (hv (X i)))) =
      fun i => sand y (Matrix.vecCons (hv (Y g)) (fun i => v' ((2 : ℝ) • hv (X i))) i) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Matrix.cons_val_zero]
      rw [hW y x, hYg]
    · simp only [Matrix.cons_val_succ]
      rw [← hv'', map_smul (sand y)]
  rw [mulVecL_apply, hk_apply, e3, hfe y h x t (by rw [hYg]; exact hh)]
  refine key.trans ?_
  rw [Fin.prod_univ_succ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ]
  have b1 : ∏ i, ‖v' ((2 : ℝ) • hv (X i))‖ ≤ (B₃ * 2) ^ q * ∏ i, ‖hv (X i)‖ := by
    calc ∏ i, ‖v' ((2 : ℝ) • hv (X i))‖ ≤ ∏ i : Fin q, (B₃ * 2) * ‖hv (X i)‖ :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => (hv' _).trans_eq (by
            rw [norm_smul, Real.norm_ofNat, mul_assoc])
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have b2 := mul_le_mul (h₂ g).1 b1 (Finset.prod_nonneg fun _ _ => norm_nonneg _) hB₂
  calc _ ≤ B₁ * M * (B₂ * ((B₃ * 2) ^ q * ∏ i, ‖hv (X i)‖)) := mul_le_mul_of_nonneg_left b2 (mul_nonneg hB₁ hM)
    _ = _ := by ring
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullHomForm
section
open UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Dr
open Set ContinuousAlternatingMap
open scoped ContDiff

private theorem extDeriv_smooth {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {Y : Set V} (hY : IsOpen Y) {q : ℕ} {w : V → V [⋀^Fin q]→L[ℝ] F}
    (hw : ContDiffOn ℝ ∞ w Y) : ContDiffOn ℝ ∞ (extDeriv w) Y :=
  (alternatizeUncurryFinCLM ℝ V F).contDiff.comp_contDiffOn
    (hw.fderiv_of_isOpen hY (by simp))

private theorem pb_flow_zero {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (W : V → V) {q : ℕ} (w : V → V [⋀^Fin q]→L[ℝ] F) (p : V) :
    pb (flow W 0) w p = w p := by
  have h : flow W 0 = id := by
    funext x
    simp [flow]
  ext v
  simp [pb_apply, h]

private theorem homForm_of (hP : HomPt) (hS : HkSmooth) : HomForm := by
  intro V F _ _ _ _ _ _ Y hY W hW p hp
  have hWp : ContDiffAt ℝ ∞ W p := hW.1.contDiffAt (hY.mem_nhds hp)
  refine ⟨fun w hw => ?_, fun q w hw => ?_⟩
  · have hI := ((hS V F Y hY W hW 0 _ (extDeriv_smooth hY hw)).2.2.1 p hp).intervalIntegrable_of_Icc
      (μ := MeasureTheory.volume) zero_le_one
    have hder : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun r => pb (flow W r) w p) (hk W t (extDeriv w) p) t := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      exact (hP V F W p t hWp).1 w (hw.contDiffAt (hY.mem_nhds (hW.2 p hp t ht)))
    have h3 := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hI
    rw [pb_flow_zero] at h3
    exact h3.symm
  · have hI := ((hS V F Y hY W hW (q + 1) _ (extDeriv_smooth hY hw)).2.2.1 p hp).intervalIntegrable_of_Icc
      (μ := MeasureTheory.volume) zero_le_one
    obtain ⟨hU, hΦ, -, -⟩ := hS V F Y hY W hW q w hw
    obtain ⟨hc, hD⟩ := paramDeriv V _ p _ _ hU (fun t ht => ⟨hp, hW.2 p hp t ht⟩) hΦ
    dsimp only at hc hD
    have hJ := hc.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) zero_le_one
    have hJ' : IntervalIntegrable (fun t => alternatizeUncurryFinCLM ℝ V F (fderiv ℝ (fun x => hk W t w x) p))
        MeasureTheory.volume 0 1 :=
      ((alternatizeUncurryFinCLM ℝ V F).continuous.comp_continuousOn hc).intervalIntegrable_of_Icc
      (μ := MeasureTheory.volume) zero_le_one
    have hder : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun r => pb (flow W r) w p)
        (alternatizeUncurryFinCLM ℝ V F (fderiv ℝ (fun x => hk W t w x) p) + hk W t (extDeriv w) p) t := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      exact (hP V F W p t hWp).2 q w (hw.contDiffAt (hY.mem_nhds (hW.2 p hp t ht)))
    have h3 := intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hJ'.add hI)
    rw [pb_flow_zero, intervalIntegral.integral_add hJ' hI,
      (alternatizeUncurryFinCLM ℝ V F).intervalIntegral_comp_comm hJ, ← hD.fderiv] at h3
    exact h3.symm

theorem UpperTheory.V.Lit.Geo.homForm :
    HomForm :=
  homForm_of homPt hkSmooth
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullOmEquiv
section
open UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Dr

theorem UpperTheory.V.Lit.Geo.omEquiv :
    OmEquiv := by
  intro Γ V S _ _ _ _ d G W hW q γ
  have hρρ : ∀ x, G.ρ γ (G.ρ γ⁻¹ x) = x := fun x => by simpa using G.ρ_inv_apply γ⁻¹ x
  have hσ : ∀ s, G.σ γ (G.σ γ⁻¹ s) = s := fun s => by simp
  have hout : ∀ p, p ∉ G.Y → G.ρ γ⁻¹ p ∉ G.Y := fun p hp h => hp (by simpa [hρρ] using G.maps γ _ h)
  have heq : ∀ s, ∀ p ∈ G.Y, W s (G.ρ γ p) = G.ρ γ (W (G.σ γ⁻¹ s) p) := fun s p hp => by
    have := hW.equiv γ (G.σ γ⁻¹ s) p hp
    rwa [hσ] at this
  have hnat := fun s => pbNat V (Fin d → ℂ) G.Y G.isOpen (G.ρ γ) (mulVecL (G.ξ γ)) (W (G.σ γ⁻¹ s)) (W s)
    (hW.field _) (hW.field s) (G.maps γ) (heq s) q
  have hrel : ∀ (k : ℕ) (w : G.Om k) (s : S), ∀ p ∈ G.Y, ∀ v : Fin k → V,
      ((G.act k γ w).1 s (G.ρ γ p)) (fun i => G.ρ γ (v i)) = mulVecL (G.ξ γ) (w.1 (G.σ γ⁻¹ s) p v) := by
    intro k w s p hp v
    simp only [Geo.act_apply, mulVecL_apply, Geo.ρ_inv_apply]
  have hz : ∀ (k : ℕ) (w : G.Om k) (s : S) (p : V), p ∉ G.Y → w.1 s p = 0 :=
    fun k w s p hp => (w.2 s).2 p hp
  have hsm := fun (k : ℕ) (w : G.Om k) (s : S) => (w.2 s).1
  obtain ⟨hA, hB⟩ := omApply Γ V S d G W hW q
  refine ⟨fun w => ?_, fun w => ?_⟩
  · apply Subtype.ext
    funext s p
    ext v
    by_cases hp : p ∈ G.Y
    · have hp' := G.maps γ⁻¹ p hp
      rw [Geo.act_apply, hA w _ _ hp', hA (G.act q γ w) s p hp]
      have := (hnat s).1 (w.1 (G.σ γ⁻¹ s)) ((G.act q γ w).1 s) (hrel q w s) 1 ⟨zero_le_one, le_rfl⟩
        (G.ρ γ⁻¹ p) hp' (fun i => G.ρ γ⁻¹ (v i))
      simp only [hρρ] at this
      rw [← mulVecL_apply]
      exact congrFun this.symm _
    · rw [Geo.act_apply, hz q _ _ _ (hout p hp), hz q _ s p hp]
      simp
  · apply Subtype.ext
    funext s p
    ext v
    by_cases hp : p ∈ G.Y
    · have hp' := G.maps γ⁻¹ p hp
      rw [Geo.act_apply, hB w _ _ hp', hB (G.act (q + 1) γ w) s p hp]
      have := ((hnat s).2 (w.1 (G.σ γ⁻¹ s)) ((G.act (q + 1) γ w).1 s) (hrel (q + 1) w s)).2
        (hsm _ w _) (hsm _ _ s) (G.ρ γ⁻¹ p) hp' (fun i => G.ρ γ⁻¹ (v i))
      simp only [hρρ] at this
      rw [← mulVecL_apply]
      exact congrFun this.symm _
    · rw [Geo.act_apply, hz q _ _ _ (hout p hp), hz q _ s p hp]
      simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullPbBd
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.pbBd :
    PbBd := by
  intro E _ _ _ a ho U Ξ Y C hY W hW q
  obtain ⟨B₁, hB₁, hc⟩ := corrBd E a U Ξ C q
  obtain ⟨B₂, hB₂, hf⟩ := fieldBd E a U Y C hY W hW
  obtain ⟨hfl, hflow⟩ := fieldFlow E a ho U Ξ Y C hY W hW
  refine ⟨B₁ * (2 * B₂) ^ q, by positivity, fun α α' w hα hw hw' g M hM hb X => ?_⟩
  obtain ⟨y, x, hyx⟩ : ∃ (y : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)),
      (retractOne g : KernelIndexFullLattice.G1 E a).1 = infGL E a y * finGL E a x :=
    ⟨_, _, (GlobalTheory.CuspRep.infGL_mul_finGL _).symm⟩
  have hYg : Y (infGL E a y * finGL E a x) = Y g := by
    obtain ⟨t, ht⟩ := (retrFacts E a).1 g
    rw [← hyx, ht, ← hY.left 1 t g, map_one, one_mul]
  obtain ⟨h, hh, h1, h2⟩ := hY.root g 1 (by simp)
  have hbd := hb h (by rw [hh, one_smul])
  have hpt := hflow y h x 1 (by rw [hYg]; exact hh)
  choose v' hv' hv'' using hf y x 1 (by simp)
  have hmem : sand y (hOne E a) ∈ (geo ho U Ξ).Y := sand_mem_cone y hOne_mem_cone
  have e1 := hw' y x X
  rw [(omApply _ _ _ _ (geo ho U Ξ) W hfl q).1 w _ _ hmem, pb_apply, hpt] at e1
  have e2 : (fun i => fderiv ℝ (flow (W (x : GL (Fin a) (Af E) ⧸ U)) 1) (sand y (hOne E a))
      ((2 : ℝ) • sand y (hv (X i)))) = fun i => sand y (v' ((2 : ℝ) • hv (X i))) := by
    funext i
    rw [← hv'', map_smul (sand y)]
  rw [e2] at e1
  have e3 := hc α w.1 hα hw g y h x M hyx h1 h2 hM hbd (fun i => v' ((2 : ℝ) • hv (X i)))
  have e4 : Ξ.mat y⁻¹ * Ξ.mat y = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  rw [e1, Matrix.mulVec_mulVec, e4, Matrix.one_mulVec, ← hyx] at e3
  refine e3.trans ?_
  have e5 : ∏ i, ‖v' ((2 : ℝ) • hv (X i))‖ ≤ (2 * B₂) ^ q * ∏ i, ‖hv (X i)‖ := by
    calc ∏ i, ‖v' ((2 : ℝ) • hv (X i))‖ ≤ ∏ i, (2 * B₂) * ‖hv (X i)‖ := by
          refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => (hv' _).trans (le_of_eq ?_)
          rw [norm_smul, Real.norm_ofNat]
          ring
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc B₁ * M * ∏ i, ‖v' ((2 : ℝ) • hv (X i))‖ ≤ B₁ * M * ((2 * B₂) ^ q * ∏ i, ‖hv (X i)‖) :=
        mul_le_mul_of_nonneg_left e5 (mul_nonneg hB₁ hM)
    _ = _ := by ring
end

