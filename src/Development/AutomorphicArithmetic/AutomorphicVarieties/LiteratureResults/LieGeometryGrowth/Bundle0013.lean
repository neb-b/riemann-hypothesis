module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermUnipotentIntegralVariant
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0007
public import Mathlib.Analysis.Normed.Module.Alternating.Curry
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsAltEv
section
open UpperTheory.V.Lit.Geo.Cs

theorem UpperTheory.V.Lit.Geo.Cs.altEv :
    AltEv := by
  classical
  intro V F _ _ _ _ _ _ q k
  let bs := Module.finBasis ℝ V
  let L : (V [⋀^Fin q]→L[ℝ] F) →ₗ[ℝ] ((Fin q → Fin (Module.finrank ℝ V)) → F) :=
    { toFun := fun g σ => g (fun i => bs (σ i))
      map_add' := fun g h => by ext σ; simp
      map_smul' := fun c g => by ext σ; simp }
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro g hg
    have e : g.toAlternatingMap = (0 : V [⋀^Fin q]→L[ℝ] F).toAlternatingMap :=
      Module.Basis.ext_alternating bs (fun v _ => by simpa [L] using congrFun hg v)
    ext m
    simpa using DFunLike.congr_fun e m
  obtain ⟨M, hM⟩ := L.exists_leftInverse_of_injective hker
  let A : (Fin q → Fin (Module.finrank ℝ V)) → F →L[ℝ] (V [⋀^Fin q]→L[ℝ] F) := fun σ =>
    LinearMap.toContinuousLinearMap (M.comp (LinearMap.single ℝ (fun _ => F) σ))
  refine ⟨Finset.univ.image (fun σ : Fin q → Fin (Module.finrank ℝ V) => fun i => bs (σ i)),
    ∑ σ, ‖A σ‖, Finset.sum_nonneg (fun _ _ => norm_nonneg _), ?_⟩
  intro f x b hb hcd hsz
  have mem : ∀ σ : Fin q → Fin (Module.finrank ℝ V),
      (fun i => bs (σ i)) ∈ Finset.univ.image (fun σ : Fin q → Fin (Module.finrank ℝ V) =>
        fun i => bs (σ i)) :=
    fun σ => Finset.mem_image_of_mem _ (Finset.mem_univ σ)
  have hrep : f = fun y => ∑ σ, A σ (f y (fun i => bs (σ i))) := by
    funext y
    calc f y = M (L (f y)) := (LinearMap.congr_fun hM (f y)).symm
      _ = M (∑ σ, Pi.single σ (L (f y) σ)) := by rw [Finset.univ_sum_single]
      _ = ∑ σ, A σ (f y (fun i => bs (σ i))) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        rfl
  intro i hi
  have hcdi : ∀ σ : Fin q → Fin (Module.finrank ℝ V),
      ContDiffAt ℝ i (fun y => f y (fun i => bs (σ i))) x :=
    fun σ => (hcd _ (mem σ)).of_le (by exact_mod_cast le_top)
  have hsum := iteratedFDeriv_fun_sum_apply (𝕜 := ℝ) (n := i) (x := x) (u := Finset.univ)
    (f := fun σ y => A σ (f y (fun i => bs (σ i))))
    (fun σ _ => (A σ).contDiff.contDiffAt.comp x (hcdi σ))
  rw [hrep, hsum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun σ _ => ?_)
  refine ((A σ).norm_iteratedFDeriv_comp_left (hcdi σ) le_rfl).trans ?_
  exact mul_le_mul_of_nonneg_left (hsz _ (mem σ) i hi) (norm_nonneg _)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsChartSz
section
open UpperTheory.V.Lit.Geo.Cs GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTSmooth
open GlobalTheory.ThetaPull (invL invL_smooth)
open scoped ContDiff Topology

private theorem sz_succ {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} {f : V → F} {p : V} {b : ℝ} (h0 : ‖f p‖ ≤ b) (h1 : Sz k (fderiv ℝ f) p b) : Sz (k + 1) f p b := by
  intro i hi
  cases i with
  | zero => simpa using h0
  | succ i =>
    rw [← norm_iteratedFDeriv_fderiv]
    exact h1 i (Nat.le_of_succ_le_succ hi)

theorem UpperTheory.V.Lit.Geo.Cs.chartSz :
    ChartSz := by
  intro E _ _ _ a k ρ hρ
  have h1 : oneL E a ∈ invSet E a := isUnit_one
  have hval : ∀ (φ : Sm E a), (∀ l : List (Lie E a), ∃ C : ℝ, ∀ g, ‖((l.map (lie E a)).prod φ).1 g‖ ≤ C * ρ g) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ g, ‖chart φ.1 g (oneL E a)‖ ≤ C * ρ g := by
    intro φ hφ
    obtain ⟨C, hC⟩ := hφ []
    refine ⟨max C 0, le_max_right _ _, fun g => ?_⟩
    have e := chart_val φ.1 g 1
    rw [map_one, mul_one] at e
    have e' : chart φ.1 g (oneL E a) = φ.1 g := e
    rw [e']
    exact (hC g).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hρ g))
  induction k with
  | zero =>
    intro φ hφ
    obtain ⟨C, hC0, hC⟩ := hval φ hφ
    refine ⟨C, hC0, fun g i hi => ?_⟩
    obtain rfl : i = 0 := Nat.le_zero.1 hi
    simpa using hC g
  | succ k ih =>
    intro φ hφ
    obtain ⟨C₀, hC0, hC⟩ := hval φ hφ
    have hi : ∀ i : Ix E a, ∃ C : ℝ, 0 ≤ C ∧ ∀ g, Sz k (chart (lie E a (bs E a i) φ).1 g) (oneL E a) (C * ρ g) := by
      intro i
      refine ih _ fun l => ?_
      obtain ⟨C, hC⟩ := hφ (l ++ [bs E a i])
      refine ⟨C, fun g => ?_⟩
      have := hC g
      rwa [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton, Module.End.mul_apply] at this
    choose D hD0 hD using hi
    let Θ : Ix E a → Lie E a → (ℂ →L[ℝ] (Lie E a →L[ℝ] ℂ)) := fun i y =>
      ContinuousLinearMap.smulRightL ℝ (Lie E a) ℂ (coordL i (invL y))
    have hΘ : ∀ i, ContDiffAt ℝ ∞ (Θ i) (oneL E a) := fun i =>
      (ContinuousLinearMap.smulRightL ℝ (Lie E a) ℂ).contDiff.contDiffAt.comp _
        ((coordL i).contDiff.contDiffAt.comp _ ((invL_smooth (E := E) (a := a)).1 _ h1))
    choose B hB using fun i => exists_sz k (Θ i) (oneL E a)
    have hS0 : 0 ≤ ∑ i, 2 ^ k * B i * D i :=
      Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (by positivity) (hB i).nonneg) (hD0 i)
    refine ⟨C₀ + ∑ i, 2 ^ k * B i * D i, add_nonneg hC0 hS0, fun g => sz_succ ?_ ?_⟩
    · exact (hC g).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hS0) (hρ g))
    · have hc : ∀ i, ContDiffAt ℝ ∞ (chart (lie E a (bs E a i) φ).1 g) (oneL E a) := fun i =>
        contDiffAt_chart (lie E a (bs E a i) φ).2 g h1
      have key := (appSz (Lie E a) ℂ (Lie E a →L[ℝ] ℂ) k (oneL E a)).2.2 (Ix E a) Finset.univ
        (fun i y => Θ i y (chart (lie E a (bs E a i) φ).1 g y)) (fun i => 2 ^ k * B i * (D i * ρ g))
        (fun i _ => (hΘ i).clm_apply (hc i))
        (fun i _ => (appSz (Lie E a) ℂ (Lie E a →L[ℝ] ℂ) k (oneL E a)).1 _ _ _ _ (hΘ i) (hc i) (hB i) (hD i g))
      refine (key.congr ?_).mono ?_
      · filter_upwards [isOpen_invSet.mem_nhds h1] with y hy
        exact (fderiv_chart_eq φ g hy).symm
      · rw [add_mul, Finset.sum_mul]
        refine le_add_of_nonneg_of_le (mul_nonneg hC0 (hρ g)) (le_of_eq ?_)
        exact Finset.sum_congr rfl fun i _ => by ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsCorrForm
section
open UpperTheory.V.Lit.Geo.Cs
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct ContDiff Topology

private theorem ev_eq_cmp {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a d : ℕ}
    (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) (g : GA E a) : ev m g j = (UpperTheory.V.Lit.Bor.cmp j m).1 g := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul φ v => simp [mul_comm]

private theorem alt_expand {V W M : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [AddCommGroup M] [Module ℝ M] {q n : ℕ} (α : V [⋀^Fin q]→ₗ[ℝ] M) (e : V ≃ₗ[ℝ] W) (b : Module.Basis (Fin n) ℝ W)
    (u : Fin q → W) :
    α (fun i => e.symm (u i)) = ∑ I : Fin q → Fin n, (∏ i, b.repr (u i) (I i)) • α fun i => e.symm (b (I i)) := by
  have h : (fun i => e.symm (u i)) = fun i => ∑ k, b.repr (u i) k • e.symm (b k) := by
    funext i
    conv_lhs => rw [← b.sum_repr (u i)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  rw [h]
  refine (α.toMultilinearMap.map_sum (fun i k => b.repr (u i) k • e.symm (b k))).trans ?_
  exact Finset.sum_congr rfl fun I _ => α.map_smul_univ _ _

theorem UpperTheory.V.Lit.Geo.Cs.corrForm :
    CorrForm := by
  intro E _ _ _ a Ξ q v
  classical
  obtain ⟨τ, h1, hτ, -, -, hi, hs⟩ := secOne E a
  let b := Module.finBasis ℝ (HV E a)
  let u : HV E a → Fin q → HV E a := fun p i => (2 : ℝ)⁻¹ • sand (τ p)⁻¹ (v i)
  refine ⟨(Fin q → Fin (Module.finrank ℝ (HV E a))) × Fin Ξ.d, inferInstance,
    fun I i => hv.symm (b (I.1 i)), fun I => I.2,
    fun I p k => ((∏ i, b.repr (u p i) (I.1 i) : ℝ) : ℂ) * Ξ.mat (τ p) k I.2,
    fun p => toL (τ p).val, by simp only [h1]; rfl, hτ, fun I => ?_, fun U α w hc g x => ?_⟩
  · refine contDiffAt_pi.2 fun k => ContDiffAt.mul ?_ ?_
    · refine Complex.ofRealCLM.contDiff.contDiffAt.comp (hOne E a)
        (f := fun p => ∏ i, b.repr (u p i) (I.1 i)) ?_
      refine contDiffAt_prod fun i _ => ?_
      have hu : ContDiffAt ℝ ∞ (fun p => u p i) (hOne E a) := (hi.clm_apply contDiffAt_const).const_smul _
      exact (LinearMap.toContinuousLinearMap (b.coord (I.1 i))).contDiff.contDiffAt.comp (hOne E a) hu
    · have := (((matSmooth E a Ξ k I.2).1).contDiffAt
          (isOpen_invSet.mem_nhds (val_mem_invSet (τ (hOne E a))))).comp (hOne E a) hτ
      simpa only [Function.comp_def, extGL_val] using this
  · refine hs.mono fun p hp => ?_
    have e1 : sand (g * τ p) (hOne E a) = sand g p := by
      rw [map_mul, ContinuousLinearMap.mul_apply, hp]
    have e2 : ∀ i, (2 : ℝ) • sand (g * τ p) (u p i) = sand g (v i) := fun i => by
      simp only [u, map_smul, smul_smul]
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel_right]
      simp
    have h := hc (g * τ p) x fun i => hv.symm (u p i)
    simp only [LinearEquiv.apply_symm_apply, e1, e2] at h
    have e3 : infGL E a (g * τ p) * finGL E a x = pt g x * infGL E a (τ p) := pt_mul g (τ p) x
    simp only [Tw, tp_apply, mulVecL_apply, h, e3, Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel_left, chart_val]
    rw [alt_expand α hv b (u p)]
    funext k
    have e4 : ∀ (I : Fin q → Fin (Module.finrank ℝ (HV E a))) (r : ℝ) (y : GA E a),
        ev (r • α fun i => hv.symm (b (I i))) y = (r : ℂ) • ev (α fun i => hv.symm (b (I i))) y := fun I r y => by
      rw [← algebraMap_smul ℂ r, map_smul]; rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [Finset.sum_apply, e4, Matrix.mulVec, dotProduct, Pi.smul_apply, ← ev_eq_cmp,
      Fintype.sum_prod_type, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun j _ => ?_
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsGeoSum
section
open UpperTheory.V.Lit.Geo.Cs
open scoped Topology ContDiff

theorem UpperTheory.V.Lit.Geo.Cs.geoSum :
    GeoSum := by
  intro Γ V S _ _ _ _ d G Φ hΦ R q y w hy hdy hsz hw
  have hopen : ∀ s, IsOpen {p | p ∈ G.Y ∧ R < Φ s p} := fun s =>
    (hΦ.1 s).continuousOn.isOpen_inter_preimage G.isOpen isOpen_Ioi
  have hmem : ∀ j s, ContDiffOn ℝ ∞ ((y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s) G.Y :=
    fun j s => ((y j).2 s).1
  have hsm : ∀ s,
      ContDiffOn ℝ ∞ (fun x => ∑' j, (y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x)
        {p | p ∈ G.Y ∧ R < Φ s p} ∧
      ∀ p ∈ {p | p ∈ G.Y ∧ R < Φ s p},
        HasSum (fun j => fderiv ℝ ((y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s) p)
          (fderiv ℝ (fun x => ∑' j, (y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x) p) :=
    fun s => sumSm V _ _ (hopen s) (fun j x => (y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x)
      (fun j => (hmem j s).mono (fun p hp => hp.1)) (fun k p hp => hsz k s p hp.1 hp.2)
  have hsumv : ∀ s, ∀ p ∈ G.Y, R < Φ s p →
      Summable (fun j => (y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p) := by
    intro s p hp hR
    obtain ⟨N, hN, b, hb, hbd⟩ := hsz 0 s p hp hR
    refine Summable.of_norm_bounded hb (fun j => ?_)
    have h0 := hbd j p (mem_of_mem_nhds hN) 0 le_rfl
    simpa using h0
  obtain ⟨z, hzinv, hz⟩ := geoCut Γ V S d G Φ hΦ R q
    (fun s p => -∑' j, (y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p)
    (fun s => (hsm s).1.neg) (by
      intro γ s p hp hR
      have hp2 : (G.ρ γ⁻¹) p ∈ G.Y := G.maps _ p hp
      have hR2 : R < Φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) := by rw [hΦ.2.1 γ⁻¹ s p hp]; exact hR
      simp only [map_neg]
      congr 1
      rw [ContinuousLinearMap.map_tsum _ (hsumv _ _ hp2 hR2)]
      congr 1
      funext j
      exact congrFun (congrFun (congrArg Subtype.val (hy j γ)) s) p)
  refine ⟨z, hzinv, fun s p hp hR => ?_⟩
  have hev : (z : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s =ᶠ[𝓝 p]
      (fun x => -∑' j, (y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x) := by
    have hc : ContinuousAt (Φ s) p := (hΦ.1 s).continuousOn.continuousAt (G.isOpen.mem_nhds hp)
    filter_upwards [G.isOpen.mem_nhds hp, Filter.Tendsto.eventually hc (lt_mem_nhds hR)]
      with x hx hx'
    exact hz s x hx hx'.le
  have hp' : p ∈ {p | p ∈ G.Y ∧ R < Φ s p} := ⟨hp, by linarith⟩
  have hD := ((hsm s).2 p hp').mapL (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V (Fin d → ℂ))
  have hterm : ∀ j, ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V (Fin d → ℂ)
      (fderiv ℝ ((y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s) p) =
      (w (j + 1) : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s p -
        (w j : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s p := by
    intro j
    have h1 := congrFun (congrFun (congrArg Subtype.val (hdy j)) s) p
    rw [ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]
    change _ = ((w (j + 1) - w j : G.Om (q + 1)) : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s p
    rw [← h1]
    show _ = G.Y.indicator (extDeriv ((y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s)) p
    rw [Set.indicator_of_mem hp]
    rfl
  have hL : ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V (Fin d → ℂ)
      (fderiv ℝ (fun x => ∑' j, (y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x) p) =
      -(w 0 : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s p := by
    have ht := hD.tendsto_sum_nat
    simp_rw [hterm, Finset.sum_range_sub
      (fun j => (w j : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s p)] at ht
    have ht2 := (hw s p hp (by linarith)).sub_const
      ((w 0 : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s p)
    rw [zero_sub] at ht2
    exact tendsto_nhds_unique ht ht2
  show G.Y.indicator (extDeriv ((z : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s)) p = _
  rw [Set.indicator_of_mem hp, hev.extDeriv_eq]
  show ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ
    (-(fun x => ∑' j, (y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x)) p) = _
  rw [fderiv_neg, ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply, map_neg, hL, neg_neg]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsHkSz
section
open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff

theorem UpperTheory.V.Lit.Geo.Cs.hkSz :
    HkSz := by
  intro V F _ _ _ _ _ _ q k c
  obtain ⟨hA, C₁, hC₁⟩ := altSz V F q k (1 + c)
  obtain ⟨C₂, h₂, hC₂⟩ := compSz V (V →L[ℝ] V) ((V [⋀^Fin q]→L[ℝ] F) →L[ℝ] (V [⋀^Fin q]→L[ℝ] F)) k (1 + c)
  obtain ⟨C₃, h₃, hC₃⟩ := compSz V V (V [⋀^Fin (q + 1)]→L[ℝ] F) k (1 + c)
  let L : (V [⋀^Fin (q + 1)]→L[ℝ] F) →L[ℝ] (V →L[ℝ] V [⋀^Fin q]→L[ℝ] F) :=
    (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := V) (F := F) (n := q)).toContinuousLinearMap
  refine ⟨2 ^ k * (C₂ * |C₁|) * (2 ^ k * (‖L‖ * C₃) * |c|), by positivity, ?_⟩
  intro W t w p b ht hW hWs hw hws
  obtain ⟨f1, f2, f3, f4⟩ := flowSz V k c W t p ht hW hWs
  have a1 : Sz k (fun y => w (UpperTheory.V.Lit.Geo.flow W t y)) p (C₃ * b) :=
    hC₃ w _ p b f1 hw (fun i h1 h2 => f4 i h1 (h2.trans (Nat.le_succ k))) hws
  have s1 : ContDiffAt ℝ ∞ (fun y => w (UpperTheory.V.Lit.Geo.flow W t y)) p := hw.comp p f1
  have a2 := (appSz V _ _ k p).2.1 L _ _ s1 a1
  have s2 : ContDiffAt ℝ ∞ (fun y => L (w (UpperTheory.V.Lit.Geo.flow W t y))) p := L.contDiff.contDiffAt.comp p s1
  have a3 := (appSz V _ _ k p).1 _ W _ _ s2 hW a2 ((hWs.of_le (Nat.le_succ k)).mono (le_abs_self c))
  have s3 : ContDiffAt ℝ ∞ (fun y => L (w (UpperTheory.V.Lit.Geo.flow W t y)) (W y)) p := s2.clm_apply hW
  have a4 := hC₂ _ _ p _ f2 hA.contDiffAt (fun i _ h2 => f3 i h2) ((hC₁ _ f3.norm_le).mono (le_abs_self C₁))
  have s4 := hA.contDiffAt.comp p f2
  have a5 := (appSz V _ _ k p).1 _ _ _ _ s4 s3 a4 a3
  have e : 2 ^ k * (C₂ * |C₁|) * (2 ^ k * (‖L‖ * C₃) * |c|) * b =
      2 ^ k * (C₂ * |C₁|) * (2 ^ k * (‖L‖ * (C₃ * b)) * |c|) := by ring
  rw [e]
  exact a5
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsPbSz
section
open UpperTheory.V.Lit.Geo.Cs

theorem UpperTheory.V.Lit.Geo.Cs.pbSz :
    PbSz := by
  intro V F _ _ _ _ _ _ q k c
  obtain ⟨hAcd, C2, hC2⟩ := altSz V F q k (1 + c)
  obtain ⟨C1, hC1, hcomp1⟩ := compSz V V (V [⋀^Fin q]→L[ℝ] F) k (1 + c)
  obtain ⟨C3, hC3, hcomp3⟩ := compSz V (V →L[ℝ] V)
    ((V [⋀^Fin q]→L[ℝ] F) →L[ℝ] (V [⋀^Fin q]→L[ℝ] F)) k (1 + c)
  refine ⟨2 ^ k * (C3 * max C2 0) * C1, by positivity, ?_⟩
  intro W t w p b ht hW hWs hw hws
  obtain ⟨hF1, hF2, hF3, hF4⟩ := flowSz V k c W t p ht hW hWs
  have hg := hcomp1 w (UpperTheory.V.Lit.Geo.flow W t) p b hF1 hw
    (fun i h1 h2 => hF4 i h1 (by omega)) hws
  have hL : ‖fderiv ℝ (UpperTheory.V.Lit.Geo.flow W t) p‖ ≤ 1 + c := by
    simpa using hF3 0 (Nat.zero_le _)
  have hA : Sz k _ (fderiv ℝ (UpperTheory.V.Lit.Geo.flow W t) p) (max C2 0) :=
    fun i hi => (hC2 _ hL i hi).trans (le_max_left _ _)
  have hf := hcomp3 _ (fderiv ℝ (UpperTheory.V.Lit.Geo.flow W t)) p (max C2 0) hF2
    hAcd.contDiffAt (fun i h1 h2 => hF3 i h2) hA
  have hprod := (appSz V (V [⋀^Fin q]→L[ℝ] F) (V [⋀^Fin q]→L[ℝ] F) k p).1 _ _ _ _
    (hAcd.contDiffAt.comp p hF2) (hw.comp p hF1) hf hg
  have e : 2 ^ k * (C3 * max C2 0) * C1 * b = 2 ^ k * (C3 * max C2 0) * (C1 * b) := by ring
  rw [e]
  exact hprod
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsRapidAll
section
open UpperTheory.V.Lit.Geo.Cs

private theorem le_div_one_add_pow_succ_of_mul_le {x K Q A C F : ℝ} {N : ℕ} (hQ : 1 ≤ Q) (hA : 0 ≤ A) (hN : A * C ≤ N)
    (hF : F ≤ C * (1 + Real.log Q)) (hx : 0 ≤ x) (h : x * Q ^ N ≤ K) :
    x ≤ K * Real.exp (A * C) * Real.exp (-(A * F)) := by
  have hQ0 : 0 < Q := lt_of_lt_of_le one_pos hQ
  have hl : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hp : Q ^ N = Real.exp (N * Real.log Q) := by
    rw [Real.exp_nat_mul, Real.exp_log hQ0]
  have h1 : A * F - A * C ≤ N * Real.log Q := by
    have := mul_le_mul_of_nonneg_left hF hA
    have := mul_le_mul_of_nonneg_right hN hl
    nlinarith
  have h2 : x * Real.exp (A * F - A * C) ≤ K := by
    refine le_trans ?_ h
    rw [hp]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h1) hx
  have h3 : x = x * Real.exp (A * F - A * C) * (Real.exp (A * C) * Real.exp (-(A * F))) := by
    rw [mul_assoc, ← Real.exp_add, ← Real.exp_add, show A * F - A * C + (A * C + -(A * F)) = 0 by ring,
      Real.exp_zero, mul_one]
  rw [h3, mul_assoc K]
  exact mul_le_mul_of_nonneg_right h2 (by positivity)

open GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
  GroundTheory.Automorphic.CuspidalSpectrum in
theorem UpperTheory.V.Lit.Geo.Cs.rapidAll :
    RapidAll := by
  intro E _ _ _ a U Ξ f lam C hlam hf q α hα hR
  obtain ⟨r, hr⟩ := UpperTheory.V.Lit.Bor.oneReal E a Ξ
  obtain ⟨hq1, hq2, -⟩ := UpperTheory.V.Lit.Geo.qhtFacts E a
  refine ⟨|r|, abs_nonneg r, fun A hA X j l => ?_⟩
  obtain ⟨he, hv⟩ := UpperTheory.V.Lit.Geo.Cs.rapidEig E a U Ξ r hr q α hα X j l
  obtain ⟨K, hK⟩ := hR l X ⌈A * C⌉₊
  refine ⟨K * Real.exp (A * C), fun g => ?_⟩
  obtain ⟨g₁, hs⟩ : ∃ g₁ : KernelIndexFullLattice.G1 E a, splitCentre E a (lam g) * g₁.1 = g := ⟨_, hlam.split g⟩
  have hK' := hK g₁
  have hq : qht g = qht (E := E) (a := a) g₁.1 := by
    have := hq2 1 (lam g) g₁.1
    rw [map_one, one_mul, hs] at this
    exact this
  have ha := UpperTheory.V.Lit.Bor.aInv E a _ _ he (lam g) g₁.1
  rw [hs] at ha
  rw [← hq] at hK'
  have hb := le_div_one_add_pow_succ_of_mul_le (hq1 g) hA (Nat.le_ceil (A * C)) (hf g) (norm_nonneg _)
    (le_trans (mul_le_mul_of_nonneg_right (norm_le_pi_norm _ j) (pow_nonneg (zero_le_one.trans (hq1 g)) _)) hK')
  have hb' : ‖((l.map (lie E a)).prod (Bor.cmp j (α X))).1 g₁.1‖ ≤
      K * Real.exp (A * C) * Real.exp (-(A * f g)) := by
    rw [← hv]
    exact hb
  have hc : ‖Complex.exp (-(r : ℂ) * (lam g : ℂ))‖ ≤ Real.exp (|r| * |lam g|) := by
    rw [Complex.norm_exp, Real.exp_le_exp, ← abs_mul]
    simpa using neg_le_abs (r * lam g)
  rw [ha, norm_mul, sub_eq_add_neg, Real.exp_add, mul_left_comm]
  exact mul_le_mul hc hb' (norm_nonneg _) (Real.exp_pos _).le
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsTpSz
section
open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff

theorem UpperTheory.V.Lit.Geo.Cs.tpSz :
    TpSz := by
  intro V F _ _ _ _ q k c
  obtain ⟨C, hC, h⟩ := compSz V V (V [⋀^Fin q]→L[ℝ] F) k c
  refine ⟨|c| * |c| ^ q * C, by positivity, fun A B w p b hA hB hw hs => ?_⟩
  have hA' : ‖A‖ ≤ |c| := hA.trans (le_abs_self c)
  have hB' : ‖B‖ ≤ |c| := hB.trans (le_abs_self c)
  have h1 : Sz k (fun y => w (A y)) p (C * b) := by
    refine h w A p b A.contDiff.contDiffAt hw (fun i hi _ => ?_) hs
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [← norm_iteratedFDeriv_fderiv]
    have e : fderiv ℝ (A : V → V) = fun _ => A := funext fun x => A.fderiv
    rw [e]
    rcases j with _ | j
    · simpa using hA
    · rw [iteratedFDeriv_succ_const]
      simpa using (norm_nonneg A).trans hA
  let L₀ : (V [⋀^Fin q]→L[ℝ] F) →ₗ[ℝ] (V [⋀^Fin q]→L[ℝ] F) :=
    { toFun := fun m => B.compContinuousAlternatingMap (m.compContinuousLinearMap A)
      map_add' := fun m n => by ext v; simp
      map_smul' := fun r m => by ext v; simp }
  have hL : ∀ m, ‖L₀ m‖ ≤ |c| * |c| ^ q * ‖m‖ := fun m => by
    refine ContinuousAlternatingMap.opNorm_le_bound _ (by positivity) fun v => ?_
    have a1 : ‖m fun i => A (v i)‖ ≤ ‖m‖ * ∏ i, ‖A (v i)‖ := m.le_opNorm _
    have a2 : ∏ i, ‖A (v i)‖ ≤ ∏ i, (|c| * ‖v i‖) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => A.le_of_opNorm_le hA' _
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at a2
    calc ‖L₀ m v‖ = ‖B (m fun i => A (v i))‖ := rfl
      _ ≤ |c| * ‖m fun i => A (v i)‖ := B.le_of_opNorm_le hB' _
      _ ≤ |c| * (‖m‖ * (|c| ^ q * ∏ i, ‖v i‖)) := by
        gcongr
        exact a1.trans (mul_le_mul_of_nonneg_left a2 (norm_nonneg _))
      _ = _ := by ring
  have hn : ‖L₀.mkContinuous _ hL‖ ≤ |c| * |c| ^ q := L₀.mkContinuous_norm_le (by positivity) hL
  have h2 := (appSz V (V [⋀^Fin q]→L[ℝ] F) (V [⋀^Fin q]→L[ℝ] F) k p).2.1 (L₀.mkContinuous _ hL)
    (fun y => w (A y)) (C * b) (hw.comp p A.contDiff.contDiffAt) h1
  refine Sz.mono h2 ?_
  rw [mul_assoc (|c| * |c| ^ q)]
  exact mul_le_mul_of_nonneg_right hn h1.nonneg
end

