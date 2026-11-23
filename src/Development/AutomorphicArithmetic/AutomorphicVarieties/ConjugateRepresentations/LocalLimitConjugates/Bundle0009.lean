module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CorrLim
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem basis_bd {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {n : ℕ}
    (b : Module.Basis (Fin n) ℝ V) (q : ℕ) : ∃ c : ℝ, 0 ≤ c ∧ ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
      (m : V [⋀^Fin q]→L[ℝ] F) (δ : ℝ), 0 ≤ δ → (∀ I : Fin q → Fin n, ‖m fun i => b (I i)‖ ≤ δ) →
      ∀ v, ‖m v‖ ≤ c * δ * ∏ i, ‖v i‖ := by
  refine ⟨∑ I : Fin q → Fin n, ∏ i, ‖LinearMap.toContinuousLinearMap (b.coord (I i))‖, by positivity, ?_⟩
  intro F _ _ m δ hδ h v
  have e : m v = ∑ I : Fin q → Fin n, (∏ i, b.repr (v i) (I i)) • m fun i => b (I i) := by
    have e1 : v = fun i => ∑ j, b.repr (v i) j • b j := funext fun i => (b.sum_repr (v i)).symm
    conv_lhs => rw [e1]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ContinuousAlternatingMap.map_sum]
    exact Finset.sum_congr rfl fun I _ => m.map_smul_univ _ _
  rw [e, mul_assoc, Finset.sum_mul]
  refine norm_sum_le_of_le _ fun I _ => ?_
  rw [norm_smul, norm_prod, mul_comm δ, ← mul_assoc, ← Finset.prod_mul_distrib]
  refine mul_le_mul (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => ?_) (h I) (norm_nonneg _) (by positivity)
  exact (LinearMap.toContinuousLinearMap (b.coord (I i))).le_opNorm (v i)

private theorem ev_cmp {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a d : ℕ}
    (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (g : GA E a) (j : Fin d) : ev m g j = (cmp j m).1 g := by
  induction m using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; rfl
  | tmul φ v => simp [mul_comm]
  | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, Submodule.coe_add, hx, hy]

private theorem cont_inf (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    Continuous (infGL E a) := by
  have hs : Continuous (sInf E : Cinf E → Ad E) := (GlobalTheory.CuspRep.continuous_infEq E).prodMk continuous_const
  exact Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map hs))

theorem UpperTheory.V.Cj.H.corrLim :
    UpperTheory.V.Cj.H.CorrLim := by
  intro E _ _ _ a ho U Ξ q ω w hw hl s K hK hKc
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
  obtain ⟨C, hC, hCK⟩ := coneCpt E a K hK hKc
  have c1 : Continuous fun g : GL (Fin a) (Cinf E) => toL g.val :=
    Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))
  have c2 : Continuous fun g : GL (Fin a) (Cinf E) => toL (g⁻¹).val :=
    Units.continuous_coe_inv (M := Matrix (Fin a) (Fin a) (Cinf E))
  obtain ⟨R1, hR1⟩ := hC.exists_bound_of_continuousOn c1.continuousOn
  obtain ⟨R2, hR2⟩ := hC.exists_bound_of_continuousOn c2.continuousOn
  obtain ⟨B, hB, hM⟩ := matBd E a Ξ (max R1 R2)
  let b := Module.finBasis ℝ (HV E a)
  obtain ⟨c, hc, hb⟩ := basis_bd b q
  have hD : IsCompact ((fun g => infGL E a g * finGL E a x) '' C) :=
    hC.image ((cont_inf E a).mul continuous_const)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hA : 0 ≤ c * B * B ^ q := by positivity
  obtain ⟨δ, hδ, hδε⟩ := exists_pos_mul_lt hε (c * B * B ^ q)
  have hev : ∀ᶠ k in atTop, ∀ (I : Fin q → Fin (Module.finrank ℝ (HV E a))) (j : Fin Ξ.d),
      ∀ y ∈ (fun g => infGL E a g * finGL E a x) '' C,
        dist ((0 : Sm E a).1 y) ((cmp j (ω k fun i => hv.symm (b (I i)))).1 y) < δ :=
    eventually_all.2 fun I => eventually_all.2 fun j =>
      Metric.tendstoUniformlyOn_iff.1 (hl (fun i => hv.symm (b (I i))) j _ hD) δ hδ
  filter_upwards [hev] with k hk p hp
  obtain ⟨g, hg, rfl⟩ := hCK p hp
  obtain ⟨m1, -, m3⟩ := hM g ((hR1 g hg).trans (le_max_left _ _)) ((hR2 g hg).trans (le_max_right _ _))
  rw [Pi.zero_apply, dist_zero_left]
  refine lt_of_le_of_lt (ContinuousAlternatingMap.opNorm_le_bound _ (by positivity) fun v => ?_) hδε
  have key := hb _ (((w k).1 x (sand g (hOne E a))).compContinuousLinearMap ((2 : ℝ) • sand g)) (B * δ)
    (by positivity) (fun I => ?_) fun i => (1 / 2 : ℝ) • sand g⁻¹ (v i)
  · have e : (((2 : ℝ) • sand g : HV E a →L[ℝ] HV E a) ∘ fun i => (1 / 2 : ℝ) • sand g⁻¹ (v i)) = v := by
      funext i
      simp only [Function.comp_apply, ContinuousLinearMap.smul_apply, map_smul, smul_smul]
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      norm_num
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, e] at key
    have hp : ∏ i, ‖(1 / 2 : ℝ) • sand g⁻¹ (v i)‖ ≤ B ^ q * ∏ i, ‖v i‖ := by
      have : B ^ q * ∏ i, ‖v i‖ = ∏ i, B * ‖v i‖ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [this]
      refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
      rw [norm_smul]
      have h3 := m3 (v i)
      have h4 := norm_nonneg (sand g⁻¹ (v i))
      have h5 : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
      rw [h5]
      linarith
    calc _ ≤ _ := key
      _ ≤ c * (B * δ) * (B ^ q * ∏ i, ‖v i‖) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by ring
  · have hc := hw k g x fun i => hv.symm (b (I i))
    simp only [LinearEquiv.apply_symm_apply] at hc
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    refine (congrArg norm hc).le.trans ((m1 _).trans (mul_le_mul_of_nonneg_left ?_ hB))
    refine (pi_norm_le_iff_of_nonneg hδ.le).2 fun j => ?_
    have := hk I j _ ⟨g, hg, rfl⟩
    rw [ev_cmp]
    simpa using this.le
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.HasDerivAtConv
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem hasDerivAt_conv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) (f ψ ψ' : G → ℂ) (hf : LocallyIntegrable f μ)
    (h' : Continuous ψ') (hs' : HasCompactSupport ψ')
    (hi : ∀ x, Integrable (fun y => f y * ψ (y⁻¹ * x)) μ) (hi' : ∀ x, Integrable (fun y => f y * ψ' (y⁻¹ * x)) μ)
    (c : ℝ → G) (hc : Continuous c) (c0 : c 0 = 1) (cadd : ∀ s t, c (s + t) = c s * c t)
    (hd : ∀ g, HasDerivAt (fun t => ψ (g * c t)) (ψ' g) 0) (x : G) :
    HasDerivAt (fun t => ∫ y, f y * ψ (y⁻¹ * (x * c t)) ∂μ) (∫ y, f y * ψ' (y⁻¹ * x) ∂μ) 0 := by
  obtain ⟨M, hM⟩ := h'.bounded_above_of_compact_support hs'
  let K : Set G := (fun p : ℝ × G => x * c p.1 * p.2⁻¹) '' (Set.Icc (-1 : ℝ) 1 ×ˢ tsupport ψ')
  have hK : IsCompact K := (isCompact_Icc.prod hs').image (by fun_prop)
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hb : Integrable (K.indicator fun y => ‖f y‖ * M) μ :=
    (integrable_indicator_iff hKm).2 ((hf.integrableOn_isCompact hK).norm.mul_const M)
  have hdt : ∀ g t, HasDerivAt (fun s => ψ (g * c s)) (ψ' (g * c t)) t := fun g t => by
    have h1 : HasDerivAt (fun s => ψ (g * c t * c s)) (ψ' (g * c t)) (t - t) := by
      rw [sub_self]; exact hd _
    have h2 := h1.comp_sub_const t t
    refine h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    simp only [mul_assoc, ← cadd, add_sub_cancel]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℝ)
    (F := fun t y => f y * ψ (y⁻¹ * (x * c t))) (F' := fun t y => f y * ψ' (y⁻¹ * (x * c t)))
    (x₀ := (0 : ℝ)) (s := Set.Icc (-1 : ℝ) 1) (bound := K.indicator fun y => ‖f y‖ * M)
    (Icc_mem_nhds (by norm_num) (by norm_num))
    (Eventually.of_forall fun t => (hi _).aestronglyMeasurable) (hi _) (hi' _).aestronglyMeasurable
    (Eventually.of_forall fun y t ht => by
      by_cases hy : y ∈ K
      · rw [Set.indicator_of_mem hy, norm_mul]
        exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
      · rw [Set.indicator_of_notMem hy]
        have : ψ' (y⁻¹ * (x * c t)) = 0 := by
          by_contra hne
          exact hy ⟨(t, y⁻¹ * (x * c t)), ⟨ht, subset_tsupport _ hne⟩, by simp [mul_assoc]⟩
        simp [this]) hb
    (Eventually.of_forall fun y t _ => by
      simpa only [mul_assoc] using (hdt (y⁻¹ * x) t).const_mul (f y))
  simpa only [c0, mul_one] using key.2

theorem UpperTheory.V.Cj.H.cvLie :
    UpperTheory.V.Cj.H.CvLie := by
  intro E _ _ _ a μ _ _ ψ φ hψ F hφ X
  obtain ⟨c, c0, cadd, ccont, cder, -⟩ := UpperTheory.V.Lit.Bor.oneParam E a X
  have t1 := UpperTheory.V.Cj.H.testOps E a ψ
  have hψ' : IsTest (lie E a X ψ) := (t1.2 hψ).1 X
  have k1 : Continuous ψ.1 := (t1.1 hψ.2).1
  have k2 : Continuous (lie E a X ψ).1 := ((UpperTheory.V.Cj.H.testOps E a _).1 hψ'.2).1
  funext x
  have d := hasDerivAt_conv μ (GlobalTheory.AutomorphicL2Unitary.lift (latticeGL E a) F) ψ.1 (lie E a X ψ).1
    ((UpperTheory.V.Cj.H.locInt (GA E a) (latticeGL E a) μ).1 F) k2 hψ'.1
    ((UpperTheory.V.Cj.H.cvAlg (GA E a) (latticeGL E a) μ ψ.1 k1 hψ.1).1 F)
    ((UpperTheory.V.Cj.H.cvAlg (GA E a) (latticeGL E a) μ _ k2 hψ'.1).1 F)
    (fun s => infGL E a (c s)) ccont (by rw [c0, map_one]) (fun s t => by rw [cadd, map_mul])
    (fun g => hasDerivAt_curve ψ g c X c0 cder) x
  have d' := hasDerivAt_curve φ x c X c0 cder
  exact d'.unique (d.congr_of_eventuallyEq (Eventually.of_forall fun t => congrFun hφ _))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ResExact
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.resExact :
    UpperTheory.V.Cj.H.ResExact := by
  intro E _ _ _ a ha n e he U Ξ r c hc q ω hω hd
  obtain ⟨k0, k1⟩ := kugaSm E a n e he Ξ r c hc
  cases q with
  | zero => exact ⟨k0 ω hω.equiv hd, fun _ _ => trivial⟩
  | succ q =>
    have hk := k1 q ω hω.equiv hd
    obtain ⟨d1, d2⟩ := delLev E a n e he U Ξ r q ω
    obtain ⟨l1, l2, -⟩ := levLin E a U Ξ q
    have hl := d1 hω
    refine ⟨⟨(-1 : ℂ) • del (smAdj Ξ r) e ω + (0 : ℂ) • del (smAdj Ξ r) e ω, l1 _ _ _ _ hl hl, ?_⟩, fun hs h0 => ?_⟩
    · rw [l2, hk, zero_smul, add_zero]
      exact AlternatingMap.ext fun X => neg_one_smul ℂ _
    · rw [hk, neg_eq_zero] at h0
      exact (sqOrth E a ha n e he Ξ r q).2 ω hs (d2 hs) h0
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.TmulMem
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem tens_map {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (N : Submodule ℂ W)
    (T : Module.End ℂ (W ⊗[ℂ] (Fin d → ℂ))) (h : ∀ φ ∈ N, ∀ v, T (φ ⊗ₜ[ℂ] v) ∈ tens d N) :
    ∀ m ∈ tens d N, T m ∈ tens d N := by
  intro m hm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← sum_cmp m, map_sum]
  exact Submodule.sum_mem _ fun i _ => h _ (mem_tens.1 hm i) _

private theorem tmul_mem {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} {N : Submodule ℂ W} {φ : W} (h : φ ∈ N)
    (v : Fin d → ℂ) : φ ⊗ₜ[ℂ] v ∈ tens d N :=
  mem_tens.2 fun i => by rw [cmp_tmul]; exact N.smul_mem _ h

theorem UpperTheory.V.Cj.H.wigSm :
    UpperTheory.V.Cj.H.WigSm := by
  intro E _ _ _ a Ξ N hN τ m hm u q ω hc hd hv
  obtain ⟨hA, hB, hAB, -, -, hI⟩ := smAB E a Ξ
  obtain ⟨c1, c2, -, -⟩ := capSm E a Ξ τ u
  have hs : smA Ξ + smB Ξ = smLie Ξ := LinearMap.ext fun X => by
    rw [LinearMap.add_apply, smA_apply, smB_apply]; rfl
  have key := wigSub E a _ (smA Ξ) (smB Ξ) hA hB hAB (tens Ξ.d N)
    (fun X => tens_map N _ fun φ hφ v => by
      rw [smA_apply, LinearMap.rTensor_tmul]; exact tmul_mem (hN X φ hφ) _)
    (fun X => tens_map N _ fun φ hφ v => by
      rw [smB_apply, LinearMap.lTensor_tmul]; exact tmul_mem hφ _)
    τ (u + ((a : ℂ) - 1) / 2)
    ((cap τ u - (m.map (u + ·)).prod • (1 : Module.End ℂ (Sm E a))).rTensor (Fin Ξ.d → ℂ)) (by
      rw [c1, c2 m hm, LinearMap.rTensor_sub, LinearMap.rTensor_smul]
      congr 2
      exact LinearMap.rTensor_id _ _)
  rw [hs] at key
  cases q with
  | zero =>
    show app _ ω = 0
    refine AlternatingMap.ext fun Y => ?_
    exact key.1 ω (hI _ ω hc) hd Y
  | succ q =>
    obtain ⟨η, h1, h2⟩ := key.2 q ω (hI _ ω hc) hd (fun Y => mem_tens.2 (hv Y))
    exact ⟨η, fun X => mem_tens.1 (h1 X), AlternatingMap.ext fun Y => h2 Y⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ZigLim
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section

variable {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ} {G : Dr.Geo Γ V S d} {q : ℕ}

private theorem fLim_add {w w' : ℕ → G.Om q} (h : FLim G w) (h' : FLim G w') : FLim G fun j => w j + w' j := by
  intro s K hK hc
  have := (h s K hK hc).add (h' s K hK hc)
  rw [add_zero] at this
  exact this

private theorem fLim_zsmul (n : ℤ) {w : ℕ → G.Om q} (h : FLim G w) : FLim G fun j => n • w j := by
  intro s K hK hKc
  have h1 := (uniformContinuous_id.const_smul n).comp_tendstoUniformlyOn (h s K hK hKc)
  convert (preTransparency := .reducible) h1 using 1
  · funext k x
    simp
  · funext x
    simp

private theorem fLim_sum {ι : Type} (T : Finset ι) {w : ι → ℕ → G.Om q} (h : ∀ i ∈ T, FLim G (w i)) :
    FLim G fun j => ∑ i ∈ T, w i j := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro s K _ _
    simp only [Finset.sum_empty, ZeroMemClass.coe_zero, Pi.zero_apply]
    exact Metric.tendstoUniformlyOn_iff.2 fun ε hε =>
      Filter.Eventually.of_forall fun _ x _ => by simpa using hε
  | insert i T hi ih =>
    have hsum := fLim_add (h i (Finset.mem_insert_self i T))
      (ih fun i' hi' => h i' (Finset.mem_insert_of_mem hi'))
    simpa [Finset.sum_insert hi] using hsum

end

theorem UpperTheory.V.Cj.H.zigLim :
    UpperTheory.V.Cj.H.ZigLim := by
  intro Γ V S _ _ _ _ d G hconv hne
  obtain ⟨p, hp⟩ := hne
  have hincl := inclFacts Γ V S d G hconv ⟨p, hp⟩
  have main : ∀ (q k : ℕ) (u : ℕ → List Γ → G.Om q), (∀ j, HCoc (G.act q) k (u j)) →
      (∀ j (x : List Γ), x.length = k + 1 → G.dOm q (u j x) = 0) →
      (∀ x : List Γ, x.length = k + 1 → FLim G fun j => u j x) →
      ∃ c : ℕ → List Γ → S → Fin d → ℂ, (∀ j, Zig G q k (u j) (c j)) ∧
        ∀ x : List Γ, x.length = k + q + 1 → ∀ s, Tendsto (fun j => c j x s) atTop (𝓝 0) := by
    intro q
    induction q with
    | zero =>
      intro k u _ hcl hlim
      classical
      have hex : ∀ j (x : List Γ), x.length = k + 1 → ∃ f, G.incl f = u j x :=
        fun j x hx => (hincl.2.2 (u j x)).mp (hcl j x hx)
      choose f hf using hex
      refine ⟨fun j x => if h : x.length = k + 1 then f j x h else 0, ?_, ?_⟩
      · intro j x hx
        show u j x = G.incl (if h : x.length = k + 1 then f j x h else 0)
        rw [dif_pos hx, hf j x hx]
      · intro x hx s
        have hx' : x.length = k + 1 := by simpa using hx
        have ht := (hlim x hx' s {p} (Set.singleton_subset_iff.2 hp)
          isCompact_singleton).tendsto_at (Set.mem_singleton p)
        have hc := ((continuous_eval_const (fun _ : Fin 0 => (0 : V))).tendsto _).comp ht
        have heq : ∀ j, ((u j x : S → V → V [⋀^Fin 0]→L[ℝ] (Fin d → ℂ)) s p) (fun _ => 0) =
            f j x hx' s := by
          intro j
          rw [← hf j x hx']
          simp [Dr.Geo.incl, Set.indicator_of_mem hp]
        simp only [dif_pos hx']
        have hfun : (fun j => f j x hx' s) =
            fun j => ((u j x : S → V → V [⋀^Fin 0]→L[ℝ] (Fin d → ℂ)) s p) (fun _ => 0) :=
          funext fun j => (heq j).symm
        rw [hfun]
        simp at hc
        exact hc
    | succ q ih =>
      intro k u hcoc hcl hlim
      obtain ⟨K, hK1, hK2, hK3⟩ := poinOp Γ V S d G hconv q
      have hpt : ∀ x : List Γ, G.ρ (x.headD 1) p ∈ G.Y := fun x => G.maps _ p hp
      have hbeq : ∀ j, HEquiv (G.act q) k (fun x => K (G.ρ (x.headD 1) p) (u j x)) := by
        intro j γ x hx
        have hne : x ≠ [] := by
          rintro rfl
          simp at hx
        obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hne
        have hu := (hcoc j).1 γ (y :: ys) hx
        simp only [List.map_cons] at hu
        simp only [List.map_cons, List.headD_cons, map_mul]
        rw [hu, hK2 γ _ (G.maps y p hp)]
        rfl
      have hlen : ∀ (x : List Γ) i, x.length = k + 1 + 1 → i ∈ Finset.range x.length →
          (x.eraseIdx i).length = k + 1 := by
        intro x i hx hi
        rw [List.length_eraseIdx_of_lt (Finset.mem_range.1 hi)]
        omega
      have hcl' : ∀ j (x : List Γ), x.length = k + 1 + 1 →
          G.dOm q (hd (fun x => K (G.ρ (x.headD 1) p) (u j x)) x) = 0 := by
        intro j x hx
        have h0 := (hcoc j).2 x hx
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [hd, map_sum, map_zsmul] at h0 ⊢
        rw [← h0]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hK1 _ (hpt _) _ (hcl j _ (hlen x i hx hi))]
      have hlim' : ∀ x : List Γ, x.length = k + 1 + 1 →
          FLim G fun j => hd (fun x => K (G.ρ (x.headD 1) p) (u j x)) x := by
        intro x hx
        simp only [hd]
        apply fLim_sum
        intro i hi
        apply fLim_zsmul
        exact hK3 _ (hpt _) _ (hlim _ (hlen x i hx hi))
      obtain ⟨c, hc1, hc2⟩ := ih (k + 1) (fun j => hd (fun x => K (G.ρ (x.headD 1) p) (u j x)))
        (fun j => hdHd Γ (G.Om q) (G.act q) k _ (hbeq j)) hcl' hlim'
      refine ⟨c, fun j => ⟨_, hbeq j, fun x hx => hK1 _ (hpt _) _ (hcl j x hx), hc1 j⟩, ?_⟩
      intro x hx s
      exact hc2 x (by omega) s
  exact main
end

