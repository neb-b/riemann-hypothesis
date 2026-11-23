module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.WordDerivativeBlocks
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0734
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0719
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0731
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
public import Formalism.MeanHeightDescent.AverageDegreeBounds.GlobalBoundRefinements
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0721
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0466

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivAtZeroReindexEqTaylorCoefficient
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.DerivReindex

open GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials

theorem wordDeriv_eq {Λ W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] (dir : Λ → W) (l : List Λ)
    (F : W → ℂ) (p : W) {n : ℕ} (h : l.length = n) :
    iteratedFDeriv ℂ n F p (fun i => dir (l.get ⟨i, by rw [h]; exact i.2⟩)) = wordDeriv dir l F p := by
  subst h; rfl

theorem wordDeriv_comp {Λ Λ' W W' : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [NormedAddCommGroup W'] [NormedSpace ℂ W'] (dir : Λ → W) (dir' : Λ' → W') (g : Λ → Λ')
    (T : W →L[ℂ] W') (hT : ∀ x, T (dir x) = dir' (g x)) (l : List Λ) (F : W' → ℂ)
    (hF : ContDiff ℂ l.length F) :
    wordDeriv dir l (F ∘ T) 0 = wordDeriv dir' (l.map g) F 0 := by
  rw [← wordDeriv_eq dir' (l.map g) F 0 (n := l.length) (by simp), wordDeriv,
    T.iteratedFDeriv_comp_right hF 0 le_rfl, map_zero,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  simp [hT]

theorem derivAt0_reindex : ∀ (D : D7) (ι : Type) [Fintype ι] (e : ι ≃ D.what₂.Tau) (a b : ℕ) (F : TaylorLogMetric.VC D a b → ℂ), Differentiable ℂ F → ∀ m : DVar ι a b →₀ ℕ, derivAt0 (fun z : VCx ι a b => F fun τ => z (e.symm τ)) m = (m.prod fun _ n => (n.factorial : ℂ)) * TaylorLogMetric.taylor D F (Finsupp.equivMapDomain (e.prodCongr (Equiv.refl (Fin b × Fin a))) m) := by
  intro D ι _ e a b F hF m
  have han : AnalyticOnNhd ℂ F Set.univ := GlobalTheory.SCV.analyticOnNhd_of_differentiable hF _
  set g := e.prodCongr (Equiv.refl (Fin b × Fin a)) with hg
  let T : VCx ι a b →L[ℂ] TaylorLogMetric.VC D a b :=
    ContinuousLinearMap.pi fun τ => ContinuousLinearMap.proj (e.symm τ)
  have hT : ∀ x, T (coordX x) = TaylorLogMetric.coordV D (g x) := by
    intro x
    funext τ i j
    change coordX x (e.symm τ) i j = _
    unfold coordX TaylorLogMetric.coordV
    exact @if_congr _ _ _ (_) (_) _ _ _ _ (and_congr_left' e.symm_apply_eq) rfl rfl
  have hne : (m.prod fun _ n => (n.factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have h1 : derivAt0 (fun z : VCx ι a b => F fun τ => z (e.symm τ)) m
      = wordDeriv coordX m.toMultiset.toList (F ∘ T) 0 :=
    wordDeriv_eq coordX m.toMultiset.toList (F ∘ T) 0 (Multiset.length_toList _)
  have h2 : TaylorLogMetric.taylor D F (Finsupp.equivMapDomain g m)
      = wordDeriv (TaylorLogMetric.coordV D) (Finsupp.equivMapDomain g m).toMultiset.toList F 0 /
        (m.prod fun _ n => (n.factorial : ℂ)) := by
    rw [TaylorLogMetric.taylor, Finsupp.prod_equivMapDomain]
    congr 1
    exact wordDeriv_eq _ _ F 0 (Multiset.length_toList _)
  rw [h1, h2, mul_div_cancel₀ _ hne, wordDeriv_comp coordX (TaylorLogMetric.coordV D) g T hT _ F han.contDiff]
  refine wordDeriv_perm _ (han 0 trivial) ?_
  rw [← Multiset.coe_eq_coe, ← Multiset.map_coe, Multiset.coe_toList, Multiset.coe_toList,
    Finsupp.toMultiset_map, Finsupp.equivMapDomain_eq_mapDomain]

end GlobalTheory.DerivReindex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivWeierstrassPMulProdTranslateKernel
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem derivWeierstrassP_mul_prod_translate_kernel :
    ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), α ≠ 0 → Formalism.L2.Th1.F.MulStable L α → IsKerReps L α S →
      Even S.card → ∀ z, α * z ∉ L.lattice →
      L.derivWeierstrassP z * ∏ t ∈ S, L.derivWeierstrassP (z + t)
        = (∏ t ∈ S, L.derivWeierstrassP t) * α ^ 3 * L.derivWeierstrassP (α * z) := by
  intro L α S hα hst hS hev z hz
  have hper : ∀ z l, l ∈ L.lattice → L.derivWeierstrassP (z + l) = L.derivWeierstrassP z :=
    fun z l hl => L.derivWeierstrassP_add_coe z ⟨l, hl⟩
  obtain ⟨k1, k2⟩ := _root_.GlobalTheory.KerPerm.prod_ker_translate_neg L α S L.derivWeierstrassP hS hst hper
  have hdiff : ∀ w, w ∉ L.lattice → DifferentiableAt ℂ L.derivWeierstrassP w := fun w hw =>
    (L.analyticOnNhd_derivWeierstrassP w hw).differentiableAt
  have hcancel : ∀ w : ℂ, α * (w / α) = w := fun w => mul_div_cancel₀ w hα
  have h1 : ∀ w, w ∉ L.lattice → w / α ∉ L.lattice := fun w hw h => by
    have := hst _ h
    rw [hcancel] at this
    exact hw this
  have h2 : ∀ w, w ∉ L.lattice → ∀ t ∈ S, w / α + t ∉ L.lattice := fun w hw t ht h => by
    have h3 := hst _ h
    rw [mul_add, hcancel] at h3
    have h4 := L.lattice.sub_mem h3 (hS.1 t ht).1
    rw [add_sub_cancel_right] at h4
    exact hw h4
  set c : ℂ := ∏ t ∈ S, L.derivWeierstrassP t with hc
  have key := _root_.GlobalTheory.eq_zero_of_odd_elliptic_of_tendsto L
    (fun w => L.derivWeierstrassP (w / α) * ∏ t ∈ S, L.derivWeierstrassP (w / α + t)
      - c * α ^ 3 * L.derivWeierstrassP w) ?_ ?_ ?_ ?_ (α * z) hz
  · have e : α * z / α = z := mul_div_cancel_left₀ z hα
    simp only [e] at key
    exact sub_eq_zero.mp key
  · intro w hw
    have d0 : DifferentiableAt ℂ (fun w : ℂ => w / α) w := differentiableAt_id.div_const α
    refine DifferentiableAt.sub (DifferentiableAt.mul ?_ ?_) ((hdiff w hw).const_mul _)
    · exact DifferentiableAt.comp w (g := L.derivWeierstrassP) (hdiff _ (h1 w hw)) d0
    · refine DifferentiableAt.fun_finsetProd fun t ht => ?_
      exact DifferentiableAt.comp w (g := L.derivWeierstrassP) (f := fun w : ℂ => w / α + t)
        (hdiff _ (h2 w hw t ht)) (d0.add_const t)
  · intro w l _ hl
    have := k1 (w / α) (l / α) (by rw [hcancel]; exact hl)
    simp only [add_div, this, hper w l hl]
  · intro w _
    have e1 : ∏ t ∈ S, L.derivWeierstrassP (-w / α + t) = ∏ t ∈ S, L.derivWeierstrassP (w / α + t) := by
      rw [← k2 (w / α)]
      have : ∀ t ∈ S, L.derivWeierstrassP (-w / α + t) = (-1) * L.derivWeierstrassP (w / α - t) := by
        intro t _
        rw [neg_one_mul, ← L.derivWeierstrassP_neg]
        congr 1
        ring
      rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_const, hev.neg_one_pow, one_mul]
    simp only [e1]
    rw [neg_div, L.derivWeierstrassP_neg, L.derivWeierstrassP_neg]
    ring
  · have c0 := _root_.GlobalTheory.CMModel.tendsto_cube_mul_derivWeierstrassP L
    have tdiv : Filter.Tendsto (fun w : ℂ => w / α) (𝓝 0) (𝓝 0) := by
      have : Continuous (fun w : ℂ => w / α) := continuous_id.div_const α
      simpa using this.tendsto 0
    have tdiv' : Filter.Tendsto (fun w : ℂ => w / α) (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨tdiv.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact div_ne_zero hw hα
    have t1 := c0.comp tdiv'
    have t2 : Filter.Tendsto (fun w : ℂ => ∏ t ∈ S, L.derivWeierstrassP (w / α + t)) (𝓝[≠] 0) (𝓝 c) := by
      refine tendsto_finsetProd S fun t ht => ?_
      have ht' := (hdiff t (hS.1 t ht).2).continuousAt.tendsto
      have : Filter.Tendsto (fun w : ℂ => w / α + t) (𝓝[≠] 0) (𝓝 t) := by
        simpa using (tdiv.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))).add_const t
      exact ht'.comp this
    have t3 := ((t1.const_mul (α ^ 3)).mul t2).sub (c0.const_mul (c * α ^ 3))
    have e : α ^ 3 * (-2) * c - c * α ^ 3 * (-2) = 0 := by ring
    rw [e] at t3
    refine t3.congr fun w => ?_
    simp only [Function.comp]
    field_simp

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightNodesFarAndSpread
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop

theorem Wts.node_lower_int {ι : Type} {N : ℕ} (W : Wts ι N) (H : W.Hyp) (hd : W.IsDiv) (τ : ι) :
    ∀ (n : ℕ) (i : Fin N), (i : ℕ) + 1 = W.kc + n →
      -W.u τ i - (if W.p ≤ (i : ℕ) then W.c0 + 2 * (N : ℤ) else 0) - n * ((W.T : ℤ) + W.Dd + 1) ≤
        ((W.T : ℤ) + W.Dd + 1) * (-W.u1 τ i) := by
  intro n
  have hkp := H.kc_lt
  induction n with
  | zero =>
    intro i hi
    have h1 := (hd τ).1 i (by simpa using hi)
    have h2 := H.anchor τ i (by simpa using hi)
    have h3 : ¬ W.p ≤ (i : ℕ) := by omega
    simp [h1, h2, h3]
  | succ n ih =>
    intro i hi
    have hk := H.kc_pos
    have hlt : (i : ℕ) - 1 < N := by omega
    have hab : (i : ℕ) = ((⟨(i : ℕ) - 1, hlt⟩ : Fin N) : ℕ) + 1 := by simp; omega
    have ha : ((⟨(i : ℕ) - 1, hlt⟩ : Fin N) : ℕ) + 1 = W.kc + n := by simp; omega
    generalize (⟨(i : ℕ) - 1, hlt⟩ : Fin N) = a at hab ha
    have h1 := ih a ha
    have h2 := (hd τ).2 a i hab
    have hM : (0 : ℤ) < (W.T : ℤ) + W.Dd + 1 := by positivity
    generalize (W.T : ℤ) + W.Dd + 1 = M at h1 h2 hM ⊢
    set x := (W.u τ a - W.u τ i + if (i : ℕ) = W.p then -W.c0 - (2 * (N : ℤ) - 2) else 2) with hx
    have h3 := Int.mul_ediv_add_emod x M
    have h4 := Int.emod_lt_of_pos x hM
    rw [← h2] at h3
    have h5 : M * -W.u1 τ i = M * -W.u1 τ a + M * (W.u1 τ a - W.u1 τ i) := by ring
    have h6 : ((n + 1 : ℕ) : ℤ) * M = n * M + M := by push_cast; ring
    rw [h5, h6]
    by_cases hp : (i : ℕ) = W.p
    · have e1 : W.p ≤ (i : ℕ) := by omega
      have e2 : ¬ W.p ≤ (a : ℕ) := by omega
      rw [if_pos hp] at hx
      rw [if_neg e2] at h1
      rw [if_pos e1]
      linarith
    · rw [if_neg hp] at hx
      by_cases e1 : W.p ≤ (i : ℕ)
      · have e2 : W.p ≤ (a : ℕ) := by omega
        rw [if_pos e2] at h1
        rw [if_pos e1]
        linarith
      · have e2 : ¬ W.p ≤ (a : ℕ) := by omega
        rw [if_neg e2] at h1
        rw [if_neg e1]
        linarith

theorem nodes_far_and_spread : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : Wts ι N), W.Hyp → W.IsDiv → ∀ τ, (∀ i : Fin N, W.kc ≤ (i : ℕ) → W.w τ / (2 * W.T) ≤ -(W.u1 τ i : ℝ) ∧ W.w τ / (4 * W.T) ≤ |(W.u' τ i : ℝ)|) ∧ ∀ i l : Fin N, (W.u' τ i : ℝ) - W.u' τ l ≤ 3 / 2 * W.w τ / W.T := by
  intro ι _ N W H hd τ
  have hk := H.kc_pos
  have hkp := H.kc_lt
  have hpN := H.p_lt
  have hc0 : (0 : ℝ) ≤ W.c0 := by exact_mod_cast H.weightConst_nonneg
  have hT : 4 * (W.Dd : ℝ) + 4 ≤ W.T := by exact_mod_cast H.h1
  have hD : (0 : ℝ) ≤ W.Dd := by positivity
  have hN : (0 : ℝ) ≤ N := by positivity
  have hT0 : (0 : ℝ) < W.T := by linarith
  have hw := H.h3w τ
  have hS : 0 ≤ W.S := by
    have := H.h3cloud τ ⟨0, by omega⟩ (by simp; omega)
    have h0 : (0 : ℝ) ≤ W.u τ ⟨0, by omega⟩ := by exact_mod_cast this.1
    linarith [this.2]
  have hr : 0 ≤ W.eta + W.S + N := (abs_nonneg _).trans (H.h3node τ ⟨W.p, hpN⟩ hkp.le)
  have hNT : 4 * (N : ℝ) ≤ N * W.T := by nlinarith
  have hw0 : 0 ≤ W.w τ := by linarith
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = W.w τ / W.T := ⟨_, rfl⟩
  have hqT : W.w τ = q * W.T := by rw [hq]; field_simp
  have e2 : W.w τ / (2 * W.T) = q / 2 := by rw [hq]; field_simp
  have e4 : W.w τ / (4 * W.T) = q / 4 := by rw [hq]; field_simp
  have e3 : 3 / 2 * W.w τ / W.T = 3 / 2 * q := by rw [hq]; field_simp
  rw [e2, e4, e3]
  have hq20 : 20 * (N : ℝ) ≤ q := by
    have : 20 * (N : ℝ) * W.T ≤ q * W.T := by linarith
    exact le_of_mul_le_mul_right this hT0
  have hq0 : 0 ≤ q := by linarith
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (W.T : ℝ) + W.Dd + 1 := ⟨_, rfl⟩
  have hM0 : 0 < M := by linarith
  have hM1 : M ≤ 5 / 4 * W.T := by linarith
  have hM2 : (W.T : ℝ) ≤ M := by linarith
  have hu' : ∀ i : Fin N, (W.u1 τ i : ℝ) ≤ W.u' τ i ∧ (W.u' τ i : ℝ) ≤ W.u1 τ i + 3 * N ∧
      ((i : ℕ) < W.kc → (W.u' τ i : ℝ) = W.u1 τ i) := by
    intro i
    unfold Wts.u'
    by_cases h : (i : ℕ) < W.p
    · simp [h]
    · simp only [h, if_false]
      push_cast
      exact ⟨by linarith, le_rfl, fun h' => by omega⟩
  have node : ∀ i : Fin N, W.kc ≤ (i : ℕ) → q / 2 ≤ -(W.u1 τ i : ℝ) := by
    intro i hi
    have h1 := W.node_lower_int H hd τ ((i : ℕ) + 1 - W.kc) i (by omega)
    have hn : (((i : ℕ) + 1 - W.kc : ℕ) : ℝ) ≤ N := by
      have : (i : ℕ) + 1 - W.kc ≤ N := by omega
      exact_mod_cast this
    generalize (i : ℕ) + 1 - W.kc = n at h1 hn
    have h2 : -W.u τ i - (W.c0 + 2 * (N : ℤ)) - n * ((W.T : ℤ) + W.Dd + 1) ≤
        ((W.T : ℤ) + W.Dd + 1) * (-W.u1 τ i) := by
      have := H.weightConst_nonneg
      split_ifs at h1
      · exact h1
      · have : (0 : ℤ) ≤ N := by positivity
        linarith
    have h3 : -(W.u τ i : ℝ) - (W.c0 + 2 * (N : ℝ)) - n * M ≤ M * (-(W.u1 τ i : ℝ)) := by
      rw [hM]; exact_mod_cast h2
    have h4 := (abs_le.1 (H.h3node τ i hi)).2
    have h5 : (n : ℝ) * M ≤ q / 10 * M := mul_le_mul_of_nonneg_right (by linarith) hM0.le
    have h6 : q * M ≤ q * (5 / 4 * W.T) := mul_le_mul_of_nonneg_left hM1 hq0
    have h7 : M * (q / 2) ≤ M * (-(W.u1 τ i : ℝ)) := by nlinarith
    exact le_of_mul_le_mul_left h7 hM0
  have ent : ∀ i : Fin N, M * |(W.u1 τ i : ℝ)| ≤ |(W.u τ i : ℝ)| + W.c0 + 4 * N := by
    intro i
    rw [hM]
    exact_mod_cast (GlobalTheory.MeanTop.divided_entries ι N W H hd τ i).1
  refine ⟨fun i hi => ⟨node i hi, ?_⟩, fun i l => ?_⟩
  · have h1 := node i hi
    have h2 := (hu' i).2.1
    have h3 := neg_le_abs (W.u' τ i : ℝ)
    linarith
  · have up : M * (W.u' τ i : ℝ) ≤ W.S + W.c0 + 4 * N := by
      by_cases hi : (i : ℕ) < W.kc
      · rw [(hu' i).2.2 hi]
        have h1 := ent i
        have h2 := H.h3cloud τ i hi
        have h3 : (0 : ℝ) ≤ W.u τ i := by exact_mod_cast h2.1
        rw [abs_of_nonneg h3] at h1
        have h4 := mul_le_mul_of_nonneg_left (le_abs_self (W.u1 τ i : ℝ)) hM0.le
        linarith [h2.2]
      · have h1 := node i (by omega)
        have h2 := (hu' i).2.1
        have h3 : M * (W.u' τ i : ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hM0.le (by linarith)
        linarith
    have lo : M * (-(W.u' τ l : ℝ)) ≤ W.w τ + (W.eta + W.S + N) + W.S + W.c0 + 4 * N := by
      have h1 := ent l
      have h2 : -(W.u' τ l : ℝ) ≤ |(W.u1 τ l : ℝ)| := by
        linarith [(hu' l).1, neg_le_abs (W.u1 τ l : ℝ)]
      have h3 := mul_le_mul_of_nonneg_left h2 hM0.le
      have h4 : |(W.u τ l : ℝ)| ≤ W.w τ + (W.eta + W.S + N) + W.S := by
        by_cases hl : (l : ℕ) < W.kc
        · have h2 := H.h3cloud τ l hl
          have h3 : (0 : ℝ) ≤ W.u τ l := by exact_mod_cast h2.1
          rw [abs_of_nonneg h3]
          linarith [h2.2]
        · have h5 := abs_le.1 (H.h3node τ l (by omega))
          rw [abs_le]
          constructor <;> linarith [h5.1, h5.2]
      linarith
    have h6 : q * W.T ≤ q * M := mul_le_mul_of_nonneg_left hM2 hq0
    have h7 : M * ((W.u' τ i : ℝ) - W.u' τ l) ≤ M * (3 / 2 * q) := by nlinarith
    exact le_of_mul_le_mul_left h7 hM0

end GlobalTheory.MeanTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquidistributedIdealClassesOfHilbertClassFieldJ
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors
open GlobalTheory.Published
open scoped IntermediateField

noncomputable section

namespace GlobalTheory.EquidistJ

theorem card_ext_mul_finrank (L M : IntermediateField ℚ ℂ) (hML : M ≤ L) [FiniteDimensional ℚ L] (σ : ℂ ≃+* ℂ) :
    Nat.card {τ : L →+* ℂ // ∀ x : L, (x : ℂ) ∈ M → τ x = σ x} * Module.finrank ℚ M = Module.finrank ℚ L := by
  let E := IntermediateField.extendScalars hML
  have hEL : Module.finrank ℚ E = Module.finrank ℚ L := rfl
  have hEpos : 0 < Module.finrank ℚ E := by rw [hEL]; exact Module.finrank_pos
  haveI : FiniteDimensional ℚ E := Module.finite_of_finrank_pos hEpos
  haveI : FiniteDimensional M E := FiniteDimensional.right ℚ M E
  let ι : L →+* E :=
    { toFun := fun x => ⟨x.1, x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl }
  let ι' : E →+* L :=
    { toFun := fun x => ⟨x.1, x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl }
  let e : {τ : L →+* ℂ // ∀ x : L, (x : ℂ) ∈ M → τ x = σ x} ≃ (E →ₐ[M] ℂ) :=
    { toFun := fun τ =>
        { toRingHom := σ.symm.toRingHom.comp (τ.1.comp ι')
          commutes' := fun m => by
            change σ.symm (τ.1 ⟨m.1, hML m.2⟩) = m.1
            rw [τ.2 ⟨m.1, hML m.2⟩ m.2]
            exact σ.symm_apply_apply _ }
      invFun := fun f => ⟨σ.toRingHom.comp (f.toRingHom.comp ι), fun x hx => by
          change σ (f ⟨x.1, x.2⟩) = σ x.1
          congr 1
          exact f.commutes ⟨x.1, hx⟩⟩
      left_inv := fun τ => Subtype.ext (RingHom.ext fun x => by
          change σ (σ.symm (τ.1 ⟨x.1, x.2⟩)) = τ.1 x
          rw [σ.apply_symm_apply])
      right_inv := fun f => AlgHom.ext fun x => by
          change σ.symm (σ (f ⟨x.1, x.2⟩)) = f x
          rw [σ.symm_apply_apply] }
  set_option synthInstance.maxHeartbeats 200000 in
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, AlgHom.card M E ℂ, mul_comm,
      Module.finrank_mul_finrank ℚ M E, hEL]

theorem equidistributed_of_hilbertClassFieldJ : ∀ (hH : GlobalTheory.Published.HilbertClassFieldJ) {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) (φK : K →+* ℂ) (ΛK : PeriodPair) (hΛ : IsLatOf φK 1 ΛK) (𝔞 : (ℂ ≃+* ℂ) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (h𝔞 : ∀ σ : ℂ ≃+* ℂ, Fixes φK σ → ∃ Λ : PeriodPair, IsLatOf φK (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) Λ ∧ jLat Λ = σ (jLat ΛK)), Equidistributed φK (jLat ΛK) 𝔞 := by
  intro hH K _ _ _ h2 φK ΛK hΛ 𝔞 h𝔞
  letI : Algebra K ℂ := φK.toAlgebra
  have hj : ∀ Λ : PeriodPair, jLat Λ = (latticeCurve Λ).j := fun Λ => by rw [latticeCurve_j_eq]; rfl
  have hlat : ∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Λ : PeriodPair),
      IsLatOf φK (𝔟 : FractionalIdeal (𝓞 K)⁰ K) Λ → IsIdealLattice 𝔟 Λ := fun _ _ h => h
  obtain ⟨-, hfin, hcl, -, hrange⟩ := hH K h2 ΛK (hlat 1 ΛK hΛ)
  set H : IntermediateField K ℂ := K⟮(latticeCurve ΛK).j⟯ with hHdef
  have hpos : 0 < Module.finrank K H := hfin ▸ Fintype.card_pos
  haveI : FiniteDimensional K H := Module.finite_of_finrank_pos hpos
  have hj0 : (latticeCurve ΛK).j ∈ H := IntermediateField.mem_adjoin_simple_self K _
  have hj0' : jLat ΛK ∈ H := by rw [hj]; exact hj0
  have halg : IsAlgebraic ℚ (jLat ΛK) := by
    rw [hj]
    exact (IntermediateField.isAlgebraic_iff.1
      (Algebra.IsAlgebraic.isAlgebraic (⟨_, hj0⟩ : H))).restrictScalars ℚ
  have hclass : ∀ σ σ' : ℂ ≃+* ℂ, Fixes φK σ → Fixes φK σ' →
      (ClassGroup.mk K (𝔞 σ) = ClassGroup.mk K (𝔞 σ') ↔ σ (jLat ΛK) = σ' (jLat ΛK)) := by
    intro σ σ' hσ hσ'
    obtain ⟨Λ, hl, hjl⟩ := h𝔞 σ hσ
    obtain ⟨Λ', hl', hjl'⟩ := h𝔞 σ' hσ'
    rw [← hjl, ← hjl', hj, hj]
    exact (hcl _ _ Λ Λ' (hlat _ _ hl) (hlat _ _ hl')).symm
  refine ⟨halg, hclass, ?_⟩
  intro L hLf hLg hKL hjL C
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective C
  obtain ⟨Lb, hLb⟩ := exists_isIdealLattice h2 (FractionalIdeal.mk0 K I)
  have hinv : (latticeCurve Lb).j ∈ idealInvariants K := ⟨_, Lb, hLb, rfl⟩
  rw [← hrange] at hinv
  obtain ⟨g, hg⟩ := hinv
  haveI : NumberField H := NumberField.of_module_finite K H
  haveI : Countable H := (Module.finBasis ℚ H).equivFun.injective.countable
  obtain ⟨σC, hσC⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq H.val.toRingHom
    (H.val.toRingHom.comp g.toAlgHom.toRingHom)
  have hfixC : Fixes φK σC := fun x => by
    have := hσC (algebraMap K H x)
    exact (by simpa using this : σC (algebraMap K ℂ x) = algebraMap K ℂ x)
  have hσCj : σC (jLat ΛK) = jLat Lb := by
    have := hσC (IntermediateField.AdjoinSimple.gen K (latticeCurve ΛK).j)
    rw [hj, hj]
    simpa [hg] using this
  have hclC : ClassGroup.mk K (𝔞 σC) = ClassGroup.mk0 I := by
    obtain ⟨Λ, hl, hjl⟩ := h𝔞 σC hfixC
    rw [← ClassGroup.mk_mk0 K]
    refine (hcl _ _ Λ Lb (hlat _ _ hl) hLb).1 ?_
    rw [← hj, hjl, hσCj, hj]
  let L' : IntermediateField K ℂ := L.toSubfield.toIntermediateField hKL
  have hHL : H ≤ L' := IntermediateField.adjoin_simple_le_iff.2 (by rw [← hj]; exact hjL)
  haveI : FiniteDimensional ℚ L := hLf
  haveI : Countable L := (Module.finBasis ℚ L).equivFun.injective.countable
  have hcount := card_ext_mul_finrank L (H.restrictScalars ℚ) (fun x hx => hHL hx) σC
  have hM : Module.finrank ℚ (H.restrictScalars ℚ) = Module.finrank ℚ K * Module.finrank K H := by
    rw [Module.finrank_mul_finrank ℚ K H]
    rfl
  rw [hM, h2, hfin] at hcount
  have hiff : ∀ τ : L →+* ℂ, (∃ σ : ℂ ≃+* ℂ, Fixes φK σ ∧ (∀ x : L, σ (x : ℂ) = τ x) ∧
      ClassGroup.mk K (𝔞 σ) = ClassGroup.mk0 I) ↔ ∀ x : L, (x : ℂ) ∈ H.restrictScalars ℚ → τ x = σC x := by
    intro τ
    constructor
    · rintro ⟨σ, hσ, hστ, hcσ⟩ x hx
      have e : σ (jLat ΛK) = σC (jLat ΛK) := (hclass σ σC hσ hfixC).1 (hcσ.trans hclC.symm)
      rw [hj] at e
      let a : H →ₐ[K] ℂ := ((AlgEquiv.ofRingEquiv (f := σ) hσ).toAlgHom).comp H.val
      let b : H →ₐ[K] ℂ := ((AlgEquiv.ofRingEquiv (f := σC) hfixC).toAlgHom).comp H.val
      have hab : a = b := by
        refine IntermediateField.algHom_ext_of_eq_adjoin K rfl ?_
        rintro y rfl
        exact e
      rw [← hστ x]
      exact DFunLike.congr_fun hab ⟨x, hx⟩
    · intro hτ
      obtain ⟨σ, hσ⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq L.val.toRingHom τ
      have hσf : Fixes φK σ := fun x => by
        have h1 := hσ ⟨φK x, hKL x⟩
        have h2 := hτ ⟨φK x, hKL x⟩ (H.algebraMap_mem x)
        have h3 := hfixC x
        exact h1.trans (h2.trans h3)
      refine ⟨σ, hσf, fun x => hσ x, ?_⟩
      refine ((hclass σ σC hσf hfixC).2 ?_).trans hclC
      have h1 := hσ ⟨jLat ΛK, hjL⟩
      have h2 := hτ ⟨jLat ΛK, hjL⟩ hj0'
      exact h1.trans h2
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
  linarith

end GlobalTheory.EquidistJ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarIntegralEqUnitriangularChartStatement
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume GlobalTheory.FlagQuotHaar
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haarIntegral_eq_unitriangularChart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r), ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ HaarChart X c := by
  first | exact @GlobalTheory.FlagQuotHaar.exists_haarChart | exact GlobalTheory.FlagQuotHaar.exists_haarChart | (intros; apply GlobalTheory.FlagQuotHaar.exists_haarChart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntVVariableChangeStatement
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_variableChange_intV_of_j_mem : ∀ (W : WeierstrassCurve ℂ) [W.IsElliptic] (V : ValuationSubring ℂ) (u : ℂˣ), W.j ∈ V → V.valuation (u : ℂ) ^ 12 = V.valuation W.Δ → ∃ r s t : ℂ, IntV V ((⟨u, r, s, t⟩ : VariableChange ℂ) • W) := by
  first | exact @GlobalTheory.CMModel.exists_intV_variableChange | exact GlobalTheory.CMModel.exists_intV_variableChange | (intros; apply GlobalTheory.CMModel.exists_intV_variableChange <;> assumption)
end

