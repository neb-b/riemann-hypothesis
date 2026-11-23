module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComparisonIsFiltered

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionBasicProperties
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.DiscBasic

variable (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0)

theorem norm_add_le_max_disc (x y : Disc l u ρ) : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := by
  refine (denseRange_ofPre l u ρ).induction_on₂ (p := fun x y => ‖x + y‖ ≤ max ‖x‖ ‖y‖)
    (isClosed_le (by fun_prop) (by fun_prop)) (fun a b => ?_) x y
  rw [← map_add (f := _), norm_ofPre, norm_ofPre, norm_ofPre]
  exact gauge_add_le_max l u ρ a b

theorem isUltrametricDist_disc : IsUltrametricDist (Disc l u ρ) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm (norm_add_le_max_disc l u ρ)

theorem norm_l_disc_le : ‖((l : ℕ) : Disc l u ρ)‖ ≤ 1 / l := by
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  rw [← map_natCast (ofPre l u ρ), norm_ofPre]
  refine gauge_le l u ρ (by positivity) (Submodule.subset_span ⟨1, 0, 0, ?_, ?_⟩)
  · field_simp; simp
  · simp

theorem norm_inv_disc_le : ‖ofPre l u ρ (IsLocalization.Away.invSelf (l : A))‖ ≤ l := by
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  rw [norm_ofPre]
  refine gauge_le l u ρ hl0 (Submodule.subset_span ⟨0, 0, 1, ?_, ?_⟩)
  · simp
  · simp

theorem inv_mul_l_disc : ofPre l u ρ (IsLocalization.Away.invSelf (l : A)) * ((l : ℕ) : Disc l u ρ) = 1 := by
  rw [← map_natCast (ofPre l u ρ), ← map_mul, ← map_one (ofPre l u ρ)]
  congr 1
  rw [mul_comm, ← map_natCast (algebraMap A (PreDisc l u ρ))]
  exact IsLocalization.Away.mul_invSelf _

theorem norm_l_mul (y : Disc l u ρ) : ‖((l : ℕ) : Disc l u ρ) * y‖ = ‖y‖ / l := by
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  apply le_antisymm
  · calc ‖((l : ℕ) : Disc l u ρ) * y‖ ≤ ‖((l : ℕ) : Disc l u ρ)‖ * ‖y‖ := norm_mul_le _ _
      _ ≤ 1 / l * ‖y‖ := mul_le_mul_of_nonneg_right (norm_l_disc_le l u ρ) (norm_nonneg _)
      _ = ‖y‖ / l := by ring
  · rw [div_le_iff₀ hl0]
    calc ‖y‖ = ‖ofPre l u ρ (IsLocalization.Away.invSelf (l : A)) * (((l : ℕ) : Disc l u ρ) * y)‖ := by
          rw [← mul_assoc, inv_mul_l_disc, one_mul]
      _ ≤ ‖ofPre l u ρ (IsLocalization.Away.invSelf (l : A))‖ * ‖((l : ℕ) : Disc l u ρ) * y‖ := norm_mul_le _ _
      _ ≤ l * ‖((l : ℕ) : Disc l u ρ) * y‖ :=
          mul_le_mul_of_nonneg_right (norm_inv_disc_le l u ρ) (norm_nonneg _)
      _ = _ := by ring

theorem addHom_ext (N : Type) [NormedAddCommGroup N] (hN : ∀ z : N, l • z = 0 → z = 0)
    (F G : Disc l u ρ →+ N) (hF : Continuous F) (hG : Continuous G)
    (h : ∀ a, F (toDisc l u ρ a) = G (toDisc l u ρ a)) : F = G := by
  have hN' : ∀ n : ℕ, ∀ z : N, (l ^ n) • z = 0 → z = 0 := by
    intro n
    induction n with
    | zero => intro z hz; simpa using hz
    | succ n ih => intro z hz; exact ih z (hN _ (by rw [← mul_smul, ← pow_succ']; exact hz))
  have hpre : ∀ y : PreDisc l u ρ, F (ofPre l u ρ y) = G (ofPre l u ρ y) := by
    intro y
    obtain ⟨n, a, hy⟩ := IsLocalization.Away.surj (l : A) y
    have e : ((l ^ n : ℕ) : Disc l u ρ) * ofPre l u ρ y = toDisc l u ρ a := by
      rw [toDisc, RingHom.comp_apply, ← hy, map_mul, mul_comm (ofPre l u ρ y), ← map_natCast (ofPre l u ρ),
        ← map_natCast (algebraMap A (PreDisc l u ρ)), Nat.cast_pow, map_pow, map_pow]
    refine sub_eq_zero.1 (hN' n _ ?_)
    rw [smul_sub, ← map_nsmul F, ← map_nsmul G, nsmul_eq_mul, e, h, sub_self]
  ext x
  exact (denseRange_ofPre l u ρ).induction_on x (isClosed_eq hF hG) hpre

theorem isDiscMap_comp {A' A'' : Type} [CommRing A'] [CommRing A''] {u' : A'} {u'' : A''} {ρ' ρ'' : ℝ≥0}
    {f : A →+* A'} {f' : A' →+* A''} {F : Disc l u ρ →+* Disc l u' ρ'} {F' : Disc l u' ρ' →+* Disc l u'' ρ''}
    (hF : IsDiscMap (l := _) (u := _) (ρ := _) f F) (hF' : IsDiscMap (l := _) (u := _) (ρ := _) f' F') : IsDiscMap (l := _) (u := _) (ρ := _) (f'.comp f) (F'.comp F) :=
  ⟨fun a => by rw [RingHom.comp_apply, hF.ext, hF'.ext, RingHom.comp_apply],
    fun x => (hF'.norm_le _).trans (hF.norm_le x)⟩

theorem disc_basic : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (u : A) (ρ : ℝ≥0), IsUltrametricDist (Disc l u ρ) ∧ (∀ y : Disc l u ρ, ‖((l : ℕ) : Disc l u ρ) * y‖ = ‖y‖ / l) ∧ (∀ (N : Type) [NormedAddCommGroup N], (∀ z : N, l • z = 0 → z = 0) → ∀ F G : Disc l u ρ →+ N, Continuous F → Continuous G → (∀ a, F (toDisc l u ρ a) = G (toDisc l u ρ a)) → F = G) ∧ ∀ (A' A'' : Type) [CommRing A'] [CommRing A''] (u' : A') (u'' : A'') (ρ' ρ'' : ℝ≥0) (f : A →+* A') (f' : A' →+* A'') (F : Disc l u ρ →+* Disc l u' ρ') (F' : Disc l u' ρ' →+* Disc l u'' ρ''), IsDiscMap (l := _) (u := _) (ρ := _) f F → IsDiscMap (l := _) (u := _) (ρ := _) f' F' → IsDiscMap (l := _) (u := _) (ρ := _) (f'.comp f) (F'.comp F) :=
  fun l _ A _ u ρ => ⟨isUltrametricDist_disc l u ρ, norm_l_mul l u ρ,
    fun N _ hN F G hF hG h => addHom_ext l u ρ N hN F G hF hG h,
    fun _ _ _ _ _ _ _ _ _ _ _ _ hF hF' => isDiscMap_comp l u ρ hF hF'⟩

end GlobalTheory.BSP.DiscBasic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscTopologicalBasisExpansion
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.DiscExpand

theorem ultra (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) : IsUltrametricDist (Disc l u ρ) := by
  refine IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => ?_
  refine (denseRange_ofPre l u ρ).induction_on₂ (p := fun x y => ‖x + y‖ ≤ max ‖x‖ ‖y‖)
    (isClosed_le (by fun_prop) (by fun_prop)) (fun a b => ?_) x y
  rw [← map_add (f := _), norm_ofPre, norm_ofPre, norm_ofPre]
  exact gauge_add_le_max l u ρ a b

def smallIdeal (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) (r : ℝ≥0) : Ideal A where
  carrier := {x | ‖toDisc l u ρ x‖ ≤ r}
  zero_mem' := by simp
  add_mem' {x y} hx hy := by
    haveI := ultra l u ρ
    change ‖toDisc l u ρ (x + y)‖ ≤ r
    rw [map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  smul_mem' a x hx := by
    change ‖toDisc l u ρ (a * x)‖ ≤ r
    rw [map_mul]
    exact (norm_mul_le _ _).trans ((mul_le_mul (norm_toDisc_le _) hx (norm_nonneg _) zero_le_one).trans
      (one_mul _).le)

theorem pow_le_smallIdeal (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ θ : ℝ≥0) (I : Ideal A)
    (h : I ≤ smallIdeal l u ρ θ) (n : ℕ) : I ^ n ≤ smallIdeal l u ρ (θ ^ n) := by
  induction n with
  | zero => intro x _; change ‖toDisc l u ρ x‖ ≤ _; simpa using norm_toDisc_le x
  | succ n ih =>
    rw [pow_succ]
    refine Ideal.mul_le.2 fun x hx y hy => ?_
    change ‖toDisc l u ρ (x * y)‖ ≤ _
    rw [map_mul, pow_succ, NNReal.coe_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul (ih hx) (h hy) (norm_nonneg _) (by positivity))

theorem small (l : ℕ) [hl : Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A)
    (ρ : ℝ≥0) (h0 : 0 < ρ) (h1 : ρ < 1) (r : ℝ) (hr : 0 < r) :
    ∃ n : ℕ, ∀ x ∈ (bk.J ^ n).map s, ‖toDisc l (s X) ρ x‖ ≤ r := by
  have hl1 : (1 : ℝ≥0) < l := by exact_mod_cast hl.out.one_lt
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  set θ : ℝ≥0 := max (l : ℝ≥0)⁻¹ ρ with hθ
  have hθ1 : θ < 1 := max_lt (inv_lt_one_of_one_lt₀ hl1) h1
  have hlm : (l : A) ∈ smallIdeal l (s X) ρ θ := by
    change ‖toDisc l (s X) ρ l‖ ≤ _
    refine le_trans ?_ (NNReal.coe_le_coe.2 (le_max_left _ _))
    refine (norm_ofPre l (s X) ρ _).trans_le (gauge_le l (s X) ρ (by simpa using hl.out.pos)
      (Submodule.subset_span ⟨1, 0, 0, ?_, by simp⟩))
    simp [inv_mul_cancel₀ hl0.ne']
  have hXm : s X ∈ smallIdeal l (s X) ρ θ := by
    change ‖toDisc l (s X) ρ (s X)‖ ≤ _
    refine le_trans ?_ (NNReal.coe_le_coe.2 (le_max_right _ _))
    simpa using norm_toDisc_pow_le (l := l) (u := s X) 1 h0
  have hE : s bk.E ∈ smallIdeal l (s X) ρ θ := by
    obtain ⟨w, hw⟩ := bk.coeff_zero
    have e : bk.E = X * (bk.Ep.divX : (Wq l bk.a)⟦X⟧) + (l : bk.S) * C (w : Wq l bk.a) := by
      have := congrArg (fun p : Polynomial (Wq l bk.a) => (p : (Wq l bk.a)⟦X⟧)) (Polynomial.X_mul_divX_add bk.Ep)
      simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_X, Polynomial.coe_C] at this
      rw [hw, map_mul, map_natCast] at this
      exact this.symm
    rw [e, map_add (f := _), map_mul, map_mul, map_natCast]
    exact add_mem (Ideal.mul_mem_right _ _ hXm) (Ideal.mul_mem_right _ _ hlm)
  have hJ : bk.J.map s ≤ smallIdeal l (s X) ρ θ := by
    rw [Ideal.map_le_iff_le_comap]
    refine sup_le ?_ ?_ <;> rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    · rwa [map_natCast]
    · exact hE
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr (NNReal.coe_lt_one.2 hθ1)
  refine ⟨n, fun x hx => ?_⟩
  rw [Ideal.map_pow] at hx
  have := pow_le_smallIdeal l (s X) ρ θ _ hJ n hx
  exact le_trans this (by rw [NNReal.coe_pow]; exact hn.le)

theorem isClosed_expand {D D' ι : Type} [NormedCommRing D] [NormedCommRing D'] [IsUltrametricDist D']
    (j : D →+* D') (hj : ∀ x, ‖j x‖ ≤ ‖x‖) (c : ι → (D' →+ D)) (hc : ∀ i y, ‖c i y‖ ≤ ‖y‖) (b : ι → D')
    (hb : ∀ i, ‖b i‖ ≤ 1) :
    IsClosed {y | Filter.Tendsto (fun i => c i y) Filter.cofinite (nhds 0) ∧ HasSum (fun i => j (c i y) * b i) y} := by
  refine isClosed_of_closure_subset fun y hy => ?_
  rw [Metric.mem_closure_iff] at hy
  refine ⟨Metric.tendsto_nhds.2 fun ε hε => ?_, Metric.tendsto_nhds.2 fun ε hε => ?_⟩
  · obtain ⟨z, hz, hd⟩ := hy (ε / 2) (by positivity)
    filter_upwards [Metric.tendsto_nhds.1 hz.1 (ε / 2) (by positivity)] with i hi
    rw [dist_zero_right] at hi ⊢
    rw [dist_eq_norm] at hd
    have e : c i y = c i z + c i (y - z) := by rw [← map_add (f := _)]; congr 1; ring
    have := norm_add_le (c i z) (c i (y - z))
    have := hc i (y - z)
    rw [e]; linarith
  · obtain ⟨z, hz, hd⟩ := hy (ε / 3) (by positivity)
    filter_upwards [Metric.tendsto_nhds.1 hz.2 (ε / 3) (by positivity)] with F hF
    rw [dist_eq_norm] at hd hF ⊢
    have e : ∑ i ∈ F, j (c i y) * b i - y =
        (∑ i ∈ F, j (c i z) * b i - z) + (∑ i ∈ F, j (c i (y - z)) * b i) - (y - z) := by
      simp only [map_sub, sub_mul, Finset.sum_sub_distrib]; ring
    have h2 : ‖∑ i ∈ F, j (c i (y - z)) * b i‖ ≤ ‖y - z‖ :=
      IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ =>
        (norm_mul_le _ _).trans ((mul_le_mul ((hj _).trans (hc _ _)) (hb i) (norm_nonneg _) (norm_nonneg _)).trans
          (mul_one _).le)
    have h3 := norm_sub_le ((∑ i ∈ F, j (c i z) * b i - z) + (∑ i ∈ F, j (c i (y - z)) * b i)) (y - z)
    have h4 := norm_add_le (∑ i ∈ F, j (c i z) * b i - z) (∑ i ∈ F, j (c i (y - z)) * b i)
    rw [e]; linarith

theorem disc_expand (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A)
    (ι : Type) (TB : TopBasis s bk.J ι) (ρ : ℝ≥0) (h0 : 0 < ρ) (h1 : ρ < 1) (j : bk.DS ρ →+* Disc l (s X) ρ)
    (hj : IsDiscMap (l := _) (u := _) (ρ := _) s j) (cD : ι → (Disc l (s X) ρ →+ bk.DS ρ))
    (hc : (∀ i a, cD i (toDisc l (s X) ρ a) = toDisc l (X : bk.S) ρ (TB.c i a)) ∧
      (∀ i x y, cD i (j x * y) = x * cD i y) ∧ (∀ i y, ‖cD i y‖ ≤ ‖y‖)) (y : Disc l (s X) ρ) :
    Filter.Tendsto (fun i => cD i y) Filter.cofinite (nhds 0) ∧
      HasSum (fun i => j (cD i y) * toDisc l (s X) ρ (TB.b i)) y := by
  haveI := ultra l (s X) ρ
  obtain ⟨hc1, hc2, hc3⟩ := hc
  refine (denseRange_ofPre l (s X) ρ).induction_on y
    (isClosed_expand j hj.norm_le cD hc3 _ fun i => norm_toDisc_le _) fun p => ?_
  have base : ∀ a : A, Filter.Tendsto (fun i => cD i (toDisc l (s X) ρ a)) Filter.cofinite (nhds 0) ∧
      HasSum (fun i => j (cD i (toDisc l (s X) ρ a)) * toDisc l (s X) ρ (TB.b i)) (toDisc l (s X) ρ a) := by
    intro a
    refine ⟨Metric.tendsto_nhds.2 fun ε hε => ?_, Metric.tendsto_nhds.2 fun ε hε => ?_⟩
    · obtain ⟨n, hn⟩ := small l K bk bk.S (RingHom.id _) ρ h0 h1 (ε / 2) (by positivity)
      refine Filter.mem_of_superset (TB.fin a n).compl_mem_cofinite fun i hi => ?_
      have hi' : TB.c i a ∈ bk.J ^ n := by simpa using hi
      have h2 : ‖toDisc l (X : bk.S) ρ (TB.c i a)‖ ≤ ε / 2 := hn _ (by rwa [Ideal.map_id])
      change dist (cD i (toDisc l (s X) ρ a)) 0 < ε
      rw [dist_zero_right, hc1]; linarith
    · obtain ⟨n, hn⟩ := small l K bk A s ρ h0 h1 (ε / 2) (by positivity)
      change ∀ᶠ F in Filter.atTop, _
      filter_upwards [Filter.eventually_ge_atTop (TB.fin a n).toFinset] with F hF
      have h2 := hn _ (TB.approx a n F fun i hi => by
        by_contra h
        exact hi (hF (by simpa using h)))
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum] at h2
      rw [dist_comm, dist_eq_norm]
      simp only [hc1, hj.ext, ← map_mul]
      linarith
  obtain ⟨n, a, h⟩ := IsLocalization.Away.surj (l : A) p
  obtain ⟨w, hw⟩ := (isUnit_l_disc l (X : bk.S) ρ).exists_left_inv
  have hw' : j w * l = 1 := by rw [← map_natCast j, ← map_mul, hw, map_one]
  have e : ofPre l (s X) ρ p = j (w ^ n) * toDisc l (s X) ρ a := by
    have h2 : ofPre l (s X) ρ p * (l : Disc l (s X) ρ) ^ n = toDisc l (s X) ρ a := by
      have := congrArg (ofPre l (s X) ρ) h
      rwa [map_mul, map_pow, map_natCast, map_natCast] at this
    rw [← h2, map_pow, mul_left_comm, ← mul_pow, hw', one_pow, mul_one]
  rw [e]
  simp only [hc2]
  refine ⟨by simpa using (base a).1.const_mul (w ^ n), ?_⟩
  simpa only [map_mul, mul_assoc] using (base a).2.mul_left (j (w ^ n))

end GlobalTheory.BSP.DiscExpand
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroMapPowNullFacts
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.TopBasis

variable {S A ι : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S}

theorem pow_smul_top_eq {R : Type} [CommRing R] (J : Ideal R) (n : ℕ) :
    (J ^ n • ⊤ : Submodule R R) = J ^ n := by
  rw [smul_eq_mul, Ideal.mul_top]

theorem c_mem_of_mem (tb : TopBasis s I ι) (n : ℕ) {x : A} (hx : x ∈ (I ^ n).map s) (i : ι) :
    tb.c i x ∈ I ^ n := by
  have key : ∀ a : A, tb.c i (a * x) ∈ I ^ n := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      intro a
      rw [mul_comm, tb.c_mul]
      exact Ideal.mul_mem_right _ _ hz
    | zero => intro a; simp
    | add y z _ _ hy hz => intro a; rw [mul_add, map_add (f := _)]; exact add_mem (hy a) (hz a)
    | smul b y _ hy => intro a; rw [smul_eq_mul, ← mul_assoc]; exact hy (a * b)
  simpa using key 1

theorem mem_map_pow_iff (tb : TopBasis s I ι) (n : ℕ) (x : A) :
    x ∈ (I ^ n).map s ↔ ∀ i, tb.c i x ∈ I ^ n :=
  ⟨fun h i => c_mem_of_mem tb n h i, fun h => by simpa using tb.approx x n ∅ (fun i _ => h i)⟩

theorem eq_zero_of_c_eq_zero (tb : TopBasis s I ι) (x : A) (h : ∀ i, tb.c i x = 0) : x = 0 := by
  refine tb.complete.toIsHausdorff.haus x fun n => ?_
  rw [SModEq.sub_mem, sub_zero, pow_smul_top_eq, ← Ideal.map_pow]
  exact (mem_map_pow_iff tb n x).2 fun i => by rw [h i]; exact zero_mem _

theorem exists_coeffs_eq_of_null (tb : TopBasis s I ι) (hS : IsHausdorff I S) (a : ι → S)
    (ha : ∀ n : ℕ, {i | a i ∉ I ^ n}.Finite) : ∃ x, ∀ i, tb.c i x = a i := by
  classical
  let F : ℕ → Finset ι := fun n => (ha n).toFinset
  have hF : ∀ n i, i ∉ F n → a i ∈ I ^ n := fun n i hi => by
    simpa [F] using hi
  have hFm : Monotone F := by
    intro m n hmn i hi
    simp only [F, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hi ⊢
    exact fun h => hi (Ideal.pow_le_pow_right hmn h)
  let y : ℕ → A := fun n => ∑ i ∈ F n, s (a i) * tb.b i
  have hy : ∀ m n, m ≤ n → y n - y m ∈ (I ^ m).map s := by
    intro m n hmn
    have e : y n - y m = ∑ i ∈ F n \ F m, s (a i) * tb.b i := by
      simp only [y]; rw [← Finset.sum_sdiff (hFm hmn)]; ring
    rw [e]
    exact Ideal.sum_mem _ fun i hi =>
      Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hF m i (Finset.mem_sdiff.1 hi).2))
  obtain ⟨x, hx⟩ := tb.complete.toIsPrecomplete.prec (f := y) (fun {m n} hmn => by
    rw [SModEq.sub_mem, pow_smul_top_eq, ← Ideal.map_pow, ← neg_sub]
    exact neg_mem (hy m n hmn))
  refine ⟨x, fun i => ?_⟩
  rw [← sub_eq_zero]
  refine hS.haus _ fun n => ?_
  rw [SModEq.sub_mem, sub_zero, pow_smul_top_eq]
  have h1 : tb.c i (x - y n) ∈ I ^ n := by
    have h := hx n
    rw [SModEq.sub_mem, pow_smul_top_eq, ← Ideal.map_pow, ← neg_sub] at h
    exact c_mem_of_mem tb n (by simpa using neg_mem h) i
  have h2 : tb.c i (y n) - a i ∈ I ^ n := by
    have e : tb.c i (y n) = ∑ j ∈ F n, a j * tb.c i (tb.b j) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [y, map_sum, tb.c_mul]
    rw [e]
    by_cases hi : i ∈ F n
    · rw [Finset.sum_eq_single i (fun j _ hj => by rw [tb.c_ne i j (Ne.symm hj), mul_zero])
        (fun h => (h hi).elim), tb.c_self, mul_one, sub_self]
      exact zero_mem _
    · rw [Finset.sum_eq_zero (fun j hj => by rw [tb.c_ne i j (fun h => hi (h ▸ hj)), mul_zero]), zero_sub]
      exact neg_mem (hF n i hi)
  have e : tb.c i x - a i = tb.c i (x - y n) + (tb.c i (y n) - a i) := by rw [map_sub]; ring
  rw [e]
  exact add_mem h1 h2

end GlobalTheory.BSP.TopBasis

theorem GlobalTheory.BSP.TopBasis.coeff_facts : ∀ (S A ι : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S)
    (tb : TopBasis s I ι), (∀ x, (∀ i, tb.c i x = 0) → x = 0) ∧ (∀ (n : ℕ) x, x ∈ (I ^ n).map s ↔ ∀ i, tb.c i x ∈ I ^ n) ∧
    (IsHausdorff I S → ∀ a : ι → S, (∀ n : ℕ, {i | a i ∉ I ^ n}.Finite) → ∃ x, ∀ i, tb.c i x = a i) :=
  fun _ _ _ _ _ _ _ tb => ⟨GlobalTheory.BSP.TopBasis.eq_zero_of_c_eq_zero tb, GlobalTheory.BSP.TopBasis.mem_map_pow_iff tb,
    fun hS a ha => GlobalTheory.BSP.TopBasis.exists_coeffs_eq_of_null tb hS a ha⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAndResidualTrivComplexConj
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

namespace GlobalTheory.ResConjTriv

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

theorem continuous_cConj : Continuous (GlobalTheory.TwistDet.cConj X) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨L, hL, hLs⟩ := (krullTopology_mem_nhds_one_iff D.host.E N.Om s).1 hs
  have h := GlobalTheory.TwistDet.isOpen_comap_cConj X (H := L.fixingSubgroup) (IntermediateField.fixingSubgroup_isOpen L)
  rw [Filter.mem_map]
  exact Filter.mem_of_superset (h.mem_nhds (Subgroup.one_mem _)) fun g hg => hLs hg

theorem cycZ_cConj (l : ℕ) [Fact l.Prime] (g : GE N) :
    cycZ (F := D.host.E) (Ω := N.Om) l (GlobalTheory.TwistDet.cConj X g) = cycZ (F := D.host.E) (Ω := N.Om) l g := by
  have e : (GlobalTheory.TwistDet.cConj X g).toRingEquiv = X.cc * g.toRingEquiv * X.cc⁻¹ := by
    ext x; rfl
  change cyclotomicCharacter N.Om l (GlobalTheory.TwistDet.cConj X g).toRingEquiv = cyclotomicCharacter N.Om l g.toRingEquiv
  rw [e, map_mul, map_mul, map_inv, mul_inv_cancel_comm]

theorem auxiliaryCharacter_complexConj_invariant (i : X.Tw) (g : GE N) : eps0 X i (GlobalTheory.TwistDet.cConj X g) = eps0 X i g := by
  simp only [eps0, MonoidHom.comp_apply, cycZ_cConj]

theorem resTriv_cConj (i : X.Tw) (s : X.Sig i) (hS : SelfDual i s) (g : GE N) (hg : ResTriv i s g) :
    ResTriv i s (GlobalTheory.TwistDet.cConj X g) := by
  obtain ⟨A, hA⟩ := hS
  obtain ⟨h1, h2⟩ := hg
  have h3 := hA g _ (GlobalTheory.TwistDet.cConj_apply X g)
  refine ⟨?_, by rw [auxiliaryCharacter_complexConj_invariant, h2]⟩
  set φ := IsLocalRing.residue (X.O0 i) with hφ
  have hsm : ∀ (c : X.O0 i) (M : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)), φ c = 1 → (c • M).map φ = M.map φ := by
    intro c M hc
    ext a b
    simp [hc]
  have h4 := congrArg (fun M => M.map φ) h3
  simp only [Tdual] at h4
  rw [hsm _ _ (by rw [auxiliaryCharacter_complexConj_invariant, h2]), Matrix.map_mul, Matrix.map_mul, hsm _ _ (by rw [map_pow, h2, one_pow]), h1,
    mul_one, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.transpose_map,
    Matrix.transpose_eq_one] at h4
  have hu : IsUnit (Tmat i s (GlobalTheory.TwistDet.cConj X g)).det := by
    rw [← Tgl_coe]
    exact (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
  have h5 := congrArg (fun M => M.map φ) (Matrix.mul_nonsing_inv _ hu)
  rwa [Matrix.map_mul, h4, mul_one, Matrix.map_one _ (map_zero φ) (map_one φ)] at h5

theorem continuous_cConj_and_resTriv : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N), Continuous (GlobalTheory.TwistDet.cConj X) ∧ ∀ (i : X.Tw) (s : X.Sig i), SelfDual i s → ∀ g : GE N, ResTriv i s g → ResTriv i s (GlobalTheory.TwistDet.cConj X g) :=
  fun _ _ X => ⟨continuous_cConj X, resTriv_cConj X⟩

end GlobalTheory.ResConjTriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineFilteredDeRhamComparison
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.SeedFil
open Module Formalism.MainNotions.N

theorem crys_filtered : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsCrys (P.PD K) ρ → ∀ (a : ℤ), ∀ y ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) a, ∃ (m : ℕ) (k : Fin m → ℤ) (b : Fin m → P.R.BdR) (d : Fin m → V ⊗[ℚ_[l]] P.R.BdR), (∀ i, d i ∈ DdR (P.PD K) ρ ∧ d i ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) (k i) ∧ b i ∈ (P.PD K).Fil (a - k i)) ∧ y = ∑ i, AlgebraTensorModule.map (LinearMap.id : V →ₗ[ℚ_[l]] V) (LinearMap.mulLeft ℚ_[l] (b i)) (d i) := by
  intro l _ P AI TT K V _ _ _ ρ hC a y hy
  let LL : FinExt l := ⟨⊥, inferInstance⟩
  let e : ↥LL.1 ≃ₐ[ℚ_[l]] ℚ_[l] := IntermediateField.botEquiv ℚ_[l] (Om l)
  letI iM : Module ↥LL.1 V := Module.compHom V (e : ↥LL.1 →+* ℚ_[l])
  haveI : IsScalarTower ℚ_[l] ↥LL.1 V := ⟨fun c x v => by
    show e (c • x) • v = c • (e x • v)
    have h1 := e.toLinearEquiv.map_smul c x
    simp only [AlgEquiv.toLinearEquiv_apply] at h1
    rw [h1, smul_eq_mul, mul_smul]⟩
  haveI : FiniteDimensional ↥LL.1 V := Module.Finite.of_restrictScalars_finite ℚ_[l] _ V
  let ρ' : Representation ↥LL.1 ↥(GK K) V :=
    { toFun := fun g =>
        { toFun := ρ g
          map_add' := fun u w => (ρ g).map_add u w
          map_smul' := fun c v => (ρ g).map_smul (e c) v }
      map_one' := by ext v; simp
      map_mul' := fun g h => by ext v; simp; rfl }
  have hV : finrank ↥LL.1 V = finrank ℚ_[l] V := by
    rw [← Module.finrank_mul_finrank ℚ_[l] ↥LL.1 V, IntermediateField.finrank_bot, one_mul]
  have hB : ∀ g x, actVB (P.PD K) ρ' g x = actVB (P.PD K) ρ g x := fun g x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v w => simp [actVB]; rfl
    | add u w hu hw => simp only [map_add (f := _), hu, hw]
  have hR : ∀ g x, actVdR (P.PD K) ρ' g x = actVdR (P.PD K) ρ g x := fun g x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v w => simp [actVdR]; rfl
    | add u w hu hw => simp only [map_add (f := _), hu, hw]
  have hD : ∀ x, x ∈ DdR (P.PD K) ρ' ↔ x ∈ DdR (P.PD K) ρ := fun x => by
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, hR]
  have hDc : (Dcris (P.PD K) ρ').restrictScalars ℚ_[l] = Dcris (P.PD K) ρ := by
    ext x
    simp only [Submodule.restrictScalars_mem, Dcris, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.id_apply, hB]
  set_option synthInstance.maxHeartbeats 200000 in
  have hCr : finrank ↥LL.1 ↥(Dcris (P.PD K) ρ') = finrank ℚ_[l] ↥(Dcris (P.PD K) ρ) := by
    rw [← hDc, LinearEquiv.finrank_eq
      ((Submodule.restrictScalarsEquiv ℚ_[l] ↥LL.1 _ (Dcris (P.PD K) ρ')).restrictScalars ℚ_[l]),
      ← Module.finrank_mul_finrank ℚ_[l] ↥LL.1 ↥(Dcris (P.PD K) ρ'), IntermediateField.finrank_bot, one_mul]
  have hC' : IsCrys (P.PD K) ρ' := by
    unfold IsCrys at hC ⊢
    rw [hCr, hV]; exact hC
  have hDR := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI TT K LL V ρ' hC').1
  obtain ⟨m, k, b, d, h, hy'⟩ := GlobalTheory.DRFil.deRham_filtered l P AI TT K LL V ρ' hDR a y hy
  exact ⟨m, k, b, d, fun i => ⟨(hD _).1 (h i).1, (h i).2.1, (h i).2.2⟩, hy'⟩

end GlobalTheory.SeedFil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClosedDiscExtensionOfPowDvd
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_discMap_of_pow_dvd : ∀ (l : ℕ) [Fact l.Prime], ∀ (A A' : Type) [CommRing A] [CommRing A'] (f : A →+* A') (u : A) (u' : A') (ρ ρ' : ℝ≥0) (k : ℕ), 0 < ρ' → u' ^ k ∣ f u → ρ' ^ k ≤ ρ → ∃ F : Disc l u ρ →+* Disc l u' ρ', IsDiscMap (l := _) (u := _) (ρ := _) f F := by
  intro l _ A A' _ _ f u u' ρ ρ' k hρ' hdvd hk
  obtain ⟨z, hz⟩ := hdvd
  have h : ‖toDisc l u' ρ' (f u)‖ ≤ ρ := by
    rw [hz, map_mul]
    calc ‖toDisc l u' ρ' (u' ^ k) * toDisc l u' ρ' z‖
        ≤ ‖toDisc l u' ρ' (u' ^ k)‖ * ‖toDisc l u' ρ' z‖ := norm_mul_le _ _
      _ ≤ (ρ' : ℝ) ^ k * 1 :=
          mul_le_mul (norm_toDisc_pow_le k hρ') (norm_toDisc_le z) (norm_nonneg _) (by positivity)
      _ = ((ρ' ^ k : ℝ≥0) : ℝ) := by simp
      _ ≤ ρ := NNReal.coe_le_coe.2 hk
  exact ⟨Disc.map f h, isDiscMap_map f h⟩

end GlobalTheory.BSP
end

