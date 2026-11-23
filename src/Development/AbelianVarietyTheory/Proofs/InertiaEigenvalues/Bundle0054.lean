module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0026

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfAlgHomEqMul
section
open PowerSeries GlobalTheory.CycFr

namespace GlobalTheory.CycFr


open PowerSeries in
theorem _root_.GlobalTheory.CycFr.eq_act_of_comm {l : ℕ} [Fact l.Prime] {O : Type}
    [CommRing O] [IsDomain O] [CharZero O]
    [Algebra ℤ_[l] O] (φ₀ g : O⟦X⟧ →ₐ[O] O⟦X⟧) (c : ℤ_[l]) (hφ : φ₀ X = (1 + X) ^ l - 1)
    (hc : ∀ a, φ₀ (g a) = g (φ₀ a)) (h0 : constantCoeff (g X) = 0)
    (h1 : coeff 1 (g X) = algebraMap ℤ_[l] O c) :
    g = _root_.GlobalTheory.CycFr.act O c := by
  set A := _root_.GlobalTheory.CycFr.act O c X with hAdef
  set G := g X with hGdef
  set P : O⟦X⟧ := ∑ i ∈ Finset.range l, (1 + X) ^ i with hPdef
  have hP : (1 + X : O⟦X⟧) ^ l - 1 = X * P := by
    rw [← geom_sum_mul, add_sub_cancel_left, mul_comm]
  have hPc : constantCoeff P = (l : O) := by simp [P]
  have hXφ : X ∣ φ₀ X := by rw [hφ, hP]; exact dvd_mul_right _ _
  have hφact : φ₀ = _root_.GlobalTheory.CycFr.act O (l : ℤ_[l]) := by
    apply _root_.GlobalTheory.CycFr.algHom_ext_X _ _ hXφ
    rw [hφ, _root_.GlobalTheory.CycFr.act_nat_X]
  have hA0 : constantCoeff A = 0 :=
    PowerSeries.X_dvd_iff.mp (_root_.GlobalTheory.CycFr.X_dvd_act_X c)
  have hG : φ₀ G = (1 + G) ^ l - 1 := by
    rw [hGdef, hc, hφ]; simp [map_sub, map_pow, map_add (f := _), map_one]
  have hA : φ₀ A = (1 + A) ^ l - 1 := by
    rw [hAdef, hφact, _root_.GlobalTheory.CycFr.act_comm, ← hφact, hφ]
    simp [map_sub, map_pow, map_add (f := _), map_one]
  have hstep : ∀ n, 2 ≤ n → ∀ E : O⟦X⟧, G - A = X ^ n * E → constantCoeff E = 0 := by
    intro n hn E hE
    set S : O⟦X⟧ := ∑ i ∈ Finset.range l, (1 + G) ^ i * (1 + A) ^ (l - 1 - i) with hSdef
    have hSc : constantCoeff S = (l : O) := by simp [S, hA0, h0]
    have hD : φ₀ (G - A) = (G - A) * S := by
      have hgs := geom_sum₂_mul (1 + G) (1 + A) l
      rw [add_sub_add_left_eq_sub] at hgs
      rw [map_sub, hG, hA, mul_comm, hgs]; ring
    rw [hE, map_mul, map_pow, hφ, hP, mul_pow, mul_assoc, mul_assoc] at hD
    have hcancel := mul_left_cancel₀ (pow_ne_zero n PowerSeries.X_ne_zero) hD
    have hcc := congrArg constantCoeff hcancel
    rw [map_mul, map_mul, map_pow, hPc, hSc,
      _root_.GlobalTheory.CycFr.constantCoeff_algHom φ₀ hXφ E] at hcc
    have hne : ((l : O) ^ n) ≠ (l : O) := by
      rw [← Nat.cast_pow, Ne, Nat.cast_inj]
      intro h
      have h2 : 2 ≤ l := (Fact.out : l.Prime).two_le
      have := Nat.pow_right_injective h2 (h.trans (pow_one l).symm)
      omega
    have : constantCoeff E * ((l : O) ^ n - l) = 0 := by linear_combination hcc
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hne
  have hdvd : ∀ n, X ^ (n + 2) ∣ G - A := by
    intro n
    induction n with
    | zero =>
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      interval_cases m
      · simp [hA0, h0]
      · rw [map_sub, h1, hAdef, _root_.GlobalTheory.CycFr.coeff_one_act_X, sub_self]
    | succ k ih =>
      obtain ⟨E, hE⟩ := ih
      have he := hstep (k + 2) (by omega) E hE
      obtain ⟨F, hF⟩ := PowerSeries.X_dvd_iff.mpr he
      exact ⟨F, by rw [hE, hF]; ring⟩
  have hGA : G = A := by
    rw [← sub_eq_zero]
    ext m
    have := PowerSeries.X_pow_dvd_iff.mp (hdvd m) m (by omega)
    simpa using this
  exact _root_.GlobalTheory.CycFr.algHom_ext_X _ _ (PowerSeries.X_dvd_iff.mpr h0) hGA

end GlobalTheory.CycFr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerOperatorInjectiveEigenvector
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem eulerOp_Zbound : ∀ (ι : Type) [DecidableEq ι] (X : ι → Type) (x0 : ∀ v, X v) (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] (a : ∀ v, X v → ℂ) (s : ι → ℝ) (B : (∀ v, X v) → (H →L[ℂ] H)) (Z : ι → (H →L[ℂ] H)), (∀ v, a v (x0 v) = 1) → (∀ v (C : Finset (X v)), x0 v ∉ C → ∑ x ∈ C, ‖a v x‖ ≤ s v) → (∀ f, ‖B f‖ ≤ 1) → B x0 = 1 → (∀ v (f : ∀ v, X v), {w | f w ≠ x0 w}.Finite → f v = x0 v → HasSum (fun x => a v x • B (Function.update f v x)) (B f * Z v)) → ∀ v, ‖Z v - 1‖ ≤ s v := by
  intro ι _ X x0 H _ _ _ a s B Z ha0 hC hB hB0 hZ v
  classical
  have h := hZ v x0 (by simp) rfl
  rw [hB0, one_mul] at h
  have ht0 : a v (x0 v) • B (Function.update x0 v (x0 v)) = 1 := by simp [ha0, hB0]
  have h2 := h.update (x0 v) 0
  rw [ht0] at h2
  let g : X v → ℝ := fun x => if x = x0 v then 0 else ‖a v x‖
  have hg0 : 0 ≤ g := fun x => by simp only [g]; split_ifs <;> simp
  have hgsum : ∀ u : Finset (X v), ∑ x ∈ u, g x ≤ s v := by
    intro u
    have e : ∑ x ∈ u, g x = ∑ x ∈ u.filter (fun x => ¬ x = x0 v), ‖a v x‖ := by
      simp only [g]; rw [Finset.sum_ite]; simp
    rw [e]; exact hC v _ (by simp)
  have hgs : Summable g := summable_of_sum_le hg0 hgsum
  have h3 := h2.norm_le_of_bounded hgs.hasSum (fun x => ?_)
  · calc ‖Z v - 1‖ = ‖0 - 1 + Z v‖ := by congr 1; abel
      _ ≤ ∑' x, g x := h3
      _ ≤ s v := hgs.tsum_le_of_sum_le hgsum
  · by_cases hx : x = x0 v
    · rw [hx]; simp [g]
    · rw [Function.update_of_ne hx]
      simp only [g, if_neg hx, norm_smul]
      exact (mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)).trans (by simp)

theorem eulerOp_rec : ∀ (ι : Type) [DecidableEq ι] (X : ι → Type) (x0 : ∀ v, X v) (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] (a : ∀ v, X v → ℂ) (s : ι → ℝ) (B : (∀ v, X v) → (H →L[ℂ] H)) (Z : ι → (H →L[ℂ] H)), (∀ v, a v (x0 v) = 1) → (∀ v (f : ∀ v, X v), {w | f w ≠ x0 w}.Finite → f v = x0 v → HasSum (fun x => a v x • B (Function.update f v x)) (B f * Z v)) → Summable (fun f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} => (∏ᶠ u, a u (f.1 u)) • B f.1) → ∀ (S : Finset ι) (v : ι), v ∉ S → HasSum (fun f : {f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} // ∀ w ∉ insert v S, f.1 w = x0 w} => (∏ᶠ u, a u (f.1.1 u)) • B f.1.1) ((∑' f : {f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} // ∀ w ∉ S, f.1 w = x0 w}, (∏ᶠ u, a u (f.1.1 u)) • B f.1.1) * Z v) := by
  intro ι _ X x0 H _ _ _ a s B Z ha0 hZ hsum S v hv
  classical
  have hprod : ∀ (T : Finset ι) (f : ∀ v, X v), (∀ w ∉ T, f w = x0 w) →
      (∏ᶠ u, a u (f u)) = ∏ u ∈ T, a u (f u) := by
    intro T f hf
    apply finprod_eq_prod_of_mulSupport_subset
    intro w hw
    rw [Function.mem_mulSupport] at hw
    by_contra h
    exact hw (by rw [hf w h, ha0])
  have hfinU : ∀ (g : ∀ v, X v) (x : X v), {w | g w ≠ x0 w}.Finite →
      {w | Function.update g v x w ≠ x0 w}.Finite := by
    intro g x hg
    apply (hg.insert v).subset
    intro w hw
    by_cases h : w = v
    · exact Or.inl h
    · right; simpa [Function.update_of_ne h] using hw
  let e : {f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} // ∀ w ∉ S, f.1 w = x0 w} × X v →
      {f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} // ∀ w ∉ insert v S, f.1 w = x0 w} :=
    fun p => ⟨⟨Function.update p.1.1.1 v p.2, hfinU _ _ p.1.1.2⟩, fun w hw => by
      have h1 : w ≠ v := fun h => hw (h ▸ Finset.mem_insert_self _ _)
      have h2 : w ∉ S := fun h => hw (Finset.mem_insert_of_mem h)
      simp only [Function.update_of_ne h1]; exact p.1.2 w h2⟩
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨g, x⟩ ⟨g', x'⟩ h
      have h' : Function.update g.1.1 v x = Function.update g'.1.1 v x' :=
        congrArg (fun f => f.1.1) h
      have hx : x = x' := by simpa using congrFun h' v
      subst hx
      have hg : g.1.1 = g'.1.1 := by
        funext w
        by_cases hw : w = v
        · rw [hw, g.2 v hv, g'.2 v hv]
        · simpa [Function.update_of_ne hw] using congrFun h' w
      exact Prod.ext (Subtype.ext (Subtype.ext hg)) rfl
    · intro f
      refine ⟨(⟨⟨Function.update f.1.1 v (x0 v), hfinU _ _ f.1.2⟩, fun w hw => ?_⟩, f.1.1 v), ?_⟩
      · show Function.update f.1.1 v (x0 v) w = x0 w
        by_cases h : w = v
        · rw [h]; simp
        · rw [Function.update_of_ne h]; exact f.2 w (by simp [h, hw])
      · apply Subtype.ext; apply Subtype.ext; simp [e]
  have hsumI : Summable (fun f : {f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} // ∀ w ∉ insert v S, f.1 w = x0 w} =>
      (∏ᶠ u, a u (f.1.1 u)) • B f.1.1) :=
    hsum.comp_injective (f := fun f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} => (∏ᶠ u, a u (f.1 u)) • B f.1) Subtype.val_injective
  have hsumS : Summable (fun f : {f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} // ∀ w ∉ S, f.1 w = x0 w} =>
      (∏ᶠ u, a u (f.1.1 u)) • B f.1.1) :=
    hsum.comp_injective (f := fun f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} => (∏ᶠ u, a u (f.1 u)) • B f.1) Subtype.val_injective
  have hall := (Equiv.ofBijective e he).hasSum_iff.mpr hsumI.hasSum
  have hfib : ∀ g : {f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} // ∀ w ∉ S, f.1 w = x0 w},
      HasSum (fun x => ((fun f : {f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} // ∀ w ∉ insert v S, f.1 w = x0 w} =>
        (∏ᶠ u, a u (f.1.1 u)) • B f.1.1) ∘ (Equiv.ofBijective e he)) (g, x))
        (((∏ᶠ u, a u (g.1.1 u)) • B g.1.1) * Z v) := by
    intro g
    have hgv : g.1.1 v = x0 v := g.2 v hv
    have key : ∀ x, ((fun f : {f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} // ∀ w ∉ insert v S, f.1 w = x0 w} =>
        (∏ᶠ u, a u (f.1.1 u)) • B f.1.1) ∘ (Equiv.ofBijective e he)) (g, x) =
        (∏ᶠ u, a u (g.1.1 u)) • (a v x • B (Function.update g.1.1 v x)) := by
      intro x
      simp only [Function.comp, Equiv.ofBijective_apply, e]
      rw [smul_smul, hprod (insert v S) _ ?_, hprod S _ g.2, Finset.prod_insert hv]
      · congr 1
        rw [Function.update_self, mul_comm]
        congr 1
        apply Finset.prod_congr rfl
        intro w hw
        rw [Function.update_of_ne (by rintro rfl; exact hv hw)]
      · intro w hw
        have h1 : w ≠ v := fun h => hw (h ▸ Finset.mem_insert_self _ _)
        have h2 : w ∉ S := fun h => hw (Finset.mem_insert_of_mem h)
        rw [Function.update_of_ne h1]; exact g.2 w h2
    simp_rw [key]
    rw [smul_mul_assoc]
    exact (hZ v g.1.1 g.1.2 hgv).const_smul _
  have h3 := hall.prod_fiberwise hfib
  have h4 := hsumS.hasSum.mul_right (Z v)
  rw [← h3.unique h4]
  exact hsumI.hasSum

theorem eulerOp_normSummable (ι : Type) [DecidableEq ι] (X : ι → Type) (x0 : ∀ v, X v) (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] (a : ∀ v, X v → ℂ) (s : ι → ℝ) (B : (∀ v, X v) → (H →L[ℂ] H)) (ha0 : ∀ v, a v (x0 v) = 1) (hs : Summable s) (hC : ∀ v (C : Finset (X v)), x0 v ∉ C → ∑ x ∈ C, ‖a v x‖ ≤ s v) (hB : ∀ f, ‖B f‖ ≤ 1) :
    Summable (fun f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} => ‖(∏ᶠ v, a v (f.1 v)) • B f.1‖) := by
  have h1 := _root_.GlobalTheory.summable_finprod_of_finite_support_euler ι X x0 (fun v x => ‖a v x‖) s (fun v x => norm_nonneg _) (by intro v; simp [ha0]) hs hC
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun f => ?_) h1
  rw [norm_smul]
  have hfin := f.2
  have e1 : (∏ᶠ v, a v (f.1 v)) = ∏ v ∈ hfin.toFinset, a v (f.1 v) := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro w hw
    rw [Function.mem_mulSupport] at hw
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h; exact hw (by simp [h, ha0])
  have e2 : (∏ᶠ v, ‖a v (f.1 v)‖) = ∏ v ∈ hfin.toFinset, ‖a v (f.1 v)‖ := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro w hw
    rw [Function.mem_mulSupport] at hw
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h; exact hw (by simp [h, ha0])
  rw [e1, e2, norm_prod]
  calc (∏ v ∈ hfin.toFinset, ‖a v (f.1 v)‖) * ‖B f.1‖ ≤ (∏ v ∈ hfin.toFinset, ‖a v (f.1 v)‖) * 1 :=
        mul_le_mul_of_nonneg_left (hB _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = _ := mul_one _

theorem eulerOp_injective_eigen : ∀ (ι : Type) [DecidableEq ι] (X : ι → Type) (x0 : ∀ v, X v) (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] (a : ∀ v, X v → ℂ) (s : ι → ℝ) (B : (∀ v, X v) → (H →L[ℂ] H)) (Z : ι → (H →L[ℂ] H)), (∀ v, a v (x0 v) = 1) → Summable s → (∀ v, s v < 1) → (∀ v (C : Finset (X v)), x0 v ∉ C → ∑ x ∈ C, ‖a v x‖ ≤ s v) → (∀ f, ‖B f‖ ≤ 1) → B x0 = 1 → (∀ v (f : ∀ v, X v), {w | f w ≠ x0 w}.Finite → f v = x0 v → HasSum (fun x => a v x • B (Function.update f v x)) (B f * Z v)) → ∃ W : H →L[ℂ] H, HasSum (fun f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} => (∏ᶠ v, a v (f.1 v)) • B f.1) W ∧ Function.Injective W ∧ ∀ (y : H) (z : ι → ℂ), (∀ v, Z v y = z v • y) → W y = (∏' v, z v) • y := by
  intro ι _ X x0 H _ _ _ a s B Z ha0 hs hs1 hC hB hB0 hZ
  let t : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} → (H →L[ℂ] H) := fun f => (∏ᶠ v, a v (f.1 v)) • B f.1
  have hnorm : Summable (fun f => ‖t f‖) := eulerOp_normSummable ι X x0 H a s B ha0 hs hC hB
  have hsum : Summable t := hnorm.of_norm
  let A : Finset ι → Set {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} := fun S => {f | ∀ w ∉ S, f.1 w = x0 w}
  let WS : Finset ι → (H →L[ℂ] H) := fun S => ∑' f : A S, t f
  have hs0 : ∀ v, 0 ≤ s v := fun v => by simpa using hC v ∅ (by simp)
  have hZb := eulerOp_Zbound ι X x0 H a s B Z ha0 hC hB hB0 hZ
  have hrec : ∀ S v, v ∉ S → WS (insert v S) = WS S * Z v := fun S v hv =>
    (eulerOp_rec ι X x0 H a s B Z ha0 hZ hsum S v hv).tsum_eq
  have hbase : WS ∅ = 1 := by
    let f0 : A ∅ := ⟨⟨x0, by simp⟩, fun w _ => rfl⟩
    have hf0 : ∀ b : A ∅, b = f0 := fun b =>
      Subtype.ext (Subtype.ext (funext fun w => b.2 w (by simp)))
    show ∑' f : A ∅, t f = 1
    rw [tsum_eq_single f0 (fun b hb => absurd (hf0 b) hb)]
    simp [t, f0, ha0, hB0]
  have hlim : Tendsto WS atTop (𝓝 (∑' f, t f)) := by
    have e : WS = fun S => ∑' f, (A S).indicator t f := by
      funext S; exact tsum_subtype (A S) t
    rw [e]
    refine tendsto_tsum_of_dominated_convergence hnorm (fun f => ?_)
      (Eventually.of_forall fun S f => norm_indicator_le_norm_self _ _)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop f.2.toFinset] with S hS
    have hm : f ∈ A S := by
      intro w hw
      by_contra h
      exact hw (hS (by simpa using h))
    exact (Set.indicator_of_mem hm t).symm
  obtain ⟨δ, hδ, hδS⟩ := _root_.GlobalTheory.prod_one_sub_bounded_below ι s hs0 hs1 hs
  have hlow : ∀ S : Finset ι, ∀ y, (∏ v ∈ S, (1 - s v)) * ‖y‖ ≤ ‖WS S y‖ := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro y; simp [hbase]
    | insert v S hv ih =>
      intro y
      rw [hrec S v hv, Finset.prod_insert hv, ContinuousLinearMap.mul_apply]
      have h1 : ‖(Z v - 1) y‖ ≤ s v * ‖y‖ :=
        ((Z v - 1).le_opNorm y).trans (mul_le_mul_of_nonneg_right (hZb v) (norm_nonneg _))
      have h2 : ‖y‖ ≤ ‖Z v y‖ + ‖(Z v - 1) y‖ := by
        calc ‖y‖ = ‖Z v y - (Z v - 1) y‖ := by simp
          _ ≤ _ := norm_sub_le _ _
      have hZy : (1 - s v) * ‖y‖ ≤ ‖Z v y‖ := by nlinarith
      have hP : 0 ≤ ∏ v ∈ S, (1 - s v) := Finset.prod_nonneg fun w _ => by linarith [hs1 w]
      calc (1 - s v) * (∏ v ∈ S, (1 - s v)) * ‖y‖ = (∏ v ∈ S, (1 - s v)) * ((1 - s v) * ‖y‖) := by ring
        _ ≤ (∏ v ∈ S, (1 - s v)) * ‖Z v y‖ := mul_le_mul_of_nonneg_left hZy hP
        _ ≤ _ := ih _
  have heig : ∀ S : Finset ι, ∀ y (z : ι → ℂ), (∀ v, Z v y = z v • y) → WS S y = (∏ v ∈ S, z v) • y := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro y z _; simp [hbase]
    | insert v S hv ih =>
      intro y z hyz
      rw [hrec S v hv, ContinuousLinearMap.mul_apply, hyz v, map_smul, ih y z hyz, Finset.prod_insert hv, smul_smul]
  have hWy : ∀ y, Tendsto (fun S => WS S y) atTop (𝓝 ((∑' f, t f) y)) := fun y =>
    ((ContinuousLinearMap.apply ℂ H y).continuous.tendsto _).comp hlim
  have hlowW : ∀ y, δ * ‖y‖ ≤ ‖(∑' f, t f) y‖ := fun y =>
    ge_of_tendsto (hWy y).norm (Eventually.of_forall fun S =>
      (mul_le_mul_of_nonneg_right (hδS S) (norm_nonneg y)).trans (hlow S y))
  refine ⟨∑' f, t f, hsum.hasSum, ?_, ?_⟩
  · intro y1 y2 h
    have h1 := hlowW (y1 - y2)
    rw [map_sub, h, sub_self, norm_zero] at h1
    have h2 : ‖y1 - y2‖ ≤ 0 := le_of_mul_le_mul_left (by rw [mul_zero]; exact h1) hδ
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h2)
  · intro y z hyz
    by_cases hy : y = 0
    · subst hy; simp
    obtain ⟨φ, -, hφ⟩ := exists_dual_vector ℂ y (norm_ne_zero_iff.mpr hy)
    have h1 : Tendsto (fun S => (∏ v ∈ S, z v) • y) atTop (𝓝 ((∑' f, t f) y)) :=
      Tendsto.congr (fun S => heig S y z hyz) (hWy y)
    have h2 : Tendsto (fun S => φ ((∏ v ∈ S, z v) • y)) atTop (𝓝 (φ ((∑' f, t f) y))) :=
      (φ.continuous.tendsto _).comp h1
    simp only [map_smul, hφ, smul_eq_mul] at h2
    have hy' : ((‖y‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hy
    have h3 : Tendsto (fun S => ∏ v ∈ S, z v) atTop (𝓝 (φ ((∑' f, t f) y) / ‖y‖)) := by
      refine (h2.div_const ((‖y‖ : ℂ))).congr (fun S => ?_)
      exact mul_div_cancel_right₀ _ hy'
    have hP : HasProd z (φ ((∑' f, t f) y) / ‖y‖) := h3
    rw [hP.tprod_eq]
    exact tendsto_nhds_unique h1 (h3.smul_const y)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdicCompletionExtension
section
open PowerSeries GlobalTheory.NB.LT

namespace GlobalTheory.NB.LT

theorem factorPow_evalₐ_adic {B : Type} [CommRing B] (J : Ideal B) {m n : ℕ} (h : m ≤ n)
    (x : AdicCompletion J B) :
    Ideal.Quotient.factorPow J h (AdicCompletion.evalₐ J n x) = AdicCompletion.evalₐ J m x := by
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J B x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
  have hs := s.prop h
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hs
  rw [← neg_sub]
  exact (J ^ m).neg_mem hs

theorem exists_adicCompletion_extension {B : Type} [CommRing B] (l : ℕ)
    (f : B →+* AdicCompletion (Ideal.span {(l : B)}) B) :
    ∃ g : AdicCompletion (Ideal.span {(l : B)}) B →+* AdicCompletion (Ideal.span {(l : B)}) B,
      ∀ b, g (algebraMap B _ b) = f b := by
  have hJ : ∀ n, ∀ b ∈ Ideal.span {(l : B)} ^ n,
      AdicCompletion.evalₐ (Ideal.span {(l : B)}) n (f b) = 0 := by
    intro n b hb
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hb
    obtain ⟨c, rfl⟩ := hb
    rw [map_mul, map_pow, map_natCast, map_mul, map_pow, map_natCast]
    have hl : ((l : B ⧸ Ideal.span {(l : B)} ^ n)) ^ n = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(l : B)} ^ n)), ← map_pow,
        Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton_self _
    rw [hl, zero_mul]
  let ψ : ∀ n, B ⧸ Ideal.span {(l : B)} ^ n →+* B ⧸ Ideal.span {(l : B)} ^ n := fun n =>
    Ideal.Quotient.lift (Ideal.span {(l : B)} ^ n)
      ((AdicCompletion.evalₐ (Ideal.span {(l : B)}) n : _ →+* _).comp f) (hJ n)
  have hψ : ∀ n b, ψ n (Ideal.Quotient.mk _ b) =
      AdicCompletion.evalₐ (Ideal.span {(l : B)}) n (f b) := fun n b => rfl
  let F : ∀ n, AdicCompletion (Ideal.span {(l : B)}) B →+* B ⧸ Ideal.span {(l : B)} ^ n :=
    fun n => (ψ n).comp (AdicCompletion.evalₐ (Ideal.span {(l : B)}) n : _ →+* _)
  have hF : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (Ideal.span {(l : B)}) hle).comp (F n) = F m := by
    intro m n hle
    ext x
    obtain ⟨b, hb⟩ :=
      Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (Ideal.span {(l : B)}) n x)
    simp only [F, RingHom.comp_apply, RingHom.coe_coe]
    rw [← factorPow_evalₐ_adic _ hle x, ← hb, hψ, factorPow_evalₐ_adic, Ideal.Quotient.factor_mk, hψ]
  refine ⟨AdicCompletion.liftRingHom _ F hF, fun b => ?_⟩
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [AdicCompletion.evalₐ_liftRingHom]
  simp only [F, RingHom.comp_apply, RingHom.coe_coe]
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of, hψ]
  rfl

theorem exists_EE_extension {l : ℕ} {O : Type} [CommRing O] (ψ : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (hu : IsUnit (algebraMap O⟦X⟧ (EE O l) (ψ X))) :
    ∃ ψE : EE O l →ₐ[O] EE O l,
      ∀ a, ψE (algebraMap O⟦X⟧ (EE O l) a) = algebraMap O⟦X⟧ (EE O l) (ψ a) := by
  have hu' : IsUnit (((algebraMap O⟦X⟧ (EE O l)).comp (ψ : O⟦X⟧ →+* O⟦X⟧)) X) := hu
  obtain ⟨g, hg⟩ := exists_adicCompletion_extension l
    (IsLocalization.Away.lift (X : O⟦X⟧) (S := Localization.Away (X : O⟦X⟧)) hu')
  have key : ∀ a, g (algebraMap O⟦X⟧ (EE O l) a) = algebraMap O⟦X⟧ (EE O l) (ψ a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply O⟦X⟧ (Localization.Away (X : O⟦X⟧)) (EE O l), hg,
      IsLocalization.Away.lift_eq]
    rfl
  refine ⟨{ g with commutes' := fun c => ?_ }, key⟩
  show g (algebraMap O (EE O l) c) = algebraMap O (EE O l) c
  rw [IsScalarTower.algebraMap_apply O O⟦X⟧ (EE O l), key, AlgHom.commutes]

end GlobalTheory.NB.LT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgEquivXAddC
section
noncomputable section

open PowerSeries GlobalTheory.NB.LT

namespace GlobalTheory.NB.LT


open scoped PowerSeries.WithPiTopology in
theorem exists_algHom_X_add_C {O : Type} [CommRing O] (I : Ideal O) [h : IsAdicComplete I O]
    (c : O) (hc : c ∈ I) : ∃ t : O⟦X⟧ →ₐ[O] O⟦X⟧, t X = X + C c := by
  let : WithIdeal O := ⟨I⟩
  have hI : IsAdic I := rfl
  obtain ⟨h1, h2⟩ := hI.isAdicComplete_iff.mp h
  have ha : PowerSeries.HasEval c := WithIdeal.isTopologicallyNilpotent_of_mem hc
  have hC : PowerSeries.HasEval (C c : O⟦X⟧) :=
    ha.map (φ := (C : O →+* O⟦X⟧)) PowerSeries.WithPiTopology.continuous_C
  have : IsLinearTopology O⟦X⟧ O⟦X⟧ :=
    inferInstance
  have hX : PowerSeries.HasEval (X + C c : O⟦X⟧) := PowerSeries.HasEval.X.add hC
  have : ContinuousSMul O O⟦X⟧ := ⟨by
    have : (fun p : O × O⟦X⟧ => p.1 • p.2) = fun p => C p.1 * p.2 := by
      funext p; rw [smul_eq_C_mul]
    rw [this]
    exact (PowerSeries.WithPiTopology.continuous_C.comp continuous_fst).mul continuous_snd⟩
  refine ⟨PowerSeries.aeval hX, ?_⟩
  rw [PowerSeries.coe_aeval, PowerSeries.eval₂_X]

theorem exists_algEquiv_X_add_C : ∀ {O : Type} [CommRing O] (I : Ideal O) [IsAdicComplete I O] (c : O), c ∈ I → ∃ lev : O⟦X⟧ ≃ₐ[O] O⟦X⟧, lev X = X + C c := by
  intro O _ I _ c hc
  obtain ⟨s, hs⟩ := exists_algHom_X_add_C I c hc
  obtain ⟨t, ht⟩ := exists_algHom_X_add_C I (-c) (neg_mem hc)
  have hC : ∀ (u : O⟦X⟧ →ₐ[O] O⟦X⟧) (a : O), u (C a) = C a := fun u a => u.commutes a
  have h1 : (s.comp t) X = X := by
    rw [AlgHom.comp_apply, ht, map_add (f := _), hs, hC, map_neg]; ring
  have h2 : (t.comp s) X = X := by
    rw [AlgHom.comp_apply, hs, map_add (f := _), ht, hC, map_neg]; ring
  exact ⟨AlgEquiv.ofAlgHom s t (algHom_ext_X _ _ h1 (by rw [h1])) (algHom_ext_X _ _ h2 (by rw [h2])), hs⟩

end GlobalTheory.NB.LT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCosetRepresentativesOfFiniteSubgroupPadicIStatement
section
open PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coset_reps_finite_subgroup_padicInt_units : ∀ {l : ℕ} [Fact l.Prime] (Δ : Subgroup ℤ_[l]ˣ) [Finite Δ], l ≠ 2 → ∃ (e : ℕ) (a : Fin e → ℕ), e * Nat.card Δ = l - 1 ∧ (∀ τ, ¬ l ∣ a τ) ∧ (∀ τ τ', τ ≠ τ' → (a τ : ZMod l) ^ Nat.card Δ ≠ (a τ' : ZMod l) ^ Nat.card Δ) ∧ ∀ x : ZMod l, x ≠ 0 → ∃! p : Fin e × Δ, x = (a p.1 : ZMod l) * PadicInt.toZMod ((p.2 : ℤ_[l]ˣ) : ℤ_[l]) := by
  first | exact @GlobalTheory.exists_coset_representatives_of_finite_subgroup_padicInt_units | exact GlobalTheory.exists_coset_representatives_of_finite_subgroup_padicInt_units | (intros; apply GlobalTheory.exists_coset_representatives_of_finite_subgroup_padicInt_units <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusCompatibleLift
section
open scoped NNReal

namespace GlobalTheory.DworkLift

theorem exists_frobenius_compatible_lift : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (φ : A →+* A),
    (∀ a, ((l : ℕ) : A) ∣ φ a - a ^ l) → (∀ a : A, ((l : ℕ) : A) * a = 0 → a = 0) →
    ∀ (O : Type) [CommRing O] [CharP O l] (f : A →+* O), ∃ F : A →+* WittVector l O,
      (∀ a, (F a).coeff 0 = f a) ∧ ∀ a, F (φ a) = WittVector.frobenius (F a) := by
  intro l _ A _ φ hφ htor O _ _ f
  have hex := _root_.GlobalTheory.DworkGhost.exists_witt_ghost_iterate l A φ hφ
  have inj := _root_.GlobalTheory.WittVector.ghostComponent_injective_of_noTorsion l A htor
  let s : A → WittVector l A := fun a => Classical.choose (hex a)
  have hs : ∀ a n, WittVector.ghostComponent n (s a) = φ^[n] a := fun a => Classical.choose_spec (hex a)
  have hit : ∀ (n : ℕ) (a : A), φ^[n] a = (φ ^ n) a := fun n a => by rw [RingHom.coe_pow]
  let S : A →+* WittVector l A :=
    { toFun := s
      map_one' := inj _ _ fun n => by rw [hs, map_one, hit, map_one]
      map_mul' := fun a b => inj _ _ fun n => by rw [map_mul, hs, hs, hs, hit, hit, hit, map_mul]
      map_zero' := inj _ _ fun n => by rw [hs, map_zero, hit, map_zero]
      map_add' := fun a b => inj _ _ fun n => by rw [map_add (f := _), hs, hs, hs, hit, hit, hit, map_add (f := _)] }
  have hS0 : ∀ a, (S a).coeff 0 = a := fun a => by
    change (s a).coeff 0 = a
    have h := hs a 0
    rw [WittVector.ghostComponent_apply, wittPolynomial_zero] at h
    simpa using h
  have hSφ : ∀ a, S (φ a) = WittVector.frobenius (S a) := fun a => inj _ _ fun n => by
    change WittVector.ghostComponent n (s (φ a)) = WittVector.ghostComponent n (WittVector.frobenius (s a))
    rw [WittVector.ghostComponent_frobenius, hs, hs, Function.iterate_succ_apply]
  refine ⟨(WittVector.map f).comp S, fun a => ?_, fun a => ?_⟩
  · simp only [RingHom.comp_apply, WittVector.map_coeff, hS0]
  · simp only [RingHom.comp_apply, hSφ]
    exact WittVector.IsPoly.map (WittVector.frobenius_isPoly l) f (S a)

end GlobalTheory.DworkLift
end

