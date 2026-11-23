module

public import ReciprocityTheory.SemistableReduction.Bundle0005
public import ReciprocityTheory.SemistableReduction.Bundle0002
public import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement
public import ReciprocityTheory.SemistableReduction.Bundle0004
public import ReciprocityTheory.SemistableReduction.Bundle0006
public import ReciprocityTheory.SemistableReduction.Bundle0008

@[expose] public section

-- bundled from ReciprocityTheory.SemistableReduction.ApproxBasisB
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField ComplexConjugate

theorem approxB_h_add_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y z : Fin r → K) : S.h x (y + z) = S.h x y + S.h x z := by
  unfold ReciprocityTheory.MultiplicativeHeights.HermForm.h
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem approxB_h_smul_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y : Fin r → K) (a : K) : S.h x (a • y) = a * S.h x y := by
  unfold ReciprocityTheory.MultiplicativeHeights.HermForm.h
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  ring

theorem approxB_h_sub_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y z : Fin r → K) : S.h x (y - z) = S.h x y - S.h x z := by
  unfold ReciprocityTheory.MultiplicativeHeights.HermForm.h
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem approxB_h_zero_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x : Fin r → K) : S.h x 0 = 0 := by
  simp [ReciprocityTheory.MultiplicativeHeights.HermForm.h]

theorem approxB_h_sum_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    {α : Type*} (s : Finset α) (x : Fin r → K) (f : α → Fin r → K) :
    S.h x (∑ j ∈ s, f j) = ∑ j ∈ s, S.h x (f j) := by
  exact map_sum (AddMonoidHom.mk' (S.h x) ((approxB_h_add_right S) x)) f s

theorem approxB_h_smul_left {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y : Fin r → K) (a : K) : S.h (a • x) y = S.c a * S.h x y := by
  unfold ReciprocityTheory.MultiplicativeHeights.HermForm.h
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

private theorem hermForm_h_add_left {K : Type} [Field K] [NumberField K] {r : ℕ}
    (S : HermForm K r) (x y z : Fin r → K) : S.h (x + y) z = S.h x z + S.h y z := by
  unfold ReciprocityTheory.MultiplicativeHeights.HermForm.h
  simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem approxB_h_sum_left {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    {α : Type*} (s : Finset α) (y : Fin r → K) (f : α → Fin r → K) :
    S.h (∑ j ∈ s, f j) y = ∑ j ∈ s, S.h (f j) y := by
  exact map_sum (AddMonoidHom.mk' (fun z => S.h z y) (fun a b => (hermForm_h_add_left S) a b y)) f s

theorem approxB_embVec_add {K : Type} [Field K] [NumberField K] {r : ℕ} (σ : K →+* ℂ)
    (x y : Fin r → K) : embVec σ (x + y) = embVec σ x + embVec σ y := by
  funext a
  simp [embVec]

theorem approxB_embVec_sub {K : Type} [Field K] [NumberField K] {r : ℕ} (σ : K →+* ℂ)
    (x y : Fin r → K) : embVec σ (x - y) = embVec σ x - embVec σ y := by
  funext a
  simp [embVec]

theorem approxB_embVec_smul {K : Type} [Field K] [NumberField K] {r : ℕ} (σ : K →+* ℂ)
    (a : K) (x : Fin r → K) : embVec σ (a • x) = σ a • embVec σ x := by
  funext i
  simp [embVec]

theorem approxB_embVec_sum {K : Type} [Field K] [NumberField K] {r : ℕ} (σ : K →+* ℂ)
    {α : Type*} (s : Finset α) (f : α → Fin r → K) :
    embVec σ (∑ j ∈ s, f j) = ∑ j ∈ s, embVec σ (f j) := by
  exact map_sum (AddMonoidHom.mk' (embVec σ) (approxB_embVec_add σ)) f s

theorem approxB_split {K : Type} [Field K] [NumberField K] {r p : ℕ} (hp : p ≤ r) (S : HermForm K r)
    (L : Submodule (𝓞 K) (Fin r → K)) (hL : IsIntegralOn S L) (l v : Fin r → Fin r → K)
    (hl : ∀ j, l j ∈ L) (hvi : LinearIndependent K v)
    (hinj : ∀ g : ApproxPosIdx r p → K,
      (∀ k : ApproxPosIdx r p, S.h (l k.1) (∑ j : ApproxPosIdx r p, g j • l j.1) = 0) → g = 0) :
    ∃ (Δ : K) (coef : (Fin r → K) → ApproxPosIdx r p → K) (a : {j : Fin r // ¬ (j : ℕ) < p} → Fin r),
      Δ ≠ 0 ∧ Δ = (Matrix.of fun k j : ApproxPosIdx r p => S.h (l k.1) (l j.1)).det ∧
      (∀ x (k : ApproxPosIdx r p), S.h (l k.1) (Δ • x - ∑ k', coef x k' • l k'.1) = 0) ∧
      (∀ x ∈ L, Δ • x - ∑ k', coef x k' • l k'.1 ∈ L) ∧
      LinearIndependent K (fun j : Fin r => if h : (j : ℕ) < p then l j else
        Δ • v (a ⟨j, h⟩) - ∑ k', coef (v (a ⟨j, h⟩)) k' • l k'.1) := by
  classical
  set M : Matrix (ApproxPosIdx r p) (ApproxPosIdx r p) K := Matrix.of fun k j => S.h (l k.1) (l j.1) with hM
  set Δ := M.det with hΔdef
  let bv : (Fin r → K) → ApproxPosIdx r p → K := fun x k => S.h (l k.1) x
  let coef : (Fin r → K) → ApproxPosIdx r p → K := fun x => M.adjugate *ᵥ bv x
  let T : (Fin r → K) → (Fin r → K) := fun x => Δ • x - ∑ k', coef x k' • l k'.1

  have hMinj : ∀ g, M *ᵥ g = 0 → g = 0 := by
    intro g hg
    apply hinj g
    intro k
    have := congrFun hg k
    simp only [mulVec, dotProduct, hM, Matrix.of_apply, Pi.zero_apply] at this
    rw [approxB_h_sum_right]
    simpa [approxB_h_smul_right, mul_comm] using this
  have hΔ : Δ ≠ 0 := by
    intro h0
    obtain ⟨g, hg0, hg⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    exact hg0 (hMinj g hg)

  have horth : ∀ x (k : ApproxPosIdx r p), S.h (l k.1) (T x) = 0 := by
    intro x k
    have hMc : M *ᵥ coef x = Δ • bv x := by
      simp only [coef, mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec, hΔdef]
    have hk := congrFun hMc k
    simp only [mulVec, dotProduct, hM, Matrix.of_apply, Pi.smul_apply, smul_eq_mul] at hk
    simp only [T, approxB_h_sub_right, approxB_h_smul_right, approxB_h_sum_right]
    rw [← hk]
    simp [bv, mul_comm]

  have hint : ∀ x ∈ L, T x ∈ L := by
    intro x hx
    let f := algebraMap (𝓞 K) K
    have hMi : ∀ k j, ∃ z : 𝓞 K, f z = M k j := fun k j => hL _ (hl _) _ (hl _)
    choose Mz hMz using hMi
    have hbi : ∀ k, ∃ z : 𝓞 K, f z = bv x k := fun k => hL _ (hl _) _ hx
    choose bz hbz using hbi
    have hMmap : f.mapMatrix (Matrix.of Mz) = M := by ext k j; simp [hMz]
    have hΔz : f (Matrix.of Mz).det = Δ := by rw [RingHom.map_det, hMmap]
    have hcz : ∀ k, f (((Matrix.of Mz).adjugate *ᵥ bz) k) = coef x k := by
      intro k
      rw [show coef x = M.adjugate *ᵥ bv x from rfl, ← hMmap, ← RingHom.map_adjugate]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, map_sum,
        map_mul, hbz]
    have hT : T x = (Matrix.of Mz).det • x -
        ∑ k', ((Matrix.of Mz).adjugate *ᵥ bz) k' • l k'.1 := by
      simp only [T, ← hΔz, ← hcz]
      simp only [f, algebraMap_smul]
    rw [hT]
    exact L.sub_mem (L.smul_mem _ hx) (L.sum_mem fun k _ => L.smul_mem _ (hl _))

  have hbadd : ∀ x y, bv (x + y) = bv x + bv y :=
    fun x y => funext fun k => approxB_h_add_right S _ x y
  have hbsmul : ∀ (c : K) x, bv (c • x) = c • bv x :=
    fun c x => funext fun k => by simp [bv, approxB_h_smul_right]
  let Tl : (Fin r → K) →ₗ[K] (Fin r → K) :=
    { toFun := T
      map_add' := fun x y => by
        simp only [T, coef, hbadd, mulVec_add, Pi.add_apply, add_smul, Finset.sum_add_distrib,
          smul_add]
        abel
      map_smul' := fun c x => by
        simp only [T, coef, hbsmul, mulVec_smul, Pi.smul_apply, smul_eq_mul, mul_smul,
          ← Finset.smul_sum, RingHom.id_apply, smul_sub]
        rw [smul_comm Δ c x] }
  have hker : LinearMap.ker Tl ≤ Submodule.span K (Set.range fun k : ApproxPosIdx r p => l k.1) := by
    intro x hx
    have h0 : T x = 0 := LinearMap.mem_ker.mp hx
    have hx' : x = Δ⁻¹ • ∑ k', coef x k' • l k'.1 := by
      have h1 : Δ • x = ∑ k', coef x k' • l k'.1 := sub_eq_zero.mp h0
      rw [← h1, smul_smul, inv_mul_cancel₀ hΔ, one_smul]
    rw [hx']
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  have hfk : Module.finrank K (LinearMap.ker Tl) ≤ p := by
    calc _ ≤ Module.finrank K (Submodule.span K (Set.range fun k : ApproxPosIdx r p => l k.1)) :=
          Submodule.finrank_mono hker
      _ ≤ Fintype.card (ApproxPosIdx r p) := finrank_range_le_card (R := K) _
      _ = p := approxB_card_pos hp
  have hrn := LinearMap.finrank_range_add_finrank_ker Tl
  rw [Module.finrank_fin_fun] at hrn
  have hfr : r - p ≤ Module.finrank K (LinearMap.range Tl) := by omega
  have hspan_v : Submodule.span K (Set.range v) = ⊤ :=
    hvi.span_eq_top_of_card_eq_finrank' (by simp)
  have hrange : Submodule.span K (Set.range (Tl ∘ v)) = LinearMap.range Tl := by
    rw [Set.range_comp, ← Submodule.map_span, hspan_v, Submodule.map_top]
  obtain ⟨κ, a0, ha0, hsp, hli⟩ := exists_linearIndependent' K (Tl ∘ v)
  have : Finite κ := Finite.of_injective a0 ha0
  have : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = Module.finrank K (LinearMap.range Tl) := by
    rw [← hrange, ← hsp, finrank_span_eq_card hli]
  have hle : Fintype.card {j : Fin r // ¬ (j : ℕ) < p} ≤ Fintype.card κ := by
    rw [approxB_card_neg hp, hcard]; exact hfr
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hle
  have hlia : LinearIndependent K (fun k => T (v (a0 (e k)))) := hli.comp e e.injective
  refine ⟨Δ, coef, fun k => a0 (e k), hΔ, rfl, horth, hint, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hsplit : ∑ k : ApproxPosIdx r p, g k.1 • l k.1 +
      ∑ k : {j : Fin r // ¬ (j : ℕ) < p}, g k.1 • T (v (a0 (e k))) = 0 := by
    rw [← hg, ← Fintype.sum_subtype_add_sum_subtype (fun j : Fin r => (j : ℕ) < p)]
    congr 1
    · exact Finset.sum_congr rfl fun k _ => by simp only [dif_pos k.2]
    · exact Finset.sum_congr rfl fun k _ => by simp only [dif_neg k.2]; rfl
  have hBorth : ∀ k' : ApproxPosIdx r p,
      S.h (l k'.1) (∑ k : {j : Fin r // ¬ (j : ℕ) < p}, g k.1 • T (v (a0 (e k)))) = 0 := by
    intro k'
    rw [approxB_h_sum_right]
    exact Finset.sum_eq_zero fun k _ => by rw [approxB_h_smul_right, horth, mul_zero]
  have hApos : ∀ k' : ApproxPosIdx r p, S.h (l k'.1) (∑ k : ApproxPosIdx r p, g k.1 • l k.1) = 0 := by
    intro k'
    have := congrArg (S.h (l k'.1)) hsplit
    rw [approxB_h_add_right, hBorth, add_zero, approxB_h_zero_right] at this
    exact this
  have hg1 := hinj (fun k => g k.1) hApos
  have hA0 : ∑ k : ApproxPosIdx r p, g k.1 • l k.1 = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [show g k.1 = 0 from congrFun hg1 k, zero_smul]
  rw [hA0, zero_add] at hsplit
  have hg2 := (Fintype.linearIndependent_iff.mp hlia) (fun k => g k.1) hsplit
  intro j
  by_cases hj : (j : ℕ) < p
  · exact congrFun hg1 ⟨j, hj⟩
  · exact hg2 ⟨j, hj⟩

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.ApproxGraphB
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.ApproximationGraph

open ComplexConjugate

lemma posPart_posPart (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : posPart p (posPart p u) = posPart p u := by
  ext k
  simp only [posPart, negPart, Pi.zero_apply]
  split_ifs <;> rfl

lemma posPart_negPart (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : posPart p (negPart p u) = 0 := by
  ext k
  simp only [posPart, negPart, Pi.zero_apply]
  split_ifs <;> rfl

lemma negPart_posPart (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : negPart p (posPart p u) = 0 := by
  ext k
  simp only [posPart, negPart, Pi.zero_apply]
  split_ifs <;> rfl

lemma negPart_negPart (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : negPart p (negPart p u) = negPart p u := by
  ext k
  simp only [posPart, negPart, Pi.zero_apply]
  split_ifs <;> rfl

lemma posPart_zero (p : ℕ) {r : ℕ} : posPart p (0 : Fin r → ℂ) = 0 := by
  ext k
  simp [posPart]

lemma negPart_zero (p : ℕ) {r : ℕ} : negPart p (0 : Fin r → ℂ) = 0 := by
  ext k
  simp [negPart]

lemma posPart_supp (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : ∀ j : Fin r, p ≤ (j : ℕ) → posPart p u j = 0 := fun j hj => by
  simp [posPart, not_lt.mpr hj]

lemma approxR_nonneg (r : ℕ) {μ ρ : ℝ} (hμ : 0 < μ) (hρ : 0 < ρ) : 0 ≤ approxR r μ ρ := by
  unfold approxR
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hμ.le) hρ.le

lemma graph_bound {r p : ℕ} {μ ρ : ℝ} (X : Fin r → Fin r → ℂ) (hμ : 0 < μ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1)
    (hX : ∀ j : Fin r, (j : ℕ) < p →
      normSq (X j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2)
    (w : Fin r → ℂ) (hw : ∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) :
    ‖euc (negPart p (∑ j, w j • X j))‖ ≤ ρ / 3 * ‖euc (posPart p (∑ j, w j • X j))‖ ∧
      3 * (√(r : ℝ) * μ * ‖euc w‖) ≤ ‖euc (posPart p (∑ j, w j • X j))‖ := by
  set R := approxR r μ ρ with hRdef
  have hR0 : 0 ≤ R := approxR_nonneg r hμ hρ
  set E : Fin r → ℂ := ∑ j, w j • (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ)) with hE
  have hEn : ‖euc E‖ ≤ √(r : ℝ) * μ * ‖euc w‖ := norm_err_le X hX hμ.le w hw

  have hsum : ∑ j, w j • X j = (R : ℂ) • w + E := by
    ext k
    simp [hE, Finset.sum_apply, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]
    ring
  have hpw : posPart p w = w := by
    ext k
    simp only [posPart]
    split_ifs with h
    · rfl
    · exact (hw k (not_lt.mp h)).symm
  have hnw : negPart p w = 0 := by
    ext k
    simp only [negPart, Pi.zero_apply]
    split_ifs with h
    · rfl
    · exact hw k (not_lt.mp h)
  have hpos : posPart p (∑ j, w j • X j) = (R : ℂ) • w + posPart p E := by
    rw [hsum, posPart_add, posPart_smul, hpw]
  have hneg : negPart p (∑ j, w j • X j) = negPart p E := by
    rw [hsum, negPart_add, negPart_smul, hnw, smul_zero, zero_add]
  set s := √(r : ℝ) * μ * ‖euc w‖ with hs
  have hs0 : 0 ≤ s := mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hμ.le) (norm_nonneg _)
  have hnegle : ‖euc (negPart p (∑ j, w j • X j))‖ ≤ s := by
    rw [hneg]; exact (norm_negPart_le p E).trans hEn
  have hRw : ‖euc ((R : ℂ) • w)‖ = 4 * s / ρ := by
    rw [euc_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg hR0, hRdef, approxR, hs]
    ring
  have hposge : 4 * s / ρ - s ≤ ‖euc (posPart p (∑ j, w j • X j))‖ := by
    rw [hpos, euc_add]
    have h1 := norm_sub_le (euc ((R : ℂ) • w) + euc (posPart p E)) (euc (posPart p E))
    rw [add_sub_cancel_right] at h1
    have h2 := (norm_posPart_le p E).trans hEn
    linarith
  have hq : 4 * s ≤ 4 * s / ρ := by
    rw [le_div_iff₀ hρ]; nlinarith
  have hqρ : 4 * s / ρ * ρ = 4 * s := div_mul_cancel₀ _ hρ.ne'
  refine ⟨?_, by linarith⟩
  calc ‖euc (negPart p (∑ j, w j • X j))‖ ≤ s := hnegle
    _ ≤ ρ / 3 * (4 * s / ρ - s) := by nlinarith [mul_le_mul_of_nonneg_right hρ1 hs0]
    _ ≤ ρ / 3 * ‖euc (posPart p (∑ j, w j • X j))‖ :=
      mul_le_mul_of_nonneg_left hposge (by positivity)

lemma approxGraph_one {r p : ℕ} {μ ρ : ℝ} (X : Fin r → Fin r → ℂ) (hμ : 0 < μ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1)
    (hX : ∀ j : Fin r, (j : ℕ) < p →
      normSq (X j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2)
    (w : Fin r → ℂ) (hw : ∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) :
    negSq p (∑ j, w j • X j) ≤ (ρ / 3) ^ 2 * posSq p (∑ j, w j • X j) ∧
      (w ≠ 0 → 0 < posSq p (∑ j, w j • X j)) := by
  obtain ⟨h1, h2⟩ := graph_bound X hμ hρ hρ1 hX w hw
  refine ⟨?_, fun hw0 => ?_⟩
  · rw [negSq_eq, posSq_eq, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  · rw [posSq_eq]
    have hwpos : 0 < ‖euc w‖ := by
      rw [norm_pos_iff]; intro h; exact hw0 (euc_eq_zero h)
    have hr : 0 < r := by
      rcases Nat.eq_zero_or_pos r with h | h
      · subst h; exact absurd (Subsingleton.elim w 0) hw0
      · exact h
    have hsq : 0 < √(r : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hr)
    have h3 : 0 < 3 * (√(r : ℝ) * μ * ‖euc w‖) :=
      mul_pos (by norm_num) (mul_pos (mul_pos hsq hμ) hwpos)
    exact pow_pos (lt_of_lt_of_le h3 h2) 2

def graphMap (p : ℕ) {r : ℕ} (X : Fin r → Fin r → ℂ) : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) where
  toFun w := posPart p (∑ j, posPart p w j • X j) + negPart p w
  map_add' u v := by
    simp only [posPart_add, negPart_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]; abel
  map_smul' c u := by
    have h : ∀ j, posPart p (c • u) j • X j = c • (posPart p u j • X j) := fun j => by
      rw [posPart_smul, Pi.smul_apply, smul_eq_mul, mul_smul]
    rw [Finset.sum_congr rfl (fun j _ => h j)]
    simp only [← Finset.smul_sum, posPart_smul, negPart_smul, RingHom.id_apply, smul_add]

lemma graphMap_apply (p : ℕ) {r : ℕ} (X : Fin r → Fin r → ℂ) (w : Fin r → ℂ) :
    graphMap p X w = posPart p (∑ j, posPart p w j • X j) + negPart p w := rfl

lemma exists_graph_pos {r p : ℕ} {μ ρ : ℝ} (X : Fin r → Fin r → ℂ) (hμ : 0 < μ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1)
    (hX : ∀ j : Fin r, (j : ℕ) < p →
      normSq (X j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2)
    (b : Fin r → ℂ) : ∃ w : Fin r → ℂ, (∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) ∧
      posPart p (∑ j, w j • X j) = posPart p b := by

  have hinj : Function.Injective (graphMap p X) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    rw [graphMap_apply] at hu
    have hn : negPart p u = 0 := by
      have := congrArg (negPart p) hu
      rwa [negPart_add, negPart_posPart, zero_add, negPart_negPart, negPart_zero] at this
    have hp : posPart p (∑ j, posPart p u j • X j) = 0 := by
      have := congrArg (posPart p) hu
      rwa [posPart_add, posPart_posPart, posPart_negPart, add_zero, posPart_zero] at this
    have h2 := (graph_bound X hμ hρ hρ1 hX (posPart p u) (posPart_supp p u)).2
    rw [hp, euc_zero, norm_zero] at h2
    have hu0 : posPart p u = 0 := by
      rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr; exact Subsingleton.elim _ _
      · have hsq : 0 < √(r : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hr)
        have hle : ‖euc (posPart p u)‖ ≤ 0 := by
          by_contra hc
          push_neg at hc
          have := mul_pos (by norm_num : (0 : ℝ) < 3) (mul_pos (mul_pos hsq hμ) hc)
          linarith
        exact euc_eq_zero (norm_le_zero_iff.mp hle)
    rw [← posPart_add_negPart p u, hu0, hn, add_zero]
  obtain ⟨u, hu⟩ := (LinearMap.injective_iff_surjective.mp hinj) (posPart p b)
  refine ⟨posPart p u, posPart_supp p u, ?_⟩
  have := congrArg (posPart p) hu
  rwa [graphMap_apply, posPart_add, posPart_posPart, posPart_negPart, add_zero,
    posPart_posPart] at this

end ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
end
end

-- bundled from ReciprocityTheory.SemistableReduction.BWPoly
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Polynomial

theorem bwPoly_holds (hH : LemmaHStatement) (hE : ∀ n, ReciprocityTheory.L2DbarEstimates.EXTStatement n)
    (hO : OnePolyGrowthStatement) : BWPolyStatement := by
  intro p a P hP hT
  obtain ⟨F, hF⟩ := bwp_ext_poly (σ := Fin p × Fin p) (∑ i, a i) (fun z => P (bwpMat z))
    (fun z => (bwpMat z).det) (bwpId p) (fun z => bwp_finite_det_id_line z)
    (fun z v hz => bwp_finite_det_line z v hz) (fun z v hB => bwp_line_poly hH hO a P hP hT z v hB)
  have hF' : ∀ z, (bwpMat z).det ≠ 0 → P (bwpMat z) = MvPolynomial.eval z F := fun z hz => hF z hz
  refine ⟨MvPolynomial.homogeneousComponent (∑ i, a i) F,
    MvPolynomial.homogeneousComponent_isHomogeneous _ _, fun x hx => ?_⟩
  set z : Fin p × Fin p → ℂ := fun ij => x ij.1 ij.2 with hz
  have hxz : bwpMat z = x := by
    ext i j
    rfl
  have hPz : P x = MvPolynomial.eval z F := by
    rw [← hxz]
    exact hF' z (by rw [hxz]; exact hx)
  rw [hPz]
  have hscale : ∀ t : ℂ, t ≠ 0 → MvPolynomial.eval (t • z) F = t ^ (∑ i, a i) * MvPolynomial.eval z F := by
    intro t ht
    have hb : bwpMat (t • z) = x * (t • (1 : Matrix (Fin p) (Fin p) ℂ)) := by
      ext i j
      simp [bwpMat, hz, Matrix.mul_smul]
    have hbdet : (t • (1 : Matrix (Fin p) (Fin p) ℂ)).det ≠ 0 := by
      rw [Matrix.det_smul, Matrix.det_one, mul_one]
      exact pow_ne_zero _ ht
    have hbtri : (t • (1 : Matrix (Fin p) (Fin p) ℂ)).BlockTriangular id := by
      intro i j h
      have hij : i ≠ j := fun hij => by subst hij; exact lt_irrefl _ h
      rw [Matrix.smul_apply, Matrix.one_apply_ne hij, smul_zero]
    have hdet : (bwpMat (t • z)).det ≠ 0 := by
      rw [hb, Matrix.det_mul]
      exact mul_ne_zero hx hbdet
    rw [← hF' _ hdet, hb, hT x _ hx hbdet hbtri, hPz]
    congr 1
    simp [triChar, Finset.prod_pow_eq_pow_sum]
  have hsum : ∀ t : ℂ, MvPolynomial.eval (t • z) F = ∑ j ∈ Finset.range (F.totalDegree + 1),
      t ^ j * MvPolynomial.eval z (MvPolynomial.homogeneousComponent j F) := by
    intro t
    conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent F]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl (fun j _ => bwp_eval_smul_of_isHomogeneous
      (MvPolynomial.homogeneousComponent_isHomogeneous j F) t z)
  have hΦ : (∑ j ∈ Finset.range (F.totalDegree + 1),
      Polynomial.C (MvPolynomial.eval z (MvPolynomial.homogeneousComponent j F)) * Polynomial.X ^ j) =
      Polynomial.C (MvPolynomial.eval z F) * Polynomial.X ^ (∑ i, a i) := by
    refine bwp_poly_eq_of_eval_eq_off _ _ {0} (Set.finite_singleton 0) (fun t ht => ?_)
    have ht0 : t ≠ 0 := ht
    rw [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, mul_comm, ← hscale t ht0, hsum t]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_comm]
  have hc := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q (∑ i, a i)) hΦ
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, if_pos rfl] at hc
  rw [Finset.sum_ite_eq] at hc
  split_ifs at hc with hk
  · exact hc.symm
  · rw [MvPolynomial.homogeneousComponent_eq_zero _ _ (by simpa using hk), map_zero]
    exact hc.symm

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.LatTest
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

end ReciprocityTheory.MultiplicativeHeights
end
end

