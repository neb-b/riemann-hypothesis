module

public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.Bundle0002
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreCyc

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreCasGl
section
noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

namespace CasGl

variable {r s : ℕ}

abbrev KI (r s : ℕ) : Type := {ab : Ix r s × Ix r s // sameBlock ab.1 ab.2}

abbrev PIx (r s : ℕ) : Type := {ab : Ix r s × Ix r s // ¬ sameBlock ab.1 ab.2}

theorem sb_iff (a b : Ix r s) : sameBlock a b ↔ a.isLeft = b.isLeft := by
  cases a <;> cases b <;> simp [sameBlock]

def swK (k : KI r s) : KI r s := ⟨(k.1.2, k.1.1), PI.FHS.sameBlock_symm k.2⟩

theorem sum_sub {N : Type} [AddCommMonoid N] (P : Ix r s → Ix r s → Prop) [∀ a b, Decidable (P a b)]
    (F : Ix r s → Ix r s → N) :
    ∑ k : {ab : Ix r s × Ix r s // P ab.1 ab.2}, F k.1.1 k.1.2 = ∑ a, ∑ b, if P a b then F a b else 0 := by
  rw [← Fintype.sum_prod_type' (f := fun a b => if P a b then F a b else 0), ← Finset.sum_filter]
  exact (Finset.sum_subtype (p := fun ab : Ix r s × Ix r s => P ab.1 ab.2)
    (Finset.univ.filter fun ab : Ix r s × Ix r s => P ab.1 ab.2) (by simp) (fun ab => F ab.1 ab.2)).symm

theorem casK_eq_sum {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Ix r s → Ix r s → Module.End ℂ M) :
    casK ρ = ∑ k : KI r s, ρ k.1.1 k.1.2 * ρ (swK k).1.1 (swK k).1.2 :=
  (sum_sub sameBlock (fun a b => ρ a b * ρ b a)).symm

theorem pc_sum {Z : Mat r s} (hZ : IsPC Z) : ∑ j : PIx r s, Z j.1.1 j.1.2 • Eab j.1.1 j.1.2 = Z := by
  rw [sum_sub (fun a b => ¬ sameBlock a b) (fun a b => Z a b • (Eab a b : Mat r s))]
  conv_rhs => rw [Matrix.matrix_eq_sum_single Z]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : sameBlock a b
  · simp [h, hZ a b h]
  · simp [h, Eab, Matrix.smul_single]

theorem kc_sum {Z : Mat r s} (hZ : IsKC Z) : ∑ j : KI r s, Z j.1.1 j.1.2 • Eab j.1.1 j.1.2 = Z := by
  rw [sum_sub sameBlock (fun a b => Z a b • (Eab a b : Mat r s))]
  conv_rhs => rw [Matrix.matrix_eq_sum_single Z]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : sameBlock a b
  · simp [h, Eab, Matrix.smul_single]
  · simp [h, hZ a b h]

theorem Eab_mul_apply (a b e f : Ix r s) (Z : Mat r s) :
    (Eab a b * Z) e f = if e = a then Z b f else 0 := by
  by_cases h : e = a
  · subst h; simp [Eab]
  · rw [if_neg h]; exact Matrix.single_mul_apply_of_ne _ _ _ _ _ h _

theorem mul_Eab_apply (a b e f : Ix r s) (Z : Mat r s) :
    (Z * Eab a b) e f = if f = b then Z e a else 0 := by
  by_cases h : f = b
  · subst h; simp [Eab]
  · rw [if_neg h]; exact Matrix.mul_single_apply_of_ne _ _ _ _ _ h _

theorem Eab_apply (a b e f : Ix r s) : (Eab a b : Mat r s) e f = if a = e ∧ b = f then 1 else 0 := by
  simp [Eab, Matrix.single_apply]

theorem pc_Eab {a b : Ix r s} (h : ¬ sameBlock a b) : IsPC (Eab a b : Mat r s) := by
  intro e f hef
  rw [Eab_apply]
  split_ifs with h'
  · obtain ⟨rfl, rfl⟩ := h'
    exact absurd hef h
  · rfl

theorem pc_ad {a b : Ix r s} (h : sameBlock a b) {Z : Mat r s} (hZ : IsPC Z) :
    IsPC (Eab a b * Z - Z * Eab a b) := by
  intro e f hef
  have hb : ∀ x y, x.isLeft = y.isLeft → Z x y = 0 := fun x y hxy => hZ x y ((sb_iff x y).mpr hxy)
  rw [sb_iff] at h hef
  rw [Matrix.sub_apply, Eab_mul_apply, mul_Eab_apply]
  by_cases h1 : e = a <;> by_cases h2 : f = b
  · rw [if_pos h1, if_pos h2, hb b f (by rw [← h2]), hb e a (by rw [h1]), sub_zero]
  · rw [if_pos h1, if_neg h2, hb b f (by rw [← h, ← h1, hef]), sub_zero]
  · rw [if_neg h1, if_pos h2, hb e a (by rw [hef, h2, ← h]), sub_zero]
  · rw [if_neg h1, if_neg h2, sub_zero]

theorem kc_mul {Z W : Mat r s} (hZ : IsPC Z) (hW : IsPC W) : IsKC (Z * W) := by
  intro a b hab
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : sameBlock a x
  · rw [hZ a x hx, zero_mul]
  · rw [hW x b ?_, mul_zero]
    rw [sb_iff] at hx hab ⊢
    cases a <;> cases x <;> cases b <;> simp_all

def adC (k : KI r s) : Matrix (PIx r s) (PIx r s) ℂ := fun j i =>
  ((Eab k.1.1 k.1.2 * Eab i.1.1 i.1.2 - Eab i.1.1 i.1.2 * Eab k.1.1 k.1.2 : Mat r s)) j.1.1 j.1.2

theorem adC_sw (k : KI r s) : adC (swK k) = (adC k)ᴴ := by
  ext j i
  obtain ⟨⟨a, b⟩, hk⟩ := k
  obtain ⟨⟨c, d⟩, hi⟩ := i
  obtain ⟨⟨e, f⟩, hj⟩ := j
  simp only [adC, swK, Matrix.conjTranspose_apply, Matrix.sub_apply, Eab_mul_apply, Eab_apply]
  clear hk hi hj
  simp only [star_sub, apply_ite star, star_one, star_zero]
  split_ifs <;> subst_vars <;> simp_all
  all_goals
    obtain ⟨h1, h2⟩ := ‹_ ∧ _›
    subst h1
    simp_all

theorem adC_mul (k k' : KI r s) (j i : PIx r s) :
    (adC k * adC k') j i =
      ((Eab k.1.1 k.1.2 * (Eab k'.1.1 k'.1.2 * Eab i.1.1 i.1.2 - Eab i.1.1 i.1.2 * Eab k'.1.1 k'.1.2) -
        (Eab k'.1.1 k'.1.2 * Eab i.1.1 i.1.2 - Eab i.1.1 i.1.2 * Eab k'.1.1 k'.1.2) * Eab k.1.1 k.1.2 :
          Mat r s)) j.1.1 j.1.2 := by
  have hZ : IsPC (Eab k'.1.1 k'.1.2 * Eab i.1.1 i.1.2 - Eab i.1.1 i.1.2 * Eab k'.1.1 k'.1.2 : Mat r s) :=
    pc_ad k'.2 (pc_Eab i.2)
  rw [Matrix.mul_apply]
  conv_rhs => rw [← pc_sum hZ]
  simp only [Finset.mul_sum, Finset.sum_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, adC, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem adad_apply (a b e f : Ix r s) {Z : Mat r s} (hZ : IsPC Z) :
    ((Eab a b * (Eab b a * Z - Z * Eab b a) - (Eab b a * Z - Z * Eab b a) * Eab a b : Mat r s)) e f =
      ((if e = a then 1 else 0) + (if f = b then 1 else 0)) * Z e f := by
  have hd : ∀ x, Z x x = 0 := fun x => hZ x x ((sb_iff x x).mpr rfl)
  simp only [Matrix.sub_apply, Eab_mul_apply, mul_Eab_apply]
  split_ifs <;> subst_vars <;> simp [hd] <;> ring

theorem count_cross {e f : Ix r s} (h : ¬ sameBlock e f) :
    (∑ a : Ix r s, ∑ b : Ix r s, if sameBlock a b then
      ((if e = a then 1 else 0) + (if f = b then 1 else 0) : ℂ) else 0) = (r : ℂ) + s := by
  rcases e with e | e <;> rcases f with f | f <;> simp [sameBlock] at h ⊢ <;>
    simp [Fintype.sum_sum_type, sameBlock, Finset.sum_add_distrib] <;> ring

theorem adC_cas : ∑ k : KI r s, adC k * adC (swK k) =
    ((((r : ℝ) + s : ℝ)) : ℂ) • (1 : Matrix (PIx r s) (PIx r s) ℂ) := by
  ext j i
  rw [Matrix.sum_apply]
  simp only [adC_mul, swK]
  simp only [adad_apply _ _ _ _ (pc_Eab i.2)]
  rw [sum_sub (fun a b => sameBlock a b) (fun a b => ((if j.1.1 = a then 1 else 0) +
    (if j.1.2 = b then 1 else 0)) * (Eab i.1.1 i.1.2 : Mat r s) j.1.1 j.1.2)]
  simp only [← ite_zero_mul, ← Finset.sum_mul]
  rw [count_cross j.2]
  by_cases hij : j = i
  · subst hij; simp [Eab_apply]
  · have : ¬ (i.1.1 = j.1.1 ∧ i.1.2 = j.1.2) := fun h => hij (Subtype.ext (Prod.ext h.1.symm h.2.symm))
    simp [Eab_apply, this, hij]

end CasGl

open CasGl in
theorem cas_bound_gl {r s : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] (act : Mat r s →ₗ[ℂ] Module.End ℂ M)
    (hL : IsLie act) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Ix r s → Ix r s → Module.End ℂ V) (hadj : AdjK ρ) (c0 : ℝ)
    (hc0 : casK ρ = (c0 : ℂ) • (1 : Module.End ℂ V)) (ι : V →ₗ[ℂ] M)
    (hι : ∀ a b, sameBlock a b → ∀ v, ι (ρ a b v) = act (Eab a b) (ι v))
    (h5 : StarK act (LinearMap.range ι) c0) :
    (∀ x ∈ genG act (LinearMap.range ι),
      casK (units act) x - (c0 : ℂ) • x ∈ LinearMap.range ι → x ∈ LinearMap.range ι) ∧
    ∀ x ∈ genG act (LinearMap.range ι), ∃ F : Submodule ℂ M, FiniteDimensional ℂ F ∧ x ∈ F ∧ KSt (units act) F := by
  have hcas : casK (units act) = ∑ k : KI r s, units act k.1.1 k.1.2 * units act (swK k).1.1 (swK k).1.2 :=
    casK_eq_sum (units act)
  have h1' : ∀ (k : KI r s) (i : PIx r s), units act k.1.1 k.1.2 * act (Eab i.1.1 i.1.2) -
      act (Eab i.1.1 i.1.2) * units act k.1.1 k.1.2 = ∑ j, adC k j i • act (Eab j.1.1 j.1.2) := by
    intro k i
    simp only [units]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hL, ← pc_sum (pc_ad k.2 (pc_Eab i.2)), map_sum]
    simp only [map_smul]
    rfl
  have h2' : ∀ (i j : PIx r s), act (Eab i.1.1 i.1.2) * act (Eab j.1.1 j.1.2) -
      act (Eab j.1.1 j.1.2) * act (Eab i.1.1 i.1.2) ∈
        Submodule.span ℂ (Set.range (fun k : KI r s => units act k.1.1 k.1.2)) := by
    intro i j
    have hK : IsKC (Eab i.1.1 i.1.2 * Eab j.1.1 j.1.2 - Eab j.1.1 j.1.2 * Eab i.1.1 i.1.2 : Mat r s) := by
      intro a b hab
      rw [Matrix.sub_apply, kc_mul (pc_Eab i.2) (pc_Eab j.2) a b hab,
        kc_mul (pc_Eab j.2) (pc_Eab i.2) a b hab, sub_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hL, ← kc_sum hK, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hc0' : ∑ k : KI r s, ρ k.1.1 k.1.2 * ρ (swK k).1.1 (swK k).1.2 = (c0 : ℂ) • 1 := by
    rw [← casK_eq_sum]; exact hc0
  have h5' : ∀ t ≤ c0 + ((r : ℝ) + s), ∀ x ∈ Submodule.span ℂ
      {y : M | ∃ (i : PIx r s) (v : V), y = act (Eab i.1.1 i.1.2) (ι v)},
      (∑ k : KI r s, units act k.1.1 k.1.2 * units act (swK k).1.1 (swK k).1.2) x = (t : ℂ) • x → x = 0 := by
    intro t ht x hx hxt
    refine h5 t ht x (Submodule.span_mono ?_ hx) (by rw [hcas]; exact hxt)
    rintro _ ⟨i, v, rfl⟩
    exact ⟨i.1.1, i.1.2, i.2, ι v, LinearMap.mem_range_self ι v, rfl⟩
  have hG : genG act (LinearMap.range ι) = sInf {N : Submodule ℂ M | LinearMap.range ι ≤ N ∧
      (∀ k : KI r s, ∀ x ∈ N, units act k.1.1 k.1.2 x ∈ N) ∧
      ∀ i : PIx r s, ∀ x ∈ N, act (Eab i.1.1 i.1.2) x ∈ N} := by
    simp only [genG]
    congr 1
    ext N
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hN, hW⟩
      exact ⟨hN, fun k x hx => hW _ x hx, fun i x hx => hW _ x hx⟩
    · rintro ⟨hN, hk, hp⟩
      refine ⟨hN, fun W x hx => ?_⟩
      have hE : ∀ a b, act (Eab a b) x ∈ N := by
        intro a b
        by_cases hab : sameBlock a b
        · exact hk ⟨(a, b), hab⟩ x hx
        · exact hp ⟨(a, b), hab⟩ x hx
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.matrix_eq_sum_single W, map_sum, LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun a _ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun b _ => ?_
      have : (Matrix.single a b (W a b) : Mat r s) = W a b • Eab a b := by simp [Eab]
      rw [this, map_smul, LinearMap.smul_apply]
      exact Submodule.smul_mem _ _ (hE a b)
  obtain ⟨k1, k2⟩ := cas_bound (K := KI r s) (I := PIx r s) swK (fun k => rfl)
    (fun k : KI r s => units act k.1.1 k.1.2) (fun i : PIx r s => act (Eab i.1.1 i.1.2)) adC
    ((r : ℝ) + s) c0 h1' h2' adC_sw adC_cas (fun k : KI r s => ρ k.1.1 k.1.2)
    (fun k u v => hadj k.1.1 k.1.2 k.2 u v) hc0' ι (fun k v => hι k.1.1 k.1.2 k.2 v) h5'
    (genG act (LinearMap.range ι)) hG
  refine ⟨fun x hx hx2 => k1 x hx (by rw [← hcas]; exact hx2), fun x hx => ?_⟩
  obtain ⟨F, hF, hxF, hFk⟩ := k2 x hx
  exact ⟨F, hF, hxF, fun a b hab y hy => hFk ⟨(a, b), hab⟩ y hy⟩

end PositivityTheory.KReal

end
end

-- bundled from Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreLie
section
noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

variable {p q r s : ℕ}

theorem quadT_sub {ι E : Type*} [Fintype ι] [Ring E] [Algebra ℂ E] (R L : ι → E) (A B : Matrix ι ι ℂ) :
    quadT R L (A - B) = quadT R L A - quadT R L B := by
  unfold quadT
  simp only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib]

theorem omAct_lie (M N : Matrix (Ln p q r s) (Ln p q r s) ℂ) :
    omAct p q r s M * omAct p q r s N - omAct p q r s N * omAct p q r s M = omAct p q r s (M * N - N * M) := by
  have h1 := quadT_mul (raiB (p := p) (q := q) (r := r) (s := s)) lowB low_rai M N
  have h2 := quadT_mul (raiB (p := p) (q := q) (r := r) (s := s)) lowB low_rai N M
  have h3 := quartT_comm (raiB (p := p) (q := q) (r := r) (s := s)) lowB rai_rai low_low M N
  have ht : (∑ l, (M * N - N * M) l l * (1 / 2 : ℂ)) = 0 := by
    rw [← Finset.sum_mul]
    have : (∑ l, (M * N - N * M) l l) = (M * N - N * M).trace := rfl
    rw [this, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self, zero_mul]
  rw [omAct_eq, omAct_eq, omAct_eq, ht, zero_smul, add_zero, quadT_sub]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, h1, h2, h3, smul_add, smul_smul]
  rw [mul_comm (∑ l, M l l * (1 / 2 : ℂ))]
  abel

theorem lie1 (p q r s : ℕ) : IsLie (fockAct1 p q r s) := by
  intro X Y
  have h := omAct_lie (Matrix.kroneckerMap (· * ·) X (1 : Mat r s)) (Matrix.kroneckerMap (· * ·) Y (1 : Mat r s))
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, map_sub] at h
  rw [map_sub]
  exact h

theorem lie2 (p q r s : ℕ) : IsLie (fockAct2 p q r s) := by
  intro X Y
  have h := omAct_lie (Matrix.kroneckerMap (· * ·) (1 : Mat p q) X) (Matrix.kroneckerMap (· * ·) (1 : Mat p q) Y)
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, map_sub] at h
  rw [map_sub]
  exact h

theorem lie_tw (p q r s : ℕ) (τ : ℂ) : IsLie (twAct p q r s τ) := by
  intro X Y
  refine LinearMap.ext fun f => ?_
  have h := LinearMap.congr_fun (lie2 p q r s X Y) f
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  have ht : (X * Y - Y * X).trace = 0 := by
    rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, twAct_apply]
  rw [ht, mul_zero, zero_smul, add_zero, ← h]
  simp only [map_add (f := _), map_smul, smul_add, smul_smul]
  rw [mul_comm (τ * X.trace)]
  abel

theorem lie_th (p q r s : ℕ) (c τ : ℂ) : IsLie (thAct p q r s c τ) := by
  intro X Y
  refine LinearMap.ext fun x => ?_
  obtain ⟨f, rfl⟩ : ∃ f, thMkC p q r s c f = x := Submodule.mkQ_surjective _ x
  have h := LinearMap.congr_fun (lie_tw p q r s τ X Y) f
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  simp only [LinearMap.sub_apply, Module.End.mul_apply]
  rw [thAct_mk, thAct_mk, thAct_mk, thAct_mk, thAct_mk, ← h, map_sub]

def sgnC (l : Ln p q r s) : ℂ := if linePos l = true then 1 else -1

theorem rai_adj (l : Ln p q r s) (P Q : Pol p q r s) :
    fockInner (raiB l P) Q = sgnC l * fockInner P (lowB l Q) := by
  unfold raiB lowB sgnC
  by_cases h : linePos l = true
  · simp only [h, if_true, one_mul]
    exact PI.FHS.fockInner_X_mul l P Q
  · rw [if_neg h, if_neg h, if_neg h, LinearMap.neg_apply, PI.FHS.fockInner_neg_left, neg_one_mul]
    exact congrArg Neg.neg (PI.FHS.fockInner_pderiv l P Q)

theorem low_adj (l : Ln p q r s) (P Q : Pol p q r s) :
    fockInner (lowB l P) Q = sgnC l * fockInner P (raiB l Q) := by
  unfold raiB lowB sgnC
  by_cases h : linePos l = true
  · simp only [h, if_true, one_mul]
    exact PI.FHS.fockInner_pderiv l P Q
  · rw [if_neg h, if_neg h, if_neg h, LinearMap.neg_apply, PI.FHS.fockInner_neg_right, neg_one_mul, neg_neg]
    exact PI.FHS.fockInner_X_mul l P Q

theorem omE_adj_gen (l l' : Ln p q r s) (P Q : Pol p q r s) :
    fockInner (omE l l' P) Q = (sgnC l * sgnC l') * fockInner P (omE l' l Q) := by
  unfold omE
  simp only [LinearMap.add_apply, Module.End.mul_apply]
  rw [PI.FHS.fockInner_add_left, PI.FHS.fockInner_add_right, rai_adj, low_adj, mul_add, mul_assoc]
  congr 1
  by_cases h : l = l'
  · subst h
    have hs : sgnC l * sgnC l = 1 := by
      unfold sgnC; split_ifs <;> simp
    rw [hs, one_mul, if_pos rfl]
    simp only [LinearMap.smul_apply, Module.End.one_apply]
    rw [PI.FHS.fockInner_smul_left, PI.FHS.fockInner_smul_right]
    congr 1
    simp [map_ofNat]
  · rw [if_neg h, if_neg (Ne.symm h)]
    simp only [LinearMap.zero_apply]
    rw [PI.FHS.fockInner_zero_left, PI.FHS.fockInner_zero_right, mul_zero]

theorem fockAct1_unit (a b : Ix p q) (P : Pol p q r s) :
    fockAct1 p q r s (Eab a b) P = ∑ c : Ix r s, omE ((a, c) : Ln p q r s) (b, c) P := by
  rw [PI.FHS.fockAct1_eq, PI.FHS.omAct_apply]
  simp only [Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Eab, Matrix.single_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single a (by intro x _ hx; simp [Ne.symm hx]) (by simp)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_eq_single b (by intro x _ hx; simp [Ne.symm hx]) (by simp)]
  simp

theorem fockAct2_unit (c d : Ix r s) (P : Pol p q r s) :
    fockAct2 p q r s (Eab c d) P = ∑ a : Ix p q, omE ((a, c) : Ln p q r s) (a, d) P := by
  rw [PI.FHS.fockAct2_eq, PI.FHS.omAct_apply]
  simp only [Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Eab, Matrix.single_apply, Matrix.one_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single c (by intro x _ hx; simp [Ne.symm hx]) (by simp)]
  rw [Finset.sum_eq_single a (by intro x _ hx; simp [Ne.symm hx]) (by simp)]
  rw [Finset.sum_eq_single d (by intro x _ hx; simp [Ne.symm hx]) (by simp)]
  simp

theorem fock_inner_adjoint_first (a b : Ix p q) (u v : Pol p q r s) :
    fockInner (fockAct1 p q r s (Eab a b) u) v = epsB a b * fockInner u (fockAct1 p q r s (Eab b a) v) := by
  rw [fockAct1_unit, fockAct1_unit, PI.FHS.fockInner_sum_left, PI.FHS.fockInner_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [omE_adj_gen]
  congr 1
  cases a <;> cases b <;> cases c <;> simp [sgnC, epsB, linePos, sameBlock]

theorem fock_inner_adjoint_second (a b : Ix r s) (u v : Pol p q r s) :
    fockInner (fockAct2 p q r s (Eab a b) u) v = epsB a b * fockInner u (fockAct2 p q r s (Eab b a) v) := by
  rw [fockAct2_unit, fockAct2_unit, PI.FHS.fockInner_sum_left, PI.FHS.fockInner_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [omE_adj_gen]
  congr 1
  cases a <;> cases b <;> cases c <;> simp [sgnC, epsB, linePos, sameBlock]

theorem adj1 (p q r s : ℕ) : AdjG (fvAct1 p q r s) := fun a b u v => fock_inner_adjoint_first a b u v

theorem adj2 (p q r s : ℕ) : AdjG (fvAct2 p q r s) := fun a b u v => fock_inner_adjoint_second a b u v

theorem hwK_of_hwSub {m n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {act : Mat m n →ₗ[ℂ] Module.End ℂ V}
    {μ : Ix m n → ℚ} {v : V} : v ∈ hwSub act μ ↔ HwK (units act) μ v :=
  PI.FockOneDegW.Swap.mem_hwSub_iff act μ v

theorem dom2 {ν : Ix r s → ℚ} {g : Pol p q r s} (hg : IsHW (fockAct2 p q r s) ν g) : Dom ν := by
  have hL : IsLie (fvAct2 p q r s) := lie2 p q r s
  have hw : HwK (units (fvAct2 p q r s)) ν (show FV p q r s from g) := hwK_of_hwSub.1 hg.2
  exact dom_of_hw (adjK_of_adjG (adj2 p q r s)) (glK_of_lie hL) hw hg.1

theorem hwExist2 (U : Submodule ℂ (Pol p q r s)) [FiniteDimensional ℂ U] (h0 : U ≠ ⊥)
    (hU : KSt (units (fockAct2 p q r s)) U) : ∃ ν v, v ∈ U ∧ IsHW (fockAct2 p q r s) ν v := by
  have hint : ∀ (Y : Mat r s) (w : Pol p q r s),
      fockAct1 r s p q Y (PI.FockOneDegW.Swap.swL p q r s w) =
        PI.FockOneDegW.Swap.swL p q r s (fockAct2 p q r s Y w) :=
    fun Y w => (PI.FockOneDegW.Swap.rename_fockAct2 Y w).symm
  have hinj : Function.Injective (PI.FockOneDegW.Swap.swL p q r s) :=
    PI.FockOneDegW.Swap.rename_sw_injective p q r s
  obtain ⟨ν, v, hv, hw⟩ := PI.FockOneDegW.hwExist r s p q (U.map (PI.FockOneDegW.Swap.swL p q r s))
    inferInstance (by
      intro h
      apply h0
      rw [eq_bot_iff]
      intro x hx
      have : PI.FockOneDegW.Swap.swL p q r s x ∈ (⊥ : Submodule ℂ (Pol r s p q)) :=
        h ▸ Submodule.mem_map_of_mem hx
      rw [Submodule.mem_bot] at this ⊢
      exact hinj (by rw [this, map_zero])) (by
      rintro a b hab _ ⟨w, hw, rfl⟩
      rw [hint]
      exact Submodule.mem_map_of_mem (hU a b hab w hw))
  obtain ⟨w, hw', rfl⟩ := hv
  exact ⟨ν, w, hw', PI.FockOneDegW.Swap.isHW_of_map _ _ _ hinj hint ν w hw⟩

theorem scalar_of_hw {μ : Ix p q → ℚ} (hμ : ∀ a b, sameBlock a b → μ a = μ b) {x : Pol p q r s}
    (hx : x ∈ hwSub (fockAct1 p q r s) μ) (a b : Ix p q) (hab : sameBlock a b) :
    fockAct1 p q r s (Eab a b) x = (if a = b then ((μ a : ℚ) : ℂ) else 0) • x := by
  have hL : IsLie (fvAct1 p q r s) := lie1 p q r s
  have hw : HwK (units (fvAct1 p q r s)) μ (show FV p q r s from x) := hwK_of_hwSub.1 hx
  by_cases h : a = b
  · subst h
    rw [if_pos rfl]
    exact hw.1 a
  · rw [if_neg h, zero_smul]
    rcases PI.FockOneDegW.Core.posC_or a b hab h with h1 | h1
    · exact hw.2 a b h1
    · exact low_kill (adjK_of_adjG (adj1 p q r s)) (glK_of_lie hL) hw h1 (hμ a b hab).symm

theorem mem_polChi_iff (c : ℂ) (x : Pol p q r s) : x ∈ polChi p q r s c ↔
    ∀ a b, sameBlock a b → fockAct1 p q r s (Eab a b) x = (if a = b then c else 0) • x := by
  unfold polChi jointEig
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero]
  constructor
  · intro h a b hab
    have h1 := h ⟨Eab a b, PI.FockOneDegW.isKC_Eab hab⟩
    refine h1.trans ?_
    congr 1
    by_cases e : a = b
    · subst e
      simp [chiTr, Eab]
    · simp [chiTr, Eab, e, Matrix.trace_single_eq_of_ne _ _ _ e]
  · rintro h ⟨Z, hZ⟩
    change fockAct1 p q r s Z x = chiTr c Z • x
    rw [act_eq_sum (fockAct1 p q r s) Z]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    have key : ∀ a b, Z a b • fockAct1 p q r s (Eab a b) x = (if a = b then c * Z a a else 0) • x := by
      intro a b
      by_cases hab : sameBlock a b
      · rw [h a b hab, smul_smul]
        by_cases e : a = b
        · subst e
          rw [if_pos rfl, if_pos rfl, mul_comm]
        · rw [if_neg e, if_neg e, mul_zero]
      · have e : a ≠ b := by
          rintro rfl
          exact hab (by cases a <;> trivial)
        rw [hZ a b hab, if_neg e, zero_smul, zero_smul]
    simp only [key, ← Finset.sum_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    congr 1
    simp only [chiTr, Matrix.trace, Matrix.diag_apply, Finset.mul_sum]

theorem mem_polChi_iff_hw (c : ℂ) (c0 : ℚ) (hc : c = c0) (x : Pol p q r s) :
    x ∈ polChi p q r s c ↔ x ∈ hwSub (fockAct1 p q r s) (fun _ => c0) := by
  subst hc
  rw [mem_polChi_iff]
  constructor
  · intro h
    refine (PI.FockOneDegW.Swap.mem_hwSub_iff _ _ _).2 ⟨fun a => ?_, fun a b hab => ?_⟩
    · rw [h a a (by cases a <;> trivial), if_pos rfl]
    · rw [h a b (PI.FockOneDegW.Core.posC_sb a b hab), if_neg (PI.FockOneDegW.Core.posC_ne a b hab), zero_smul]
  · intro h a b hab
    exact scalar_of_hw (μ := fun _ => c0) (fun _ _ _ => rfl) h a b hab

end PositivityTheory.KReal

end
end

