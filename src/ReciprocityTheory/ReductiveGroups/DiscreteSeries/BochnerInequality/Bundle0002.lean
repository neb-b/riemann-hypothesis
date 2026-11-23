module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasValK
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.Bundle0001
public import Lemmata.SimultaneousEigenvectors.BlSimeig
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.NumRho

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.BigCasA
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.BigCasimir

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section AlgGen

variable {X : Type*} [AddCommGroup X] [Module ℂ X] {ε : Fin n → Bool}

end AlgGen

section Slots

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem ofCoords_apply {X : Type*} [AddCommGroup X] [Module ℂ X] (k : ℕ)
    (f : (Fin k → Fin n × Fin n) → (X →ₗ[ℂ] M)) (x : X) (κ : Fin k → Fin n × Fin n) :
    (ofCoords k f x) κ = f κ x := rfl

theorem mAct_apply (k : ℕ) (a b : Fin n) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    mAct E k a b F κ = E a b (F κ) := rfl

theorem factorAd_apply (k : ℕ) (i : Fin k) (a b : Fin n) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    factorAd k i a b F κ =
      (if (κ i).1 = a then F (Function.update κ i (b, (κ i).2)) else 0) -
        (if (κ i).2 = b then F (Function.update κ i ((κ i).1, a)) else 0) := by
  show (ofCoords k _ F) κ = _
  rw [ofCoords_apply, LinearMap.sub_apply]
  split_ifs <;> rfl

theorem mem_ncV_iff {k : ℕ} {F : Big n k M} : F ∈ ncV ε V k ↔
    ∀ κ : Fin k → Fin n × Fin n, ((∀ i, ε (κ i).1 ≠ ε (κ i).2) → F κ ∈ V) ∧
      ((¬ ∀ i, ε (κ i).1 ≠ ε (κ i).2) → F κ = 0) := by
  simp only [ncV, Submodule.mem_iInf, Submodule.mem_comap]
  refine forall_congr' fun κ => ?_
  split_ifs with h <;> simp [h] <;> rfl

theorem factorAd_mem_ncV {k : ℕ} (i : Fin k) {a b : Fin n} (hab : ε a = ε b) {F : Big n k M}
    (hF : F ∈ ncV ε V k) : factorAd k i a b F ∈ ncV ε V k := by
  rw [mem_ncV_iff] at hF ⊢
  intro κ
  rcases hx : κ i with ⟨x, y⟩
  simp only [factorAd_apply, hx]
  constructor
  · intro hκ
    have hxy : ε x ≠ ε y := by simpa [hx] using hκ i
    refine Submodule.sub_mem _ ?_ ?_ <;> split_ifs with h <;> try exact Submodule.zero_mem _
    · refine (hF _).1 fun j => ?_
      by_cases hj : j = i
      · subst hj; simp only [Function.update_self]; rw [← hab, ← h]; exact hxy
      · rw [Function.update_of_ne hj]; exact hκ j
    · refine (hF _).1 fun j => ?_
      by_cases hj : j = i
      · subst hj; simp only [Function.update_self]; rw [hab, ← h]; exact hxy
      · rw [Function.update_of_ne hj]; exact hκ j
  · intro hκ
    push Not at hκ
    obtain ⟨j, hj⟩ := hκ
    have key : ∀ p : Fin n × Fin n, ε p.1 = ε p.2 → (¬ ∀ l, ε ((Function.update κ i p) l).1 ≠
        ε ((Function.update κ i p) l).2) := by
      intro p hp h
      by_cases hji : j = i
      · subst hji; exact h j (by simpa using hp)
      · exact h j (by rw [Function.update_of_ne hji]; exact hj)
    have hxy : j = i → ε x = ε y := by intro hji; subst hji; simpa [hx] using hj
    have hc : ∀ p : Fin n × Fin n, (j = i → ε p.1 = ε p.2) → F (Function.update κ i p) = 0 := by
      intro p hp
      by_cases hji : j = i
      · exact (hF _).2 (key p (hp hji))
      · refine (hF _).2 fun h => h j ?_
        rw [Function.update_of_ne hji]; exact hj
    rw [ite_eq_right_iff.2 ?_, ite_eq_right_iff.2 ?_, sub_zero]
    · intro h; subst h; exact hc _ fun hji => by show ε x = ε a; rw [hxy hji, ← hab]
    · intro h; subst h; exact hc _ fun hji => by show ε b = ε y; rw [← hab, hxy hji]

theorem mAct_mem_ncV (hV : IsKStableSub ε E V) (k : ℕ) {a b : Fin n} (hab : ε a = ε b)
    {F : Big n k M} (hF : F ∈ ncV ε V k) : mAct E k a b F ∈ ncV ε V k := by
  rw [mem_ncV_iff] at hF ⊢
  intro κ
  simp only [mAct_apply]
  exact ⟨fun h => hV a b hab _ ((hF κ).1 h), fun h => by rw [(hF κ).2 h, map_zero]⟩

end Slots

end ReciprocityTheory.ChartRestriction.DS.BigCasimir
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.IsKUnitaryOfIsInfUnitary
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section KUnit

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X}

def IsKUnitary (ε : Fin n → Bool) (A : Fin n → Fin n → Module.End ℂ X) : Prop :=
  ∀ a b, ε a = ε b → ∀ x y : X, inner ℂ (A a b x) y = inner ℂ x (A b a y)

theorem isKUnitary_of_isInfUnitary (hU : IsInfUnitary ε A) : IsKUnitary ε A := by
  intro a b h x y
  rw [hU a b x y]
  simp [adjSign, h]

theorem kUnit_diag_comm (hA : IsGlRep A) (a c : Fin n) (v : X) :
    A a a (A c c v) = A c c (A a a v) := by
  have h := LinearMap.congr_fun (hA a a c c) v
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  by_cases hac : a = c
  · subst hac; rfl
  · simp only [if_neg hac, if_neg (Ne.symm hac), LinearMap.zero_apply, sub_zero, sub_eq_zero] at h
    exact h

theorem kUnit_weight_shift (hA : IsGlRep A) {μ : Fin n → ℝ} {w : X} (hw : ∀ c, A c c w = (μ c : ℂ) • w)
    {a b : Fin n} (hab : a ≠ b) (c : Fin n) :
    A c c (A a b w) = ((μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0) : ℝ) : ℂ) • A a b w := by
  have h := LinearMap.congr_fun (hA c c a b) w
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hw c, map_smul] at h
  by_cases hca : c = a
  · subst hca
    simp [hab, Ne.symm hab] at h ⊢
    linear_combination (norm := module) h
  · by_cases hcb : c = b
    · subst hcb
      simp [hca] at h ⊢
      linear_combination (norm := module) h
    · simp [hca, hcb, Ne.symm hcb] at h ⊢
      linear_combination (norm := module) h

theorem kUnit_exists_joint (hA : IsGlRep A) (s : Finset (Fin n)) :
    ∀ T : Submodule ℂ X, FiniteDimensional ℂ T → (∀ c, ∀ v ∈ T, A c c v ∈ T) → T ≠ ⊥ →
      ∃ w ∈ T, w ≠ 0 ∧ ∃ μ : Fin n → ℂ, ∀ c ∈ s, A c c w = μ c • w := by
  first | exact Bl.SimultaneousEigenvectors.goal1 .. | (apply Bl.SimultaneousEigenvectors.goal1 <;> assumption) | (intros; apply Bl.SimultaneousEigenvectors.goal1 <;> assumption)

theorem kUnit_eig_real (hU : IsKUnitary ε A) {c : Fin n} {w : X} (hw0 : w ≠ 0) {z : ℂ}
    (hw : A c c w = z • w) : z = ((z.re : ℝ) : ℂ) := by
  have h := hU c c rfl w w
  rw [hw, inner_smul_left, inner_smul_right] at h
  have hne : inner ℂ w w ≠ (0 : ℂ) := inner_self_ne_zero.mpr hw0
  have h2 : (starRingEnd ℂ) z = z := mul_right_cancel₀ hne h
  exact (Complex.conj_eq_iff_re.mp h2).symm

def kUnitWtLin (μ : Fin n → ℝ) : ℝ := ∑ c : Fin n, ((n : ℝ) - ((c : ℕ) : ℝ)) * μ c

theorem kUnitWtLin_shift (μ : Fin n → ℝ) {a b : Fin n} (hab : a < b) :
    kUnitWtLin μ < kUnitWtLin (fun c => μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) := by
  have hlt : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  have h : kUnitWtLin (fun c => μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) =
      kUnitWtLin μ + ((n : ℝ) - ((a : ℕ) : ℝ)) - ((n : ℝ) - ((b : ℕ) : ℝ)) := by
    simp only [kUnitWtLin, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [h]
  linarith

theorem exists_khw (hA : IsGlRep A) (hU : IsKUnitary ε A) {S : Submodule ℂ X}
    (hfd : FiniteDimensional ℂ S) (hS : IsKStableSub ε A S) (hne : S ≠ ⊥) :
    ∃ w ∈ S, w ≠ 0 ∧ ∃ μ : Fin n → ℝ, IsKHWVec ε A μ w := by
  classical
  have hSc : ∀ c, ∀ v ∈ S, A c c v ∈ S := fun c => hS c c rfl
  let P : Set (Fin n → ℝ) := {μ | ∃ w ∈ S, w ≠ 0 ∧ ∀ c, A c c w = (μ c : ℂ) • w}
  have hPfin : P.Finite := by
    refine (Set.Finite.pi (t := fun c => {r : ℝ | Module.End.HasEigenvalue ((A c c).restrict (hSc c)) (r : ℂ)})
      (fun c => (Module.End.finite_hasEigenvalue _).preimage
        (Complex.ofReal_injective.injOn))).subset ?_
    rintro μ ⟨w, hw, hw0, hμ⟩ c -
    show Module.End.HasEigenvalue ((A c c).restrict (hSc c)) (μ c : ℂ)
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨w, hw⟩) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      exact Subtype.ext (by simpa using hμ c)
    · intro h
      exact hw0 (congrArg Subtype.val h)
  have hPne : P.Nonempty := by
    obtain ⟨w, hw, hw0, z, hz⟩ := kUnit_exists_joint hA Finset.univ S hfd hSc hne
    refine ⟨fun c => (z c).re, w, hw, hw0, fun c => ?_⟩
    rw [hz c (Finset.mem_univ c)]
    congr 1
    exact kUnit_eig_real hU hw0 (hz c (Finset.mem_univ c))
  obtain ⟨μ, ⟨w, hw, hw0, hμ⟩, hmax⟩ := Set.exists_max_image P kUnitWtLin hPfin hPne
  refine ⟨w, hw, hw0, μ, hμ, ?_⟩
  intro a b hab hεab
  by_contra h
  have hmem : (fun c => μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) ∈ P :=
    ⟨A a b w, hS a b hεab w hw, h, fun c => kUnit_weight_shift hA hμ (ne_of_lt hab) c⟩
  exact absurd (hmax _ hmem) (not_le.mpr (kUnitWtLin_shift μ hab))

theorem orthogonal_kStable (hU : IsKUnitary ε A) {S : Submodule ℂ X} (hS : IsKStableSub ε A S) :
    IsKStableSub ε A Sᗮ := by
  intro a b hab v hv
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro u hu
  rw [← hU b a hab.symm u v]
  exact hv _ (hS b a hab.symm u hu)

theorem starProjection_comm (hU : IsKUnitary ε A) {S : Submodule ℂ X} [S.HasOrthogonalProjection]
    (hS : IsKStableSub ε A S) {a b : Fin n} (hab : ε a = ε b) (x : X) :
    S.starProjection (A a b x) = A a b (S.starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hS a b hab _ (Submodule.starProjection_apply_mem S x)
  · intro w hw
    rw [← map_sub]
    have h1 : x - S.starProjection x ∈ Sᗮ := Submodule.sub_starProjection_mem_orthogonal x
    have h2 := orthogonal_kStable hU hS a b hab _ h1
    rw [Submodule.mem_orthogonal] at h2
    rw [inner_eq_zero_symm]
    exact h2 w hw

end KUnit

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Numerics
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Num

variable {ε : Fin n → Bool}

private theorem dot_add_l (u v w : Fin n → ℝ) : dot (u + v) w = dot u w + dot v w := by
  simp only [dot, Pi.add_apply, add_mul, sum_add_distrib]

private theorem dot_add_r (u v w : Fin n → ℝ) : dot u (v + w) = dot u v + dot u w := by
  simp only [dot, Pi.add_apply, mul_add, sum_add_distrib]

private theorem dot_comm' (u v : Fin n → ℝ) : dot u v = dot v u := by
  simp only [dot, mul_comm]

private theorem dot_neg_r (u v : Fin n → ℝ) : dot u (-v) = - dot u v := by
  simp only [dot, Pi.neg_apply, mul_neg, sum_neg_distrib]

private theorem dot_sum_r {k : ℕ} (u : Fin n → ℝ) (f : Fin k → Fin n → ℝ) :
    dot u (∑ i, f i) = ∑ i, dot u (f i) := by
  simp only [dot, Finset.sum_apply, mul_sum]
  exact Finset.sum_comm

private theorem dot_root_r (u : Fin n → ℝ) (a b : Fin n) : dot u (root a b) = u a - u b := by
  simp [dot, root, Pi.single_apply, mul_sub, sum_sub_distrib]

private theorem root_swap (a b : Fin n) : root b a = - root a b := by
  simp [root]

private theorem nsq_nonneg'' (u : Fin n → ℝ) : 0 ≤ nsq u := by
  unfold nsq dot
  exact sum_nonneg fun i _ => mul_self_nonneg (u i)

private theorem nsq_add'' (u v : Fin n → ℝ) : nsq (u + v) = nsq u + 2 * dot u v + nsq v := by
  simp only [nsq, dot_add_l, dot_add_r, dot_comm' v u]; ring

private theorem dot_le_sqrt (u v : Fin n → ℝ) : dot u v ≤ √(nsq u) * √(nsq v) := by
  rw [← Real.sqrt_mul (nsq_nonneg'' u)]
  refine le_trans (le_abs_self _) ?_
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  simpa [dot, nsq, sq] using Finset.sum_mul_sq_le_sq_mul_sq univ u v

private theorem sqrt_nsq_add_le (u v : Fin n → ℝ) : √(nsq (u + v)) ≤ √(nsq u) + √(nsq v) := by
  have h1 : nsq (u + v) ≤ (√(nsq u) + √(nsq v)) ^ 2 := by
    rw [nsq_add'', add_sq, Real.sq_sqrt (nsq_nonneg'' u), Real.sq_sqrt (nsq_nonneg'' v)]
    nlinarith [dot_le_sqrt u v]
  calc √(nsq (u + v)) ≤ √((√(nsq u) + √(nsq v)) ^ 2) := Real.sqrt_le_sqrt h1
    _ = _ := Real.sqrt_sq (by positivity)

private theorem sqrt_nsq_sum_le {ι : Type*} (s : Finset ι) (f : ι → Fin n → ℝ) :
    √(nsq (∑ i ∈ s, f i)) ≤ ∑ i ∈ s, √(nsq (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [nsq, dot]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (sqrt_nsq_add_le _ _).trans (by linarith)

private theorem pq_facts {a b : Fin n} (hε : ε a ≠ ε b) :
    1 ≤ (pOf ε : ℝ) ∧ 1 ≤ (qOf ε : ℝ) ∧ (pOf ε : ℝ) + (qOf ε : ℝ) = n := by
  have hsum : pOf ε + qOf ε = n := by
    unfold pOf qOf
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (fun a => ε a = true)
    simpa using this
  have hp : ∃ c, ε c = true := by
    cases ha : ε a
    · exact ⟨b, by cases hb : ε b <;> simp_all⟩
    · exact ⟨a, ha⟩
  have hq : ∃ c, ε c = false := by
    cases ha : ε a
    · exact ⟨a, ha⟩
    · exact ⟨b, by cases hb : ε b <;> simp_all⟩
  obtain ⟨c, hc⟩ := hp
  obtain ⟨d, hd⟩ := hq
  have h1 : 1 ≤ pOf ε := Finset.card_pos.mpr ⟨c, by simp [hc]⟩
  have h2 : 1 ≤ qOf ε := Finset.card_pos.mpr ⟨d, by simp [hd]⟩
  refine ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast hsum⟩

theorem gap_gt {a b : Fin n} (hε : ε a ≠ ε b) {h : ℝ}
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) :
    2 * (n : ℝ) - 3 < h ∧ (n : ℝ) - 1 < h := by
  obtain ⟨hp, hq, hn⟩ := pq_facts hε
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm := mul_nonneg (sub_nonneg.2 hp) (sub_nonneg.2 hq)
  have key : (n : ℝ) * ((n : ℝ) - 1) ≤ (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) := by
    nlinarith [mul_nonneg hn0 hm]
  constructor
  · nlinarith [sq_nonneg ((n : ℝ) - 2)]
  · nlinarith [sq_nonneg ((n : ℝ) - 1)]

theorem sch_gap {lam : Fin n → ℝ} (hgap : StdGap ε lam) {a b : Fin n} (hab : a < b)
    (hε : ε a ≠ ε b) : 1 + 2 * dot (rhoC ε) (rhoN ε) < dot lam (root a b) := by
  obtain ⟨hanti, h, hg, hbig⟩ := hgap
  have h1 := hg a b hε
  have hlt : lam b < lam a := hanti hab
  rw [abs_of_pos (sub_pos.2 hlt)] at h1
  rw [dot_root_r]
  linarith [two_dot_rhoC_rhoN_le ε]

theorem crossVal_pos {lam : Fin n → ℝ} (hmono : StrictAnti lam) {h : ℝ}
    (hh : GapAtLeast ε lam h) {a b : Fin n} (hab : a < b) (hε : ε a ≠ ε b) :
    2 * (h - n + 1) ≤
      casValK ε (lowK ε lam + root a b) - n - casValK ε (lowK ε lam) := by
  rw [casValK_add, lowK_add_rhoC, nsq_root (ne_of_lt hab), dot_add_l, dot_root_r lam]
  have h1 := hh a b hε
  rw [abs_of_pos (sub_pos.2 (hmono hab))] at h1
  have h2 := dot_rhoN_root_ge hab hε
  linarith

theorem crossVal_neg {lam : Fin n → ℝ} (hmono : StrictAnti lam) {h : ℝ}
    (hh : GapAtLeast ε lam h) {a b : Fin n} (hab : a < b) (hε : ε a ≠ ε b) :
    casValK ε (lowK ε lam + root b a) - n - casValK ε (lowK ε lam) ≤ -2 * h - 2 := by
  rw [casValK_add, lowK_add_rhoC, nsq_root (ne_of_gt hab), dot_add_l, dot_root_r lam,
    root_swap a b, dot_neg_r]
  have h1 := hh a b hε
  rw [abs_of_pos (sub_pos.2 (hmono hab))] at h1
  have h2 := dot_rhoN_root_ge hab hε
  linarith

theorem isNCSum_zero {ν : Fin n → ℝ} : IsNCSum ε 0 ν ↔ ν = 0 := by
  constructor
  · rintro ⟨γ, -, rfl⟩
    simp
  · rintro rfl
    exact ⟨Fin.elim0, fun i => i.elim0, by simp⟩

theorem isNCSum_succ_exists {k : ℕ} {ν : Fin n → ℝ} (hν : IsNCSum ε (k + 1) ν) :
    ∃ a b : Fin n, ε a ≠ ε b := by
  obtain ⟨γ, hγ, -⟩ := hν
  exact ⟨_, _, hγ 0⟩

theorem vogan_num {Λ ν : Fin n → ℝ} {j : ℕ} (hj : 1 ≤ j) (hν : IsNCSum ε j ν) {h : ℝ}
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h)
    (hc : casValK ε Λ + 2 * (j : ℝ) * (h - n + 1) ≤ casValK ε (Λ + ν)) :
    nsq (Λ + (2 : ℝ) • rhoC ε) ≤ nsq (Λ + ν + (2 : ℝ) • rhoC ε) := by
  obtain ⟨γ, hγ, rfl⟩ := hν
  obtain ⟨hg1, hg2⟩ := gap_gt (hγ ⟨0, hj⟩) hbig
  have hρ : -((j : ℝ) * (((n : ℝ) - 2) / 2)) ≤ dot (rhoC ε) (∑ i, root (γ i).1 (γ i).2) := by
    rw [dot_sum_r]
    have : ∑ _i : Fin j, -(((n : ℝ) - 2) / 2) ≤ ∑ i, dot (rhoC ε) (root (γ i).1 (γ i).2) := by
      apply Finset.sum_le_sum
      intro i _
      have := abs_dot_root_rhoC_le (ε := ε) (hγ i)
      rw [dot_comm'] at this
      linarith [neg_abs_le (dot (rhoC ε) (root (γ i).1 (γ i).2))]
    simpa [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_neg] using this
  rw [casValK_add] at hc
  have e2 : Λ + (2 : ℝ) • rhoC ε = (Λ + rhoC ε) + rhoC ε := by rw [two_smul]; abel
  have e3 : Λ + (∑ i, root (γ i).1 (γ i).2) + (2 : ℝ) • rhoC ε =
      ((Λ + rhoC ε) + rhoC ε) + ∑ i, root (γ i).1 (γ i).2 := by rw [two_smul]; abel
  rw [e2, e3, nsq_add'' ((Λ + rhoC ε) + rhoC ε), dot_add_l]
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hpos : 0 ≤ 2 * h - 3 * (n : ℝ) + 4 := by linarith
  nlinarith [mul_nonneg hj0 hpos]

theorem degree_num {Λ ν : Fin n → ℝ} {j k : ℕ} (hjk : j ≤ k) (hν : IsNCSum ε j ν) :
    casValK ε (Λ + ν) ≤ (√(nsq (Λ + rhoC ε)) + √2 * k) ^ 2 - nsq (rhoC ε) := by
  obtain ⟨γ, hγ, rfl⟩ := hν
  have hs : √(nsq (∑ i, root (γ i).1 (γ i).2)) ≤ √2 * k := by
    refine (sqrt_nsq_sum_le _ _).trans ?_
    have : ∀ i, √(nsq (root (γ i).1 (γ i).2)) = √2 := fun i => by
      rw [nsq_root (fun e => hγ i (by rw [e]))]
    simp only [this, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hjk) (Real.sqrt_nonneg 2)
  unfold casValK
  have e : Λ + (∑ i, root (γ i).1 (γ i).2) + rhoC ε = (Λ + rhoC ε) + ∑ i, root (γ i).1 (γ i).2 := by
    abel
  rw [e]
  have h1 := (sqrt_nsq_add_le (Λ + rhoC ε) (∑ i, root (γ i).1 (γ i).2)).trans (by linarith [hs] :
    √(nsq (Λ + rhoC ε)) + √(nsq (∑ i, root (γ i).1 (γ i).2)) ≤ √(nsq (Λ + rhoC ε)) + √2 * k)
  have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  rw [Real.sq_sqrt (nsq_nonneg'' _)] at h2
  linarith

end Num

end ReciprocityTheory.ChartRestriction.DS
end
end

