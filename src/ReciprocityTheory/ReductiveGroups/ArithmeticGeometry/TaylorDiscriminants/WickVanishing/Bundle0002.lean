module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Taylor

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.DofDApply
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.GE

variable {k : Type} [CommRing k] {d : ℕ}

def dofCoef (F : Fin d → PS k 2 d) (v : Fin d → k) (j : Fin d) : PS k 1 d :=
  ∑ i : Fin d, C (v i) * ev (n := 1) ![pt k d 0, 0] (pderiv ((1 : Fin 2), i) (F j))

def dofD (F : Fin d → PS k 2 d) (v : Fin d → k) : Derivation k (PS k 1 d) (PS k 1 d) :=
  ∑ j : Fin d, dofCoef F v j • pderiv ((0 : Fin 1), j)

theorem dofD_apply (F : Fin d → PS k 2 d) (v : Fin d → k) (f : PS k 1 d) :
    dofD F v f = Dof F v f := by
  have h : ∀ (s : Finset (Fin d)) (D : Fin d → Derivation k (PS k 1 d) (PS k 1 d)),
      (∑ j ∈ s, D j) f = ∑ j ∈ s, D j f := by
    intro s D
    refine Finset.induction_on s (by simp) ?_
    intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]
  rw [dofD, h]
  simp only [Derivation.smul_apply, smul_eq_mul, Dof, dofCoef]

theorem dof_add (F : Fin d → PS k 2 d) (v : Fin d → k) (f g : PS k 1 d) :
    Dof F v (f + g) = Dof F v f + Dof F v g := by
  simp only [← dofD_apply, map_add (f := _)]

theorem dof_mul (F : Fin d → PS k 2 d) (v : Fin d → k) (f g : PS k 1 d) :
    Dof F v (f * g) = f * Dof F v g + g * Dof F v f := by
  simp only [← dofD_apply, Derivation.leibniz, smul_eq_mul]

theorem dof_C (F : Fin d → PS k 2 d) (v : Fin d → k) (r : k) : Dof F v (C r) = 0 := by
  have hC : (C r : PS k 1 d) = r • (1 : PS k 1 d) := by
    rw [MvPowerSeries.smul_eq_C_mul, mul_one]
  rw [← dofD_apply, hC, Derivation.map_smul, Derivation.map_one_eq_zero, smul_zero]

theorem dof_C_mul (F : Fin d → PS k 2 d) (v : Fin d → k) (r : k) (f : PS k 1 d) :
    Dof F v (C r * f) = C r * Dof F v f := by
  rw [dof_mul, dof_C, mul_zero, add_zero]

theorem dof_sum (F : Fin d → PS k 2 d) (v : Fin d → k) {α : Type} (s : Finset α) (f : α → PS k 1 d) :
    Dof F v (∑ a ∈ s, f a) = ∑ a ∈ s, Dof F v (f a) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← dofD_apply, map_sum]

end ReciprocityTheory.ChartRestriction.G.TB.GE
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeBilinearTermEqNegDoubleSum
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

theorem coeff_subst_killCompl {σ τ R : Type*} [CommRing R] [Finite τ] (e : σ ↪ τ) (f : MvPowerSeries τ R)
    (a : τ → MvPowerSeries σ R) (ha : ∀ t, a t = killCompl e (X t)) (x : σ →₀ ℕ) :
    coeff x (subst a f) = coeff (embDomain e x) f := by
  classical
  have haS : HasSubst a := by
    apply hasSubst_of_constantCoeff_zero
    intro t
    rw [ha, ← coeff_zero_eq_constantCoeff_apply, coeff_killCompl, Finsupp.embDomain_zero, coeff_zero_X]
  have hterm : ∀ n : τ →₀ ℕ, coeff n f • coeff x (n.prod fun s m => a s ^ m) =
      if n = embDomain e x then coeff n f else 0 := by
    intro n
    have hprod : (n.prod fun s m => a s ^ m) = killCompl e (monomial n (1 : R)) := by
      have h1 := monomial_eq (R := R) n (fun _ => 1)
      simp only [one_pow, Finsupp.prod, Finset.prod_const_one, one_smul] at h1
      rw [h1, map_prod]
      simp only [map_pow, ha, Finsupp.prod]
    rw [hprod, coeff_killCompl, coeff_monomial]
    by_cases hn : n = embDomain e x
    · subst hn
      simp
    · rw [if_neg (Ne.symm hn), if_neg hn, smul_zero]
  rw [coeff_subst haS, finsum_eq_single _ (embDomain e x)]
  · rw [hterm, if_pos rfl]
  · intro n hn
    rw [hterm, if_neg hn]

variable {k : Type} [CommRing k] {d : ℕ}

def eZ (d : ℕ) : Fin 1 × Fin d ↪ Fin 2 × Fin d := ⟨fun p => (1, p.2), fun p q h => by
  obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (Subsingleton.elim _ _) h.2⟩

def eXv (d : ℕ) : Fin 1 × Fin d ↪ Fin 2 × Fin d := ⟨fun p => (0, p.2), fun p q h => by
  obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (Subsingleton.elim _ _) h.2⟩

theorem coeff_ev_zero_left (h : PS k 2 d) (x : Fin 1 × Fin d →₀ ℕ) :
    coeff x (ev (n := 1) ![0, pt k d 0] h) = coeff (embDomain (eZ d) x) h := by
  have hnr : ∀ i : Fin d, ((0 : Fin 2), i) ∉ Set.range (eZ d) := by
    rintro i ⟨⟨c, j⟩, hc⟩
    have h10 : (1 : Fin 2) = 0 := congrArg Prod.fst hc
    exact absurd h10 (by decide)
  apply coeff_subst_killCompl (eZ d) h
  rintro ⟨b, i⟩
  fin_cases b
  · show (0 : PS k 1 d) = killCompl (eZ d) (X ((0 : Fin 2), i))
    ext m
    rw [coeff_killCompl, coeff_X, if_neg]
    · simp
    · intro hm
      have h1 := congrArg (fun g => g ((0 : Fin 2), i)) hm
      rw [Finsupp.embDomain_notin_range _ _ _ (hnr i), Finsupp.single_eq_same] at h1
      exact zero_ne_one h1
  · show X ((0 : Fin 1), i) = killCompl (eZ d) (X ((1 : Fin 2), i))
    exact (killCompl_X (e := eZ d) ((0 : Fin 1), i)).symm

theorem coeff_ev_zero_right (h : PS k 2 d) (x : Fin 1 × Fin d →₀ ℕ) :
    coeff x (ev (n := 1) ![pt k d 0, 0] h) = coeff (embDomain (eXv d) x) h := by
  have hnr : ∀ i : Fin d, ((1 : Fin 2), i) ∉ Set.range (eXv d) := by
    rintro i ⟨⟨c, j⟩, hc⟩
    have h10 : (0 : Fin 2) = 1 := congrArg Prod.fst hc
    exact absurd h10 (by decide)
  apply coeff_subst_killCompl (eXv d) h
  rintro ⟨b, i⟩
  fin_cases b
  · show X ((0 : Fin 1), i) = killCompl (eXv d) (X ((0 : Fin 2), i))
    exact (killCompl_X (e := eXv d) ((0 : Fin 1), i)).symm
  · show (0 : PS k 1 d) = killCompl (eXv d) (X ((1 : Fin 2), i))
    ext m
    rw [coeff_killCompl, coeff_X, if_neg]
    · simp
    · intro hm
      have h1 := congrArg (fun g => g ((1 : Fin 2), i)) hm
      rw [Finsupp.embDomain_notin_range _ _ _ (hnr i), Finsupp.single_eq_same] at h1
      exact zero_ne_one h1

def swE (d : ℕ) : Fin 2 × Fin d ↪ Fin 2 × Fin d := ⟨fun p => (Fin.rev p.1, p.2), fun p q h => by
  obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
  simp only [Prod.mk.injEq, Fin.rev_inj] at h
  exact Prod.ext h.1 h.2⟩

theorem ev_swap_eq (h : PS k 2 d) : ev (n := 2) ![pt k d 1, pt k d 0] h = rename (swE d) h := by
  rw [rename_eq_subst]
  show subst (fun p : Fin 2 × Fin d => (![pt k d 1, pt k d 0] : Fin 2 → Pt k 2 d) p.1 p.2) h = _
  congr 1
  funext p
  obtain ⟨a, b⟩ := p
  fin_cases a <;> rfl

theorem coeff_ev_swap (h : PS k 2 d) (x : Fin 2 × Fin d →₀ ℕ) :
    coeff (embDomain (swE d) x) (ev (n := 2) ![pt k d 1, pt k d 0] h) = coeff x h := by
  rw [ev_swap_eq, ← coeff_killCompl]
  rw [show killCompl (swE d) (rename (swE d) h) = h from DFunLike.congr_fun killCompl_comp_rename h]

theorem coeff_eq_zero_of_vanish_first_axis (h : PS k 2 d) (hax : ev (n := 1) ![0, pt k d 0] h = 0)
    (m : Fin 2 × Fin d →₀ ℕ) (hm : ∀ i, m (0, i) = 0) : coeff m h = 0 := by
  have hsupp : ↑m.support ⊆ Set.range (eZ d) := by
    rintro ⟨a, b⟩ hab
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hab
    fin_cases a
    · exact absurd (hm b) hab
    · exact ⟨(0, b), rfl⟩
  rw [← Finsupp.embDomain_comapDomain hsupp, ← coeff_ev_zero_left, hax]
  simp

theorem coeff_eq_zero_of_vanish_second_axis (h : PS k 2 d) (hax : ev (n := 1) ![pt k d 0, 0] h = 0)
    (m : Fin 2 × Fin d →₀ ℕ) (hm : ∀ i, m (1, i) = 0) : coeff m h = 0 := by
  have hsupp : ↑m.support ⊆ Set.range (eXv d) := by
    rintro ⟨a, b⟩ hab
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hab
    fin_cases a
    · exact ⟨(0, b), rfl⟩
    · exact absurd (hm b) hab
  rw [← Finsupp.embDomain_comapDomain hsupp, ← coeff_ev_zero_right, hax]
  simp

theorem two_le_degree {m : Fin 2 × Fin d →₀ ℕ} {i i' : Fin d} (h0 : m (0, i) ≠ 0) (h1 : m (1, i') ≠ 0) :
    2 ≤ m.degree := by
  classical
  have hne : ((0 : Fin 2), i) ≠ ((1 : Fin 2), i') := by simp
  have hs : ({((0 : Fin 2), i), ((1 : Fin 2), i')} : Finset (Fin 2 × Fin d)) ⊆ m.support := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simpa
  have h2 : m (0, i) + m (1, i') ≤ ∑ x ∈ m.support, m x := by
    rw [← Finset.sum_pair hne]
    exact Finset.sum_le_sum_of_subset hs
  have hdeg : m.degree = ∑ x ∈ m.support, m x := by
    unfold Finsupp.degree
    rfl
  omega

theorem coeff_eq_zero_of_axes (h : PS k 2 d) (h0 : ev (n := 1) ![0, pt k d 0] h = 0)
    (h1 : ev (n := 1) ![pt k d 0, 0] h = 0) (m : Fin 2 × Fin d →₀ ℕ) (hm : m.degree < 2) : coeff m h = 0 := by
  by_cases hA : ∀ i, m (0, i) = 0
  · exact coeff_eq_zero_of_vanish_first_axis h h0 m hA
  by_cases hB : ∀ i, m (1, i) = 0
  · exact coeff_eq_zero_of_vanish_second_axis h h1 m hB
  push_neg at hA hB
  obtain ⟨i, hi⟩ := hA
  obtain ⟨i', hi'⟩ := hB
  have := two_le_degree hi hi'
  omega

theorem gaugeBilinearTerm_eq_neg_double_sum (h : PS k 2 d) (i j : Fin d) :
    sg1 k h i j = -coeff (single ((0 : Fin 2), j) 1 + single ((1 : Fin 2), i) 1) h := by
  unfold sg1 sgOf
  rw [map_neg, coeff_ev_zero_right, Finsupp.embDomain_single, coeff_pderiv]
  have he : eXv d ((0 : Fin 1), j) = ((0 : Fin 2), j) := rfl
  rw [he]
  simp [Finsupp.single_apply]

theorem swE_swE (t : Fin 2 × Fin d) : swE d (swE d t) = t := by
  obtain ⟨a, b⟩ := t
  show (Fin.rev (Fin.rev a), b) = (a, b)
  rw [Fin.rev_rev]

theorem embDomain_swE_apply (m : Fin 2 × Fin d →₀ ℕ) (t : Fin 2 × Fin d) :
    embDomain (swE d) m (swE d t) = m t := by
  simp

theorem coeff_ev_swap' (h : PS k 2 d) (m : Fin 2 × Fin d →₀ ℕ) :
    coeff m (ev (n := 2) ![pt k d 1, pt k d 0] h) = coeff (embDomain (swE d) m) h := by
  have hm : embDomain (swE d) (embDomain (swE d) m) = m := by
    ext t
    conv_lhs => rw [← swE_swE t]
    rw [embDomain_swE_apply, embDomain_swE_apply]
  have := coeff_ev_swap h (embDomain (swE d) m)
  rw [hm] at this
  exact this

theorem coeff_swap_sub_low (h : PS k 2 d) (h0 : ev (n := 1) ![0, pt k d 0] h = 0)
    (h1 : ev (n := 1) ![pt k d 0, 0] h = 0) (m : Fin 2 × Fin d →₀ ℕ) (hm : m.degree < 2) :
    coeff m (ev (n := 2) ![pt k d 1, pt k d 0] h - h) = 0 := by
  have hdeg : (embDomain (swE d) m).degree = m.degree := by
    show ∑ i ∈ (embDomain (swE d) m).support, (embDomain (swE d) m) i = ∑ i ∈ m.support, m i
    rw [Finsupp.support_embDomain, Finset.sum_map]
    exact Finset.sum_congr rfl (fun x _ => embDomain_swE_apply m x)
  rw [map_sub, coeff_ev_swap', coeff_eq_zero_of_axes h h0 h1 _ (by rw [hdeg]; exact hm),
    coeff_eq_zero_of_axes h h0 h1 m hm, sub_zero]

section Exp

variable [Algebra ℚ k]

private theorem coeff_mul_eq_zero_of_order_two_of_degree_le_two {n : ℕ} (f g : PS k n d)
    (hf : ∀ m : Fin n × Fin d →₀ ℕ, m.degree < 2 → coeff m f = 0)
    (hg : ∀ m : Fin n × Fin d →₀ ℕ, m.degree < 2 → coeff m g = 0)
    (m : Fin n × Fin d →₀ ℕ) (hm : m.degree ≤ 2) : coeff m (f * g) = 0 := by
  classical
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hdeg : p.1.degree + p.2.degree = m.degree := by rw [← hp, map_add (f := _)]
  by_cases h1 : p.1.degree < 2
  · rw [hf _ h1, zero_mul]
  · rw [hg _ (by omega), mul_zero]

private theorem coeff_mul_eq_zero_of_left_vanishes_degree_le_two {n : ℕ} (F g : PS k n d)
    (hF : ∀ m : Fin n × Fin d →₀ ℕ, m.degree ≤ 2 → coeff m F = 0)
    (m : Fin n × Fin d →₀ ℕ) (hm : m.degree ≤ 2) : coeff m (F * g) = 0 := by
  classical
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hdeg : p.1.degree + p.2.degree = m.degree := by rw [← hp, map_add (f := _)]
  rw [hF _ (by omega), zero_mul]

theorem coeff_expS_two {n : ℕ} (f : PS k n d) (hf : ∀ m : Fin n × Fin d →₀ ℕ, m.degree < 2 → coeff m f = 0)
    (m : Fin n × Fin d →₀ ℕ) (hm : m.degree = 2) : coeff m (FB.expS k f) = coeff m f := by
  classical
  have haS : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero
    (by rw [← coeff_zero_eq_constantCoeff_apply]; exact hf 0 (by simp))
  show coeff m (PowerSeries.subst f (PowerSeries.exp k)) = _
  rw [PowerSeries.coeff_subst haS, finsum_eq_single _ 1]
  · simp [PowerSeries.coeff_exp]
  · intro j hj
    rcases j with _ | _ | j
    · have hm0 : m ≠ 0 := by
        rintro rfl
        simp at hm
      simp [hm0, coeff_one]
    · exact absurd rfl hj
    · rw [show f ^ (j + 2) = f * f * f ^ j by ring,
        coeff_mul_eq_zero_of_left_vanishes_degree_le_two (f * f) _ (fun q hq => coeff_mul_eq_zero_of_order_two_of_degree_le_two f f hf hf q hq) m hm.le,
        smul_zero]

end Exp

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.TaylorMul
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.TM

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped ContDiff Topology

variable {g : ℕ}

theorem mD_local {f h : (Fin g → ℂ) → ℂ} (hfh : f =ᶠ[𝓝 0] h) (s : Multiset (Fin g → ℂ)) :
    mD f 0 s = mD h 0 s := by
  unfold mD lD
  rw [((hfh.iteratedFDeriv ℂ _).eq_of_nhds)]

theorem tay_local {f h : (Fin g → ℂ) → ℂ} (hfh : f =ᶠ[𝓝 0] h) (s : Multiset (Fin g → ℂ)) : tay f s = tay h s := by
  ext n
  show mD f 0 (dirs n + s) / fct n = mD h 0 (dirs n + s) / fct n
  rw [mD_local hfh]

theorem mD_add {f h : (Fin g → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (hh : ContDiffAt ℂ ω h 0)
    (s : Multiset (Fin g → ℂ)) : mD (f + h) 0 s = mD f 0 s + mD h 0 s := by
  unfold mD lD
  rw [iteratedFDeriv_add_apply (hf.of_le le_top) (hh.of_le le_top)]
  rfl

theorem tay_add {f h : (Fin g → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (hh : ContDiffAt ℂ ω h 0)
    (s : Multiset (Fin g → ℂ)) : tay (f + h) s = tay f s + tay h s := by
  ext n
  rw [map_add (f := _)]
  show mD (f + h) 0 (dirs n + s) / fct n = mD f 0 (dirs n + s) / fct n + mD h 0 (dirs n + s) / fct n
  rw [mD_add hf hh, add_div]

theorem mD_zero (θ : (Fin g → ℂ) → ℂ) : mD θ 0 0 = θ 0 := by
  have key : ∀ l : List (Fin g → ℂ), l = [] →
      iteratedFDeriv ℂ l.length θ 0 (fun i => l.get i) = θ 0 := by
    rintro l rfl
    simp
  exact key _ (Multiset.toList_eq_nil.2 rfl)

theorem mD_const (c : ℂ) (s : Multiset (Fin g → ℂ)) :
    mD (fun _ : Fin g → ℂ => c) 0 s = if s = 0 then c else 0 := by
  by_cases hs : s = 0
  · subst hs
    have key : ∀ l : List (Fin g → ℂ), l = [] →
        iteratedFDeriv ℂ l.length (fun _ : Fin g → ℂ => c) 0 (fun i => l.get i) = c := by
      rintro l rfl
      simp
    rw [if_pos rfl]
    exact key _ (Multiset.toList_eq_nil.2 rfl)
  · have hlen : s.toList.length ≠ 0 := by
      rw [Multiset.length_toList]
      exact fun h0 => hs (Multiset.card_eq_zero.1 h0)
    unfold mD lD
    rw [iteratedFDeriv_const_of_ne hlen, if_neg hs]
    rfl

theorem tay_const (c : ℂ) : tay (g := g) (fun _ => c) 0 = C c := by
  ext n
  rw [MvPowerSeries.coeff_C]
  show mD (fun _ => c) 0 (dirs n + 0) / fct n = _
  rw [add_zero, mD_const]
  by_cases hn : n = 0
  · subst hn
    simp [dirs, fct]
  · have hd : dirs n ≠ 0 := by
      intro h0
      apply hn
      have h1 : Finsupp.toMultiset n = 0 := by simpa [dirs] using h0
      simpa using congrArg Multiset.toFinsupp h1
    rw [if_neg hd, if_neg hn, zero_div]

theorem mD_cons_deriv {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) (v : Fin g → ℂ) (t : Multiset (Fin g → ℂ)) :
    mD θ 0 (v ::ₘ t) = mD (fun y => fderiv ℂ θ y v) 0 t := by
  have ht : ((t.toList : List (Fin g → ℂ)) : Multiset (Fin g → ℂ)) = t := Multiset.coe_toList t
  have hperm : (v ::ₘ t) = ((t.toList ++ [v] : List (Fin g → ℂ)) : Multiset (Fin g → ℂ)) := by
    conv_lhs => rw [← ht]
    rw [Multiset.cons_coe, Multiset.coe_eq_coe]
    exact (List.perm_append_singleton v t.toList).symm
  have hlen : (t.toList ++ [v]).length = t.toList.length + 1 := by simp
  rw [hperm, mD_coe hθ, lD_eq θ 0 (t.toList ++ [v]) hlen, iteratedFDeriv_succ_apply_right]
  have hf : ContDiffAt ℂ ω (fderiv ℂ θ) 0 := hθ.fderiv_right (by simp)
  have hcomp : (fun y => fderiv ℂ θ y v) = (ContinuousLinearMap.apply ℂ ℂ v) ∘ (fderiv ℂ θ) := rfl
  unfold mD lD
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_left _ hf le_top]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousLinearMap.apply_apply]
  congr 1
  · congr 1
    funext i
    simp only [Fin.init]
    exact List.getElem_append_left i.isLt
  · simp

theorem deriv_analytic {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) (v : Fin g → ℂ) :
    ContDiffAt ℂ ω (fun y => fderiv ℂ θ y v) 0 :=
  (hθ.fderiv_right (by simp)).clm_apply contDiffAt_const

theorem pderiv_tay {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) (j : Fin g) :
    MvPowerSeries.pderiv ((0 : Fin 1), j) (tay θ 0) =
      tay (fun y => fderiv ℂ θ y (Pi.single j 1)) 0 := by
  ext n
  rw [MvPowerSeries.coeff_pderiv]
  show mD θ 0 (dirs (n + Finsupp.single ((0 : Fin 1), j) 1) + 0) / fct (n + Finsupp.single ((0 : Fin 1), j) 1) * ((n ((0 : Fin 1), j) : ℂ) + 1) =
    mD (fun y => fderiv ℂ θ y (Pi.single j 1)) 0 (dirs n + 0) / fct n
  have hd : dirs (n + Finsupp.single ((0 : Fin 1), j) 1) = (Pi.single j 1 : Fin g → ℂ) ::ₘ dirs n := by
    unfold dirs
    rw [Finsupp.toMultiset_add, Finsupp.toMultiset_single, one_nsmul, Multiset.map_add (f := _),
      Multiset.map_singleton, add_comm, Multiset.singleton_add]
  have hf : fct (n + Finsupp.single ((0 : Fin 1), j) 1) = fct n * ((n ((0 : Fin 1), j) : ℂ) + 1) := by
    unfold fct
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ ((0 : Fin 1), j)),
      ← Finset.mul_prod_erase Finset.univ (fun p => ((n p).factorial : ℂ)) (Finset.mem_univ ((0 : Fin 1), j))]
    have hrest : ∏ x ∈ Finset.univ.erase ((0 : Fin 1), j), (((n + Finsupp.single ((0 : Fin 1), j) 1 : Fin 1 × Fin g →₀ ℕ) x).factorial : ℂ) =
        ∏ x ∈ Finset.univ.erase ((0 : Fin 1), j), ((n x).factorial : ℂ) := by
      refine Finset.prod_congr rfl fun x hx => ?_
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hx), add_zero]
    rw [hrest, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
    push_cast
    ring
  have hne : ((n ((0 : Fin 1), j) : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero _
  rw [add_zero, add_zero, hd, mD_cons_deriv hθ, hf, ← div_div, div_mul_cancel₀ _ hne]

theorem deriv_mul_ev {f h : (Fin g → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (hh : ContDiffAt ℂ ω h 0) (v : Fin g → ℂ) :
    (fun y => fderiv ℂ (f * h) y v) =ᶠ[𝓝 0]
      (fun y => fderiv ℂ f y v) * h + f * (fun y => fderiv ℂ h y v) := by
  filter_upwards [hf.eventually (by simp), hh.eventually (by simp)] with y hy1 hy2
  rw [fderiv_mul (hy1.differentiableAt (by simp)) (hy2.differentiableAt (by simp))]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    Pi.add_apply, Pi.mul_apply]
  ring

theorem taylor_mul_coeff_low_degree (N : ℕ) : ∀ (f h : (Fin g → ℂ) → ℂ), ContDiffAt ℂ ω f 0 → ContDiffAt ℂ ω h 0 →
    ∀ n : Fin 1 × Fin g →₀ ℕ, n.degree < N → coeff n (tay (f * h) 0) = coeff n (tay f 0 * tay h 0) := by
  induction N with
  | zero =>
    intro f h _ _ n hn
    exact absurd hn (Nat.not_lt_zero _)
  | succ N ih =>
    intro f h hf hh n hn
    by_cases h0 : n = 0
    · subst h0
      simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul]
      simp only [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
      show mD (f * h) 0 (dirs 0 + 0) / fct 0 = (mD f 0 (dirs 0 + 0) / fct 0) * (mD h 0 (dirs 0 + 0) / fct 0)
      simp [dirs, fct, mD_zero]
    · obtain ⟨x, hx⟩ : ∃ x, n x ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact h0 (Finsupp.ext hc)
      obtain ⟨i, j⟩ := x
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      obtain ⟨m, hm⟩ : ∃ m, m = n - Finsupp.single ((0 : Fin 1), j) 1 := ⟨_, rfl⟩
      have hnm : n = m + Finsupp.single ((0 : Fin 1), j) 1 := by
        rw [hm]
        exact (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hx))).symm
      have hmdeg : m.degree < N := by
        have h1 : n.degree = m.degree + 1 := by
          rw [hnm, map_add (f := _), Finsupp.degree_single]
        omega
      have key : ∀ F : MvPowerSeries (Fin 1 × Fin g) ℂ,
          coeff m (MvPowerSeries.pderiv ((0 : Fin 1), j) F) =
            coeff n F * ((m ((0 : Fin 1), j) : ℂ) + 1) := fun F => by
        rw [MvPowerSeries.coeff_pderiv, ← hnm]
      have hc : ((m ((0 : Fin 1), j) : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero _
      apply mul_right_cancel₀ hc
      rw [← key, ← key]
      have hfh : ContDiffAt ℂ ω (f * h) 0 := hf.mul hh
      have hf' := deriv_analytic hf (Pi.single j 1)
      have hh' := deriv_analytic hh (Pi.single j 1)
      rw [pderiv_tay hfh, tay_local (deriv_mul_ev hf hh (Pi.single j 1)), tay_add (f := (fun y => fderiv ℂ f y (Pi.single j 1)) * h)
        (h := f * fun y => fderiv ℂ h y (Pi.single j 1)) (hf'.mul hh) (hf.mul hh'),
        map_add, Derivation.leibniz, pderiv_tay hf, pderiv_tay hh, ih _ _ hf' hh m hmdeg,
        ih _ _ hf hh' m hmdeg, smul_eq_mul, smul_eq_mul, map_add, mul_comm (tay h 0)]
      ring

theorem taylor_multiplication : TaylorMulSt := by
  refine ⟨fun g f h hf hh => ⟨?_, tay_add hf hh 0⟩, fun g c => tay_const c,
    fun g f h hfh => tay_local hfh 0⟩
  ext n
  exact taylor_mul_coeff_low_degree (n.degree + 1) f h hf hh n (Nat.lt_succ_self _)

end ReciprocityTheory.ChartRestriction.G.PullbackSections.TM
end
end

