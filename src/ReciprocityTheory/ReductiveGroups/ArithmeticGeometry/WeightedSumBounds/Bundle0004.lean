module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0003
public import ReciprocityTheory.DualLattices.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtRescaleGood

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.CoeffLgPcurveTop
section
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb

open MvPowerSeries ReciprocityTheory.PGsh

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

theorem coeff_lg_pcurve (G : LogFGL v d) {p : ℕ} (hp : p ≠ 0)
    {γ : Fin d → Fin d → PowerSeries C} (hγ : ∀ a, IsCurve v (γ a)) (x : ℕ → Fin d → C) (n : ℕ)
    (hx : ∀ s < n, ∀ b, IsIntV v (x s b)) (a : Fin d) (m : ℕ) :
    PowerSeries.coeff m (G.lgCurve (pcurve G p γ x n) a) = ∑ s ∈ Finset.range n, ∑ b,
      if p ^ s ∣ m then x s b ^ (m / p ^ s) * PowerSeries.coeff (m / p ^ s) (G.lgCurve (γ b) a)
      else 0 := by
  have hlog : G.lgCurve (pcurve G p γ x n) a =
      ∑ s ∈ Finset.range n, ∑ b, PowerSeries.expand (p ^ s) (pow_ne_zero s hp)
        (PowerSeries.rescale (x s b) (G.lgCurve (γ b) a)) := by
    induction n with
    | zero => simp [pcurve, lgCurve_zero]
    | succ n ih =>
      have hx' : ∀ s < n, ∀ b, IsIntV v (x s b) := fun s hs b => hx s (by omega) b
      have hrescale : ∀ b, IsCurve v (rescaleCurve (x n b) (γ b)) := fun b =>
        isCurve_rescale (hx n (Nat.lt_succ_self n) b) (hγ b)
      have hexpand : ∀ b, IsCurve v (expC (p ^ n) (rescaleCurve (x n b) (γ b))) := fun b =>
        isCurve_expC (pow_ne_zero n hp) (hrescale b)
      rw [pcurve, lgCurve_add G (fun b => (isCurve_pcurve G hp hγ x n hx' b).1)
        (fun b => (isCurve_sumF G _ hexpand b).1), ih hx', lgCurve_sumF G _ hexpand,
        Finset.sum_range_succ]
      congr 1
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [lgCurve_expC G (pow_ne_zero n hp) (fun c => (hrescale b c).1),
        lgCurve_rescale G _ (fun c => (hγ b c).1)]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hlog, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [coeff_expand_rescale]

theorem lg_agree (G : LogFGL v d) {p : ℕ} (hp : p.Prime) {γ : Fin d → Fin d → PowerSeries C}
    (hγ : ∀ a, IsCurve v (γ a)) (hγt : ∀ b, G.IsPTypical p (γ b)) (hdet : v (tmat γ).det = 0)
    (ga : Fin d → PowerSeries C) (hga : G.IsPTypical p ga) (n : ℕ)
    (hx : ∀ s < n, ∀ b, IsIntV v (ptx G p γ ga s b)) :
    ∀ a, ∀ j < p ^ n, PowerSeries.coeff j (G.lgCurve ga a) =
      PowerSeries.coeff j (G.lgCurve (pcurve G p γ (ptx G p γ ga) n) a) := by
  intro a j hj
  rw [coeff_lg_pcurve G hp.ne_zero hγ _ n hx a j]
  by_cases hpow : ∃ m, j = p ^ m
  · obtain ⟨m, rfl⟩ := hpow
    have hmn : m < n := by
      by_contra h
      push_neg at h
      exact absurd hj (not_lt.mpr (Nat.pow_le_pow_right hp.pos h))
    have hrel := congrFun (ptx_rel G p hγ hdet ga m) a
    change G.lc p ga m a = _
    rw [hrel]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.sum_range_add_sum_Ico _ (show m + 1 ≤ n by omega)]
    have hzero : ∑ s ∈ Finset.Ico (m + 1) n, ∑ b, (if p ^ s ∣ p ^ m then
        ptx G p γ ga s b ^ (p ^ m / p ^ s) * PowerSeries.coeff (p ^ m / p ^ s) (G.lgCurve (γ b) a)
        else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro s hs
      have hs' : m < s := by
        rw [Finset.mem_Ico] at hs
        omega
      apply Finset.sum_eq_zero
      intro b _
      rw [if_neg]
      intro hd
      have hle : s ≤ m := by
        first
        | exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hd
        | exact (Nat.pow_dvd_pow_iff_le_right' ).mp hd
      omega
    rw [hzero, add_zero]
    apply Finset.sum_congr rfl
    intro s hs
    have hsm : s ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    apply Finset.sum_congr rfl
    intro b _
    rw [if_pos (pow_dvd_pow p hsm), Nat.pow_div hsm hp.pos]
    rfl
  · push_neg at hpow
    rw [hga a j hpow]
    symm
    apply Finset.sum_eq_zero
    intro s _
    apply Finset.sum_eq_zero
    intro b _
    split_ifs with hd
    · obtain ⟨k, hk⟩ := hd
      have hk' : j / p ^ s = k := by
        rw [hk, Nat.mul_div_cancel_left _ (pow_pos hp.pos s)]
      have hnp : ∀ m', k ≠ p ^ m' := by
        intro m' hm'
        apply hpow (s + m')
        rw [hk, hm', pow_add]
      rw [hk', hγt b a k hnp, mul_zero]
    · rfl

theorem coeff_lg_pcurve_top (G : LogFGL v d) {p : ℕ} (hp : p.Prime)
    {γ : Fin d → Fin d → PowerSeries C} (hγ : ∀ a, IsCurve v (γ a)) (x : ℕ → Fin d → C) (n : ℕ)
    (hx : ∀ s < n, ∀ b, IsIntV v (x s b)) (a : Fin d) :
    PowerSeries.coeff (p ^ n) (G.lgCurve (pcurve G p γ x n) a) =
      (∑ s ∈ Finset.range n, ∑ b, (x s b) ^ (p ^ (n - s)) • G.lc p (γ b) (n - s)) a := by
  rw [coeff_lg_pcurve G hp.ne_zero hγ x n hx a (p ^ n)]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro s hs
  have hsn : s ≤ n := (Finset.mem_range.mp hs).le
  apply Finset.sum_congr rfl
  intro b _
  rw [if_pos (pow_dvd_pow p hsn), Nat.pow_div hsn hp.pos]
  rfl

private theorem exists_subring_mem_iff_isIntV : ∃ S : Subring C, ∀ x, x ∈ S ↔ IsIntV v x :=
  ⟨{ carrier := {x | 0 ≤ v x}
     mul_mem' := fun {a b} ha hb => by
       simp only [Set.mem_setOf_eq, AddValuation.map_mul] at *
       exact add_nonneg ha hb
     one_mem' := by simp
     add_mem' := fun {a b} ha hb => le_trans (le_min ha hb) (AddValuation.map_add v a b)
     zero_mem' := by simp
     neg_mem' := fun {a} ha => by simpa [AddValuation.map_neg] using ha }, fun _ => Iff.rfl⟩

theorem ptx_int (G : LogFGL v d) {p : ℕ} (hp : p.Prime) {γ : Fin d → Fin d → PowerSeries C}
    (hγ : ∀ a, IsCurve v (γ a)) (hγt : ∀ b, G.IsPTypical p (γ b)) (hdet : v (tmat γ).det = 0)
    (ga : Fin d → PowerSeries C) (hgaC : IsCurve v ga) (hga : G.IsPTypical p ga) :
    ∀ n b, IsIntV v (ptx G p γ ga n b) := by
  obtain ⟨S, hS⟩ := exists_subring_mem_iff_isIntV (v := v)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro b
    have hx : ∀ s < n, ∀ b, IsIntV v (ptx G p γ ga s b) := fun s hs b => ih s hs b
    have hagree := lg_agree G hp hγ hγt hdet ga hga n hx
    have hα : ∀ c, PowerSeries.constantCoeff (ga c) = 0 := fun c => (hgaC c).1
    have hpcC := isCurve_pcurve G hp.ne_zero hγ (ptx G p γ ga) n hx
    have hβ : ∀ c, PowerSeries.constantCoeff (pcurve G p γ (ptx G p γ ga) n c) = 0 :=
      fun c => (hpcC c).1
    have hw : ∀ c, IsIntV v (ptw G p γ ga n c) := by
      intro c
      have h1 := coeff_lgCurve_sub_eq G hα hβ (p ^ n) hagree c
      have h2 := coeff_lg_pcurve_top G hp hγ (ptx G p γ ga) n hx c
      have e : ptw G p γ ga n c =
          PowerSeries.coeff (p ^ n) (ga c - pcurve G p γ (ptx G p γ ga) n c) := by
        rw [← h1, map_sub, h2]
        simp only [ptw, Pi.sub_apply]
        rfl
      rw [e, ← hS, map_sub]
      exact S.sub_mem ((hS _).2 ((hgaC c).2 _)) ((hS _).2 ((hpcC c).2 _))
    rw [ptx_eq]
    exact isIntV_vecMul_inv hγ hdet hw b

private theorem lgCurve_const_zero (G : LogFGL v d) (a : Fin d) :
    G.lgCurve (fun _ => (0 : PowerSeries C)) a = 0 := by
  have h0 : HasSubst (fun _ : Fin d => (0 : PowerSeries C)) := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun _ => by simp)
  ext j
  rw [map_zero]
  change MvPowerSeries.coeff (Finsupp.single () j) (subst _ (G.lg a)) = 0
  rw [MvPowerSeries.coeff_subst h0]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e
  by_cases he : e = 0
  · subst he
    rw [coeff_zero_eq_constantCoeff_apply, G.lg_const a, zero_smul]
  · obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact he (Finsupp.ext hcon)
    rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (by simp [hs]),
      map_zero, smul_zero]

private theorem lc_zero_eq_tangent_of_constantCoeff_eq_zero (G : LogFGL v d) (p : ℕ) (ga : Fin d → PowerSeries C)
    (h0 : ∀ b, PowerSeries.constantCoeff (ga b) = 0) : G.lc p ga 0 = tangent ga := by
  funext a
  have hk : ∀ b, (PowerSeries.X : PowerSeries C) ^ 1 ∣ ga b - (fun _ => (0 : PowerSeries C)) b := by
    intro b
    show (PowerSeries.X : PowerSeries C) ^ 1 ∣ ga b - 0
    rw [pow_one, sub_zero]
    exact PowerSeries.X_dvd_iff.mpr (h0 b)
  have h1 := lgCurve_sub_dvd (β := fun _ => (0 : PowerSeries C)) G h0 (fun _ => by simp) 1 hk a
  simp only [lgCurve_const_zero, sub_zero] at h1
  have h2 := PowerSeries.X_pow_dvd_iff.mp h1 1 (by norm_num)
  rw [map_sub, sub_eq_zero] at h2
  show PowerSeries.coeff (p ^ 0) (G.lgCurve ga a) = PowerSeries.coeff 1 (ga a)
  rw [pow_zero, h2]

theorem ptx_type {h : ℕ} (ty : Fin d → ZMod h) (G : LogFGL v d) {p : ℕ} (hp : p.Prime)
    {γ : Fin d → Fin d → PowerSeries C} (hγ : ∀ a, IsCurve v (γ a)) (hdet : v (tmat γ).det = 0)
    (hγty : ∀ b, G.IsOfType p ty (ty b) (γ b)) (ga : Fin d → PowerSeries C) (i : ZMod h)
    (hga : G.IsOfType p ty i ga) :
    ∀ n b, ptx G p γ ga n b ≠ 0 → ty b = i + n := by
  have ht : ∀ b c, ty c ≠ ty b → tangent (γ b) c = 0 := by
    intro b c hc
    have h0 := (hγty b).2 0 c (by simpa using hc)
    rwa [lc_zero_eq_tangent_of_constantCoeff_eq_zero G p (γ b) (fun c' => (hγ b c').1)] at h0
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hw : ∀ c, ty c ≠ i + n → Matrix.vecMul (ptx G p γ ga n) (tmat γ) c = 0 := by
      intro c hc
      rw [ptx_eq, vecMul_inv_tmat hdet]
      simp only [ptw, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [hga.2 n c hc, zero_sub, neg_eq_zero]
      apply Finset.sum_eq_zero
      intro s hs
      have hsn : s < n := Finset.mem_range.mp hs
      apply Finset.sum_eq_zero
      intro b _
      by_cases hx0 : ptx G p γ ga s b = 0
      · rw [hx0, zero_pow (pow_ne_zero _ hp.ne_zero), zero_mul]
      · have htb := ih s hsn b hx0
        have hlc : G.lc p (γ b) (n - s) c = 0 := by
          apply (hγty b).2 (n - s) c
          rw [htb, Nat.cast_sub hsn.le]
          intro h'
          apply hc
          rw [h']
          ring
        rw [hlc, mul_zero]
    intro b hb
    by_contra hne
    exact hb (vecMul_tmat_support ty hdet ht (ptx G p γ ga n) (i + n) hw b hne)

end

end ReciprocityTheory.ChartRestriction.G.Sh.PTb
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtBasisMapGood
section
namespace ReciprocityTheory.ChartRestriction.G.Sh

open MvPowerSeries ReciprocityTheory.PGsh

open Classical

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

def ptOn (a : Fin d) (ga : Fin d → PowerSeries C) : Fin d → MvPowerSeries (Fin d) C :=
  fun b => PowerSeries.subst (X a : MvPowerSeries (Fin d) C) (ga b)

def ptBasisMap (G : LogFGL v d) (γ : Fin d → Fin d → PowerSeries C) :
    Fin d → MvPowerSeries (Fin d) C :=
  ptSumL G (List.ofFn fun a => ptOn a (γ a))

theorem ptOn_hs (a : Fin d) : HasSubst (fun _ : Unit => (X a : MvPowerSeries (Fin d) C)) := MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X a

theorem ptOn_good (a : Fin d) {ga : Fin d → PowerSeries C} (h : IsCurve v ga) :
    PTGood v (ptOn a ga) := by
  intro b
  refine ⟨PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X a) _ (h b).1, ?_⟩
  show ∀ α, coeff α (ptOn a ga b) ∈ ptIntSub v
  intro e
  rw [ptOn, PowerSeries.coeff_subst_single]
  split_ifs
  · exact (ptIsIntV_iff _).mp ((h b).2 _)
  · exact (ptIntSub v).zero_mem

theorem ptOn_lin (a : Fin d) {ga : Fin d → PowerSeries C} (h : IsCurve v ga) (b s : Fin d) :
    coeff (Finsupp.single s 1) (ptOn a ga b) = if s = a then tangent ga b else 0 := by
  rw [ptOn, PowerSeries.coeff_subst_single]
  by_cases hs : s = a
  · subst hs
    simp [tangent]
  · simp [Finsupp.single_apply, hs, Ne.symm hs]

theorem ptOn_lg (G : LogFGL v d) (a : Fin d) {ga : Fin d → PowerSeries C} (h : IsCurve v ga)
    (b : Fin d) :
    subst (ptOn a ga) (G.lg b) = PowerSeries.subst (X a : MvPowerSeries (Fin d) C) (G.lgCurve ga b) := by
  have hga : HasSubst ga := MvPowerSeries.hasSubst_of_constantCoeff_zero fun c => (h c).1
  show subst (ptOn a ga) (G.lg b) = PowerSeries.subst (X a : MvPowerSeries (Fin d) C) (subst ga (G.lg b))
  rw [PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply hga (ptOn_hs a)]
  rfl

theorem ptBasisMap_good (G : LogFGL v d) {γ : Fin d → Fin d → PowerSeries C}
    (hγ : ∀ a, IsCurve v (γ a)) : PTGood v (ptBasisMap G γ) := by
  unfold ptBasisMap
  refine ptSumL_good G _ fun x hx => ?_
  obtain ⟨a, rfl⟩ : ∃ a, ptOn a (γ a) = x := by simpa [List.mem_ofFn] using hx
  exact ptOn_good a (hγ a)

theorem ptBasisMap_lin (G : LogFGL v d) {γ : Fin d → Fin d → PowerSeries C}
    (hγ : ∀ a, IsCurve v (γ a)) (b s : Fin d) :
    coeff (Finsupp.single s 1) (ptBasisMap G γ b) = tangent (γ s) b := by
  have hc : ∀ x ∈ List.ofFn (fun a => ptOn a (γ a)), ∀ c, constantCoeff (x c) = 0 := by
    intro x hx c
    obtain ⟨a, rfl⟩ : ∃ a, ptOn a (γ a) = x := by simpa [List.mem_ofFn] using hx
    exact (ptOn_good a (hγ a) c).1
  have hsum (l : List (Fin d → MvPowerSeries (Fin d) C))
      (h : ∀ x ∈ l, ∀ c, constantCoeff (x c) = 0) :
      coeff (Finsupp.single s 1) (ptSumL G l b) =
        (l.map fun x => coeff (Finsupp.single s 1) (x b)).sum := by
    induction l with
    | nil => simp [ptSumL]
    | cons x l ih =>
      have hl : ∀ y ∈ l, ∀ c, constantCoeff (y c) = 0 :=
        fun y hy => h y (List.mem_cons_of_mem x hy)
      rw [ptSumL, ptAdd_lin G (h x List.mem_cons_self) (ptSumL_const G l hl), ih hl,
        List.map_cons, List.sum_cons]
  rw [ptBasisMap, hsum _ hc, List.map_ofFn, List.sum_ofFn]
  simp [Function.comp_def, ptOn_lin _ (hγ _)]

theorem ptBasisMap_lg (G : LogFGL v d) {γ : Fin d → Fin d → PowerSeries C}
    (hγ : ∀ a, IsCurve v (γ a)) (b : Fin d) :
    subst (ptBasisMap G γ) (G.lg b) =
      ∑ a, PowerSeries.subst (X a : MvPowerSeries (Fin d) C) (G.lgCurve (γ a) b) := by
  have hc : ∀ x ∈ List.ofFn (fun a => ptOn a (γ a)), ∀ c, constantCoeff (x c) = 0 := by
    intro x hx c
    obtain ⟨a, rfl⟩ : ∃ a, ptOn a (γ a) = x := by simpa [List.mem_ofFn] using hx
    exact (ptOn_good a (hγ a) c).1
  have hsum (l : List (Fin d → MvPowerSeries (Fin d) C))
      (h : ∀ x ∈ l, ∀ c, constantCoeff (x c) = 0) :
      subst (ptSumL G l) (G.lg b) = (l.map fun x => subst x (G.lg b)).sum := by
    induction l with
    | nil =>
      simp only [ptSumL, List.map_nil, List.sum_nil]
      exact subst_zero_of_constantCoeff_zero (G.lg_const b)
    | cons x l ih =>
      have hl : ∀ y ∈ l, ∀ c, constantCoeff (y c) = 0 :=
        fun y hy => h y (List.mem_cons_of_mem x hy)
      rw [ptSumL, ptAdd_lg G (h x List.mem_cons_self) (ptSumL_const G l hl), ih hl,
        List.map_cons, List.sum_cons]
  rw [ptBasisMap, hsum _ hc, List.map_ofFn, List.sum_ofFn]
  exact Finset.sum_congr rfl fun a _ => ptOn_lg G a (hγ a) b

theorem pt_inv_int {M : Matrix (Fin d) (Fin d) C} (hM : ∀ i j, M i j ∈ ptIntSub v)
    (hdet : v M.det = 0) : IsUnit M.det ∧ ∀ i j, M⁻¹ i j ∈ ptIntSub v := by
  have hdet0 : M.det ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hdet
    exact WithTop.top_ne_coe hdet
  refine ⟨isUnit_iff_ne_zero.mpr hdet0, fun i j => ?_⟩
  obtain ⟨M', rfl⟩ : ∃ M' : Matrix (Fin d) (Fin d) (ptIntSub v), M = M'.map (ptIntSub v).subtype :=
    ⟨fun i j => ⟨M i j, hM i j⟩, by ext i j; rfl⟩
  have hadj : (M'.map (ptIntSub v).subtype).adjugate i j = (ptIntSub v).subtype (M'.adjugate i j) :=
    (congrArg (fun N : Matrix (Fin d) (Fin d) C => N i j) (RingHom.map_adjugate (ptIntSub v).subtype M')).symm
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, hadj, Ring.inverse_eq_inv']
  refine (ptIntSub v).mul_mem ?_ (M'.adjugate i j).2
  show 0 ≤ v (M'.map (ptIntSub v).subtype).det⁻¹
  rw [AddValuation.map_inv, hdet, neg_zero]

theorem ptBasisMap_inv (G : LogFGL v d) {γ : Fin d → Fin d → PowerSeries C}
    (hγ : ∀ a, IsCurve v (γ a)) (hdet : v (Matrix.det (Matrix.of fun a b => tangent (γ a) b)) = 0) :
    ∃ Ψ : Fin d → MvPowerSeries (Fin d) C, (∀ a, MvIsInt v (Ψ a)) ∧
      (∀ a, constantCoeff (Ψ a) = 0) ∧
      (∀ a, subst Ψ (ptBasisMap G γ a) = X a) ∧ (∀ a, subst (ptBasisMap G γ) (Ψ a) = X a) := by
  have hΦ : PTGood v (ptBasisMap G γ) := ptBasisMap_good G hγ
  have hΦs : HasSubst (ptBasisMap G γ) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => (hΦ s).1
  let M : Matrix (Fin d) (Fin d) C := Matrix.of fun a b => tangent (γ a) b
  have hMint : ∀ i j, M i j ∈ ptIntSub v := fun i j => (ptIsIntV_iff _).mp (((hγ i) j).2 1)
  obtain ⟨hdu, hNint⟩ := pt_inv_int hMint hdet
  have hNM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hdu
  have hMN : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hdu
  let K : Fin d → MvPowerSeries (Fin d) C := fun b => ptBasisMap G γ b - ∑ a, M a b • X a
  have hlin : ∀ b s, coeff (Finsupp.single s 1) (ptBasisMap G γ b) = M s b :=
    fun b s => ptBasisMap_lin G hγ b s
  have hlow : ∀ b (α : Fin d →₀ ℕ), α.degree ≤ 1 → coeff α (K b) = 0 :=
    fun b => pt_low_of_lin (hΦ b).1 (fun a => M a b) (hlin b)
  have hK : ∀ b (α : Fin d →₀ ℕ), coeff α (K b) ≠ 0 → 2 ≤ α.degree ∨
      ∀ x y : Fin d → MvPowerSeries (Fin d) C, PTGood v x → PTGood v y → ∀ s ∈ α.support, x s = y s := by
    intro b α h
    left
    by_contra h'
    push_neg at h'
    exact h (hlow b α (by omega))
  have hKi : ∀ b, K b ∈ ptIntSer v (Fin d) := fun b =>
    Subring.sub_mem _ (hΦ b).2 (Subring.sum_mem _ fun a _ => ptIntSer_smul (hMint a b) (ptIntSer_X a))
  have hK0 : ∀ b, constantCoeff (K b) = 0 := fun b => by simp [K, (hΦ b).1]
  have hA0 : ∀ x : Fin d → MvPowerSeries (Fin d) C, PTGood v x → ∀ s, constantCoeff (x s) = 0 :=
    fun x hx s => (hx s).1
  have hAi : ∀ x : Fin d → MvPowerSeries (Fin d) C, PTGood v x → ∀ s, x s ∈ ptIntSer v (Fin d) :=
    fun x hx s => (hx s).2
  have hAag : ∀ k (x y : Fin d → MvPowerSeries (Fin d) C), PTGood v x → PTGood v y → PTAgree k x y →
      ∀ s (e : Fin d →₀ ℕ), e.degree < k → coeff e (x s) = coeff e (y s) :=
    fun k x y _ _ hxy s e he => hxy s e he
  have hfX : PTGood v (fun b => (X b : MvPowerSeries (Fin d) C)) := fun b => ⟨by simp, ptIntSer_X b⟩
  have hsub : ∀ x : Fin d → MvPowerSeries (Fin d) C, PTGood v x → ∀ b,
      subst x (ptBasisMap G γ b) = ∑ a, M a b • x a + subst x (K b) := fun x hx b =>
    pt_subst_lin_split (MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => (hx s).1) _ (fun a => M a b)
  obtain ⟨Ψ, ⟨hΨg, hΨeq⟩, -⟩ := pt_solve (M := M) (N := M⁻¹) (A := fun x => x) (K := K)
    (f := fun b => (X b : MvPowerSeries (Fin d) C)) hNM hMN hNint hfX hA0 hAi hAag hK hKi hK0
  have hΨs : HasSubst Ψ := MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => (hΨg s).1
  have hright : ∀ b, subst Ψ (ptBasisMap G γ b) = X b := fun b => (hsub Ψ hΨg b).trans (hΨeq b)
  obtain ⟨y0, -, huniq⟩ := pt_solve (M := M) (N := M⁻¹) (A := fun x => x) (K := K)
    (f := ptBasisMap G γ) hNM hMN hNint hΦ hA0 hAi hAag hK hKi hK0
  let y : Fin d → MvPowerSeries (Fin d) C := fun a => subst (ptBasisMap G γ) (Ψ a)
  have hyg : PTGood v y := fun a =>
    ⟨MvPowerSeries.constantCoeff_subst_eq_zero hΦs (fun s => (hΦ s).1) (hΨg a).1,
      ptIntSer_subst hΦs (fun s => (hΦ s).2) (hΨg a).2⟩
  have hy : y = y0 := huniq y ⟨hyg, fun b => by
    rw [← hsub y hyg b]
    show subst (fun a => subst (ptBasisMap G γ) (Ψ a)) (ptBasisMap G γ b) = ptBasisMap G γ b
    rw [← MvPowerSeries.subst_comp_subst_apply hΨs hΦs, hright b, MvPowerSeries.subst_X hΦs]⟩
  have hX : (fun b => (X b : MvPowerSeries (Fin d) C)) = y0 := huniq _ ⟨hfX, fun b => by
    rw [← hsub _ hfX b, MvPowerSeries.subst_self]
    rfl⟩
  refine ⟨Ψ, fun a => (ptMvIsInt_iff _).mpr (hΨg a).2, fun a => (hΨg a).1, hright, fun a => ?_⟩
  exact congrFun (hy.trans hX.symm) a

end

end ReciprocityTheory.ChartRestriction.G.Sh
end

