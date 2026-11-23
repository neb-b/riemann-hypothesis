module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.CardToMultisetEqDegree
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0002
public import ReciprocityTheory.DualLattices.Bundle0003

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.GeomSumRoot
section
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb

open MvPowerSeries ReciprocityTheory.PGsh

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

theorem geom_sum_root {p : ℕ} {ζ : C} (hζ : IsPrimitiveRoot ζ p) (m : ℕ) :
    ∑ j ∈ Finset.range p, (ζ ^ m) ^ j = if p ∣ m then (p : C) else 0 := by
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    rw [pow_mul, hζ.pow_eq_one, one_pow]
    simp
  · have hne : ζ ^ m ≠ 1 := fun h1 => h (hζ.dvd_of_pow_eq_one m h1)
    rw [geom_sum_eq hne, pow_right_comm, hζ.pow_eq_one, one_pow, sub_self, zero_div]

theorem exists_average (G : LogFGL v d) {p : ℕ} (hp : p.Prime) {ζ : C}
    (hζ : IsPrimitiveRoot ζ p) {ga : Fin d → PowerSeries C} (hga : IsCurve v ga) :
    ∃ δ : Fin d → PowerSeries C, IsCurve v δ ∧ ∀ c j, PowerSeries.coeff j (G.lgCurve δ c) =
      (p : C) * PowerSeries.coeff (p * j) (G.lgCurve ga c) := by
  classical
  have hp0 : p ≠ 0 := hp.ne_zero
  have h0 : ∀ b, PowerSeries.constantCoeff (ga b) = 0 := fun b => (hga b).1
  have hζv : ∀ j : ℕ, IsIntV v (ζ ^ j) := fun j => by
    unfold IsIntV
    rw [v_eq_zero_of_pow_eq_one (v := v) hp0
      (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow])]

  obtain ⟨g, hgdef⟩ : ∃ g : Fin p → Fin d → PowerSeries C,
      ∀ u, g u = rescaleCurve (ζ ^ (u : ℕ)) ga := ⟨fun u => rescaleCurve (ζ ^ (u : ℕ)) ga, fun u => rfl⟩
  have hg : ∀ u, IsCurve v (g u) := fun u => by
    rw [hgdef]
    exact isCurve_rescale (hζv u) hga
  obtain ⟨ε, hεdef⟩ : ∃ ε : Fin d → PowerSeries C, ε = G.sumF g := ⟨_, rfl⟩
  have hε : IsCurve v ε := by
    rw [hεdef]
    exact isCurve_sumF G g hg
  have hεc : ∀ b, PowerSeries.constantCoeff (ε b) = 0 := fun b => (hε b).1
  have hsum : ∀ m : ℕ, ∑ u : Fin p, (ζ ^ (u : ℕ)) ^ m = if p ∣ m then (p : C) else 0 := by
    intro m
    rw [← geom_sum_root hζ m, Fin.sum_univ_eq_sum_range (fun j => (ζ ^ j) ^ m) p]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← pow_mul, ← pow_mul, mul_comm]
  have hlgε : ∀ c m, PowerSeries.coeff m (G.lgCurve ε c) =
      if p ∣ m then (p : C) * PowerSeries.coeff m (G.lgCurve ga c) else 0 := by
    intro c m
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hεdef, lgCurve_sumF G g hg c, map_sum]
    simp only [hgdef, lgCurve_rescale G _ h0, PowerSeries.coeff_rescale]
    rw [← Finset.sum_mul, hsum m]
    split_ifs <;> simp

  have hinv : ∀ a, rescaleCurve ζ ε a = ε a := by
    have hζ1 : IsIntV v ζ := by simpa using hζv 1
    have hεζc : ∀ b, PowerSeries.constantCoeff (rescaleCurve ζ ε b) = 0 :=
      fun b => (isCurve_rescale hζ1 hε b).1
    intro a
    have hdvd : ∀ N, (PowerSeries.X : PowerSeries C) ^ N ∣ rescaleCurve ζ ε a - ε a := fun N =>
      dvd_of_lgCurve_low G hεζc hεc N (fun a' j _ => by
        rw [lgCurve_rescale G ζ hεc, PowerSeries.coeff_rescale, hlgε]
        split_ifs with h
        · obtain ⟨k, rfl⟩ := h
          rw [pow_mul, hζ.pow_eq_one, one_pow, one_mul]
        · rw [mul_zero]) a
    rw [← sub_eq_zero]
    ext m
    have := (PowerSeries.X_pow_dvd_iff.mp (hdvd (m + 1))) m (Nat.lt_succ_self m)
    simpa using this
  have hoff : ∀ a m, ¬ p ∣ m → PowerSeries.coeff m (ε a) = 0 := by
    intro a m hm
    have h1 := congrArg (PowerSeries.coeff m) (hinv a)
    simp only [rescaleCurve, PowerSeries.coeff_rescale] at h1
    have hne : ζ ^ m ≠ 1 := fun h => hm (hζ.dvd_of_pow_eq_one m h)
    have h2 : (ζ ^ m - 1) * PowerSeries.coeff m (ε a) = 0 := by
      rw [sub_mul, one_mul, h1, sub_self]
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne)

  obtain ⟨δ, hδdef⟩ : ∃ δ : Fin d → PowerSeries C,
      ∀ a, δ a = PowerSeries.mk fun j => PowerSeries.coeff (p * j) (ε a) :=
    ⟨fun a => PowerSeries.mk fun j => PowerSeries.coeff (p * j) (ε a), fun a => rfl⟩
  have hexpand : ∀ (f : PowerSeries C) (m : ℕ), PowerSeries.coeff m (PowerSeries.expand p hp0 f) =
      if p ∣ m then PowerSeries.coeff (m / p) f else 0 := by
    intro f m
    have h := coeff_expand_rescale p hp0 1 f m
    rw [PowerSeries.rescale_one, RingHom.id_apply] at h
    rw [h]
    split_ifs <;> simp
  have hexp : ∀ a, PowerSeries.expand p hp0 (δ a) = ε a := by
    intro a
    ext m
    rw [hexpand]
    split_ifs with h
    · rw [hδdef, PowerSeries.coeff_mk, Nat.mul_div_cancel' h]
    · exact (hoff a m h).symm
  have hδ : IsCurve v δ := fun a => by
    refine ⟨?_, fun j => ?_⟩
    · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hδdef, PowerSeries.coeff_mk, mul_zero,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact hεc a
    · rw [hδdef, PowerSeries.coeff_mk]
      exact (hε a).2 (p * j)
  have hεδ : expC p δ = ε := funext fun a => by
    rw [expC_apply hp0]
    exact hexp a
  refine ⟨δ, hδ, fun c j => ?_⟩
  have h1 := lgCurve_expC G hp0 (fun b => (hδ b).1) c
  rw [hεδ] at h1
  have h2 := congrArg (PowerSeries.coeff (p * j)) h1
  rw [hlgε, if_pos (dvd_mul_right p j), hexpand, if_pos (dvd_mul_right p j),
    Nat.mul_div_cancel_left j hp.pos] at h2
  exact h2.symm

end

end ReciprocityTheory.ChartRestriction.G.Sh.PTb
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.LgCurvePcurve
section
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb

open MvPowerSeries ReciprocityTheory.PGsh

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

def ptx (G : LogFGL v d) (p : ℕ) (γ : Fin d → Fin d → PowerSeries C)
    (ga : Fin d → PowerSeries C) (n : ℕ) : Fin d → C :=
  Matrix.vecMul (G.lc p ga n - ∑ s : Fin n, ∑ b,
    (ptx G p γ ga s b) ^ (p ^ (n - s)) • G.lc p (γ b) (n - s)) (tmat γ)⁻¹
termination_by n
decreasing_by exact s.isLt

def ptw (G : LogFGL v d) (p : ℕ) (γ : Fin d → Fin d → PowerSeries C)
    (ga : Fin d → PowerSeries C) (n : ℕ) : Fin d → C :=
  G.lc p ga n - ∑ s ∈ Finset.range n, ∑ b,
    (ptx G p γ ga s b) ^ (p ^ (n - s)) • G.lc p (γ b) (n - s)

theorem ptx_eq (G : LogFGL v d) (p : ℕ) (γ : Fin d → Fin d → PowerSeries C)
    (ga : Fin d → PowerSeries C) (n : ℕ) :
    ptx G p γ ga n = Matrix.vecMul (ptw G p γ ga n) (tmat γ)⁻¹ := by
  rw [ptx, ptw, Finset.sum_range]

private theorem lgCurve_zero' (G : LogFGL v d) (a : Fin d) :
    G.lgCurve (fun _ => (0 : PowerSeries C)) a = 0 := by
  have h0 : HasSubst (fun _ : Fin d => (0 : PowerSeries C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
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
      push Not at hcon
      exact he (Finsupp.ext hcon)
    rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (by simp [hs]),
      map_zero, smul_zero]

private theorem lc_at_zero_eq_tangent (G : LogFGL v d) (p : ℕ) (ga : Fin d → PowerSeries C)
    (h0 : ∀ b, PowerSeries.constantCoeff (ga b) = 0) : G.lc p ga 0 = tangent ga := by
  funext a
  have hk : ∀ b, (PowerSeries.X : PowerSeries C) ^ 1 ∣ ga b - (fun _ => (0 : PowerSeries C)) b := by
    intro b
    show (PowerSeries.X : PowerSeries C) ^ 1 ∣ ga b - 0
    rw [pow_one, sub_zero]
    exact PowerSeries.X_dvd_iff.mpr (h0 b)
  have h1 := lgCurve_sub_dvd (β := fun _ => (0 : PowerSeries C)) G h0 (fun _ => by simp) 1 hk a
  simp only [lgCurve_zero', sub_zero] at h1
  have h2 := PowerSeries.X_pow_dvd_iff.mp h1 1 (by norm_num)
  rw [map_sub, sub_eq_zero] at h2
  show PowerSeries.coeff (p ^ 0) (G.lgCurve ga a) = PowerSeries.coeff 1 (ga a)
  rw [pow_zero, h2]

theorem ptx_rel (G : LogFGL v d) (p : ℕ) {γ : Fin d → Fin d → PowerSeries C}
    (hγ : ∀ a, IsCurve v (γ a)) (hdet : v (tmat γ).det = 0) (ga : Fin d → PowerSeries C)
    (n : ℕ) :
    G.lc p ga n = ∑ s ∈ Finset.range (n + 1), ∑ b,
      (ptx G p γ ga s b) ^ (p ^ (n - s)) • G.lc p (γ b) (n - s) := by
  have hlast : ∑ b, (ptx G p γ ga n b) ^ (p ^ (n - n)) • G.lc p (γ b) (n - n) =
      ptw G p γ ga n := by
    simp only [Nat.sub_self, pow_zero, pow_one]
    rw [Finset.sum_congr rfl (fun b _ => by rw [lc_at_zero_eq_tangent G p (γ b) (fun c => (hγ b c).1)]),
      sum_smul_tangent, ptx_eq, vecMul_inv_tmat hdet]
  rw [Finset.sum_range_succ, hlast, ptw]
  abel

def pcurve (G : LogFGL v d) (p : ℕ) (γ : Fin d → Fin d → PowerSeries C) (x : ℕ → Fin d → C) :
    ℕ → Fin d → PowerSeries C
  | 0 => 0
  | s + 1 => G.add (pcurve G p γ x s) (G.sumF fun b => expC (p ^ s) (rescaleCurve (x s b) (γ b)))

theorem isCurve_pcurve (G : LogFGL v d) {p : ℕ} (hp : p ≠ 0) {γ : Fin d → Fin d → PowerSeries C}
    (hγ : ∀ a, IsCurve v (γ a)) (x : ℕ → Fin d → C) :
    ∀ n, (∀ s < n, ∀ b, IsIntV v (x s b)) → IsCurve v (pcurve G p γ x n)
  | 0, _ => isCurve_zero
  | n + 1, hx => isCurve_add G (isCurve_pcurve G hp hγ x n fun s hs b => hx s (by omega) b)
      (isCurve_sumF G _ fun b => isCurve_expC (pow_ne_zero _ hp)
        (isCurve_rescale (hx n (by omega) b) (hγ b)))

theorem lgCurve_pcurve (G : LogFGL v d) {p : ℕ} (hp : p ≠ 0) {γ : Fin d → Fin d → PowerSeries C}
    (hγ : ∀ a, IsCurve v (γ a)) (x : ℕ → Fin d → C) :
    ∀ n, (∀ s < n, ∀ b, IsIntV v (x s b)) → ∀ a, G.lgCurve (pcurve G p γ x n) a =
      ∑ s ∈ Finset.range n, ∑ b, PowerSeries.expand (p ^ s) (pow_ne_zero _ hp)
        (PowerSeries.rescale (x s b) (G.lgCurve (γ b) a))
  | 0, _, a => by simp [pcurve, lgCurve_zero]
  | n + 1, hx, a => by
      have hx' : ∀ s < n, ∀ b, IsIntV v (x s b) := fun s hs b => hx s (by omega) b
      have hc : ∀ b, IsCurve v (expC (p ^ n) (rescaleCurve (x n b) (γ b))) := fun b =>
        isCurve_expC (pow_ne_zero _ hp) (isCurve_rescale (hx n (by omega) b) (hγ b))
      rw [pcurve, lgCurve_add G (fun b => (isCurve_pcurve G hp hγ x n hx' b).1)
        (fun b => (isCurve_sumF G _ hc b).1), lgCurve_pcurve G hp hγ x n hx' a,
        lgCurve_sumF G _ hc, Finset.sum_range_succ]
      congr 1
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [lgCurve_expC G (pow_ne_zero _ hp) (fun c => (isCurve_rescale (hx n (by omega) b) (hγ b) c).1),
        lgCurve_rescale G _ (fun c => (hγ b c).1)]

end

end ReciprocityTheory.ChartRestriction.G.Sh.PTb
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.NsmulCoprimeBijectiveCurves
section
namespace ReciprocityTheory.ChartRestriction.G.Sh

open MvPowerSeries ReciprocityTheory.PGsh

open Classical

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

def ptNs (G : LogFGL v d) : ℕ → Fin d → MvPowerSeries (Fin d) C
  | 0 => 0
  | n + 1 => fun a => subst (Sum.elim (fun b => X b) (ptNs G n)) (G.F a)

theorem ptNs_const (G : LogFGL v d) : ∀ n a, constantCoeff (ptNs G n a) = 0
  | 0, a => by simp [ptNs]
  | n + 1, a => by
    have h0 : ∀ i, constantCoeff (Sum.elim (fun b => (X b : MvPowerSeries (Fin d) C))
        (ptNs G n) i) = 0 := by
      rintro (i | i)
      · simp
      · exact ptNs_const G n i
    change constantCoeff
      (subst (Sum.elim (fun b => (X b : MvPowerSeries (Fin d) C)) (ptNs G n)) (G.F a)) = 0
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h0) h0 (G.F_const a)

theorem ptNs_hasSubst (G : LogFGL v d) (n : ℕ) :
    HasSubst (Sum.elim (fun b => (X b : MvPowerSeries (Fin d) C)) (ptNs G n)) := by
  exact MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
    cases i with
    | inl b => simp
    | inr b => exact ptNs_const G n b

theorem ptNs_int (G : LogFGL v d) : ∀ n a, ptNs G n a ∈ ptIntSer v (Fin d)
  | 0, a => by simp only [ptNs, Pi.zero_apply]; exact Subring.zero_mem _
  | n + 1, a => by
    refine ptIntSer_subst (ptNs_hasSubst G n) ?_ (G.F_int a)
    rintro (i | i)
    · exact ptIntSer_X i
    · exact ptNs_int G n i

theorem ptNs_lin (G : LogFGL v d) : ∀ (n : ℕ) (a s : Fin d),
    coeff (Finsupp.single s 1) (ptNs G n a) = if s = a then (n : C) else 0
  | 0, a, s => by simp [ptNs]
  | n + 1, a, s => by
    have h0 : ∀ i, constantCoeff (Sum.elim (fun b => (X b : MvPowerSeries (Fin d) C))
        (ptNs G n) i) = 0 := by
      rintro (i | i)
      · simp
      · exact ptNs_const G n i
    change coeff (Finsupp.single s 1)
      (subst (Sum.elim (fun b => (X b : MvPowerSeries (Fin d) C)) (ptNs G n)) (G.F a)) = _
    rw [pt_coeff_single_subst (ptNs_hasSubst G n) h0 (G.F_const a) s, Fintype.sum_sum_type]
    simp only [pt_F_lin, Sum.elim_inl, Sum.elim_inr, pt_coeff_single_X, ptNs_lin G n,
      Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false, add_zero, zero_add,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    split_ifs <;> push_cast <;> ring

theorem nsmulF_eq_subst (G : LogFGL v d) {ga : Fin d → PowerSeries C}
    (hga : HasSubst ga) : ∀ n, G.nsmulF n ga = fun a => subst ga (ptNs G n a)
  | 0 => by
    funext a
    simp only [LogFGL.nsmulF, ptNs, Pi.zero_apply]
    rw [← substAlgHom_apply hga, map_zero]
  | n + 1 => by
    funext a
    simp only [LogFGL.nsmulF, LogFGL.add, ptNs]
    rw [subst_comp_subst_apply (ptNs_hasSubst G n) hga, nsmulF_eq_subst G hga n]
    congr 1
    funext i
    rcases i with i | i
    · simp [subst_X hga]
    · rfl

theorem isCurve_iff_good {ga : Fin d → PowerSeries C} : IsCurve v ga ↔ PTGood v ga := by
  constructor
  · intro h a
    exact ⟨(h a).1, (ptPsIsInt_iff _).mp (h a).2⟩
  · intro h a
    exact ⟨(h a).1, (ptPsIsInt_iff _).mpr (h a).2⟩

private theorem valuation_natCast_eq_zero_of_not_dvd {p : ℕ} (hp : p.Prime) (hvp : v (p : C) = 1) (n : ℕ)
    (hn : ¬ p ∣ n) : v (n : C) = 0 := by
  have hcop : IsCoprime (p : ℤ) (n : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn)
  obtain ⟨u, w, huw⟩ := hcop
  have hC : (u : C) * p + (w : C) * n = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → C) huw
  have hu : 0 ≤ v (u : C) := intCast_mem (ptIntSub v) u
  have hw : 0 ≤ v (w : C) := intCast_mem (ptIntSub v) w
  have hn0 : 0 ≤ v (n : C) := natCast_mem (ptIntSub v) n
  refine le_antisymm ?_ hn0
  by_contra hpos
  push_neg at hpos
  have h1 : 0 < v ((u : C) * p) := by
    rw [v.map_mul, hvp]
    exact lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left hu)
  have h2 : 0 < v ((w : C) * n) := by
    rw [v.map_mul]
    exact lt_of_lt_of_le hpos (le_add_of_nonneg_left hw)
  have h3 := v.map_add ((u : C) * p) ((w : C) * n)
  rw [hC, v.map_one] at h3
  exact absurd h3 (not_le.mpr (lt_min h1 h2))

private theorem exists_eq_single_of_degree_eq_one {σ : Type} (α : σ →₀ ℕ) (h : α.degree = 1) :
    ∃ s, α = Finsupp.single s 1 := by
  have hne : α ≠ 0 := by
    rintro rfl
    simp at h
  obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hne
  refine ⟨s, ?_⟩
  have hsum : ∑ i ∈ α.support, α i = 1 := by rw [← h]; rfl
  have hle : α s ≤ 1 := hsum ▸ Finset.single_le_sum (fun i _ => Nat.zero_le (α i)) hs
  have hs1 : α s = 1 := le_antisymm hle (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hs))
  have hrest : ∑ i ∈ α.support.erase s, α i = 0 := by
    rw [← Finset.add_sum_erase _ _ hs, hs1] at hsum
    omega
  ext i
  by_cases hi : i = s
  · subst hi
    simp [hs1]
  · rw [Finsupp.single_apply, if_neg (Ne.symm hi)]
    by_contra hne'
    have hmem : i ∈ α.support.erase s :=
      Finset.mem_erase.mpr ⟨hi, Finsupp.mem_support_iff.mpr hne'⟩
    have := Finset.single_le_sum (fun j _ => Nat.zero_le (α j)) hmem
    omega

theorem nsmul_coprime_bijective_curves [CharZero C] (G : LogFGL v d) {p : ℕ} (hp : p.Prime) (hvp : v (p : C) = 1)
    (n : ℕ) (hn : ¬ p ∣ n) (gb : Fin d → PowerSeries C) (hgb : IsCurve v gb) :
    ∃! ga : Fin d → PowerSeries C, IsCurve v ga ∧ G.nsmulF n ga = gb := by
  have hn0' : n ≠ 0 := fun h => hn (h ▸ dvd_zero p)
  have hn0 : (n : C) ≠ 0 := by exact_mod_cast hn0'
  have hvn := valuation_natCast_eq_zero_of_not_dvd hp hvp n hn
  have hvinv : (n : C)⁻¹ ∈ ptIntSub v := by
    show 0 ≤ v (n : C)⁻¹
    have h := v.map_mul (n : C) (n : C)⁻¹
    rw [mul_inv_cancel₀ hn0, v.map_one, hvn, zero_add] at h
    rw [← h]
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin d) (Fin d) C, M = (n : C) • 1 := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin d) (Fin d) C, N = (n : C)⁻¹ • 1 := ⟨_, rfl⟩
  have hNM : N * M = 1 := by
    rw [hN, hM, smul_mul_smul_comm, mul_one, inv_mul_cancel₀ hn0, one_smul]
  have hMN : M * N = 1 := by
    rw [hN, hM, smul_mul_smul_comm, mul_one, mul_inv_cancel₀ hn0, one_smul]
  have hMab : ∀ a b, M a b = if a = b then (n : C) else 0 := by
    intro a b
    rw [hM, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  have hNint : ∀ i j, N i j ∈ ptIntSub v := by
    intro i j
    rw [hN, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs
    · rw [mul_one]; exact hvinv
    · rw [mul_zero]; exact (ptIntSub v).zero_mem
  have hMint : ∀ a b, M a b ∈ ptIntSub v := by
    intro a b
    rw [hMab]
    split_ifs
    · exact natCast_mem (ptIntSub v) n
    · exact (ptIntSub v).zero_mem
  obtain ⟨K, hK⟩ : ∃ K : Fin d → MvPowerSeries (Fin d) C,
      K = fun b => ptNs G n b - ∑ a, M a b • X a := ⟨_, rfl⟩
  have hK0 : ∀ b, constantCoeff (K b) = 0 := by
    intro b
    simp [hK, ptNs_const]
  have hKi : ∀ b, K b ∈ ptIntSer v (Fin d) := by
    intro b
    rw [hK]
    exact (ptIntSer v (Fin d)).sub_mem (ptNs_int G n b)
      ((ptIntSer v (Fin d)).sum_mem fun a _ => ptIntSer_smul (hMint a b) (ptIntSer_X a))
  have hKdeg : ∀ b α, coeff α (K b) ≠ 0 → 2 ≤ α.degree ∨
      ∀ x y : Fin d → PowerSeries C, PTGood v x → PTGood v y → ∀ s ∈ α.support, x s = y s := by
    intro b α hα
    left
    by_contra hlt
    push_neg at hlt
    apply hα
    rcases (show α.degree = 0 ∨ α.degree = 1 by omega) with hd | hd
    · rw [(Finsupp.degree_eq_zero_iff α).mp hd, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
        hK0 b]
    · obtain ⟨s, rfl⟩ := exists_eq_single_of_degree_eq_one α hd
      rw [hK]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sub, map_sum, MvPowerSeries.coeff_smul, ptNs_lin, MvPowerSeries.coeff_X,
        Finsupp.single_left_inj one_ne_zero, hMab, smul_eq_mul, mul_ite, mul_one, mul_zero]
      simp [Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]
  have hf : PTGood v gb := isCurve_iff_good.mp hgb
  have key : ∀ y : Fin d → PowerSeries C, PTGood v y →
      (G.nsmulF n y = gb ↔ ∀ b, ∑ a, M a b • y a + subst y (K b) = gb b) := by
    intro y hy
    have hys : HasSubst y := MvPowerSeries.hasSubst_of_constantCoeff_zero fun a => (hy a).1
    rw [nsmulF_eq_subst G hys n]
    constructor
    · intro h b
      rw [← congrFun h b, pt_subst_lin_split hys (ptNs G n b) (fun a => M a b), hK]
    · intro h
      funext b
      rw [pt_subst_lin_split hys (ptNs G n b) (fun a => M a b), ← h b, hK]
  obtain ⟨x, ⟨hx, hxeq⟩, huniq⟩ := pt_solve (A := fun x => x) (K := K) (M := M) (N := N) (f := gb)
    hNM hMN hNint hf (fun x hx s => (hx s).1) (fun x hx s => (hx s).2)
    (fun k x y _ _ hxy s e he => hxy s e he) hKdeg hKi hK0
  refine ⟨x, ⟨isCurve_iff_good.mpr hx, (key x hx).mpr hxeq⟩, fun y hy => ?_⟩
  have hyg := isCurve_iff_good.mp hy.1
  exact huniq y ⟨hyg, (key y hyg).mp hy.2⟩

end

end ReciprocityTheory.ChartRestriction.G.Sh
end

