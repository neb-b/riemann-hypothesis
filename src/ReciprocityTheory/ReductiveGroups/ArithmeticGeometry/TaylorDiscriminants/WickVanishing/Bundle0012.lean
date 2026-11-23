module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.SecondColumnOperator
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0009

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LemmaHCols
section
set_option autoImplicit false

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols

variable {k : Type} [CommRing k] {ι : Type} [Fintype ι] {n : ℕ}

def Mf (mu : Fin n → MvPolynomial ι k →ₗ[k] k) (P : MvPolynomial (ι × Fin n) k) : k :=
  ∑ mo ∈ P.support, P.coeff mo * ∏ b, mu b (monomial (colM mo b) 1)

variable (mu : Fin n → MvPolynomial ι k →ₗ[k] k)

theorem Mf_subset (P : MvPolynomial (ι × Fin n) k) (S : Finset (ι × Fin n →₀ ℕ)) (hS : P.support ⊆ S) :
    Mf mu P = ∑ mo ∈ S, P.coeff mo * ∏ b, mu b (monomial (colM mo b) 1) := by
  unfold Mf
  refine Finset.sum_subset hS (fun mo _ h => ?_)
  first
    | rw [MvPolynomial.notMem_support_iff.mp h, zero_mul]
    | rw [MvPolynomial.not_mem_support_iff.mp h, zero_mul]

theorem Mf_add (P Q : MvPolynomial (ι × Fin n) k) : Mf mu (P + Q) = Mf mu P + Mf mu Q := by
  classical
  rw [Mf_subset mu (P + Q) (P.support ∪ Q.support) MvPolynomial.support_add,
    Mf_subset mu P _ Finset.subset_union_left, Mf_subset mu Q _ Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun mo _ => ?_)
  rw [MvPolynomial.coeff_add, add_mul]

theorem Mf_smul (a : k) (P : MvPolynomial (ι × Fin n) k) : Mf mu (a • P) = a * Mf mu P := by
  rw [Mf_subset mu (a • P) P.support MvPolynomial.support_smul, Mf, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun mo _ => ?_)
  rw [MvPolynomial.coeff_smul, smul_eq_mul, mul_assoc]

theorem Mf_zero : Mf mu (0 : MvPolynomial (ι × Fin n) k) = 0 := by
  simp [Mf]

theorem Mf_sum {α : Type} (s : Finset α) (P : α → MvPolynomial (ι × Fin n) k) :
    Mf mu (∑ a ∈ s, P a) = ∑ a ∈ s, Mf mu (P a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Mf_zero mu]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Mf_add, ih]

theorem Mf_monomial (mo : ι × Fin n →₀ ℕ) (a : k) :
    Mf mu (monomial mo a) = a * ∏ b, mu b (monomial (colM mo b) 1) := by
  classical
  rw [Mf_subset mu _ {mo} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
    MvPolynomial.coeff_monomial, if_pos rfl]

def combine (f : Fin n → (ι →₀ ℕ)) : ι × Fin n →₀ ℕ :=
  ∑ b, Finsupp.mapDomain (fun l => (l, b)) (f b)

theorem combine_apply (f : Fin n → (ι →₀ ℕ)) (l : ι) (b : Fin n) : combine f (l, b) = f b l := by
  classical
  unfold combine
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single b]
  · exact Finsupp.mapDomain_apply_of_injective (fun x y h => (Prod.mk.inj h).1) (f b) l
  · intro b' _ hb'
    apply Finsupp.mapDomain_notin_range
    rintro ⟨l', hl'⟩
    exact hb' (Prod.mk.inj hl').2
  · intro h
    exact absurd (Finset.mem_univ b) h

theorem colM_combine (f : Fin n → (ι →₀ ℕ)) (b : Fin n) : colM (combine f) b = f b := by
  ext l
  simp [colM, combine_apply]

theorem combine_colM (mo : ι × Fin n →₀ ℕ) : combine (colM mo) = mo := by
  ext ⟨l, b⟩
  rw [combine_apply]
  simp [colM]

theorem prod_monomial' {β : Type} (s : Finset β) (g : β → ι × Fin n →₀ ℕ) (a : β → k) :
    ∏ b ∈ s, monomial (g b) (a b) = monomial (∑ b ∈ s, g b) (∏ b ∈ s, a b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, ih, MvPolynomial.monomial_mul, Finset.sum_insert hx, Finset.prod_insert hx]

theorem prodQ_monomial (f : Fin n → (ι →₀ ℕ)) (a : Fin n → k) :
    prodQ (fun b => monomial (f b) (a b)) = monomial (combine f) (∏ b, a b) := by
  unfold prodQ
  simp only [colE, MvPolynomial.rename_monomial]
  rw [prod_monomial']
  rfl

theorem Mf_prodQ (R : Fin n → MvPolynomial ι k) : Mf mu (prodQ R) = ∏ b, mu b (R b) := by
  classical
  have hR : ∀ b, colE b (R b) = ∑ α ∈ (R b).support, colE b (monomial α (AddMonoidAlgebra.coeff (R b) α)) := by
    intro b
    conv_lhs => rw [as_sum (R b)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
  have hmu : ∀ b, mu b (R b) = ∑ α ∈ (R b).support, AddMonoidAlgebra.coeff (R b) α * mu b (monomial α 1) := by
    intro b
    conv_lhs => rw [as_sum (R b)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun α _ => by
      rw [show monomial α (AddMonoidAlgebra.coeff (R b) α) = AddMonoidAlgebra.coeff (R b) α • monomial α (1 : k) by
        rw [smul_monomial, smul_eq_mul, mul_one], map_smul, smul_eq_mul]
  rw [prodQ, Finset.prod_congr rfl (fun b _ => hR b), Finset.prod_univ_sum, Mf_sum,
    Finset.prod_congr rfl (fun b _ => hmu b), Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hp := prodQ_monomial x (fun b => AddMonoidAlgebra.coeff (R b) (x b))
  simp only [prodQ] at hp
  rw [hp, Mf_monomial, Finset.prod_mul_distrib]
  simp only [colM_combine]

theorem degree_colM (mo : ι × Fin n →₀ ℕ) : ∑ b, (colM mo b).degree = mo.degree := by
  classical
  have hd : ∀ {σ : Type} [Fintype σ] (m : σ →₀ ℕ), m.degree = ∑ i, m i := by
    intro σ _ m
    unfold Finsupp.degree
    exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => Finsupp.notMem_support_iff.mp hi)
  simp only [hd]
  rw [Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp [colM]

theorem totalDegree_monomial_one_le (α : ι →₀ ℕ) : (monomial α (1 : k)).totalDegree ≤ α.degree := by
  classical
  unfold MvPolynomial.totalDegree
  apply Finset.sup_le
  intro s hs
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hs)]
  exact le_rfl

theorem iter_linear (c : ι × Fin n → ι × Fin n → k) (i : ℕ) :
    ∀ x : MvPolynomial (ι × Fin n) k, (secondOrder k c)^[i] x = ((soL c) ^ i) x := by
  induction i with
  | zero => intro x; simp
  | succ i ih =>
    intro x
    rw [Function.iterate_succ_apply', ih, pow_succ']
    rfl

theorem iter_zero' (c : ι × Fin n → ι × Fin n → k) (i : ℕ) :
    (secondOrder k c)^[i] (0 : MvPolynomial (ι × Fin n) k) = 0 := by
  rw [iter_linear]
  exact map_zero _

variable [Algebra ℚ k]

theorem colAlg (κ : ι → ι → k) (lam : Fin n → (ι →₀ ℕ) → k)
    (hlm : ∀ b α, lam b α = ∑ i ∈ Finset.range ((monomial α (1 : k)).totalDegree + 1),
        mu b (((i.factorial : ℚ)⁻¹) • (secondOrder k κ)^[i] (monomial α 1)))
    (P : MvPolynomial (ι × Fin n) k)
    (hP : secondOrder k (fun p q : ι × Fin n => if p.2 = q.2 then κ p.1 q.1 else 0) P = 0) :
    ∑ mo ∈ P.support, P.coeff mo * ∏ b, lam b (colM mo b) = Mf mu P := by
  classical
  set N := P.totalDegree with hN
  set cc : ι × Fin n → ι × Fin n → k := cS κ (Finset.univ : Finset (Fin n)) with hcc
  have hccu : cc = fun p q : ι × Fin n => if p.2 = q.2 then κ p.1 q.1 else 0 := cS_univ κ
  have hE : ∀ b α, (monomial α (1 : k)).totalDegree ≤ N →
      lam b α = mu b (E1 κ 1 N (monomial α 1)) := by
    intro b α hα
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hlm, E1, map_sum]
    refine Finset.sum_subset (Finset.range_subset_range.2 (Nat.succ_le_succ hα)) (fun i hi hi' => ?_) |>.trans ?_
    · rw [so_iter_eq_zero κ i _ (by simp only [Finset.mem_range] at hi'; omega), smul_zero, map_zero]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [one_pow, mul_one, ← algebraMap_smul k ((i.factorial : ℚ)⁻¹)]
  have hmo : ∀ mo ∈ P.support, ∏ b, lam b (colM mo b) =
      ∑ i ∈ Finset.range (N + 1), (algebraMap ℚ k ((i.factorial : ℚ)⁻¹) * 1 ^ i) *
        Mf mu ((secondOrder k cc)^[i] (monomial mo 1)) := by
    intro mo hmo
    have hdeg : mo.degree ≤ N := by
      have := le_totalDegree hmo
      exact le_of_eq_of_le (by rfl) this
    have hD : ∀ b, (monomial (colM mo b) (1 : k)).totalDegree ≤ (colM mo b).degree :=
      fun b => totalDegree_monomial_one_le _
    have hsum : ∑ b, (colM mo b).degree ≤ N := (degree_colM mo).le.trans hdeg
    have hb : ∀ b, (monomial (colM mo b) (1 : k)).totalDegree ≤ N := fun b =>
      (hD b).trans ((Finset.single_le_sum (fun b _ => Nat.zero_le _) (Finset.mem_univ b)).trans hsum)
    rw [Finset.prod_congr rfl (fun b _ => hE b (colM mo b) (hb b)), ← Mf_prodQ]
    have hx := exp_cols κ 1 N (fun b => (colM mo b).degree) hsum Finset.univ
      (fun b => monomial (colM mo b) 1) hD
    simp only [Finset.mem_univ, if_true] at hx
    rw [← hx, prodQ_monomial, Finset.prod_const_one, combine_colM,
      exp_opA_apply _ _ _ _ ((totalDegree_monomial_one_le mo).trans hdeg), Mf_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Mf_smul]
  rw [Finset.sum_congr rfl fun mo hmo' => by rw [hmo mo hmo']]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hlin : ∀ i, ∑ mo ∈ P.support, P.coeff mo * ((algebraMap ℚ k ((i.factorial : ℚ)⁻¹) * 1 ^ i) *
      Mf mu ((secondOrder k cc)^[i] (monomial mo 1))) =
      (algebraMap ℚ k ((i.factorial : ℚ)⁻¹) * 1 ^ i) * Mf mu ((secondOrder k cc)^[i] P) := by
    intro i
    conv_rhs => rw [as_sum P]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [iter_linear, map_sum, Mf_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun mo _ => ?_
    rw [show monomial mo (P.coeff mo) = P.coeff mo • monomial mo (1 : k) by
      rw [smul_monomial, smul_eq_mul, mul_one], map_smul, Mf_smul, ← iter_linear]
    ring
  rw [Finset.sum_congr rfl fun i _ => hlin i, Finset.sum_range_succ', Finset.sum_eq_zero]
  · simp
  · intro i _
    rw [Function.iterate_succ_apply, hccu, hP, iter_zero', Mf_zero, mul_zero]

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

def valL {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type} [CommRing k]
    [Algebra ℚ k] [Algebra R k] (B : FB R d O) {ι : Type} [Fintype ι] (u : ι → Fin d → k) (g : PS k 1 d) :
    MvPolynomial ι k →ₗ[k] k where
  toFun Q := MvPowerSeries.constantCoeff (DpolyOf (B.FK k) u Q g)
  map_add' P Q := by rw [GE.dpolyOf_add_P, map_add (f := _)]
  map_smul' a Q := by
    rw [GE.dpolyOf_smul_P, map_mul, MvPowerSeries.constantCoeff_C, RingHom.id_apply, smul_eq_mul]

theorem lemmaHCols_of (hV : ValueSt) (hN2 : ConnectionCommutator) (hN3 : ConnectionKillsSeries) : LemmaHColsSt := by
  intro R _ d O _ _ k _ _ _ B h hax m ι π _ _ c s u φ _ hUF hFU n P hP g
  have hP' : secondOrder k (fun p q : ι × Fin n =>
      if p.2 = q.2 then SCPf.kapH m c s u φ p.1 q.1 else 0) P = 0 := by
    rw [← hP]
    congr 1
    funext p q
    unfold SCPf.kapH
    by_cases h1 : p.2 = q.2
    · simp [h1]
    · simp [h1]
  have key := colAlg (fun b => valL B u (g b)) (SCPf.kapH m c s u φ)
    (fun b α => MvPowerSeries.constantCoeff (ordNabla k B h m s (fun l => (u l, φ l))
      (MvPolynomial.monomial α 1) (liftX k (g b))))
    (fun b α => SCPf.ordNabla_value_expand hV hN2 hN3 B h hax m c s u φ hUF hFU _ (g b)) P hP'
  exact key

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LogInv
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf

variable {k : Type} [CommRing k] {d : ℕ}

theorem cc_pt {n : ℕ} (j : Fin n) (i : Fin d) : constantCoeff (pt k (n := n) d j i) = 0 := by
  simp [pt]

theorem cc_zero {n : ℕ} (i : Fin d) : constantCoeff ((0 : Pt k n d) i) = 0 := by
  simp

theorem CZ.nil {n : ℕ} : CZ (![] : Fin 0 → Pt k n d) := by
  intro j
  exact j.elim0

theorem CZ.cons {m n : ℕ} {p : Pt k n d} {a : Fin m → Pt k n d} (hp : ∀ i, constantCoeff (p i) = 0) (ha : CZ a) :
    CZ (Matrix.vecCons p a) := by
  intro j
  cases j using Fin.cases with
  | zero => simpa using hp
  | succ j => simpa using ha j

theorem pt_apply {n : ℕ} (j : Fin n) (i : Fin d) : pt k (n := n) d j i = (X (j, i) : PS k n d) := rfl

variable (G : FGLaw k d)

theorem cz_F : ∀ i, constantCoeff (G.F i) = 0 := G.const

theorem formalGroupLaw_ev_x_zero (i : Fin d) : ev (n := 1) ![pt k d 0, 0] (G.F i) = (X ((0 : Fin 1), i) : PS k 1 d) := by
  have ha : CZ (![pt k (n := 1) d 0, 0] : Fin 2 → Pt k 1 d) := CZ.cons (cc_pt _) (CZ.cons cc_zero CZ.nil)
  have hb : CZ (![pt k (n := 2) d 1, pt k d 0] : Fin 2 → Pt k 2 d) :=
    CZ.cons (cc_pt _) (CZ.cons (cc_pt _) CZ.nil)
  rw [← G.comm i, ev_ev ha hb]
  have e : (fun j l => ev (n := 1) (![pt k d 0, 0] : Fin 2 → Pt k 1 d)
      ((![pt k (n := 2) d 1, pt k d 0] : Fin 2 → Pt k 2 d) j l)) = (![0, pt k d 0] : Fin 2 → Pt k 1 d) := by
    funext j l
    fin_cases j <;> simp [pt_apply, ev_X ha]
  rw [e]
  exact G.unit i

open scoped MvPowerSeries.WithPiTopology

local macro "prove_ev_chain_rule " k:ident a:ident ha:term:max f:term:max v:term:max : term =>
  `(by
    classical
    let : UniformSpace $k := ⊥
    let family := fun p : _ × _ => $a p.1 p.2
    change pderiv $v (subst family $f) = ∑ p, subst family (pderiv p $f) * pderiv $v (family p)
    have hsubst := continuous_subst (R := $k) (CZ.hasSubst (show CZ $a from $ha))
    have hderiv {σ : Type} (i : σ) : Continuous (pderiv (R := $k) i) := by
      apply continuous_pi
      intro e
      change Continuous (fun g => coeff e (pderiv i g))
      simp only [coeff_pderiv]
      exact (WithPiTopology.continuous_coeff $k _).mul continuous_const
    refine congrFun (WithPiTopology.denseRange_toMvPowerSeries.equalizer
      ((hderiv $v).comp hsubst) (continuous_finsetSum _ fun p _ =>
        (hsubst.comp (hderiv p)).mul continuous_const) ?_) $f
    funext q
    change pderiv $v (subst family (q : MvPowerSeries _ $k)) =
      ∑ p, subst family (pderiv p (q : MvPowerSeries _ $k)) * pderiv $v (family p)
    simp only [pderiv_coe, subst_coe]
    induction q using MvPolynomial.induction_on with
    | C c => simp
    | add q r hq hr => simp only [map_add, hq, hr, add_mul, Finset.sum_add_distrib]
    | mul_X q p hq =>
      rw [map_mul, MvPolynomial.aeval_X, Derivation.leibniz, hq, smul_eq_mul, smul_eq_mul,
        Finset.mul_sum]
      simp [Pi.single_apply, apply_ite (MvPolynomial.aeval family), add_mul,
        Finset.sum_add_distrib, mul_assoc])

theorem pderiv_ev_zero {m n : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) (v : Fin n × Fin d)
    (h : ∀ j i, pderiv (R := k) v (a j i) = 0) : pderiv (R := k) v (ev a f) = 0 := by
  have hchain : pderiv v (ev a f) =
      ∑ p : Fin m × Fin d, ev a (pderiv p f) * pderiv v (a p.1 p.2) :=
    prove_ev_chain_rule k a ha f v
  rw [hchain]
  exact Finset.sum_eq_zero (fun p _ => by rw [h p.1 p.2, mul_zero])

theorem pderiv_pt {n : ℕ} (v : Fin n × Fin d) (j : Fin n) (i : Fin d) :
    pderiv (R := k) v (pt k (n := n) d j i) = if (j, i) = v then 1 else 0 := by
  rw [pt_apply, MvPowerSeries.pderiv_X, Pi.single_apply]

def Jac : Fin d → Fin d → PS k 1 d := fun i b => ev (n := 1) ![pt k d 0, 0] (pderiv (R := k) ((1 : Fin 2), b) (G.F i))

def Ar : Fin d → Fin d → PS k 2 d := fun i b => pderiv (R := k) ((1 : Fin 2), b) (G.F i)

section Fams

theorem cz1 : CZ (![pt k (n := 1) d 0, 0] : Fin 2 → Pt k 1 d) := CZ.cons (cc_pt _) (CZ.cons cc_zero CZ.nil)
theorem czY : CZ (![pt k (n := 2) d 1] : Fin 1 → Pt k 2 d) := CZ.cons (cc_pt _) CZ.nil
theorem czZ : CZ (![pt k (n := 2) d 0, pt k d 1, 0] : Fin 3 → Pt k 2 d) :=
  CZ.cons (cc_pt _) (CZ.cons (cc_pt _) (CZ.cons cc_zero CZ.nil))
theorem czFF : CZ (![G.F] : Fin 1 → Pt k 2 d) := CZ.cons (cz_F G) CZ.nil
theorem cz01 : CZ (![pt k (n := 3) d 0, pt k d 1] : Fin 2 → Pt k 3 d) := CZ.cons (cc_pt _) (CZ.cons (cc_pt _) CZ.nil)
theorem cz12 : CZ (![pt k (n := 3) d 1, pt k d 2] : Fin 2 → Pt k 3 d) := CZ.cons (cc_pt _) (CZ.cons (cc_pt _) CZ.nil)

end Fams

private theorem ev_zero_of_CZ {m n : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) : ev a (0 : PS k m d) = 0 := by
  simpa using ev_sub ha (0 : PS k m d) 0

theorem formal_ev_second_point_of_x_zero (g : PS k 2 d) :
    ev (n := 2) ![pt k d 1] (ev (n := 1) ![pt k d 0, 0] g) = ev (n := 2) ![pt k d 1, 0] g := by
  rw [ev_ev czY cz1]
  congr 1
  funext j l
  fin_cases j
  · simp [pt_apply, ev_X czY]
  · simp [ev_zero_of_CZ czY]

theorem ev_z_yz (g : PS k 2 d) :
    ev (n := 2) ![pt k d 0, pt k d 1, 0] (ev (n := 3) ![pt k d 1, pt k d 2] g) = ev (n := 2) ![pt k d 1, 0] g := by
  rw [ev_ev czZ cz12]
  congr 1
  funext j l
  fin_cases j <;> simp [pt_apply, ev_X czZ]

theorem formalGroupLaw_ev_y_zero (c : Fin d) : ev (n := 2) ![pt k d 1, 0] (G.F c) = (X ((1 : Fin 2), c) : PS k 2 d) := by
  rw [← formal_ev_second_point_of_x_zero, formalGroupLaw_ev_x_zero, ev_X czY]
  simp [pt_apply]

private theorem ev_two_identity (f : PS k 2 d) : ev (n := 2) ![pt k d 0, pt k d 1] f = f := by
  have h : (![pt k (n := 2) d 0, pt k d 1] : Fin 2 → Pt k 2 d) = fun j => pt k d j := by
    funext j
    fin_cases j <;> rfl
  rw [h, ev_pt]

private theorem ev_finset_sum_of_CZ {m n : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) (f : Fin d → PS k m d) :
    ev a (∑ c, f c) = ∑ c, ev a (f c) :=
  map_sum (AddMonoidHom.mk' (ev a) (ev_add ha)) f Finset.univ

private theorem ev_zero_one_identity (g : PS k 2 d) :
    ev (n := 2) (![pt k d 0, pt k d 1, 0] : Fin 3 → Pt k 2 d) (ev (n := 3) ![pt k d 0, pt k d 1] g) = g := by
  rw [ev_ev czZ cz01]
  have e : (fun j l => ev (n := 2) (![pt k d 0, pt k d 1, 0] : Fin 3 → Pt k 2 d)
      ((![pt k (n := 3) d 0, pt k d 1] : Fin 2 → Pt k 3 d) j l)) = (![pt k d 0, pt k d 1] : Fin 2 → Pt k 2 d) := by
    funext j l
    fin_cases j <;> simp [pt_apply, ev_X czZ]
  rw [e, ev_two_identity]

private theorem pderiv_two_ev (b : Fin d) (g : PS k 2 d) :
    pderiv (R := k) ((2 : Fin 3), b) (ev (n := 3) ![pt k d 1, pt k d 2] g) =
      ev (n := 3) ![pt k d 1, pt k d 2] (pderiv (R := k) ((1 : Fin 2), b) g) := by
  let a : Fin 2 → Pt k 3 d := ![pt k d 1, pt k d 2]
  have hchain : pderiv (2, b) (ev a g) =
      ∑ p : Fin 2 × Fin d, ev a (pderiv p g) * pderiv (2, b) (a p.1 p.2) :=
    prove_ev_chain_rule k a cz12 g (2, b)
  change pderiv (2, b) (ev a g) = _
  rw [hchain, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [a, pderiv_pt]

private theorem ev_jacobian_left (i b : Fin d) :
    ev (n := 2) (![pt k d 0, pt k d 1, 0] : Fin 3 → Pt k 2 d)
      (pderiv (R := k) ((2 : Fin 3), b)
        (ev (n := 3) ![fun l => ev (n := 3) ![pt k d 0, pt k d 1] (G.F l), pt k d 2] (G.F i))) =
      ev (n := 2) ![G.F] (Jac G i b) := by
  have hA : CZ (![fun l => ev (n := 3) ![pt k d 0, pt k d 1] (G.F l), pt k d 2] : Fin 2 → Pt k 3 d) :=
    CZ.cons (fun l => constantCoeff_ev cz01 (cz_F G l)) (CZ.cons (cc_pt _) CZ.nil)
  have h0 : ∀ l, pderiv (R := k) ((2 : Fin 3), b) (ev (n := 3) ![pt k d 0, pt k d 1] (G.F l)) = 0 := fun l =>
    pderiv_ev_zero cz01 _ _ (fun j i => by fin_cases j <;> simp [pderiv_pt])
  have hs : pderiv (R := k) ((2 : Fin 3), b)
      (ev (n := 3) ![fun l => ev (n := 3) ![pt k d 0, pt k d 1] (G.F l), pt k d 2] (G.F i)) =
      ev (n := 3) ![fun l => ev (n := 3) ![pt k d 0, pt k d 1] (G.F l), pt k d 2]
        (pderiv (R := k) ((1 : Fin 2), b) (G.F i)) := by
    let a : Fin 2 → Pt k 3 d := ![fun l => ev ![pt k d 0, pt k d 1] (G.F l), pt k d 2]
    have hchain : pderiv (2, b) (ev a (G.F i)) =
        ∑ p : Fin 2 × Fin d, ev a (pderiv p (G.F i)) * pderiv (2, b) (a p.1 p.2) :=
      prove_ev_chain_rule k a hA (G.F i) (2, b)
    change pderiv (2, b) (ev a (G.F i)) = _
    rw [hchain, Fintype.sum_prod_type, Fin.sum_univ_two]
    simp [a, h0, pderiv_pt]
  have e1 : (fun j l => ev (n := 2) (![pt k d 0, pt k d 1, 0] : Fin 3 → Pt k 2 d)
      ((![fun l => ev (n := 3) ![pt k d 0, pt k d 1] (G.F l), pt k d 2] : Fin 2 → Pt k 3 d) j l)) =
      (![G.F, 0] : Fin 2 → Pt k 2 d) := by
    funext j l
    fin_cases j
    · simp [ev_zero_one_identity]
    · simp [pt_apply, ev_X czZ]
  have e2 : (fun j l => ev (n := 2) (![G.F] : Fin 1 → Pt k 2 d) ((![pt k d 0, 0] : Fin 2 → Pt k 1 d) j l)) =
      (![G.F, 0] : Fin 2 → Pt k 2 d) := by
    funext j l
    fin_cases j
    · simp [pt_apply, ev_X (czFF G)]
    · simp [ev_zero_of_CZ (czFF G)]
  rw [hs, ev_ev czZ hA, e1]
  simp only [Jac]
  rw [ev_ev (czFF G) cz1, e2]

private theorem ev_jacobian_right (i b : Fin d) :
    ev (n := 2) (![pt k d 0, pt k d 1, 0] : Fin 3 → Pt k 2 d)
      (pderiv (R := k) ((2 : Fin 3), b)
        (ev (n := 3) ![pt k d 0, fun l => ev (n := 3) ![pt k d 1, pt k d 2] (G.F l)] (G.F i))) =
      ∑ c, Ar G i c * ev (n := 2) ![pt k d 1] (Jac G c b) := by
  have hB : CZ (![pt k d 0, fun l => ev (n := 3) ![pt k d 1, pt k d 2] (G.F l)] : Fin 2 → Pt k 3 d) :=
    CZ.cons (cc_pt _) (CZ.cons (fun l => constantCoeff_ev cz12 (cz_F G l)) CZ.nil)
  have hs : pderiv (R := k) ((2 : Fin 3), b)
      (ev (n := 3) ![pt k d 0, fun l => ev (n := 3) ![pt k d 1, pt k d 2] (G.F l)] (G.F i)) =
      ∑ c, ev (n := 3) ![pt k d 0, fun l => ev (n := 3) ![pt k d 1, pt k d 2] (G.F l)]
          (pderiv (R := k) ((1 : Fin 2), c) (G.F i)) *
        ev (n := 3) ![pt k d 1, pt k d 2] (pderiv (R := k) ((1 : Fin 2), b) (G.F c)) := by
    let a : Fin 2 → Pt k 3 d := ![pt k d 0, fun l => ev ![pt k d 1, pt k d 2] (G.F l)]
    have hchain : pderiv (2, b) (ev a (G.F i)) =
        ∑ p : Fin 2 × Fin d, ev a (pderiv p (G.F i)) * pderiv (2, b) (a p.1 p.2) :=
      prove_ev_chain_rule k a hB (G.F i) (2, b)
    change pderiv (2, b) (ev a (G.F i)) = _
    rw [hchain, Fintype.sum_prod_type, Fin.sum_univ_two]
    simp [a, pderiv_pt, pderiv_two_ev]
  have e1 : (fun j l => ev (n := 2) (![pt k d 0, pt k d 1, 0] : Fin 3 → Pt k 2 d)
      ((![pt k d 0, fun l => ev (n := 3) ![pt k d 1, pt k d 2] (G.F l)] : Fin 2 → Pt k 3 d) j l)) =
      (![pt k d 0, pt k d 1] : Fin 2 → Pt k 2 d) := by
    funext j l
    fin_cases j
    · simp [pt_apply, ev_X czZ]
    · simp [ev_z_yz, formalGroupLaw_ev_y_zero, pt_apply]
  rw [hs, ev_finset_sum_of_CZ czZ]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [ev_mul czZ, ev_ev czZ hB, e1, ev_two_identity, ev_z_yz]
  simp only [Ar, Jac, formal_ev_second_point_of_x_zero]

theorem jac_F (i b : Fin d) :
    ev (n := 2) ![G.F] (Jac G i b) = ∑ c, Ar G i c * ev (n := 2) ![pt k d 1] (Jac G c b) := by
  rw [← ev_jacobian_left, ← ev_jacobian_right, G.assoc i]

end ReciprocityTheory.ChartRestriction.G.TB.LogPf
end
end

