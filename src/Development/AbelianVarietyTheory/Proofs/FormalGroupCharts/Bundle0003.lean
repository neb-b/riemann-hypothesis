module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AlgHomDualNumberExt
section
open IsLocalRing TensorProduct

namespace GlobalTheory.NoTangent

open MvPowerSeries

theorem leibniz_eq_zero {O C σ : Type} [CommRing O] [CommRing C]
    (φ₀ : MvPowerSeries σ O →+* C) (E : MvPowerSeries σ O →+ C) (a : σ → O)
    (hmul : ∀ g h, E (g * h) = φ₀ g * E h + φ₀ h * E g)
    (hC : ∀ c, E (MvPowerSeries.C c) = 0) (hX : ∀ j, E (X j) = 0)
    (ha : ∀ j, φ₀ (X j - MvPowerSeries.C (a j)) = 0)
    (hP : ∀ g : MvPowerSeries σ O, ∃ P : MvPolynomial σ O,
      g - (P : MvPowerSeries σ O) ∈
        Ideal.span (Set.range fun j => (X j - MvPowerSeries.C (a j) : MvPowerSeries σ O)))
    (g : MvPowerSeries σ O) : E g = 0 := by
  have h1 : ∀ P : MvPolynomial σ O, E (P : MvPowerSeries σ O) = 0 := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C c => rw [MvPolynomial.coe_C]; exact hC c
    | add p q hp hq => rw [MvPolynomial.coe_add, map_add (f := _), hp, hq, add_zero]
    | mul_X p j hp => rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, hmul, hp, hX]; simp
  have h2 : ∀ h ∈ Ideal.span (Set.range fun j =>
      (X j - MvPowerSeries.C (a j) : MvPowerSeries σ O)), φ₀ h = 0 ∧ E h = 0 := by
    intro h hh
    induction hh using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact ⟨ha j, by simp only [map_sub, hX, hC, sub_zero]⟩
    | zero => simp
    | add x y _ _ hx hy => simp [hx.1, hx.2, hy.1, hy.2]
    | smul s x _ hx => simp [hmul, hx.1, hx.2]
  obtain ⟨P, hP⟩ := hP g
  have := (h2 _ hP).2
  rwa [map_sub, h1, sub_zero] at this

theorem finite_quotient {O σ : Type} [CommRing O] [Finite σ] (I : Ideal (MvPowerSeries σ O))
    (M : ℕ) (h : ∀ g : MvPowerSeries σ O, ∃ P : MvPolynomial σ O, P.totalDegree ≤ M ∧
      g - (P : MvPowerSeries σ O) ∈ I) : Module.Finite O (MvPowerSeries σ O ⧸ I) := by
  let L : MvPolynomial.restrictTotalDegree σ O M →ₗ[O] (MvPowerSeries σ O ⧸ I) :=
    (Ideal.Quotient.mkₐ O I).toLinearMap ∘ₗ
      (MvPolynomial.coeToMvPowerSeries.algHom (σ := σ) (R := O) O).toLinearMap ∘ₗ
      (MvPolynomial.restrictTotalDegree σ O M).subtype
  refine Module.Finite.of_surjective L ?_
  intro q
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨P, hP, hg⟩ := h g
  refine ⟨⟨P, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hP⟩, ?_⟩
  have : L ⟨P, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hP⟩ =
      Ideal.Quotient.mk I (P : MvPowerSeries σ O) := by
    simp [L]
  rw [this]
  exact (Ideal.Quotient.eq.2 hg).symm

theorem algHom_dualNumber_ext : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (p : ℕ), p ≠ 0 → IsAdicComplete (Ideal.span {(p : O)}) O → ∀ J : Ideal O, J.FG → J ≠ ⊤ → (p : O) ∈ J → ∀ (σ : Type) [Finite σ] (n : ℕ) (e : Fin n ≃ σ) (f : Fin n → MvPowerSeries σ O) (M N : ℕ) (U : (MvPowerSeries σ O)ˣ), N ≠ 0 → Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) ^ M ≤ Ideal.span (Set.range f) ⊔ Ideal.map (MvPowerSeries.C : O →+* MvPowerSeries σ O) J → Matrix.det (Matrix.of fun i j : Fin n => MvPowerSeries.pderiv (R := O) (e j) (f i)) = (N : MvPowerSeries σ O) * U → ∀ φ φ' : (MvPowerSeries σ O ⧸ Ideal.span (Set.range f)) →ₐ[O] DualNumber C, (∀ a, (φ a).fst = (φ' a).fst) → φ = φ' := by
  intro C _ _ _ v O _ _ hv p hp hc J hJ hJt hpJ σ _ n e f M N U hN hM hdet φ φ' hfst
  classical
  have hJc := _root_.GlobalTheory.isAdicComplete_of_fg_of_natCast_mem C v O hv p hp hc J hJ hJt hpJ
  have hfin := finite_quotient _ M (_root_.GlobalTheory.CompleteBaseChange.exists_polynomial_totalDegree_le_sub_mem O J hJ hJc σ (Fin n) f M hM)
  let I := Ideal.span (Set.range f)
  let ψ : MvPowerSeries σ O →ₐ[O] DualNumber C := φ.comp (Ideal.Quotient.mkₐ O I)
  let ψ' : MvPowerSeries σ O →ₐ[O] DualNumber C := φ'.comp (Ideal.Quotient.mkₐ O I)
  let φ₀ : MvPowerSeries σ O →ₐ[O] C := (TrivSqZeroExt.fstHom O C C).comp ψ
  have h0 : ∀ g, (ψ g).fst = φ₀ g := fun g => rfl
  have h0' : ∀ g, (ψ' g).fst = φ₀ g := fun g => (hfst _).symm
  have hψI : ∀ g ∈ I, ψ g = 0 := fun g hg => by
    simp [ψ, Ideal.Quotient.eq_zero_iff_mem.2 hg]
  have hψI' : ∀ g ∈ I, ψ' g = 0 := fun g hg => by
    simp [ψ', Ideal.Quotient.eq_zero_iff_mem.2 hg]
  have hCa : ∀ c : O, (MvPowerSeries.C c : MvPowerSeries σ O) = algebraMap O _ c := fun c => rfl
  have hle : ∀ g, v (φ₀ g) ≤ 1 := by
    intro g
    have h1 : IsIntegral O (Ideal.Quotient.mkₐ O I g) := Algebra.IsIntegral.isIntegral _
    have h2 := h1.map ((TrivSqZeroExt.fstHom O C C).comp φ)
    exact hv.mem_of_integral h2
  choose a ha using fun j => hv.exists_of_le_one (hle (X j))
  let K : Ideal (MvPowerSeries σ O) :=
    { carrier := {g | v (φ₀ g) < 1}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_add (f := _)] at hx hy ⊢
        exact v.map_add_lt hx hy
      zero_mem' := by simp
      smul_mem' := fun s x hx => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at hx ⊢
        exact mul_lt_one_of_nonneg_of_lt_one_right (hle s) zero_le hx }
  have hK : ∀ g, g ∈ K ↔ v (φ₀ g) < 1 := fun g => Iff.rfl
  have hJK : J ≤ K.comap (MvPowerSeries.C : O →+* MvPowerSeries σ O) := by
    intro c hc
    rw [Ideal.mem_comap, hK, hCa, AlgHom.commutes]
    refine lt_of_le_of_ne (hv.map_le_one c) fun h => hJt ?_
    exact J.eq_top_of_isUnit_mem hc (hv.isUnit_of_one' h)
  have hIK : I ≤ K := by
    intro g hg
    rw [hK, ← h0, hψI g hg]; simp
  have hXK : ∀ j, X j ∈ K := by
    intro j
    have h1 : (X j : MvPowerSeries σ O) ^ M ∈ K :=
      (hM.trans (sup_le hIK (Ideal.map_le_iff_le_comap.2 hJK)))
        (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self j)) M)
    rw [hK, map_pow, map_pow] at h1
    have hM0 : M ≠ 0 := by
      intro h
      subst M
      simp at h1
    rw [hK]
    exact (pow_lt_one_iff_of_nonneg zero_le hM0).1 h1
  let J' : Ideal O := J ⊔ Ideal.span (Set.range a)
  have hJ' : J'.FG := Submodule.FG.sup hJ (Submodule.fg_span (Set.finite_range a))
  have hJ'K : J' ≤ K.comap (MvPowerSeries.C : O →+* MvPowerSeries σ O) := by
    refine sup_le hJK (Ideal.span_le.2 ?_)
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap, hK, hCa, AlgHom.commutes, ha]
    exact hXK j
  have hJ't : J' ≠ ⊤ := by
    intro h
    have : (1 : O) ∈ J' := h ▸ Submodule.mem_top
    have h2 := hJ'K this
    rw [Ideal.mem_comap, hK] at h2
    simp at h2
  have hJ'c := _root_.GlobalTheory.isAdicComplete_of_fg_of_natCast_mem C v O hv p hp hc J' hJ' hJ't (Ideal.mem_sup_left hpJ)
  have hP := _root_.GlobalTheory.CompleteBaseChange.exists_polynomial_totalDegree_le_sub_mem O J' hJ' hJ'c σ σ
    (fun j => (X j - MvPowerSeries.C (a j) : MvPowerSeries σ O)) 1 (by
      rw [pow_one, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      have : (X j : MvPowerSeries σ O) =
          (X j - MvPowerSeries.C (a j)) + MvPowerSeries.C (a j) := by ring
      rw [this]
      exact Submodule.add_mem_sup (Ideal.subset_span ⟨j, rfl⟩)
        (Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩))))
  let d : Fin n → C := fun j => (ψ' (X (e j))).snd - (ψ (X (e j))).snd
  let E : MvPowerSeries σ O →+ C :=
    { toFun := fun g => (ψ' g).snd - (ψ g).snd - ∑ j, φ₀ (pderiv (R := O) (e j) g) * d j
      map_zero' := by simp
      map_add' := fun x y => by
        simp only [map_add (f := _), TrivSqZeroExt.snd_add, add_mul, Finset.sum_add_distrib]; ring }
  have hE : ∀ g, E g = (ψ' g).snd - (ψ g).snd - ∑ j, φ₀ (pderiv (R := O) (e j) g) * d j :=
    fun g => rfl
  have hE0 : ∀ g, E g = 0 := by
    refine leibniz_eq_zero (φ₀ : MvPowerSeries σ O →+* C) E a ?_ ?_ ?_ ?_
      (fun g => (hP g).imp fun P h => h.2)
    · intro g h
      simp only [hE, map_mul, DualNumber.snd_mul, h0, h0', Derivation.leibniz, smul_eq_mul,
        map_add, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum,
        RingHom.coe_coe]
      ring
    · intro c
      rw [hE]
      simp only [pderiv_C, map_zero, zero_mul, Finset.sum_const_zero, sub_zero]
      rw [hCa, AlgHom.commutes, AlgHom.commutes, sub_self]
    · intro s
      obtain ⟨k, rfl⟩ := e.surjective s
      rw [hE, Finset.sum_eq_single k]
      · simp [d, pderiv_X]
      · intro j _ hj
        simp [pderiv_X, hj, hj.symm]
      · simp
    · intro j
      rw [RingHom.coe_coe, map_sub, hCa, AlgHom.commutes, ha, sub_self]
  have hd : d = 0 := by
    let A : Matrix (Fin n) (Fin n) (MvPowerSeries σ O) :=
      Matrix.of fun i j : Fin n => MvPowerSeries.pderiv (R := O) (e j) (f i)
    refine Matrix.eq_zero_of_mulVec_eq_zero
      (M := (φ₀ : MvPowerSeries σ O →+* C).mapMatrix A) ?_ ?_
    · rw [← RingHom.map_det, hdet, map_mul, map_natCast]
      exact mul_ne_zero (Nat.cast_ne_zero.2 hN) (U.isUnit.map _).ne_zero
    · funext i
      have h1 := hE0 (f i)
      have hi : f i ∈ I := Ideal.subset_span ⟨i, rfl⟩
      rw [hE, hψI _ hi, hψI' _ hi, sub_self, zero_sub, neg_eq_zero] at h1
      simpa [Matrix.mulVec, dotProduct, A] using h1
  refine AlgHom.ext fun q => ?_
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective q
  refine TrivSqZeroExt.ext (hfst _) ?_
  have h1 := hE0 g
  rw [hE, hd] at h1
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero] at h1
  exact (sub_eq_zero.1 h1).symm

end GlobalTheory.NoTangent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ConstantCoeffEv
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.FormalLog

variable {k : Type} [CommRing k] {d m n : ℕ}

def CZ (a : Fin m → Pt k n d) : Prop := ∀ j i, constantCoeff (a j i) = 0

theorem CZ.hasSubst {a : Fin m → Pt k n d} (ha : CZ a) : HasSubst (fun p : Fin m × Fin d => a p.1 p.2) :=
  hasSubst_of_constantCoeff_zero fun p => ha p.1 p.2

theorem ev_add {a : Fin m → Pt k n d} (ha : CZ a) (f g : PS k m d) : ev a (f + g) = ev a f + ev a g :=
  subst_add ha.hasSubst f g

theorem ev_mul {a : Fin m → Pt k n d} (ha : CZ a) (f g : PS k m d) : ev a (f * g) = ev a f * ev a g :=
  subst_mul ha.hasSubst f g

def evHom {a : Fin m → Pt k n d} (ha : CZ a) : PS k m d →+* PS k n d :=
  (substAlgHom ha.hasSubst).toRingHom

theorem evHom_apply {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) : evHom ha f = ev a f := by
  simp [evHom, ev]

theorem ev_sum {a : Fin m → Pt k n d} (ha : CZ a) {ι : Type} (s : Finset ι) (f : ι → PS k m d) :
    ev a (∑ x ∈ s, f x) = ∑ x ∈ s, ev a (f x) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← evHom_apply ha, map_sum]

theorem ev_C {a : Fin m → Pt k n d} (ha : CZ a) (c : k) : ev a (C c : PS k m d) = C c := by
  rw [← evHom_apply ha]
  show substAlgHom ha.hasSubst (algebraMap k _ c) = _
  rw [AlgHom.commutes]; rfl

theorem ev_X {a : Fin m → Pt k n d} (ha : CZ a) (j : Fin m) (i : Fin d) : ev a (X (j, i) : PS k m d) = a j i :=
  subst_X ha.hasSubst (j, i)

theorem ev_zero' {a : Fin m → Pt k n d} (ha : CZ a) : ev a (0 : PS k m d) = 0 := by
  simp only [← evHom_apply ha, map_zero]

theorem constantCoeff_ev {a : Fin m → Pt k n d} (ha : CZ a) {f : PS k m d} (hf : constantCoeff f = 0) :
    constantCoeff (ev a f) = 0 :=
  constantCoeff_subst_eq_zero ha.hasSubst (fun p => ha p.1 p.2) hf

theorem CZ.ev {a : Fin m → Pt k n d} (ha : CZ a) {l : ℕ} {b : Fin l → Pt k m d} (hb : CZ b) :
    CZ (fun j i => ev a (b j i)) := fun j i => constantCoeff_ev ha (hb j i)

theorem ev_ev {l : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) {b : Fin l → Pt k m d} (hb : CZ b) (f : PS k l d) :
    ev a (ev b f) = ev (fun j i => ev a (b j i)) f := by
  unfold ev
  rw [subst_comp_subst_apply hb.hasSubst ha.hasSubst]

theorem ev_pt (f : PS k m d) : ev (fun j => pt k (n := m) d j) f = f := by
  unfold ev pt
  exact congrFun subst_self f

theorem CZ.pt : CZ (fun j => pt k (n := n) d j) := fun j i => by
  show constantCoeff (X (j, i) : PS k n d) = 0
  simp

theorem pderiv_ev {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) (v : Fin n × Fin d) :
    pderiv (R := k) v (ev a f) =
      ∑ p : Fin m × Fin d, ev a (pderiv (R := k) p f) * pderiv (R := k) v (a p.1 p.2) := by
  unfold ev
  exact pderiv_subst (a := fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2) f v

theorem ev_zeroFam (f : PS k m d) : ev (fun _ _ => (0 : PS k n d)) f = C (constantCoeff f) := by
  classical
  have hz : CZ (fun (_ : Fin m) (_ : Fin d) => (0 : PS k n d)) := fun _ _ => map_zero _
  ext e
  unfold ev
  rw [coeff_subst hz.hasSubst, finsum_eq_single _ 0]
  · simp [coeff_C, coeff_one]
  · intro x hx
    obtain ⟨p, hp⟩ : ∃ p, x p ≠ 0 := by
      by_contra hc; push Not at hc; exact hx (Finsupp.ext hc)
    rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hp) (zero_pow hp), map_zero, smul_zero]

end GlobalTheory.FormalLog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ConstantCoeffPrim
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace GlobalTheory.FormalLog

variable {k : Type} [CommRing k] [Algebra ℚ k] {τ : Type} [Fintype τ] [DecidableEq τ]

def prim (ω : τ → MvPowerSeries τ k) : MvPowerSeries τ k := fun m =>
  algebraMap ℚ k ((m.degree : ℚ)⁻¹) *
    ∑ w, if m w = 0 then 0 else coeff (m - Finsupp.single w 1) (ω w)

theorem coeff_prim (ω : τ → MvPowerSeries τ k) (m : τ →₀ ℕ) :
    coeff m (prim ω) = algebraMap ℚ k ((m.degree : ℚ)⁻¹) *
      ∑ w, if m w = 0 then 0 else coeff (m - Finsupp.single w 1) (ω w) := rfl

theorem constantCoeff_prim (ω : τ → MvPowerSeries τ k) : constantCoeff (prim ω) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_prim]
  simp

theorem degree_eq_sum (n : τ →₀ ℕ) : n.degree = ∑ w, n w := by
  rw [Finsupp.degree]
  exact Finset.sum_subset (Finset.subset_univ _) (fun w _ hw => by simpa using hw)

theorem pderiv_prim (ω : τ → MvPowerSeries τ k)
    (hω : ∀ a c, pderiv (R := k) c (ω a) = pderiv (R := k) a (ω c)) (v : τ) : pderiv (R := k) v (prim ω) = ω v := by
  ext n
  rw [coeff_pderiv, coeff_prim]
  have hterm : ∀ w, ((n v : k) + 1) *
      (if (n + Finsupp.single v 1 : τ →₀ ℕ) w = 0 then 0 else coeff (n + Finsupp.single v 1 - Finsupp.single w 1) (ω w)) =
      ((n w : k) + if w = v then 1 else 0) * coeff n (ω v) := by
    intro w
    by_cases hwv : w = v
    · subst hwv
      rw [if_neg (by simp), add_tsub_cancel_right, if_pos rfl]
    · have hsw : (Finsupp.single v 1 : τ →₀ ℕ) w = 0 := by rw [Finsupp.single_apply, if_neg (Ne.symm hwv)]
      rw [Finsupp.add_apply, hsw, add_zero, if_neg hwv]
      by_cases hnw : n w = 0
      · simp [hnw]
      · rw [if_neg hnw]
        have hle : Finsupp.single w 1 ≤ n := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hnw)
        set p := n - Finsupp.single w 1 with hp
        have hpn : p + Finsupp.single w 1 = n := tsub_add_cancel_of_le hle
        have hpv : p v = n v := by
          simp [hp, Finsupp.tsub_apply, Finsupp.single_apply, hwv]
        have hpw : p w + 1 = n w := by
          simp only [hp, Finsupp.tsub_apply, Finsupp.single_eq_same]; omega
        have h1 : n + Finsupp.single v 1 - Finsupp.single w 1 = p + Finsupp.single v 1 := by
          rw [← hpn, add_right_comm, add_tsub_cancel_right]
        have hc := congrArg (coeff p) (hω v w)
        rw [coeff_pderiv, coeff_pderiv, hpn, hpv] at hc
        rw [h1, mul_comm, ← hc, ← hpw]
        push_cast
        ring
  have hsum : ((n v : k) + 1) * ∑ w, (if (n + Finsupp.single v 1 : τ →₀ ℕ) w = 0 then 0 else
      coeff (n + Finsupp.single v 1 - Finsupp.single w 1) (ω w)) = ((n.degree : k) + 1) * coeff n (ω v) := by
    rw [Finset.mul_sum, Finset.sum_congr rfl fun w _ => hterm w, ← Finset.sum_mul, Finset.sum_add_distrib,
      Finset.sum_ite_eq', if_pos (Finset.mem_univ _), degree_eq_sum]
    push_cast; ring
  have hdeg : ((n + Finsupp.single v 1).degree : ℚ) = (n.degree : ℚ) + 1 := by
    rw [map_add (f := _), Finsupp.degree_single]; push_cast; ring
  rw [mul_comm, ← mul_assoc, mul_comm _ (algebraMap ℚ k _), mul_assoc, hsum, hdeg, ← mul_assoc]
  have : algebraMap ℚ k (((n.degree : ℚ) + 1)⁻¹) * ((n.degree : k) + 1) = 1 := by
    rw [show ((n.degree : k) + 1) = algebraMap ℚ k ((n.degree : ℚ) + 1) by simp, ← map_mul,
      inv_mul_cancel₀ (by positivity), map_one]
  rw [this, one_mul]

end GlobalTheory.FormalLog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesEvalOfPowMem
section
open IsLocalRing TensorProduct

namespace GlobalTheory

namespace NilpotentEval

variable {A : Type*} [CommRing A]

theorem pow_mul_le {K J : Ideal A} {N : ℕ} (h : J ^ N ≤ K) (n : ℕ) : J ^ (N * n) ≤ K ^ n := by
  rw [pow_mul]
  exact Ideal.pow_right_mono h n

theorem isHausdorff_of_pow_le {K J : Ideal A} {N : ℕ} (h : J ^ N ≤ K) [IsHausdorff K A] :
    IsHausdorff J A := by
  refine ⟨fun x hx => IsHausdorff.haus' (I := K) x fun n => ?_⟩
  have := hx (N * n)
  rw [SModEq.zero] at this ⊢
  simp only [smul_eq_mul, Ideal.mul_top] at this ⊢
  exact pow_mul_le h n this

theorem isPrecomplete_of_pow_le {K J : Ideal A} {N : ℕ} (h : J ^ N ≤ K) (hKJ : K ≤ J)
    [IsPrecomplete K A] : IsPrecomplete J A := by
  have h' : J ^ (N + 1) ≤ K := (Ideal.pow_le_pow_right N.le_succ).trans h
  refine ⟨fun f hf => ?_⟩
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hf ⊢
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := K) (fun n => f ((N + 1) * n)) fun {m n} hmn => by
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    exact pow_mul_le h' m (hf (Nat.mul_le_mul_left _ hmn))
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hL
  refine ⟨L, fun n => ?_⟩
  have h1 := hf (m := n) (n := (N + 1) * n) (Nat.le_mul_of_pos_left n N.succ_pos)
  have h2 := Ideal.pow_right_mono hKJ n (hL n)
  simpa using add_mem h1 h2

theorem exists_pow_sup_span_le (K : Ideal A) {σ : Type*} [Finite σ] (a : σ → A)
    (ha : ∀ j, ∃ M : ℕ, a j ^ M ∈ K) : ∃ N : ℕ, (K ⊔ Ideal.span (Set.range a)) ^ N ≤ K := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, Ideal.span (Set.range a) ^ N ≤ K :=
    Ideal.exists_pow_le_of_le_radical_of_fg
      (Ideal.span_le.2 (by rintro _ ⟨j, rfl⟩; exact ha j))
      (Submodule.fg_span (Set.finite_range a))
  refine ⟨N, ?_⟩
  rw [← Ideal.mk_ker (I := K), ← Ideal.map_eq_bot_iff_le_ker] at hN
  conv_rhs => rw [← Ideal.mk_ker (I := K)]
  rw [← Ideal.map_eq_bot_iff_le_ker, Ideal.map_pow, Ideal.map_sup, Ideal.map_quotient_self,
    bot_sup_eq, ← Ideal.map_pow]
  exact hN

end NilpotentEval


open NilpotentEval in
theorem mvPowerSeries_eval_of_pow_mem : ∀ (A : Type) [CommRing A] (K : Ideal A) (σ : Type) [Finite σ] (a : σ → A), (∀ j, ∃ M : ℕ, a j ^ M ∈ K) → (IsAdicComplete K A → ∀ (R : Type) [CommRing R] [Algebra R A], ∃ ψ : MvPowerSeries σ R →ₐ[R] A, ∀ j, ψ (MvPowerSeries.X j) = a j) ∧ (IsHausdorff K A → ∀ (T : Type) [CommRing T] (ψ ψ' : MvPowerSeries σ T →+* A), (∀ t, ψ (MvPowerSeries.C t) = ψ' (MvPowerSeries.C t)) → (∀ j, ψ (MvPowerSeries.X j) = a j) → (∀ j, ψ' (MvPowerSeries.X j) = a j) → ψ = ψ') := by
  intro A _ K σ _ a ha
  obtain ⟨N, hN⟩ := NilpotentEval.exists_pow_sup_span_le K a ha
  have hmem : ∀ j, a j ∈ K ⊔ Ideal.span (Set.range a) := fun j =>
    Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩)
  refine ⟨fun hK R _ _ => ?_, fun hK T _ ψ ψ' hC hψ hψ' => ?_⟩
  · haveI : IsAdicComplete (K ⊔ Ideal.span (Set.range a)) A :=
      { toIsHausdorff := NilpotentEval.isHausdorff_of_pow_le hN
        toIsPrecomplete := NilpotentEval.isPrecomplete_of_pow_le hN le_sup_left }
    exact ⟨mvEvalAdic R _ a hmem, mvEvalAdic_X _ a hmem⟩
  · haveI := NilpotentEval.isHausdorff_of_pow_le hN
    letI : Algebra T A := (ψ.comp MvPowerSeries.C).toAlgebra
    let φ : MvPowerSeries σ T →ₐ[T] A := { ψ with commutes' := fun _ => rfl }
    let φ' : MvPowerSeries σ T →ₐ[T] A := { ψ' with commutes' := fun t => (hC t).symm }
    have : φ = φ' := mvPowerSeries_algHom_ext_of_isHausdorff (K ⊔ Ideal.span (Set.range a))
      (fun j => by change ψ _ ∈ _; rw [hψ]; exact hmem j)
      (fun j => (hψ j).trans (hψ' j).symm)
    exact RingHom.ext fun g => DFunLike.congr_fun this g

end GlobalTheory
end

