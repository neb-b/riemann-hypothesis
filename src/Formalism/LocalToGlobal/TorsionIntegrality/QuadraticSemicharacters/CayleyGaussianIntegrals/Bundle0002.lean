module

public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.Bundle0001

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.CayleyIdentity
section
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

section Diag

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

@[reducible] def coreOf (H : Sesq V) (hH : IsHerm H) (hP : IsPosDef H) : InnerProductSpace.Core ℂ V where
  inner x y := H y x
  conj_inner_symm x y := (hH x y).symm
  re_inner_nonneg x := by
    by_cases h : x = 0
    · simp [h]
    · exact (hP x h).le
  add_left x y z := by simp
  smul_left x y r := by simp
  definite x hx := by
    by_contra h
    have := hP x h
    rw [hx] at this
    simp at this

theorem symm_diag [FiniteDimensional ℂ V] (H : Sesq V) (hH : IsHerm H) (hP : IsPosDef H) (T : V →ₗ[ℂ] V)
    (hT : ∀ x y, H (T x) y = H x (T y)) :
    ∃ (b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V) (t : Fin (Module.finrank ℂ V) → ℝ),
      (∀ i j, H (b i) (b j) = if i = j then 1 else 0) ∧ ∀ i, T (b i) = (t i : ℂ) • b i := by
  letI cd : InnerProductSpace.Core ℂ V := coreOf H hH hP
  letI : NormedAddCommGroup V := @InnerProductSpace.Core.toNormedAddCommGroup ℂ V _ _ _ cd
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore cd.toCore
  haveI : FiniteDimensional ℂ V := ‹FiniteDimensional ℂ V›
  have hS : LinearMap.IsSymmetric T := fun x y => (hT y x).symm
  let b := hS.eigenvectorBasis rfl
  refine ⟨b.toBasis, fun i => hS.eigenvalues rfl i, ?_, ?_⟩
  · intro i j
    rw [OrthonormalBasis.coe_toBasis]
    have h := (orthonormal_iff_ite.mp b.orthonormal) j i
    exact h.trans (if_congr eq_comm rfl rfl)
  · intro i
    rw [OrthonormalBasis.coe_toBasis]
    exact hS.apply_eigenvectorBasis rfl i

theorem cayley_diag [FiniteDimensional ℂ V] (H : Sesq V) (hH : IsHerm H) (hP : IsPosDef H) (Ae : V ≃ₗ[ℂ] V)
    (hA : ∀ u v, H (Ae u) v + H u (Ae v) = H (Ae u) (Ae v)) :
    ∃ (b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V) (l : Fin (Module.finrank ℂ V) → ℂ),
      (∀ i j, H (b i) (b j) = if i = j then 1 else 0) ∧ (∀ i, Ae (b i) = l i • b i) ∧ ∀ i, 0 < (l i).re := by
  set B : V →ₗ[ℂ] V := (Ae.symm : V ≃ₗ[ℂ] V).toLinearMap with hBdef
  have key : ∀ x y, H (B x) y + H x (B y) = H x y := by
    intro x y
    have h := hA (Ae.symm x) (Ae.symm y)
    simp only [LinearEquiv.apply_symm_apply] at h
    simpa [hBdef, add_comm] using h
  set T : V →ₗ[ℂ] V := Complex.I • ((2 : ℂ) • B - LinearMap.id) with hTdef
  have hTx : ∀ x, T x = Complex.I • ((2 : ℂ) • B x - x) := by
    intro x; simp [hTdef]
  have hT : ∀ x y, H (T x) y = H x (T y) := by
    intro x y
    rw [hTx, hTx]
    simp only [map_smul, map_sub, map_smulₛₗ, LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul,
      Complex.conj_I, RingHom.id_apply, map_ofNat]
    linear_combination (2 * Complex.I) * key x y
  obtain ⟨b, t, hb, hbt⟩ := symm_diag H hH hP T hT
  have hne : ∀ i, (1 - Complex.I * (t i : ℂ)) ≠ 0 := by
    intro i h
    have := congrArg Complex.re h
    simp at this
  refine ⟨b, fun i => 2 / (1 - Complex.I * (t i : ℂ)), hb, ?_, ?_⟩
  · intro i
    have h1 := hbt i
    rw [hTx] at h1
    have hw : B (b i) = ((1 - Complex.I * (t i : ℂ)) / 2) • b i := by
      linear_combination (norm := skip) (-Complex.I / 2) • h1
      match_scalars <;> (ring_nf; simp only [Complex.I_sq]; ring)
    apply Ae.symm.injective
    have hB' : Ae.symm (b i) = B (b i) := rfl
    rw [LinearEquiv.symm_apply_apply, map_smul, hB', hw, smul_smul,
      show 2 / (1 - Complex.I * (t i : ℂ)) * ((1 - Complex.I * (t i : ℂ)) / 2) = 1 by
        field_simp [hne i], one_smul]
  · intro i
    have hre : (1 - Complex.I * (t i : ℂ)).re = 1 := by simp
    have him : (1 - Complex.I * (t i : ℂ)).im = -t i := by simp
    have hns : Complex.normSq (1 - Complex.I * (t i : ℂ)) = 1 + t i ^ 2 := by
      rw [Complex.normSq_apply, hre, him]; ring
    have h2r : (2 : ℂ).re = 2 := by norm_num
    have h2i : (2 : ℂ).im = 0 := by norm_num
    rw [Complex.div_re, hre, him, hns, h2r, h2i, zero_mul, zero_div, add_zero, mul_one]
    positivity

theorem cayley_identity (H : Sesq V) (δ Ae : V ≃ₗ[ℂ] V) (hδ : IsIsom H H (δ : V →ₗ[ℂ] V))
    (hAe : ∀ x, Ae x = x - δ.symm x) (u v : V) : H (Ae u) v + H u (Ae v) = H (Ae u) (Ae v) := by
  have key : H (δ.symm u) (δ.symm v) = H u v := by
    have h := hδ (δ.symm u) (δ.symm v)
    simpa using h.symm
  simp only [hAe, map_sub, LinearMap.sub_apply]
  rw [key]
  ring

theorem unitary_diag [FiniteDimensional ℂ V] (H : Sesq V) (hH : IsHerm H) (hP : IsPosDef H) (δ Ae : V ≃ₗ[ℂ] V)
    (hδ : IsIsom H H (δ : V →ₗ[ℂ] V)) (hAe : ∀ x, Ae x = x - δ.symm x) :
    ∃ (b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V) (l : Fin (Module.finrank ℂ V) → ℂ),
      (∀ i j, H (b i) (b j) = if i = j then 1 else 0) ∧ (∀ i, Ae (b i) = l i • b i) ∧ ∀ i, 0 < (l i).re :=
  cayley_diag H hH hP Ae (cayley_identity H δ Ae hδ hAe)

theorem det_of_diag {n : Type*} [Fintype n] [DecidableEq n] (b : Module.Basis n ℂ V) (l : n → ℂ) (L : V →ₗ[ℂ] V)
    (hL : ∀ i, L (b i) = l i • b i) : LinearMap.det L = ∏ i, l i := by
  rw [← LinearMap.det_toMatrix b]
  have hM : LinearMap.toMatrix b b L = Matrix.diagonal l := by
    ext i j
    rw [LinearMap.toMatrix_apply, hL, map_smul, b.repr_self, Finsupp.smul_apply]
    rcases eq_or_ne i j with rfl | h
    · simp
    · simp [Matrix.diagonal_apply, Finsupp.single_apply, h, h.symm]
  rw [hM, Matrix.det_diagonal]

theorem form_of_diag {n : Type*} [Fintype n] [DecidableEq n] (H : Sesq V) (b : Module.Basis n ℂ V) (l : n → ℂ)
    (L : V →ₗ[ℂ] V) (hb : ∀ i j, H (b i) (b j) = if i = j then 1 else 0) (hL : ∀ i, L (b i) = l i • b i)
    (w : n → ℂ) :
    H (L (b.equivFun.symm w)) (b.equivFun.symm w) = ∑ i, l i * ((‖w i‖ : ℝ) : ℂ) ^ 2 := by
  rw [Module.Basis.equivFun_symm_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, hL, smul_smul, LinearMap.sum_apply, Finset.sum_apply,
    LinearMap.smul_apply, map_smulₛₗ, hb, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := Complex.mul_conj (w i)
  rw [Complex.normSq_eq_norm_sq] at h
  push_cast at h
  linear_combination (l i) * h

end Diag

end Formalism.L2.Th1.H
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.ExtensionFiltrationStable
section
noncomputable section
open scoped BigOperators ComplexConjugate Pointwise
open MeasureTheory Module

namespace Formalism.L2.Th1.H

private theorem exists_real_basis_span_int_eq_of_isLat {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (Λ : AddSubgroup V) (hΛ : IsLat Λ) :
    ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℝ V),
      (Submodule.span ℤ (Set.range b)).toAddSubgroup = Λ := by
  obtain ⟨hdisc, hspan⟩ := hΛ
  let L : Submodule ℤ V := AddSubgroup.toIntSubmodule Λ
  haveI : DiscreteTopology L := hdisc
  haveI : IsZLattice ℝ L := ⟨hspan⟩
  refine ⟨_, inferInstance, (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L, ?_⟩
  rw [Module.Basis.ofZLatticeBasis_span]
  rfl

theorem fundamentalDomainExists : FundDomain := by
  intro V _ _ _ _ _ μ _ Λ hΛ
  obtain ⟨ι, _, b, hb⟩ := exists_real_basis_span_int_eq_of_isLat Λ hΛ
  subst hb
  set L := (Submodule.span ℤ (Set.range b)).toAddSubgroup with hL
  set D := ZSpan.fundamentalDomain b with hDdef
  have hFD : IsAddFundamentalDomain L D μ := ZSpan.isAddFundamentalDomain b μ
  have hbdd : Bornology.IsBounded D := ZSpan.fundamentalDomain_isBounded b
  have hmeas : MeasurableSet D := ZSpan.fundamentalDomain_measurableSet b
  have hne : μ D ≠ 0 := ZSpan.measure_fundamentalDomain_ne_zero b
  have htop : μ D ≠ ⊤ := hbdd.measure_lt_top.ne
  refine ⟨D, hFD, hbdd, ENNReal.toReal_pos hne htop, ?_⟩
  intro Λ' hle hidx
  have hmem : ∀ v : V, v ∈ L → ∀ x : V, (v + x ∈ D ↔ v = -(ZSpan.floor b x : V)) := by
    intro v hv x
    have := ZSpan.vadd_mem_fundamentalDomain b ⟨v, hv⟩ x
    rw [Subtype.ext_iff, Submodule.coe_neg] at this
    exact this
  have hfl : ∀ x : V, (ZSpan.floor b x : V) ∈ L := fun x => (ZSpan.floor b x).2
  set H := Λ'.addSubgroupOf L with hH
  have hcardQ : Nat.card (L ⧸ H) = relIdx Λ' L := rfl
  haveI : Finite (L ⧸ H) := Nat.finite_of_card_ne_zero (by rw [hcardQ]; exact hidx)
  letI : Fintype (L ⧸ H) := Fintype.ofFinite _
  let rep : L ⧸ H → V := fun q => ((Quotient.out q : L) : V)
  have hrepL : ∀ q, rep q ∈ L := fun q => (Quotient.out q).2
  have hrep : ∀ q : L ⧸ H, ((Quotient.out q : L) : L ⧸ H) = q := fun q => QuotientAddGroup.out_eq' q
  have hdisj : Pairwise (Function.onFun Disjoint fun q : L ⧸ H => rep q +ᵥ D) := by
    intro p q hpq
    rw [Function.onFun, Set.disjoint_left]
    intro y hyp hyq
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] at hyp hyq
    have e1 := (hmem _ (L.neg_mem (hrepL p)) y).mp hyp
    have e2 := (hmem _ (L.neg_mem (hrepL q)) y).mp hyq
    apply hpq
    have hpq' : rep p = rep q := by
      rw [← neg_neg (rep p), e1, ← e2, neg_neg]
    rw [← hrep p, ← hrep q]
    congr 1
    exact Subtype.ext hpq'
  refine ⟨⋃ q : L ⧸ H, rep q +ᵥ D, ?_, ?_, ?_⟩
  · refine IsAddFundamentalDomain.mk' (MeasurableSet.iUnion fun q => hmeas.const_vadd _).nullMeasurableSet ?_
    intro x
    set l0 : V := -(ZSpan.floor b x : V) with hl0def
    have hl0 : l0 ∈ L := L.neg_mem (hfl x)
    set q0 : L ⧸ H := ((⟨-l0, L.neg_mem hl0⟩ : L) : L ⧸ H) with hq0def
    have hq0 : rep q0 + l0 ∈ Λ' := by
      have h1 := hrep q0
      rw [hq0def, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h1
      have h2 : -(-(rep q0) + -l0) ∈ Λ' := Λ'.neg_mem (by simpa [rep] using h1)
      rwa [neg_add_rev, neg_neg, neg_neg, add_comm] at h2
    refine ⟨⟨rep q0 + l0, hq0⟩, ?_, ?_⟩
    · show rep q0 + l0 + x ∈ ⋃ q : L ⧸ H, rep q +ᵥ D
      refine Set.mem_iUnion.mpr ⟨q0, ?_⟩
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
        show -rep q0 + (rep q0 + l0 + x) = l0 + x by abel]
      exact (hmem l0 hl0 x).mpr rfl
    · intro g hg
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hg
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] at hq
      have hgx : -rep q + (g : V) + x ∈ D := by
        rw [add_assoc]
        exact hq
      have hv : -rep q + (g : V) ∈ L := L.add_mem (L.neg_mem (hrepL q)) (hle g.2)
      have e1 : -rep q + (g : V) = l0 := (hmem _ hv x).mp hgx
      have hqq : q = q0 := by
        rw [← hrep q, hq0def, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
        have h3 : -rep q + -l0 = -(g : V) := by
          rw [← e1]
          abel
        have h4 : -(g : V) ∈ Λ' := Λ'.neg_mem g.2
        simpa [rep, h3] using h4
      apply Subtype.ext
      show (g : V) = rep q0 + l0
      rw [← hqq, ← e1]
      abel
  · exact Bornology.isBounded_iUnion.mpr fun q => hbdd.vadd (rep q)
  · have hμ : μ (⋃ q : L ⧸ H, rep q +ᵥ D) = (Fintype.card (L ⧸ H) : ENNReal) * μ D := by
      rw [measure_iUnion hdisj (fun q => hmeas.const_vadd _), tsum_fintype]
      simp [measure_vadd]
    rw [hμ, ENNReal.toReal_mul, ENNReal.toReal_natCast, ← hcardQ, Nat.card_eq_fintype_card]

theorem characterIntegral : CharIntegral := by
  intro V _ _ _ _ _ μ _ H _ hH Λ' D' hD v hv hv0
  set f : V → ℂ := fun z => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H v z : ℂ)) with hf
  have hadd : ∀ x y : V, altE H v (x + y) = altE H v x + altE H v y := by
    intro x y
    simp [altE, map_add (f := _)]
  have hmul : ∀ x y : V, f (x + y) = f x * f y := by
    intro x y
    simp only [hf, hadd]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hper : ∀ (g : Λ') (z : V), f (g +ᵥ z) = f z := by
    intro g z
    obtain ⟨m, hm⟩ := hv g g.2
    show f ((g : V) + z) = f z
    rw [hmul]
    have : f (g : V) = 1 := by
      simp only [hf, hm]
      have := Complex.exp_int_mul_two_pi_mul_I m
      rw [← this]
      congr 1
      push_cast
      ring
    rw [this, one_mul]
  by_cases hμ : μ D' = 0
  · exact setIntegral_measure_zero _ hμ
  haveI : Countable Λ' := by
    have hc := Measure.countable_meas_pos_of_disjoint_iUnion₀ (μ := μ) (As := fun g : Λ' => g +ᵥ D')
      (fun g => hD.nullMeasurableSet_vadd g) hD.aedisjoint
    have huniv : {g : Λ' | 0 < μ (g +ᵥ D')} = Set.univ := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      rw [measure_vadd]
      exact pos_iff_ne_zero.mpr hμ
    rw [huniv] at hc
    exact Set.countable_univ_iff.mp hc
  have htr : ∀ w : V, ∫ z in D', f z ∂μ = f w * ∫ z in D', f z ∂μ := by
    intro w
    have hD2 : IsAddFundamentalDomain Λ' (w +ᵥ D') μ := hD.vadd_of_comm w
    have e1 : ∫ z in w +ᵥ D', f z ∂μ = ∫ z in D', f z ∂μ := hD2.setIntegral_eq hD hper
    have e2 : ∫ z in w +ᵥ D', f z ∂μ = ∫ z in D', f (w + z) ∂μ := by
      rw [← Set.image_vadd]
      exact (measurePreserving_add_left μ w).setIntegral_image_emb (measurableEmbedding_addLeft w) f D'
    calc ∫ z in D', f z ∂μ = ∫ z in w +ᵥ D', f z ∂μ := e1.symm
      _ = ∫ z in D', f (w + z) ∂μ := e2
      _ = f w * ∫ z in D', f z ∂μ := by
        simp only [hmul]
        rw [integral_const_mul]
  have ha : 0 < (H v v).re := hH v hv0
  set c : ℂ := ((1 / (2 * (H v v).re) : ℝ) : ℂ) * Complex.I with hc
  have hw : altE H v (c • v) = -(1 / 2) := by
    simp only [altE, LinearMap.map_smulₛₗ, hc, smul_eq_mul, Complex.mul_im, map_mul, Complex.conj_ofReal,
      Complex.conj_I, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.neg_re, Complex.neg_im]
    field_simp
    ring
  have hfw : f (c • v) = -1 := by
    simp only [hf, hw]
    push_cast
    have : 2 * (Real.pi : ℂ) * Complex.I * -(1 / 2) = -(Real.pi * Complex.I) := by ring
    rw [this, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  have := htr (c • v)
  rw [hfw] at this
  linear_combination this / 2

end Formalism.L2.Th1.H
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.GaloisDescentSubspaces
section
noncomputable section
open scoped BigOperators ComplexConjugate Nat
open MeasureTheory

namespace Formalism.L2.Th1.H

theorem exp_neg_le_factorial_div {s : ℝ} (hs : 0 < s) (n : ℕ) : Real.exp (-s) ≤ (n ! : ℝ) / s ^ n := by
  have h1 : s ^ n / (n ! : ℝ) ≤ Real.exp s := Real.pow_div_factorial_le_exp s hs.le n
  have hf : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast n.factorial_pos
  have hp : 0 < s ^ n := pow_pos hs n
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos s) hp]
  rw [div_le_iff₀ hf] at h1
  linarith

theorem half_sq_sub_le {V : Type*} [NormedAddCommGroup V] (x z₀ : V) :
    ‖x‖ ^ 2 / 2 - ‖z₀‖ ^ 2 ≤ ‖x - z₀‖ ^ 2 := by
  have h : ‖x‖ ≤ ‖x - z₀‖ + ‖z₀‖ := by
    simpa using norm_add_le (x - z₀) z₀
  have h0 := norm_nonneg x
  have h1 := norm_nonneg (x - z₀)
  have h2 := norm_nonneg z₀
  have h3 : ‖x‖ ^ 2 ≤ (‖x - z₀‖ + ‖z₀‖) ^ 2 := pow_le_pow_left₀ h0 h 2
  nlinarith [sq_nonneg (‖x - z₀‖ - ‖z₀‖)]

theorem summable_gauss_of_discrete {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Λ : AddSubgroup V) [hd : DiscreteTopology Λ] {a : ℝ} (ha : 0 < a) :
    Summable fun x : Λ => Real.exp (-a * ‖(x : V)‖ ^ 2) := by
  classical
  let L : Submodule ℤ V := AddSubgroup.toIntSubmodule Λ
  have : DiscreteTopology L := hd
  set n : ℕ := Module.finrank ℤ L + 1 with hn
  have hsum : Summable fun z : L => ‖z‖⁻¹ ^ (2 * n) :=
    ZLattice.summable_norm_pow_inv L (2 * n) (by omega)
  have hsum' : Summable fun x : Λ => ‖(x : V)‖⁻¹ ^ (2 * n) := hsum
  have hite : Summable fun x : Λ => if x = 0 then (1 : ℝ) else 0 := (hasSum_ite_eq (0 : Λ) (1 : ℝ)).summable
  refine Summable.of_nonneg_of_le (fun x => (Real.exp_pos _).le) (fun x => ?_)
    ((hsum'.mul_left ((n ! : ℝ) / a ^ n)).add hite)
  by_cases hx : x = 0
  · subst hx
    simp
  · have hx' : 0 < ‖(x : V)‖ := by
      rw [norm_pos_iff]
      exact fun h => hx (Subtype.ext h)
    have hs : 0 < a * ‖(x : V)‖ ^ 2 := by positivity
    have h1 := exp_neg_le_factorial_div hs n
    rw [if_neg hx, add_zero]
    calc Real.exp (-a * ‖(x : V)‖ ^ 2) = Real.exp (-(a * ‖(x : V)‖ ^ 2)) := by rw [neg_mul]
      _ ≤ (n ! : ℝ) / (a * ‖(x : V)‖ ^ 2) ^ n := h1
      _ = (n ! : ℝ) / a ^ n * ‖(x : V)‖⁻¹ ^ (2 * n) := by
          rw [mul_pow, ← pow_mul, inv_pow]
          field_simp

theorem latticeGaussSummable : LatGaussSummable := by
  intro V _ _ _ Λ hΛ c r hc
  have : DiscreteTopology Λ := hΛ.1
  have hs : Summable fun x : Λ => Real.exp (-(c / 2) * ‖(x : V)‖ ^ 2) :=
    summable_gauss_of_discrete Λ (by positivity)
  refine ⟨fun x => Real.exp (c * r ^ 2) * Real.exp (-(c / 2) * ‖(x : V)‖ ^ 2), hs.mul_left _, ?_⟩
  intro x z₀ hz
  show _ ≤ Real.exp (c * r ^ 2) * Real.exp (-(c / 2) * ‖(x : V)‖ ^ 2)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 := half_sq_sub_le (x : V) z₀
  have h2 : ‖z₀‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg z₀) hz 2
  nlinarith

theorem continuous_diag {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V) :
    Continuous fun z => H z z := by
  let b := Module.finBasis ℂ V
  have h : (fun z => H z z) = fun z => ∑ j, conj (b.coord j z) * H.flip (b j) z := by
    funext z
    have e : H z z = H z (∑ j, b.repr z j • b j) := by rw [b.sum_repr z]
    rw [e]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smulₛₗ, smul_eq_mul, LinearMap.flip_apply, Module.Basis.coord_apply]
  rw [h]
  refine continuous_finsetSum _ fun j _ => ?_
  exact (Complex.continuous_conj.comp (LinearMap.continuous_of_finiteDimensional (b.coord j))).mul
    (LinearMap.continuous_of_finiteDimensional (H.flip (b j)))

theorem exp_neg_sq_le_japanese {a : ℝ} (ha : 0 < a) (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-a * t ^ 2) ≤ Real.exp a * (m ! : ℝ) * 2 ^ m / a ^ m * (1 + t) ^ (-((2 * m : ℕ) : ℝ)) := by
  have hs : 0 < a * (1 + t ^ 2) := by positivity
  have h1 := exp_neg_le_factorial_div hs m
  have h2 : (1 + t) ^ 2 ≤ 2 * (1 + t ^ 2) := by nlinarith [sq_nonneg (1 - t)]
  have h3 : (1 + t) ^ (2 * m) ≤ 2 ^ m * (1 + t ^ 2) ^ m := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h2 m
  have h4 : 0 < (1 + t) ^ (2 * m) := by positivity
  have h5 : 0 < (1 + t ^ 2) ^ m := by positivity
  have ham : 0 < a ^ m := pow_pos ha m
  have hf : (0 : ℝ) < (m ! : ℝ) := by exact_mod_cast m.factorial_pos
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  have e : -a * t ^ 2 = a + -(a * (1 + t ^ 2)) := by ring
  rw [e, Real.exp_add]
  have h6 : ((1 + t ^ 2) ^ m)⁻¹ ≤ 2 ^ m * ((1 + t) ^ (2 * m))⁻¹ := by
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ h5 h4]
    linarith
  calc Real.exp a * Real.exp (-(a * (1 + t ^ 2)))
      ≤ Real.exp a * ((m ! : ℝ) / (a * (1 + t ^ 2)) ^ m) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos a).le
    _ = Real.exp a * (m ! : ℝ) / a ^ m * ((1 + t ^ 2) ^ m)⁻¹ := by
        rw [mul_pow]; field_simp
    _ ≤ Real.exp a * (m ! : ℝ) / a ^ m * (2 ^ m * ((1 + t) ^ (2 * m))⁻¹) :=
        mul_le_mul_of_nonneg_left h6 (by positivity)
    _ = Real.exp a * (m ! : ℝ) * 2 ^ m / a ^ m * ((1 + t) ^ (2 * m))⁻¹ := by ring

theorem GaussIntegrable_of (h : FormNorm) : GaussIntegrable := by
  intro V _ _ _ _ _ μ _ H hH hP c hc
  obtain ⟨c₀, C, hc₀, _, hb⟩ := h V H hH hP
  have hcont : Continuous fun z => Real.exp (-c * (H z z).re) :=
    Real.continuous_exp.comp (continuous_const.mul (Complex.continuous_re.comp (continuous_diag H)))
  set m : ℕ := Module.finrank ℝ V + 1 with hm
  have hJ : Integrable (fun z : V => (1 + ‖z‖) ^ (-((2 * m : ℕ) : ℝ))) μ :=
    integrable_one_add_norm (by
      have : Module.finrank ℝ V < 2 * m := by omega
      exact_mod_cast this)
  have ha : 0 < c * c₀ := by positivity
  have hint : Integrable (fun z => Real.exp (-c * (H z z).re)) μ := by
    refine Integrable.mono' (hJ.const_mul (Real.exp (c * c₀) * (m ! : ℝ) * 2 ^ m / (c * c₀) ^ m))
      hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine le_trans (Real.exp_le_exp.mpr ?_) (exp_neg_sq_le_japanese ha m (norm_nonneg z))
    have := (hb z).1
    nlinarith
  refine ⟨hint, ?_⟩
  rw [integral_pos_iff_support_of_nonneg (fun z => (Real.exp_pos _).le) hint]
  have hsupp : Function.support (fun z => Real.exp (-c * (H z z).re)) = Set.univ := by
    ext z
    simp [Real.exp_ne_zero]
  rw [hsupp]
  exact isOpen_univ.measure_pos μ Set.univ_nonempty

end Formalism.L2.Th1.H
end
end

