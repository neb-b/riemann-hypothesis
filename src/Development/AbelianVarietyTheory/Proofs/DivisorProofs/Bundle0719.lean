module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
public import Formalism.MeanHeightDescent.AverageDegreeBounds.GlobalBoundRefinements
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0418
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightGapsBlockAndBar
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop

theorem le_two_mul_ediv {x m T h : ℤ} (hm : 0 < m) (hT : 4 * m ≤ 5 * T) (hh : 0 ≤ h)
    (hx : 3 * h ≤ 4 * (x - m)) : h ≤ 2 * T * (x / m) := by
  have h1 : m * (x / m) + x % m = x := Int.mul_ediv_add_emod x m
  have h2 : x % m < m := Int.emod_lt_of_pos x hm
  have h3 : 0 ≤ x / m := Int.ediv_nonneg (by omega) hm.le
  have h4 : 4 * m * (x / m) ≤ 5 * T * (x / m) := mul_le_mul_of_nonneg_right hT h3
  have h5 : 0 ≤ T * (x / m) := mul_nonneg (by omega) h3
  nlinarith

theorem divided_gaps : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : Wts ι N), W.Hyp → W.IsDiv → ∀ τ (a b : Fin N), (b : ℕ) = a + 1 → (((b : ℕ) ≠ W.p → (W.T : ℤ) + W.Dd + 2 + 2 * N ≤ W.u1 τ a - W.u1 τ b) ∧ ((b : ℕ) = W.p → W.h0 ≤ 2 * W.T * (W.u1 τ a - W.u1 τ b) ∧ W.h0 ≤ 4 * W.T * (W.u1 τ a - W.u1 τ b - 3 * N)) ∧ ((b : ℕ) ≠ W.p → W.kc ≤ (a : ℕ) → W.h0 ≤ 4 * W.T * (W.u1 τ a - W.u1 τ b))) := by
  intro ι _ N W H hD τ a b hab
  have hq := (hD τ).2 a b hab
  obtain ⟨g1, g2, g3⟩ := H.h4 τ a b hab
  obtain ⟨k1, k2⟩ := H.h2
  have c0 := H.weightConst_nonneg
  have h1 : 4 * (W.Dd : ℤ) + 4 ≤ W.T := by exact_mod_cast H.h1
  have hm : (0 : ℤ) < (W.T : ℤ) + W.Dd + 1 := by positivity
  have hT : 4 * ((W.T : ℤ) + W.Dd + 1) ≤ 5 * (W.T : ℤ) := by omega
  have hh : 0 ≤ W.h0 := by omega
  refine ⟨fun hb => ?_, fun hb => ?_, fun hb ha => ?_⟩
  · rw [hq, if_neg hb]
    refine Int.le_ediv_of_mul_le hm ?_
    have := g1 hb
    have h0 : (0 : ℤ) ≤ (W.T : ℤ) + W.Dd + 2 + 2 * N := by positivity
    nlinarith
  · have := g3 hb
    have key : W.h0 ≤ 2 * W.T * (W.u1 τ a - W.u1 τ b) := by
      rw [hq, if_pos hb]
      exact le_two_mul_ediv hm hT hh (by omega)
    exact ⟨key, by nlinarith⟩
  · have := g2 ha
    have key : W.h0 ≤ 2 * W.T * (W.u1 τ a - W.u1 τ b) := by
      rw [hq, if_neg hb]
      exact le_two_mul_ediv hm hT hh (by omega)
    nlinarith

end GlobalTheory.MeanTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfOddEllipticOfTendsto
section
open Filter PeriodPair Polynomial
open scoped Topology

namespace GlobalTheory

private lemma eq_zero_of_tendsto_eval_cobounded {B : ℂ[X]} {l : Filter ℂ} [l.NeBot] {u : ℂ → ℂ}
    (hu : Tendsto u l (Bornology.cobounded ℂ))
    (h : Tendsto (fun z ↦ B.eval (u z)) l (𝓝 0)) : B = 0 := by
  by_cases hd : 0 < B.degree
  · exfalso
    have h1 := B.tendsto_norm_atTop hd (tendsto_norm_atTop_iff_cobounded.mpr hu)
    have h2 := h.norm
    exact h1.not_tendsto (disjoint_nhds_atTop _).symm h2
  · rw [eq_C_of_degree_le_zero (not_lt.mp hd)] at h ⊢
    simp only [eval_C] at h
    rw [tendsto_nhds_unique tendsto_const_nhds h, C_0]

private lemma exists_eq_mul_of_three_roots {A : ℂ[X]} {a b c : ℂ} (hab : b ≠ a) (hac : c ≠ a)
    (hbc : c ≠ b) (ha : A.eval a = 0) (hb : A.eval b = 0) (hc : A.eval c = 0) :
    ∃ B : ℂ[X], A = (X - C a) * ((X - C b) * ((X - C c) * B)) := by
  obtain ⟨A₁, rfl⟩ := dvd_iff_isRoot.mpr ha
  have hb₁ : A₁.eval b = 0 := by simpa [sub_eq_zero, hab] using hb
  obtain ⟨A₂, rfl⟩ := dvd_iff_isRoot.mpr hb₁
  have hc₂ : A₂.eval c = 0 := by simpa [sub_eq_zero, hac, hbc] using hc
  obtain ⟨B, rfl⟩ := dvd_iff_isRoot.mpr hc₂
  exact ⟨B, rfl⟩

theorem eq_zero_of_odd_elliptic_of_tendsto : ∀ (L : PeriodPair) (f : ℂ → ℂ), (∀ z, z ∉ L.lattice → DifferentiableAt ℂ f z) → (∀ z l, z ∉ L.lattice → l ∈ L.lattice → f (z + l) = f z) → (∀ z, z ∉ L.lattice → f (-z) = -f z) → Filter.Tendsto (fun z : ℂ => z ^ 3 * f z) (𝓝[≠] 0) (𝓝 0) → ∀ z, z ∉ L.lattice → f z = 0 := by
  classical
  intro L f hd hp ho ht
  let g : ℂ → ℂ := fun z ↦ if z ∈ L.lattice then 0 else f z ^ 2
  have hgd : ∀ z ∉ L.lattice, DifferentiableAt ℂ g z := fun z hz ↦ by
    refine ((hd z hz).pow 2).congr_of_eventuallyEq ?_
    filter_upwards [eventually_notMem_periodLattice L hz] with w hw
    simp [g, hw]
  have hgp : ∀ z, ∀ l ∈ L.lattice, g (z + l) = g z := fun z l hl ↦ by
    by_cases hz : z ∈ L.lattice
    · simp [g, hz, add_mem hz hl]
    · simp [g, hz, L.lattice.add_mem_iff_left hl, hp z l hz hl]
  have hge : ∀ z, g (-z) = g z := fun z ↦ by
    by_cases hz : z ∈ L.lattice
    · simp [g, hz]
    · simp [g, hz, ho z hz]
  have hgt : Tendsto (fun z : ℂ ↦ z ^ 6 * g z) (𝓝[≠] 0) (𝓝 0) := by
    have h1 := ht.pow 2
    rw [zero_pow two_ne_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ne_notMem_periodLattice L 0] with w hw
    simp only [g, hw, if_false]
    ring
  have hgm : MeromorphicAt g 0 := by
    refine ⟨6, Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_⟩
    · filter_upwards [eventually_ne_notMem_periodLattice L 0] with w hw
      have := hgd w hw
      fun_prop
    · rw [continuousAt_iff_punctured_nhds]
      simpa using hgt
  obtain ⟨A, hA⟩ := exists_eq_polynomial_weierstrassP L hgm hgd hgp hge
  have hhalf : ∀ z ∉ L.lattice, z + z ∈ L.lattice → A.eval (℘[L] z) = 0 := fun z hz h2 ↦ by
    have h1 := hp (-z) (z + z) (by simpa using hz) h2
    rw [ho z hz, show -z + (z + z) = z by ring, CharZero.eq_neg_self_iff] at h1
    rw [← hA z hz]
    simp [g, h1]
  have key : ∀ a b : ℚ, (a * L.ω₁ + b * L.ω₂ : ℂ) ∈ L.lattice ↔ a.den = 1 ∧ b.den = 1 :=
    fun a b ↦ L.mul_ω₁_add_mul_ω₂_mem_lattice
  let p : ℚ → ℚ → ℂ := fun a b ↦ a * L.ω₁ + b * L.ω₂
  have padd : ∀ a b c d, p a b + p c d = p (a + c) (b + d) := fun a b c d ↦ by
    simp only [p]; push_cast; ring
  have psub : ∀ a b c d, p a b - p c d = p (a - c) (b - d) := fun a b c d ↦ by
    simp only [p]; push_cast; ring
  have pm : ∀ a b, p a b ∈ L.lattice ↔ a.den = 1 ∧ b.den = 1 := key
  have n1 : p (1 / 2) 0 ∉ L.lattice := by rw [pm]; norm_num
  have n2 : p 0 (1 / 2) ∉ L.lattice := by rw [pm]; norm_num
  have n3 : p (1 / 2) (1 / 2) ∉ L.lattice := by rw [pm]; norm_num
  obtain ⟨B, hB⟩ := exists_eq_mul_of_three_roots (A := A) (a := ℘[L] (p (1 / 2) 0))
    (b := ℘[L] (p 0 (1 / 2))) (c := ℘[L] (p (1 / 2) (1 / 2)))
    (by rw [Ne, weierstrassP_eq_iff L n2 n1, padd, psub, pm, pm]; norm_num)
    (by rw [Ne, weierstrassP_eq_iff L n3 n1, padd, psub, pm, pm]; norm_num)
    (by rw [Ne, weierstrassP_eq_iff L n3 n2, padd, psub, pm, pm]; norm_num)
    (hhalf _ n1 (by rw [padd, pm]; norm_num))
    (hhalf _ n2 (by rw [padd, pm]; norm_num))
    (hhalf _ n3 (by rw [padd, pm]; norm_num))
  set a := ℘[L] (p (1 / 2) 0)
  set b := ℘[L] (p 0 (1 / 2))
  set c := ℘[L] (p (1 / 2) (1 / 2))
  let w : ℂ → ℂ := fun z ↦ z ^ 2 * L.weierstrassPExcept 0 z + 1
  have hw : AnalyticAt ℂ w 0 := by fun_prop
  have hw' : ∀ z ≠ 0, w z = z ^ 2 * ℘[L] z := fun z hz ↦ by
    simpa [hz, w] using (L.ite_eq_one_sub_sq_mul_weierstrassP 0 (zero_mem _) z).symm
  let q : ℂ → ℂ := fun z ↦ (w z - z ^ 2 * a) * ((w z - z ^ 2 * b) * (w z - z ^ 2 * c))
  have hq : ContinuousAt q 0 := by
    have := hw.continuousAt
    fun_prop
  have hq0 : q 0 = 1 := by simp [q, w]
  have hq1 : Tendsto q (𝓝[≠] 0) (𝓝 1) := hq0 ▸ hq.tendsto.mono_left nhdsWithin_le_nhds
  have hB0 : B = 0 := by
    refine eq_zero_of_tendsto_eval_cobounded (tendsto_weierstrassP_cobounded L (zero_mem _)) ?_
    have h1 := hgt.div hq1 one_ne_zero
    rw [zero_div] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ne_notMem_periodLattice L 0, self_mem_nhdsWithin,
      hq1.eventually_ne one_ne_zero] with z hz hz0 hqz
    rw [Pi.div_apply, div_eq_iff hqz, hA z hz, hB]
    simp only [q, hw' z hz0, eval_mul, eval_sub, eval_X, eval_C]
    ring
  intro z hz
  have h1 := hA z hz
  rw [hB, hB0] at h1
  simpa [g, hz] using h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalVanishingCohomology
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd

noncomputable section

namespace GlobalTheory.CurveNbhdKill

def locKer {B : Type} [CommRing B] (f : B) (P : Ideal B) (hP : P.IsPrime) : Ideal B :=
  GlobalTheory.LocalSaturationContraction.satAt f P (hP := hP)

theorem locKer_coprime {B : Type} [CommRing B] [IsDedekindDomain B] (f : B) (hf : f ≠ 0) (P P' : Ideal B)
    (hP : P.IsMaximal) (hP' : P'.IsMaximal) (hne : P ≠ P') :
    IsCoprime (locKer f P hP.isPrime) (locKer f P' hP'.isPrime) := by
  obtain ⟨N, hN⟩ := GlobalTheory.T.dedekind_power_localization B f hf P hP
  obtain ⟨N', hN'⟩ := GlobalTheory.T.dedekind_power_localization B f hf P' hP'
  have hc : IsCoprime P P' := Ideal.isCoprime_iff_sup_eq.2 (Ideal.IsMaximal.coprime_of_ne hP hP' hne)
  have hc' : IsCoprime (P ^ N) (P' ^ N') := hc.pow
  rw [Ideal.isCoprime_iff_sup_eq] at hc' ⊢
  exact eq_top_iff.2 (hc' ▸ sup_le_sup (fun b hb => hN b hb) (fun b hb => hN' b hb))

theorem mem_of_forall_locKer {B : Type} [CommRing B] (f b : B)
    (h : ∀ P : Ideal B, P.IsMaximal → f ∈ P → ∃ s : B, s ∉ P ∧ s * b ∈ Ideal.span {f}) :
    b ∈ Ideal.span {f} := by
  let J : Ideal B := Submodule.comap (LinearMap.mulRight B b) (Ideal.span {f})
  have hJ : J = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hne
    have hfJ : f ∈ J := by
      rw [Submodule.mem_comap, LinearMap.mulRight_apply]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f)
    obtain ⟨s, hs, hsb⟩ := h M hM (hJM hfJ)
    exact hs (hJM (by rw [Submodule.mem_comap, LinearMap.mulRight_apply]; exact hsb))
  have h1 : (1 : B) ∈ J := hJ ▸ Submodule.mem_top
  simpa [J] using h1

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, Spec.map_comp]

variable (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B]
  [Algebra.FiniteType k B]

theorem onePoint (hq : IsUnit (q : k)) (f : B) (hf : f ≠ 0) (m i : ℤ) (hm : 1 ≤ m) (y : Ht q (sp B) m i)
    (P : Ideal B) (hP : P.IsMaximal) (hfP : f ∈ P) :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra B A) (_ : Algebra.Etale B A),
      (∀ a : A, ∃ b : B, a - algebraMap B A b ∈ Ideal.span {algebraMap B A f}) ∧
      (∀ b : B, algebraMap B A b ∈ Ideal.span {algebraMap B A f} ↔ b ∈ locKer f P hP.isPrime) ∧
      pull _ (spMap (algebraMap B A)) _ _ y = 0 := by
  have hqB : IsUnit (q : B) := by simpa using hq.map (algebraMap k B)
  have hsep := GlobalTheory.T.residueField_atPrime_isSepClosed_of_finiteType k B P
  obtain ⟨D, _, _, _, Q, hQ, hQP, hres, hy⟩ := GlobalTheory.T.etale_neighbourhood_kills_class q B hqB P hsep m i (by omega) y
  obtain ⟨g, hS, hK⟩ := GlobalTheory.T.away_quotient_span_eq_localization B D f hf P hP hfP Q hQ hQP hres
  refine ⟨Localization.Away g, inferInstance, inferInstance, inferInstance, hS, hK, ?_⟩
  rw [IsScalarTower.algebraMap_eq B D (Localization.Away g), spMap_comp', pull_comp, hy, map_zero]

theorem exists_nbhd_pull_eq_zero : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ¬ IsUnit f → ∀ (m i : ℤ), 1 ≤ m → ∀ y : Ht q (sp B) m i, ∃ (A' : Type) (_ : CommRing A') (_ : Algebra B A') (_ : Algebra.Etale B A'), IsNbhd B A' f ∧ pull _ (spMap (algebraMap B A')) _ _ y = 0 := by
  intro q _ k B _ _ _ _ _ _ hq f hf hfu m i hm y
  let Pt := {P : Ideal B // P.IsMaximal ∧ f ∈ P}
  haveI : Finite Pt := (GlobalTheory.T.finite_maximal_containing B f hf).to_subtype
  letI : Fintype Pt := Fintype.ofFinite Pt
  let K : Pt → Ideal B := fun x => locKer f x.1 x.2.1.isPrime
  have key : ∀ T : Finset Pt, T.Nonempty → ∃ (A : Type) (_ : CommRing A) (_ : Algebra B A) (_ : Algebra.Etale B A),
      (∀ a : A, ∃ b : B, a - algebraMap B A b ∈ Ideal.span {algebraMap B A f}) ∧
      (∀ b : B, algebraMap B A b ∈ Ideal.span {algebraMap B A f} ↔ b ∈ ⨅ x ∈ T, K x) ∧
      pull _ (spMap (algebraMap B A)) _ _ y = 0 := by
    intro T hT
    induction hT using Finset.Nonempty.cons_induction with
    | singleton x =>
      obtain ⟨A, _, _, _, hS, hK, hy⟩ := onePoint q k B hq f hf m i hm y x.1 x.2.1 x.2.2
      exact ⟨A, inferInstance, inferInstance, inferInstance, hS, fun b => by simpa [K] using hK b, hy⟩
    | cons x T hx hT ih =>
      obtain ⟨A₁, _, _, _, hS₁, hK₁, hy₁⟩ := ih
      obtain ⟨A₂, _, _, _, hS₂, hK₂, hy₂⟩ := onePoint q k B hq f hf m i hm y x.1 x.2.1 x.2.2
      have hcop : IsCoprime (⨅ j ∈ T, K j) (K x) := by
        refine (Ideal.isCoprime_biInf fun j hj => ?_).symm
        refine locKer_coprime f hf x.1 j.1 x.2.1 j.2.1 fun h => hx ?_
        have : x = j := Subtype.ext h
        exact this ▸ hj
      obtain ⟨hS, hK, hy⟩ := GlobalTheory.T.approximation_quotients_agree q B A₁ A₂ f _ _ m i y hcop hS₁ hK₁ hS₂ hK₂ hy₁ hy₂
      refine ⟨A₁ × A₂, inferInstance, inferInstance, GlobalTheory.T.etale_prod_of_etale B A₁ A₂ inferInstance inferInstance, hS, fun b => ?_, hy⟩
      rw [hK b, Finset.cons_eq_insert, Finset.iInf_insert, inf_comm]
  have hne : (Finset.univ : Finset Pt).Nonempty := by
    have hspan : Ideal.span {f} ≠ ⊤ := fun h => hfu (Ideal.span_singleton_eq_top.1 h)
    obtain ⟨M, hM, hfM⟩ := Ideal.exists_le_maximal _ hspan
    exact ⟨⟨M, hM, hfM (Ideal.mem_span_singleton_self f)⟩, Finset.mem_univ _⟩
  obtain ⟨A, _, _, _, hS, hK, hy⟩ := key Finset.univ hne
  refine ⟨A, inferInstance, inferInstance, inferInstance, ⟨hS, fun b hb => ?_⟩, hy⟩
  have hb' := (hK b).1 hb
  refine mem_of_forall_locKer f b fun P hP hfP => ?_
  have := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hb' ⟨P, hP, hfP⟩) (Finset.mem_univ _)
  exact this

end GlobalTheory.CurveNbhdKill

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EulerFactorEqOneOfExpAt
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
open scoped NNReal ENNReal

noncomputable section

attribute [local instance 2000] GlobalTheory.SplitWeil.matrixMeasurableSpace

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

def StdSupp (ϖ : kˣ) (c : ℕ) (x : Matrix (Fin n ⊕ Fin n') (Fin n) k) : Prop :=
  (∀ i j, x.toRows₁ i j ∈ 𝒪[k]) ∧ valuation k x.toRows₁.det = 1 ∧ ∀ i j, x.toRows₂ i j ∈ cball (ϖ ^ c)

theorem StdSupp.det_ne {ϖ : kˣ} {c : ℕ} {x : Matrix (Fin n ⊕ Fin n') (Fin n) k} (h : StdSupp ϖ c x) :
    x.toRows₁.det ≠ 0 := fun h0 => by
  have := h.2.1
  rw [h0, map_zero] at this
  exact zero_ne_one this


open Classical in
def stdDatum (μ : kˣ →* ℂˣ) (ϖ : kˣ) (c : ℕ) (x : Matrix (Fin n ⊕ Fin n') (Fin n) k) : ℂ :=
  if h : StdSupp ϖ c x then (((μ (Units.mk0 _ h.det_ne))⁻¹ : ℂˣ) : ℂ) else 0

end GlobalTheory.StdLocZeta

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

end GlobalTheory.StdLocZeta

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

end GlobalTheory.StdLocZeta

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

end GlobalTheory.StdLocZeta

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

end GlobalTheory.StdLocZeta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirigidifiedBundleOfDescent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section
namespace GlobalTheory.UPel.HT.Hecke

theorem left_comp_of_comp {S : Scheme.{0}} {X Y Z : Over S} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (e : f ≫ g = h) :
    f.left ≫ g.left = h.left := by
  rw [← Over.comp_left, e]

theorem exists_birigidified_of_descent : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A'), IsMonHom ψ → ∀ (m : ℕ) (P₀ : LB (G2 A').left), P₀.IsLB → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P₀.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → ∃ P' : LB (G2 A').left, P'.IsLB ∧ (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) ∧ (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) ∧ LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) := by
  intro p _ D R _ b M S s o A' _ _ ψ hψ m P₀ hP₀ H
  let φ : Fin 4 → ((G2 A').left ⟶ (G2 A').left) := ![𝟙 _, (lift (fst A' A') (1 : G2 A' ⟶ A')).left,
    (lift (1 : G2 A' ⟶ A') (snd A' A')).left, (lift (1 : G2 A' ⟶ A') (1 : G2 A' ⟶ A')).left]
  let ε : Fin 4 → ℤ := ![1, -1, -1, 1]
  have hε : ε 0 = 1 ∧ ε 1 = -1 ∧ ε 2 = -1 ∧ ε 3 = 1 := ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨LB.LinComb P₀ φ ε, DVR.linComb_isLB P₀ hP₀ φ ε, ?_, ?_, ?_⟩
  · refine GlobalTheory.PrimNorm.hasGen_nested hP₀ φ ε (fun _ : PUnit => _) (fun _ => 1) ?_
    have e0 : (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ 0 = (lift (1 : A' ⟶ A') (𝟙 A')).left := Category.comp_id _
    have e1 : (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ 1 = (lift (1 : A' ⟶ A') (1 : A' ⟶ A')).left :=
      left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
    have e2 : (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ 2 = (lift (1 : A' ⟶ A') (𝟙 A')).left :=
      left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
    have e3 : (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ 3 = (lift (1 : A' ⟶ A') (1 : A' ⟶ A')).left :=
      left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
    rw [Fintype.prod_unique, zpow_one, Fin.prod_univ_four, e0, e1, e2, e3]
    rw [hε.1, hε.2.1, hε.2.2.1, hε.2.2.2, zpow_one, zpow_one, zpow_neg_one, zpow_neg_one,
      mul_right_comm _ _ (GlobalTheory.PrimNorm.cls P₀ _)⁻¹, mul_inv_cancel, _root_.one_mul, inv_mul_cancel]
  · refine GlobalTheory.PrimNorm.hasGen_nested hP₀ φ ε (fun _ : PUnit => _) (fun _ => 1) ?_
    have e0 : (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ 0 = (lift (𝟙 A') (1 : A' ⟶ A')).left := Category.comp_id _
    have e1 : (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ 1 = (lift (𝟙 A') (1 : A' ⟶ A')).left :=
      left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
    have e2 : (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ 2 = (lift (1 : A' ⟶ A') (1 : A' ⟶ A')).left :=
      left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
    have e3 : (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ 3 = (lift (1 : A' ⟶ A') (1 : A' ⟶ A')).left :=
      left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
    rw [Fintype.prod_unique, zpow_one, Fin.prod_univ_four, e0, e1, e2, e3]
    rw [hε.1, hε.2.1, hε.2.2.1, hε.2.2.2, zpow_one, zpow_one, zpow_neg_one, zpow_neg_one,
      mul_inv_cancel, _root_.one_mul, inv_mul_cancel]
  · haveI := hψ
    let ρ : Fin 4 → ((G2 o.A).left ⟶ (G2 o.A).left) := ![𝟙 _, (lift (fst o.A o.A) (1 : G2 o.A ⟶ o.A)).left,
      (lift (1 : G2 o.A ⟶ o.A) (snd o.A o.A)).left, (lift (1 : G2 o.A ⟶ o.A) (1 : G2 o.A ⟶ o.A)).left]
    have hsq : ∀ k, sq2 ψ ≫ φ k = ρ k ≫ sq2 ψ := by
      intro k
      fin_cases k
      · exact (Category.comp_id _).trans (Category.id_comp _).symm
      all_goals
        refine (left_comp_of_comp rfl).trans ((left_comp_of_comp ?_).symm)
        apply CartesianMonoidalCategory.hom_ext <;> simp
    have hP := o.isLB
    have cls1 : ∀ (r : (G2 o.A).left ⟶ (G2 o.A).left),
        GlobalTheory.MulPull.HasGen o.P (fun _ : PUnit => r) (fun _ => 1) → GlobalTheory.PrimNorm.cls o.P r = 1 := by
      intro r h
      have := (GlobalTheory.PrimNorm.hasGen_iff hP _ _).1 h
      rwa [Fintype.prod_unique, zpow_one] at this
    have h1 : GlobalTheory.PrimNorm.cls o.P (ρ 1) = 1 := by
      refine cls1 _ ?_
      have h := GlobalTheory.MulPull.HasGen.pull (φ := fun _ : PUnit => (lift (𝟙 o.A) (1 : o.A ⟶ o.A)).left)
        (ε := fun _ => 1) o.rig₂ (fst o.A o.A).left
      have e : (fst o.A o.A).left ≫ (lift (𝟙 o.A) (1 : o.A ⟶ o.A)).left = ρ 1 :=
        left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
      simpa only [e] using h
    have h2 : GlobalTheory.PrimNorm.cls o.P (ρ 2) = 1 := by
      refine cls1 _ ?_
      have h := GlobalTheory.MulPull.HasGen.pull (φ := fun _ : PUnit => (lift (1 : o.A ⟶ o.A) (𝟙 o.A)).left)
        (ε := fun _ => 1) o.rig₁ (snd o.A o.A).left
      have e : (snd o.A o.A).left ≫ (lift (1 : o.A ⟶ o.A) (𝟙 o.A)).left = ρ 2 :=
        left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
      simpa only [e] using h
    have h3 : GlobalTheory.PrimNorm.cls o.P (ρ 3) = 1 := by
      refine cls1 _ ?_
      have h := GlobalTheory.MulPull.HasGen.pull (φ := fun _ : PUnit => (lift (𝟙 o.A) (1 : o.A ⟶ o.A)).left)
        (ε := fun _ => 1) o.rig₂ (fst o.A o.A ≫ (1 : o.A ⟶ o.A)).left
      have e : (fst o.A o.A ≫ (1 : o.A ⟶ o.A)).left ≫ (lift (𝟙 o.A) (1 : o.A ⟶ o.A)).left = ρ 3 :=
        left_comp_of_comp (by apply CartesianMonoidalCategory.hom_ext <;> simp)
      simpa only [e] using h
    have L1 : (lbPow o.P m).IsLB := DVR.linComb_isLB o.P hP _ _
    have L2 : (LB.LinComb (lbPow o.P m) ρ ε).IsLB := DVR.linComb_isLB _ L1 _ _
    have L3 : (LB.LinComb P₀ (fun k => ρ k ≫ sq2 ψ) ε).IsLB := DVR.linComb_isLB _ hP₀ _ _
    have L4 : ((LB.LinComb P₀ φ ε).pull (sq2 ψ)).IsLB := DVR.linComb_isLB _ (DVR.linComb_isLB _ hP₀ _ _) _ _
    have I1 : LBIso (lbPow o.P m) (LB.LinComb (lbPow o.P m) ρ ε) := by
      refine LBIso.symm (GlobalTheory.PrimNorm.lbIso_nested hP (fun _ : Fin m => 𝟙 _) (fun _ => 1) ρ ε
        (fun _ : Fin m => 𝟙 _) (fun _ => 1) ?_)
      simp only [Category.comp_id, zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Fin.prod_univ_four, h1, h2, h3, one_pow, one_zpow, _root_.mul_one, hε.1]
      rfl
    obtain ⟨w, hw⟩ := H
    have I2 : LBIso (LB.LinComb (lbPow o.P m) ρ ε) (LB.LinComb P₀ (fun k => ρ k ≫ sq2 ψ) ε) :=
      iso_linComb ((isGen_iff w).1 hw) ρ ε
    have I3 : LBIso (LB.LinComb P₀ (fun k => ρ k ≫ sq2 ψ) ε) ((LB.LinComb P₀ φ ε).pull (sq2 ψ)) := by
      refine LBIso.symm (GlobalTheory.PrimNorm.lbIso_nested hP₀ φ ε (fun _ : PUnit => sq2 ψ) (fun _ => 1)
        (fun k => ρ k ≫ sq2 ψ) ε ?_)
      rw [Fintype.prod_unique, zpow_one]
      exact Finset.prod_congr rfl fun k _ => by rw [hsq k]
    exact LBIso.trans L1 L2 L4 I1 (LBIso.trans L2 L3 L4 I2 I3)
end GlobalTheory.UPel.HT.Hecke
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsGrpPullbackOfIsPullback
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem exists_grpObj_isGrpPullback_of_isPullback : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (A : Over (Sp R)) [GrpObj A] (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ A.left), IsPullback φ s' A.hom (spMap σ) → ∃ _ : GrpObj (Over.mk s' : Over (Sp R')), IsGrpPullback (Over.mk s' : Over (Sp R')) A (spMap σ) φ ∧ (IsAbelianScheme A → IsAbelianScheme (Over.mk s' : Over (Sp R'))) ∧ ∀ g, SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g s' := by
  intro R R' _ _ σ A _ X' s' φ h
  letI : GrpObj ((Over.pullback (spMap σ)).obj A) := Functor.grpObjObj
  let e : Over.mk s' ≅ (Over.pullback (spMap σ)).obj A := Over.isoMk h.isoPullback h.isoPullback_hom_snd
  letI I : GrpObj (Over.mk s') := GrpObj.ofIso e.symm
  have : IsMonHom e.symm.hom := CategoryTheory.isMonHom_ofIso e.symm
  have : IsMonHom e.hom := inferInstanceAs (IsMonHom e.symm.inv)
  have hP : IsGrpPullback (Over.mk s' : Over (Sp R')) A (spMap σ) φ :=
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback A (spMap σ))).congr (Category.id_comp _)
      (by simp [e])
  exact ⟨I, hP, fun hA => GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hP,
    fun g hg => (smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback h hg⟩

end GlobalTheory.AbCoh
end
end

