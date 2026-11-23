module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0002

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPolyNonnegAtZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Filter Topology

theorem PolyNonnegAtZero.proof : PolyNonnegAtZero.Statement := by
  intro d p c hc hdom hev
  by_contra h0
  push Not at h0
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  let S : Set ℝ := {t | 0 ≤ t ∧ p.eval t ≤ 0}
  have h0S : (0 : ℝ) ∈ S := ⟨le_rfl, h0.le⟩
  have hbdd : BddAbove S := ⟨N, fun t ht => by
    by_contra hlt
    push Not at hlt
    exact absurd ht.2 (not_le.2 (hN t hlt.le))⟩
  have hclosed : IsClosed S :=
    (isClosed_le continuous_const continuous_id).inter
      (isClosed_le p.continuous continuous_const)
  have ht0S : sSup S ∈ S := hclosed.csSup_mem ⟨0, h0S⟩ hbdd
  obtain ⟨ht0nn, hpt0⟩ := ht0S
  have hpos : ∀ t, sSup S < t → 0 < p.eval t := by
    intro t ht
    by_contra hle
    push Not at hle
    exact absurd (le_csSup hbdd ⟨ht0nn.trans ht.le, hle⟩) (not_le.2 ht)
  have hlim : c * (sSup S) ^ d ≤ p.eval (sSup S) := by
    by_contra hlt
    push Not at hlt
    have hcont : Continuous fun t : ℝ => p.eval t - c * t ^ d :=
      p.continuous.sub (continuous_const.mul (continuous_pow d))
    have hev' : ∀ᶠ t in 𝓝 (sSup S), p.eval t - c * t ^ d < 0 :=
      hcont.continuousAt.eventually (gt_mem_nhds (by linarith))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev'
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show sSup S < sSup S + ε by linarith)
    have hqpos : (0 : ℝ) < q := lt_of_le_of_lt ht0nn hq1
    have hd : dist (q : ℝ) (sSup S) < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    have h1 := hball hd
    have h2 := hdom q (by exact_mod_cast hqpos) (hpos q hq1)
    linarith
  rcases ht0nn.lt_or_eq with htpos | htz
  · have : 0 < c * (sSup S) ^ d := mul_pos hc (pow_pos htpos d)
    linarith
  · have hp0 : 0 ≤ p.eval (sSup S) := le_trans (mul_nonneg hc.le (pow_nonneg ht0nn d)) hlim
    rw [← htz] at hp0
    linarith

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPolySandwich
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Polynomial Filter

theorem PolySandwich.leadingCoeff_nonneg_of_eventually (f : ℚ[X])
    (hf : ∀ᶠ n : ℕ in atTop, 0 ≤ f.eval (n : ℚ)) : 0 ≤ f.leadingCoeff := by
  by_contra h
  push Not at h
  rcases Nat.eq_zero_or_pos f.natDegree with h0 | hpos
  · obtain ⟨n, hn⟩ := hf.exists
    rw [eq_C_of_natDegree_eq_zero h0, eval_C] at hn
    have : f.leadingCoeff = f.coeff 0 := by rw [leadingCoeff, h0]
    linarith
  · have hdeg : 0 < f.degree := natDegree_pos_iff_degree_pos.mp hpos
    have ht := (f.tendsto_atBot_of_leadingCoeff_nonpos hdeg h.le).comp tendsto_natCast_atTop_atTop
    obtain ⟨n, hn1, hn2⟩ := (hf.and (ht.eventually (eventually_lt_atBot 0))).exists
    simp only [Function.comp] at hn2
    linarith

theorem PolySandwich.coeff_nonneg_of_eventually (f : ℚ[X]) (E : ℕ) (hE : f.natDegree ≤ E)
    (hf : ∀ᶠ n : ℕ in atTop, 0 ≤ f.eval (n : ℚ)) : 0 ≤ f.coeff E := by
  rcases hE.lt_or_eq with hlt | heq
  · rw [coeff_eq_zero_of_natDegree_lt hlt]
  · rw [← heq]
    exact PolySandwich.leadingCoeff_nonneg_of_eventually f hf

theorem PolySandwich.natDegree_shift (p : ℚ[X]) (c : ℚ) : (p.comp (X + C c)).natDegree = p.natDegree := by
  rw [natDegree_comp, natDegree_X_add_C, mul_one]

theorem PolySandwich.coeff_shift (p : ℚ[X]) (c : ℚ) (E : ℕ) (hE : p.natDegree ≤ E) :
    (p.comp (X + C c)).coeff E = p.coeff E := by
  rcases hE.lt_or_eq with hlt | heq
  · rw [coeff_eq_zero_of_natDegree_lt hlt,
      coeff_eq_zero_of_natDegree_lt (by rwa [PolySandwich.natDegree_shift])]
  · subst heq
    have h1 : (p.comp (X + C c)).leadingCoeff = p.leadingCoeff := by
      rw [leadingCoeff_comp (by rw [natDegree_X_add_C]; exact one_ne_zero), leadingCoeff_X_add_C, one_pow,
        mul_one]
    rw [leadingCoeff, PolySandwich.natDegree_shift] at h1
    exact h1

theorem PolySandwich.proof : PolySandwich.Statement := by
  intro D c p q hq hev
  set g : ℚ[X] := p.comp (X + C (c : ℚ)) with hg
  have h1 : ∀ᶠ n : ℕ in atTop, 0 ≤ (q - p).eval (n : ℚ) :=
    hev.mono fun n hn => by rw [eval_sub]; linarith [hn.1]
  have h2 : ∀ᶠ n : ℕ in atTop, 0 ≤ (g - q).eval (n : ℚ) :=
    hev.mono fun n hn => by
      rw [eval_sub, hg, eval_comp, eval_add, eval_X, eval_C]; linarith [hn.2]
  have hgdeg : g.natDegree = p.natDegree := PolySandwich.natDegree_shift p c

  have key : ∀ E : ℕ, p.natDegree ≤ E → q.natDegree ≤ E → p.coeff E = q.coeff E := by
    intro E hp hqE
    have a := PolySandwich.coeff_nonneg_of_eventually (q - p) E
      ((natDegree_sub_le _ _).trans (max_le hqE hp)) h1
    have b := PolySandwich.coeff_nonneg_of_eventually (g - q) E
      ((natDegree_sub_le _ _).trans (max_le (hgdeg ▸ hp) hqE)) h2
    rw [coeff_sub] at a b
    rw [hg, PolySandwich.coeff_shift p c E hp] at b
    linarith
  have hpD : p.natDegree ≤ D := by
    by_contra hlt
    push Not at hlt
    have e := key p.natDegree le_rfl (hq.trans hlt.le)
    rw [coeff_eq_zero_of_natDegree_lt (hq.trans_lt hlt)] at e
    have hp0 : p = 0 := leadingCoeff_eq_zero.mp e
    rw [hp0, natDegree_zero] at hlt
    exact absurd hlt (Nat.not_lt_zero _)
  exact ⟨hpD, key D hpD hq⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPrimeComplexRadical
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial TensorProduct

noncomputable section

theorem isReduced_tensor_domain_of_formallyEtale (E L D : Type*) [Field E] [Field L] [Algebra E L]
    [Algebra.FormallyEtale E L] [Algebra.EssFiniteType E L] [CommRing D] [IsDomain D]
    [Algebra E D] : IsReduced (L ⊗[E] D) := by
  have : IsReduced (FractionRing D ⊗[E] L) :=
    Algebra.FormallyUnramified.isReduced_of_field (FractionRing D) (FractionRing D ⊗[E] L)
  have : IsReduced (L ⊗[E] FractionRing D) :=
    isReduced_of_injective (Algebra.TensorProduct.comm E L (FractionRing D))
      (AlgEquiv.injective _)
  exact isReduced_of_injective
    (Algebra.TensorProduct.map (AlgHom.id E L) (IsScalarTower.toAlgHom E D (FractionRing D)))
    (Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective D _))


open scoped IntermediateField.algebraAdjoinAdjoin in
theorem isReduced_tensor_field_of_perfectField (K L F : Type*) [Field K] [PerfectField K]
    [Field L] [Algebra K L] [Algebra.EssFiniteType K L] [Field F] [Algebra K F] :
    IsReduced (L ⊗[K] F) := by
  classical
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K L
  let R := Algebra.adjoin K (s : Set L)
  let E := IntermediateField.adjoin K (s : Set L)
  letI : Algebra R E :=
    (Subalgebra.inclusion (IntermediateField.algebra_adjoin_le_adjoin K (s : Set L))).toAlgebra
  have : IsScalarTower K R E := IsScalarTower.of_algebraMap_eq' rfl
  have : FaithfulSMul R E :=
    Subalgebra.inclusion.faithfulSMul (IntermediateField.algebra_adjoin_le_adjoin K (s : Set L))
  have : IsFractionRing R E := IsFractionRing.of_field _ _ fun ⟨_, h⟩ => by
    obtain ⟨x, hx, y, hy, eq⟩ := IntermediateField.mem_adjoin_iff_div.mp h
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, Subtype.ext eq⟩

  have eR : R ≃ₐ[K] MvPolynomial s K :=
    (Subalgebra.equivOfEq R (Algebra.adjoin K (Set.range ((↑) : s → L))) (by simp [R])).trans hs.1.aevalEquiv.symm
  have hRF : IsDomain (R ⊗[K] F) :=
    ((Algebra.TensorProduct.comm K R F).toRingEquiv.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[K] F) eR).toRingEquiv.trans
        (MvPolynomial.algebraTensorAlgEquiv (σ := s) K F).toRingEquiv)).toMulEquiv.isDomain

  have hT : IsDomain (E ⊗[R] (R ⊗[K] F)) := by
    letI : Algebra (R ⊗[K] F) (E ⊗[R] (R ⊗[K] F)) := Algebra.TensorProduct.rightAlgebra
    have := IsLocalization.tensorRight (R := R) (S := R ⊗[K] F) (A := E) (nonZeroDivisors R)
    refine IsLocalization.isDomain_of_le_nonZeroDivisors (R := R ⊗[K] F)
      (M := Algebra.algebraMapSubmonoid (R ⊗[K] F) (nonZeroDivisors R)) (E ⊗[R] (R ⊗[K] F)) ?_
    rintro _ ⟨r, hr, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero ?_
    intro h0
    have hinj : Function.Injective (algebraMap R (R ⊗[K] F)) :=
      Algebra.TensorProduct.includeLeft_injective (S := R) (RingHom.injective (algebraMap K F))
    exact nonZeroDivisors.ne_zero hr (hinj (by simpa using h0))

  have : IsDomain (E ⊗[K] F) :=
    (Algebra.TensorProduct.cancelBaseChange K R R E F).symm.toMulEquiv.isDomain

  have : Algebra.FormallyEtale E L := Algebra.FormallyEtale.of_isSeparable E L
  have : Algebra.EssFiniteType E L := Algebra.EssFiniteType.of_comp K E L
  have := isReduced_tensor_domain_of_formallyEtale E L (E ⊗[K] F)
  exact isReduced_of_injective (Algebra.TensorProduct.cancelBaseChange K E E L F).symm
    (AlgEquiv.injective _)

theorem isReduced_tensor_domain_of_perfectField (K A F : Type*) [Field K] [PerfectField K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] [Field F] [Algebra K F] :
    IsReduced (F ⊗[K] A) := by
  have : Algebra.EssFiniteType A (FractionRing A) :=
    .of_isLocalization _ (nonZeroDivisors A)
  have : Algebra.EssFiniteType K (FractionRing A) := .comp K A _
  have := isReduced_tensor_field_of_perfectField K (FractionRing A) F
  have : IsReduced (F ⊗[K] FractionRing A) :=
    isReduced_of_injective (Algebra.TensorProduct.comm K F (FractionRing A)) (AlgEquiv.injective _)
  exact isReduced_of_injective
    (Algebra.TensorProduct.map (AlgHom.id K F) (IsScalarTower.toAlgHom K A (FractionRing A)))
    (Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective A _))

theorem isRadical_map_of_isPrime_of_perfectField (K F : Type*) [Field K] [PerfectField K]
    [Field F] [Algebra K F] (σ : Type*) [Fintype σ] (Q : Ideal (MvPolynomial σ K))
    [Q.IsPrime] : (Q.map (MvPolynomial.map (algebraMap K F))).IsRadical := by
  rw [Ideal.isRadical_iff_quotient_reduced]
  let e₀ := MvPolynomial.algebraTensorAlgEquiv (σ := σ) K F
  have hJ : Q.map (MvPolynomial.map (algebraMap K F)) =
      (Q.map (Algebra.TensorProduct.includeRight (R := K) (A := F)).toRingHom).map
        e₀.toRingEquiv.toRingHom := by
    rw [Ideal.map_map]
    congr 1
    refine RingHom.ext fun p => ?_
    simp [e₀, MvPolynomial.algebraTensorAlgEquiv_tmul]
  let e : F ⊗[K] (MvPolynomial σ K ⧸ Q) ≃+*
      MvPolynomial σ F ⧸ Q.map (MvPolynomial.map (algebraMap K F)) :=
    (Algebra.TensorProduct.tensorQuotientEquiv (R := K) K (MvPolynomial σ K) F Q).toRingEquiv.trans
      (Ideal.quotientEquiv _ _ e₀.toRingEquiv (hJ.trans rfl))
  have := isReduced_tensor_domain_of_perfectField K (MvPolynomial σ K ⧸ Q) F
  exact isReduced_of_injective e.symm e.symm.injective

theorem PrimeComplexRadical.proof : PrimeComplexRadical.Statement := by
  intro σ _ P hP
  by_cases hZ : ∃ n : ℤ, n ≠ 0 ∧ C n ∈ P
  · obtain ⟨n, hn, hnP⟩ := hZ
    have htop : P.map (MvPolynomial.map (Int.castRingHom ℂ)) = ⊤ := by
      apply Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hnP)
      rw [MvPolynomial.map_C]
      exact (isUnit_iff_ne_zero.mpr (by simpa using hn)).map C
    rw [htop]
    exact fun x _ => Submodule.mem_top
  · push Not at hZ
    let _ := MvPolynomial.algebraMvPolynomial (σ := σ) (R := ℤ) (S := ℚ)
    let M := (nonZeroDivisors ℤ).map (C (σ := σ) (R := ℤ))
    have : IsLocalization M (MvPolynomial σ ℚ) := MvPolynomial.isLocalization _ _
    let Q := P.map (algebraMap (MvPolynomial σ ℤ) (MvPolynomial σ ℚ))
    have hQ : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M _ P hP (by
      rw [Set.disjoint_left]
      rintro _ ⟨n, hn, rfl⟩ hnP
      exact hZ n (nonZeroDivisors.ne_zero hn) hnP)
    have hmap : P.map (MvPolynomial.map (Int.castRingHom ℂ)) =
        Q.map (MvPolynomial.map (algebraMap ℚ ℂ)) := by
      rw [Ideal.map_map]
      congr 1
      refine RingHom.ext fun p => ?_
      change _ = MvPolynomial.map (algebraMap ℚ ℂ) (MvPolynomial.map (algebraMap ℤ ℚ) p)
      rw [MvPolynomial.map_map,
        show (algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ) = Int.castRingHom ℂ from RingHom.ext_int _ _]
    rw [hmap]
    exact isRadical_map_of_isPrime_of_perfectField ℚ ℂ σ Q

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRatPrimeDense
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Filter Topology

theorem RatPrimeDense.continuous_aeval {σ : Type} (g : MvPolynomial σ ℚ) :
    Continuous fun z : σ → ℂ => aeval z g := by
  simp_rw [aeval_def, ← eval_map]
  exact MvPolynomial.continuous_eval _

theorem RatPrimeDense.proof (h₁ : FiniteSeparatingModel.Statement) (h₂ : RootsNear.Statement)
    (h₃ : RootsBounded.Statement) (h₄ : PolyNonvanishDense.Statement) : RatPrimeDense.Statement := by
  intro σ _ P f hP hf x hx
  obtain ⟨e, ℓ, u, G, c, D, hG, hc, hD, hint, hGz, hcf, hlift, hsep⟩ := h₁ σ P f x hP hf hx
  set L : (σ → ℂ) → Fin e → ℂ := fun z j => aeval z (ℓ j) with hL
  have hLc : Continuous L := continuous_pi fun j => RatPrimeDense.continuous_aeval (ℓ j)
  have huc : Continuous fun z : σ → ℂ => aeval z u := RatPrimeDense.continuous_aeval u
  have hZ : IsClosed {z : σ → ℂ | ∀ g ∈ P, aeval z g = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun g => isClosed_iInter fun _ =>
      isClosed_eq (RatPrimeDense.continuous_aeval g) continuous_const

  choose p hp hpz using hint
  choose R hR using fun i => h₃ e (p i) (hp i) (L x)
  set Rb : ℝ := ∑ i, max (R i) 0
  have hRb : 0 ≤ Rb := Finset.sum_nonneg fun i _ => le_max_right _ _
  rw [Metric.mem_closure_iff]
  intro ε hε
  set C := ({z : σ → ℂ | ∀ g ∈ P, aeval z g = 0} ∩ Metric.closedBall 0 Rb) ∩ {z | ε ≤ dist z x}
  have hCc : IsCompact C := ((isCompact_closedBall 0 Rb).inter_left hZ).inter_right
    (isClosed_le continuous_const (continuous_id.dist continuous_const))
  set φ : (σ → ℂ) → ℝ := fun z => dist (L z) (L x) + dist (aeval z u) (aeval x u)
  have hφc : Continuous φ :=
    (hLc.dist continuous_const).add (huc.dist continuous_const)
  obtain ⟨δ, hδ, hδC⟩ : ∃ δ > 0, ∀ z ∈ C, δ ≤ φ z := by
    rcases C.eq_empty_or_nonempty with hC | hC
    · exact ⟨1, one_pos, by simp [hC]⟩
    obtain ⟨z₀, hz₀, hmin⟩ := hCc.exists_isMinOn hC hφc.continuousOn
    refine ⟨φ z₀, ?_, fun z hz => hmin hz⟩
    refine lt_of_le_of_ne (add_nonneg dist_nonneg dist_nonneg) fun h0 => ?_
    have h1 := (add_eq_zero_iff_of_nonneg dist_nonneg dist_nonneg).mp h0.symm
    have := hsep z₀ hz₀.1.1 (dist_eq_zero.mp h1.1) (dist_eq_zero.mp h1.2)
    have h2 := hz₀.2
    simp only [Set.mem_ofPred_eq, this, dist_self] at h2
    exact absurd h2 (not_le.mpr hε)

  have hE : ∀ᶠ y in 𝓝 (L x), (∃ t : ℂ, G.eval₂ (aeval y).toRingHom t = 0 ∧
      dist t (aeval x u) < δ / 2) ∧ (∀ i, ∀ t : ℂ, (p i).eval₂ (aeval y).toRingHom t = 0 → ‖t‖ ≤ R i) ∧
      dist y (L x) < δ / 2 :=
    (h₂ e G hG (L x) (aeval x u) (hGz x hx) (δ / 2) (half_pos hδ)).and
      ((eventually_all.mpr hR).and (Metric.ball_mem_nhds _ (half_pos hδ)))
  obtain ⟨y, ⟨⟨t, ht, htd⟩, hyR, hyd⟩, hyB⟩ := (mem_closure_iff_nhds.mp
    (h₄ e (D * c) (mul_ne_zero hD hc) (L x)) _ hE)
  simp only [Set.mem_ofPred_eq, map_mul, mul_ne_zero_iff] at hyB
  obtain ⟨z, hz, hzy, hzt⟩ := hlift y t hyB.1 ht
  have hzL : L z = y := hzy
  refine ⟨z, ⟨hz, hcf z hz (by rw [hzy]; exact hyB.2)⟩, ?_⟩
  have hzR : z ∈ Metric.closedBall 0 Rb := by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hRb]
    intro i
    have := hyR i (z i) (by rw [← hzL]; exact hpz i z hz)
    exact this.trans ((le_max_left _ _).trans
      (Finset.single_le_sum (fun j _ => le_max_right (R j) 0) (Finset.mem_univ i)))
  by_contra hfar
  have hφz : φ z < δ := by
    change dist (L z) (L x) + dist (aeval z u) (aeval x u) < δ
    rw [hzL, hzt]
    linarith
  exact absurd (hδC z ⟨⟨hz, hzR⟩, by show ε ≤ dist z x; rw [dist_comm]; exact not_lt.mp hfar⟩) (not_le.mpr hφz)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRootGridLower
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Finset

theorem RootGridLower.sum_fin_pow {M : ℕ} (hM : 0 < M) {ω : ℂ} (hω : IsPrimitiveRoot ω M)
    {a b : ℕ} (ha : a < M) (hb : b < M) :
    ∑ t : Fin M, (ω ^ a * (ω ^ b)⁻¹) ^ (t : ℕ) = if a = b then (M : ℂ) else 0 := by
  have hω0 : ω ≠ 0 := hω.ne_zero hM.ne'
  rw [Fin.sum_univ_eq_sum_range (fun t => (ω ^ a * (ω ^ b)⁻¹) ^ t)]
  split_ifs with hab
  · subst hab
    simp [mul_inv_cancel₀ (pow_ne_zero _ hω0)]
  · have hz : ω ^ a * (ω ^ b)⁻¹ ≠ 1 := by
      intro h
      apply hab
      apply hω.pow_inj ha hb
      have := congrArg (· * ω ^ b) h
      simpa [mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hω0)] using this
    rw [geom_sum_eq hz]
    have h1 : (ω ^ a * (ω ^ b)⁻¹) ^ M = 1 := by
      rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm a, mul_comm b, pow_mul, pow_mul,
        hω.pow_eq_one]
      simp
    simp [h1]

theorem RootGridLower.average {e M : ℕ} (hM : 0 < M) {ω : ℂ} (hω : IsPrimitiveRoot ω M)
    (Q : MvPolynomial (Fin e) ℤ) (hdeg : ∀ i, Q.degreeOf i < M) (j : Fin e →₀ ℕ)
    (hj : ∀ i, j i < M) :
    ∑ k : Fin e → Fin M, eval (fun i => ω ^ (k i : ℕ)) (map (Int.castRingHom ℂ) Q) *
        ∏ i, ((ω ^ j i)⁻¹) ^ (k i : ℕ) = (M : ℂ) ^ e * ((Q.coeff j : ℤ) : ℂ) := by
  classical
  simp_rw [eval_map, eval₂_eq', Finset.sum_mul]
  rw [Finset.sum_comm]
  have key : ∀ d ∈ Q.support, ∑ k : Fin e → Fin M,
      (Int.castRingHom ℂ) (Q.coeff d) * (∏ i, (ω ^ (k i : ℕ)) ^ d i) *
        ∏ i, ((ω ^ j i)⁻¹) ^ (k i : ℕ) =
      ((Q.coeff d : ℤ) : ℂ) * if d = j then (M : ℂ) ^ e else 0 := by
    intro d hd
    have hdM : ∀ i, d i < M := fun i => lt_of_le_of_lt (monomial_le_degreeOf i hd) (hdeg i)
    have hprod : ∀ k : Fin e → Fin M, (∏ i, (ω ^ (k i : ℕ)) ^ d i) * ∏ i, ((ω ^ j i)⁻¹) ^ (k i : ℕ)
        = ∏ i, (ω ^ d i * (ω ^ j i)⁻¹) ^ (k i : ℕ) := by
      intro k
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (k i : ℕ)]
    simp_rw [mul_assoc, hprod, ← Finset.mul_sum]
    congr 1
    rw [← Fintype.prod_sum (fun i (t : Fin M) => (ω ^ d i * (ω ^ j i)⁻¹) ^ (t : ℕ))]
    simp_rw [RootGridLower.sum_fin_pow hM hω (hdM _) (hj _)]
    split_ifs with hdj
    · subst hdj; simp
    · obtain ⟨i, hi⟩ : ∃ i, d i ≠ j i := by
        by_contra h
        push Not at h
        exact hdj (Finsupp.ext h)
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  rw [Finset.sum_congr rfl key]
  simp_rw [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with hjs
  · simp [mul_comm]
  · rw [MvPolynomial.notMem_support_iff.mp hjs]; simp

theorem RootGridLower.of_pos {e M : ℕ} (hM : 0 < M) (Q : MvPolynomial (Fin e) ℤ) (hQ : Q ≠ 0)
    (hdeg : ∀ i, Q.degreeOf i < M) :
    ∃ ζ : Fin e → ℂ, (∀ i, ζ i ^ M = 1) ∧ 1 ≤ ‖eval ζ (map (Int.castRingHom ℂ) Q)‖ := by
  classical
  have hω := Complex.isPrimitiveRoot_exp M hM.ne'
  set ω := Complex.exp (2 * Real.pi * Complex.I / M)
  obtain ⟨j, hj⟩ : Q.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]; exact hQ
  have hjM : ∀ i, j i < M := fun i => lt_of_le_of_lt (monomial_le_degreeOf i hj) (hdeg i)
  have hc : (1 : ℝ) ≤ ‖((Q.coeff j : ℤ) : ℂ)‖ := by
    rw [Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs (MvPolynomial.mem_support_iff.mp hj)
  have hω1 : ‖ω‖ = 1 := hω.norm'_eq_one hM.ne'
  by_contra hne
  push Not at hne
  have hlt : ∀ k : Fin e → Fin M,
      ‖eval (fun i => ω ^ (k i : ℕ)) (map (Int.castRingHom ℂ) Q)‖ < 1 := by
    intro k
    refine hne _ fun i => ?_
    rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
  have hne' : (Finset.univ : Finset (Fin e → Fin M)).Nonempty :=
    ⟨fun i => ⟨j i, hjM i⟩, Finset.mem_univ _⟩
  have hupper : ‖(M : ℂ) ^ e * ((Q.coeff j : ℤ) : ℂ)‖ < (M : ℝ) ^ e := by
    rw [← RootGridLower.average hM hω Q hdeg j hjM]
    calc ‖∑ k : Fin e → Fin M, eval (fun i => ω ^ (k i : ℕ)) (map (Int.castRingHom ℂ) Q) *
            ∏ i, ((ω ^ j i)⁻¹) ^ (k i : ℕ)‖
        ≤ ∑ k : Fin e → Fin M, ‖eval (fun i => ω ^ (k i : ℕ)) (map (Int.castRingHom ℂ) Q) *
            ∏ i, ((ω ^ j i)⁻¹) ^ (k i : ℕ)‖ := norm_sum_le _ _
      _ = ∑ k : Fin e → Fin M, ‖eval (fun i => ω ^ (k i : ℕ)) (map (Int.castRingHom ℂ) Q)‖ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          simp [norm_prod, hω1]
      _ < ∑ _k : Fin e → Fin M, (1 : ℝ) := Finset.sum_lt_sum_of_nonempty hne' fun k _ => hlt k
      _ = (M : ℝ) ^ e := by simp
  have hlower : (M : ℝ) ^ e ≤ ‖(M : ℂ) ^ e * ((Q.coeff j : ℤ) : ℂ)‖ := by
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    exact le_mul_of_one_le_right (by positivity) hc
  linarith

theorem RootGridLower.proof : RootGridLower.Statement := by
  intro e m Q hQ hdeg
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain ⟨ζ, -, hζ⟩ := RootGridLower.of_pos Nat.one_pos Q hQ
      (fun i => lt_trans (hdeg i) Nat.one_pos)
    exact ⟨ζ, fun i => pow_zero _, hζ⟩
  · exact RootGridLower.of_pos hm Q hQ hdeg

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

