module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SndDualLiftAlgebraMap

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralOrInvIsIntegralFiniteExtUltrametric
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

open Polynomial

noncomputable section

namespace GlobalTheory.JR.Spec

variable {F : Type} [NontriviallyNormedField F] [IsUltrametricDist F]
  {k : Type} [Field k] [Algebra F k]

theorem isIntegral_integer_of_spectralNorm_le_one [FiniteDimensional F k] {y : k}
    (h : spectralNorm F k y ≤ 1) : IsIntegral (NormedField.valuation (K := F)).integer y := by
  have hyF : IsIntegral F y := Algebra.IsIntegral.isIntegral y
  rw [spectralNorm, spectralValue_le_one_iff (minpoly.monic hyF)] at h
  have hl : minpoly F y ∈ lifts (algebraMap (NormedField.valuation (K := F)).integer F) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    refine ⟨⟨_, ?_⟩, rfl⟩
    rw [Valuation.mem_integer_iff, NormedField.valuation_apply]
    exact_mod_cast h n
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hyF)
  refine ⟨q, hqm, ?_⟩
  rw [← aeval_def, ← aeval_map_algebraMap F, hq, minpoly.aeval]

theorem isIntegral_or_isIntegral_inv : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F]
    [CompleteSpace F] (k : Type) [Field k] [Algebra F k] [FiniteDimensional F k] (y : k), y ≠ 0 →
    IsIntegral (NormedField.valuation (K := F)).integer y ∨
      IsIntegral (NormedField.valuation (K := F)).integer y⁻¹ := by
  intro F _ _ _ k _ _ _ y hy0
  have hmul : spectralNorm F k y * spectralNorm F k y⁻¹ = 1 := by
    have := spectralAlgNorm_mul (K := F) (L := k) y y⁻¹
    rw [spectralAlgNorm_def, spectralAlgNorm_def, spectralAlgNorm_def, mul_inv_cancel₀ hy0,
      spectralNorm_one] at this
    exact this.symm
  by_cases h : spectralNorm F k y ≤ 1
  · exact Or.inl (isIntegral_integer_of_spectralNorm_le_one h)
  · right
    apply isIntegral_integer_of_spectralNorm_le_one
    have h1 : 1 < spectralNorm F k y := lt_of_not_ge h
    by_contra h2
    have h2 : 1 < spectralNorm F k y⁻¹ := lt_of_not_ge h2
    have : 1 < spectralNorm F k y * spectralNorm F k y⁻¹ := one_lt_mul_of_lt_of_le h1 h2.le
    linarith

end GlobalTheory.JR.Spec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralResidueComapInvolutionIff
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.SwapInt

theorem isIntegral_map_semilinear {O S S' : Type} [CommRing O] [CommRing S] [CommRing S'] [Algebra O S]
    [Algebra O S'] (κ : O →+* O) (ψ : S →+* S')
    (hψ : ∀ o, ψ (algebraMap O S o) = algebraMap O S' (κ o)) {y : S} (h : IsIntegral O y) :
    IsIntegral O (ψ y) := by
  obtain ⟨p, hm, hp⟩ := h
  refine ⟨p.map κ, hm.map κ, ?_⟩
  rw [eval₂_map]
  have e : (algebraMap O S').comp κ = ψ.comp (algebraMap O S) := by
    ext o; simp [hψ]
  rw [e, ← hom_eval₂, hp, map_zero]

noncomputable def conjO (K : UQ) : K.O →+* K.O where
  toFun o := Classical.choose (K.c_int o)
  map_one' := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int 1)]; simp
  map_mul' a b := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int (a * b)), map_mul, map_mul, map_mul,
      ← Classical.choose_spec (K.c_int a), ← Classical.choose_spec (K.c_int b)]
  map_zero' := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int 0)]; simp
  map_add' a b := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int (a + b)), map_add (f := _), map_add (f := _), map_add (f := _),
      ← Classical.choose_spec (K.c_int a), ← Classical.choose_spec (K.c_int b)]

theorem conjO_spec (K : UQ) (o : K.O) :
    algebraMap K.O K.E (conjO K o) = K.c (algebraMap K.O K.E o) :=
  (Classical.choose_spec (K.c_int o)).symm

theorem sigma_algebraMap {K : UQ} (B : InvAlg K) (o : K.O) :
    B.σ (algebraMap K.O B.A o) = algebraMap K.O B.A (conjO K o) := by
  rw [IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, ← conjO_spec,
    ← IsScalarTower.algebraMap_apply K.O K.E B.A]

end GlobalTheory.UnitLemma.SwapInt


open GlobalTheory.UnitLemma.SwapInt in
theorem GlobalTheory.UnitLemma.InvAlg.isIntegral_mk_comap_sigma_iff :
    ∀ (K : UQ) (B : InvAlg K) (m : MaximalSpectrum B.A) (x : B.A),
      IsIntegral K.O (Ideal.Quotient.mk (m.asIdeal.comap B.σ) x) ↔
        IsIntegral K.O (Ideal.Quotient.mk m.asIdeal (B.σ x)) := by
  intro K B m x
  let σr : B.A →+* B.A := B.σ
  let ψ := Ideal.quotientMap m.asIdeal σr (le_refl (m.asIdeal.comap σr))
  have hm : m.asIdeal ≤ (m.asIdeal.comap σr).comap σr := by
    intro y hy
    simp only [Ideal.mem_comap]
    show B.σ (B.σ y) ∈ m.asIdeal
    rw [B.σ_σ]; exact hy
  let φ := Ideal.quotientMap (m.asIdeal.comap σr) σr hm
  have key : ∀ o : K.O, σr (algebraMap K.O B.A o) = algebraMap K.O B.A (conjO K o) :=
    sigma_algebraMap B
  constructor
  · intro h
    have h' : IsIntegral K.O (Ideal.Quotient.mk (m.asIdeal.comap σr) x) := h
    have := isIntegral_map_semilinear (conjO K) ψ (fun o => by
      rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap]
      simp only [ψ]
      rw [Ideal.quotientMap_mk, key]) h'
    have e2 : ψ (Ideal.Quotient.mk (m.asIdeal.comap σr) x) = Ideal.Quotient.mk m.asIdeal (σr x) :=
      Ideal.quotientMap_mk
    rw [e2] at this
    exact this
  · intro h
    have h' : IsIntegral K.O (Ideal.Quotient.mk m.asIdeal (σr x)) := h
    have := isIntegral_map_semilinear (conjO K) φ (fun o => by
      rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap]
      simp only [φ]
      rw [Ideal.quotientMap_mk, key]) h'
    have e2 : φ (Ideal.Quotient.mk m.asIdeal (σr x)) = Ideal.Quotient.mk (m.asIdeal.comap σr) (σr (σr x)) :=
      Ideal.quotientMap_mk
    have e : σr (σr x) = x := B.σ_σ x
    rw [e2, e] at this
    exact this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantPartialFourierGLBlock
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

open Matrix MeasureTheory Filter Topology in
private theorem addChar_dotProduct_eq_one_of_norm_le {F : Type} [NontriviallyNormedField F]
    [IsUltrametricDist F] {ψ : AddChar F ℂ} (hψ : _root_.GlobalTheory.JR.IsStdChar ψ) {r : ℕ}
    {R : ℝ} (x δ : Fin r → F) (hx : ‖x‖ ≤ R) (hδ : ‖δ‖ * R ≤ 1) : ψ (x ⬝ᵥ δ) = 1 := by
  apply hψ.1
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
  rw [norm_mul]
  calc ‖x i‖ * ‖δ i‖ ≤ R * ‖δ‖ :=
        mul_le_mul ((norm_le_pi_norm x i).trans hx) (norm_le_pi_norm δ i) (norm_nonneg _)
          ((norm_nonneg _).trans hx)
    _ = ‖δ‖ * R := mul_comm _ _
    _ ≤ 1 := hδ


open Matrix MeasureTheory Filter Topology in
theorem _root_.GlobalTheory.JR.fourG_isLocallyConstant_of_invariant :
    ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
      [_root_.GlobalTheory.JR.Unram F E] (r : ℕ) (M : _root_.GlobalTheory.JR.Meas r F E) (ψ : AddChar F ℂ),
      _root_.GlobalTheory.JR.IsStdChar ψ → ∀ f' : _root_.GlobalTheory.JR.Gl r F → ℂ, _root_.GlobalTheory.JR.IsTest f' →
      (∃ U ∈ 𝓝 (0 : _root_.GlobalTheory.JR.Gl r F), ∀ Y : _root_.GlobalTheory.JR.Gl r F, ∀ u ∈ U, f' (Y + u) = f' Y) →
      IsLocallyConstant (_root_.GlobalTheory.JR.fourG M ψ f') := by
  intro F E _ _ _ _ _ r M ψ hψ f hf ⟨U, hU, hUf⟩
  haveI := _root_.GlobalTheory.JR.Unram.ultraF (F := F) E
  obtain ⟨C, hC⟩ := hf.2.isCompact.exists_bound_of_continuousOn
    (f := fun x : _root_.GlobalTheory.JR.Gl r F => (x.2.1, x.2.2.1))
    (continuous_snd.fst.prodMk continuous_snd.snd.fst).continuousOn
  set R : ℝ := |C| + 1 with hRdef
  have hRpos : 0 < R := by positivity
  have hCR : C ≤ R := (le_abs_self C).trans (by rw [hRdef]; linarith)
  have hbd : ∀ x ∈ tsupport f, ‖x.2.1‖ ≤ R ∧ ‖x.2.2.1‖ ≤ R := by
    intro x hx
    have h : ‖(x.2.1, x.2.2.1)‖ ≤ C := hC x hx
    exact ⟨(norm_fst_le (x.2.1, x.2.2.1)).trans (h.trans hCR),
      (norm_snd_le (x.2.1, x.2.2.1)).trans (h.trans hCR)⟩
  let P : _root_.GlobalTheory.JR.Gl r F → _root_.GlobalTheory.JR.Gl r F := fun u => (u.1, 0, 0, u.2.2.2)
  have hP : Continuous P :=
    continuous_fst.prodMk (continuous_const.prodMk (continuous_const.prodMk continuous_snd.snd.snd))
  have hP0 : P 0 = 0 := rfl
  set W : Set (_root_.GlobalTheory.JR.Gl r F) :=
    P ⁻¹' U ∩ {u | ‖u.2.1‖ < R⁻¹} ∩ {u | ‖u.2.2.1‖ < R⁻¹} with hWdef
  have hW : W ∈ 𝓝 (0 : _root_.GlobalTheory.JR.Gl r F) := by
    refine inter_mem (inter_mem (hP.continuousAt.preimage_mem_nhds (by rwa [hP0])) ?_) ?_
    · exact (isOpen_lt (continuous_norm.comp continuous_snd.fst) continuous_const).mem_nhds
        (by simp [hRpos])
    · exact (isOpen_lt (continuous_norm.comp continuous_snd.snd.fst) continuous_const).mem_nhds
        (by simp [hRpos])
  rw [IsLocallyConstant.iff_eventually_eq]
  intro Y
  have hnb : {Y' | Y' - Y ∈ W} ∈ 𝓝 Y :=
    (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds (by simpa using hW)
  filter_upwards [hnb] with Y' hY'
  obtain ⟨⟨hu1, hu2⟩, hu3⟩ := hY'
  obtain ⟨u, rfl⟩ : ∃ u, Y' = Y + u := ⟨Y' - Y, by abel⟩
  simp only [add_sub_cancel_left] at hu1 hu2 hu3
  unfold _root_.GlobalTheory.JR.fourG
  congr 1; funext b'; congr 1; funext c'
  have hfeq : f ((Y + u).1, b', c', (Y + u).2.2.2) = f (Y.1, b', c', Y.2.2.2) := by
    have := hUf (Y.1, b', c', Y.2.2.2) (P u) hu1
    convert this using 2
    ext <;> simp [P]
  rw [hfeq]
  by_cases h0 : f (Y.1, b', c', Y.2.2.2) = 0
  · simp [h0]
  have hmem : (Y.1, b', c', Y.2.2.2) ∈ tsupport f := subset_tsupport f h0
  obtain ⟨hb', hc'⟩ := hbd _ hmem
  have e1 : ψ (c' ⬝ᵥ u.2.1) = 1 := addChar_dotProduct_eq_one_of_norm_le hψ c' u.2.1 hc'
    (by rw [← le_div_iff₀ hRpos, one_div]; exact hu2.le)
  have e2 : ψ (u.2.2.1 ⬝ᵥ b') = 1 := by
    rw [dotProduct_comm]
    exact addChar_dotProduct_eq_one_of_norm_le hψ b' u.2.2.1 hb'
      (by rw [← le_div_iff₀ hRpos, one_div]; exact hu3.le)
  have hsum : c' ⬝ᵥ (Y + u).2.1 + (Y + u).2.2.1 ⬝ᵥ b' =
      (c' ⬝ᵥ Y.2.1 + Y.2.2.1 ⬝ᵥ b') + c' ⬝ᵥ u.2.1 + u.2.2.1 ⬝ᵥ b' := by
    simp only [Prod.snd_add, Prod.fst_add, dotProduct_add, add_dotProduct]
    abel
  rw [hsum, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, e1, e2, mul_one, mul_one]

end GlobalTheory.JR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenFiniteEtaleHermitianPairOK
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.OKOpen

private theorem contCoeff {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

theorem continuous_coeff {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] (A : Et F E) (i : ℕ) :
    Continuous fun z : A.K => (LinearMap.charpoly (Algebra.lmul F A.K z)).coeff i := by
  let b := Module.finBasis F A.K
  have h : (fun z : A.K => (LinearMap.charpoly (Algebra.lmul F A.K z)).coeff i) =
      fun z => (LinearMap.toMatrix b b (Algebra.lmul F A.K z)).charpoly.coeff i := by
    funext z; rw [LinearMap.charpoly_toMatrix]
  rw [h]
  refine (contCoeff _ i).comp ?_
  refine continuous_pi fun r => continuous_pi fun s => ?_
  have hl : (fun z : A.K => LinearMap.toMatrix b b (Algebra.lmul F A.K z) r s) =
      fun z => (b.coord r) (z * b s) := by
    funext z; simp [LinearMap.toMatrix_apply]
  rw [hl]
  exact IsModuleTopology.continuous_of_linearMap ((b.coord r).comp (LinearMap.mulRight F (b s)))

theorem isOpen_OK : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E), IsOpen A.OK := by
  intro F E _ _ _ _ hU A
  haveI : IsUltrametricDist F := hU.ultraF
  have hset : A.OK = ⋂ i : Fin (Module.finrank F A.K + 1),
      (fun z : A.K => (LinearMap.charpoly (Algebra.lmul F A.K z)).coeff i) ⁻¹' Metric.closedBall 0 1 := by
    ext z
    simp only [Et.OK, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    constructor
    · intro h i; exact h i
    · intro h i
      by_cases hi : i ≤ Module.finrank F A.K
      · exact h ⟨i, Nat.lt_succ_of_le hi⟩
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [LinearMap.charpoly_natDegree]; omega)]
        simp
  rw [hset]
  exact isOpen_iInter_of_finite fun i =>
    (IsUltrametricDist.isOpen_closedBall _ one_ne_zero).preimage (continuous_coeff A i)

end GlobalTheory.JR.OKOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStableGauss
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def Hyp (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ) : Prop :=
  IsField A.K ∧ IsField A.L ∧ IsStdChar ψ ∧ SelfDual μ (A.kerL ψ x) ∧
    ∀ s : A.Kˣ, ((∃ y, A.NL y = s) → ω s = 1) ∧ ((¬ ∃ y, A.NL y = s) → ω s = -1)

def nOp (A : Et F E) (ψ : AddChar F ℂ) (x z : A.K) (φ : A.L → ℂ) : A.L → ℂ :=
  fun y => A.psiK ψ (z * x * A.NL y) * φ y

def mOp (A : Et F E) (ω : A.K → ℂ) (s : A.Kˣ) (φ : A.L → ℂ) : A.L → ℂ :=
  fun y => ω s * (A.absK s : ℂ) * φ ((s : A.K) • y)

def fOp (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L) (φ : A.L → ℂ) : A.L → ℂ :=
  fourB μ (A.kerL ψ x) φ

def gaussInt (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L) (u : A.K) (S : Set A.L) : ℂ :=
  ∫ y in S, A.psiK ψ (u * x * A.NL y) ∂μ

def IsStableGauss (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L) (u : A.K) (G : ℂ) : Prop :=
  ∃ Λ₀ : AddSubgroup A.L, IsOpen (Λ₀ : Set A.L) ∧ IsCompact (Λ₀ : Set A.L) ∧
    ∀ Λ : AddSubgroup A.L, IsOpen (Λ : Set A.L) → IsCompact (Λ : Set A.L) → Λ₀ ≤ Λ →
      gaussInt A ψ x μ u Λ = G

end GlobalTheory.JR.WeilQuad
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTestUnitIndicatorHermitianBlock
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem isTest_indicator_one_of_clopen_compact {X : Type} [TopologicalSpace X] {S : Set X} (hS : IsClopen S)
    (hK : IsCompact S) : IsTest (Set.indicator S (1 : X → ℂ)) := by
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ S
    · filter_upwards [hS.isOpen.mem_nhds hx] with y hy
      simp [hx, hy]
    · filter_upwards [hS.isClosed.isOpen_compl.mem_nhds hx] with y hy
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  · exact HasCompactSupport.intro' hK hS.isClosed fun x hx => Set.indicator_of_notMem hx _

theorem isTest_unitU (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [StarRing E]
    [IsUltrametricDist F] [LocallyCompactSpace F] [IsUltrametricDist E] [LocallyCompactSpace E] (r : ℕ)
    (hstar : ∀ y : E, ‖star y‖ = ‖y‖) : IsTest (unitU r F E) := by
  haveI : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  haveI : ProperSpace E := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace E
  haveI : ContinuousStar E := ⟨(AddMonoidHomClass.isometry_of_norm (starAddEquiv (R := E)) hstar).continuous⟩
  have hF : {x : F | ‖x‖ ≤ 1} = Metric.closedBall 0 1 := by ext x; simp
  have hE : {x : E | ‖x‖ ≤ 1} = Metric.closedBall 0 1 := by ext x; simp
  have cF : IsClopen {x : F | ‖x‖ ≤ 1} := hF ▸ IsUltrametricDist.isClopen_closedBall _ one_ne_zero
  have cE : IsClopen {x : E | ‖x‖ ≤ 1} := hE ▸ IsUltrametricDist.isClopen_closedBall _ one_ne_zero
  have kF : IsCompact {x : F | ‖x‖ ≤ 1} := hF ▸ isCompact_closedBall _ _
  have kE : IsCompact {x : E | ‖x‖ ≤ 1} := hE ▸ isCompact_closedBall _ _
  have cV : IsClopen {v : Fin r → E | ∀ i, ‖v i‖ ≤ 1} := by
    rw [Set.ofPred_forall]
    exact isClopen_iInter_of_finite fun i => cE.preimage (continuous_apply i)
  have kV : IsCompact {v : Fin r → E | ∀ i, ‖v i‖ ≤ 1} := isCompact_pi_infinite fun _ => kE
  have cM : IsClopen {A : Matrix (Fin r) (Fin r) E | ∀ i j, ‖A i j‖ ≤ 1} := by
    rw [Set.ofPred_forall]
    exact isClopen_iInter_of_finite fun i => cV.preimage (continuous_apply i)
  have kM : IsCompact {A : Matrix (Fin r) (Fin r) E | ∀ i j, ‖A i j‖ ≤ 1} :=
    isCompact_pi_infinite (s := fun _ : Fin r => {v : Fin r → E | ∀ i, ‖v i‖ ≤ 1}) fun _ => kV
  have hcl : IsClosed ((selfAdjoint (Matrix (Fin r) (Fin r) E)) : Set (Matrix (Fin r) (Fin r) E)) :=
    isClosed_eq continuous_star continuous_id
  have cA : IsClopen {A : selfAdjoint (Matrix (Fin r) (Fin r) E) | ∀ i j, ‖A.1 i j‖ ≤ 1} :=
    cM.preimage continuous_subtype_val
  have kA : IsCompact {A : selfAdjoint (Matrix (Fin r) (Fin r) E) | ∀ i j, ‖A.1 i j‖ ≤ 1} :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage kM
  exact isTest_indicator_one_of_clopen_compact (cA.prod (cV.prod cF)) (kA.prod (kV.prod kF))

end GlobalTheory.JR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchSizeOne
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.SizeOne

theorem eta_one' {F : Type} [NormedField F] : eta (1 : F) = 1 := by
  unfold eta
  rw [if_pos ⟨1, by simp⟩]

theorem unitMatch_zero : UnitMatch 0 := by
  intro F E _ _ _ _ _ M a _
  letI := M.mG; letI := M.mU
  have hG : M.μG Set.univ = 1 := by
    rw [← M.volG]; congr 1; ext g; simp [glO]
  have hU : M.μU Set.univ = 1 := by
    rw [← M.volU]; congr 1; ext g; simp [uO]
  have hw : ∀ Y : Gl 0 F, omega Y = 1 := by
    intro Y
    have : lastDet Y = 1 := by simp [lastDet, Fin.last]
    rw [omega, this, eta_one']
  refine ⟨fun X hX => ?_, fun hn => (hn ⟨(0, 0, a.2.2), ?_⟩).elim⟩
  · have hl : X.2.2 = a.2.2 := (algebraMap F E).injective (congrArg (fun t => t.2.2) hX)
    by_cases hb : ‖a.2.2‖ ≤ 1 <;>
      simp [orbG, orbU, hw, unitG, unitU, act, actU, sec, Set.indicator, hl, hb, Measure.real, hG, hU]
  · exact Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) rfl)

end GlobalTheory.JR.SizeOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KerLEqTraceDotProductOfIsIsom
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem Et.kerL_eq_of_isIsom : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ y' y : A.L, A.kerL ψ x y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y)) := by
  intro F E _ _ _ _ _ A ψ x r j hj y' y
  have h2 : Module.finrank F E = 2 := Unram.finrank_eq
  haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ h2
  haveI : Module.Finite E A.L := Module.Finite.equiv j.symm
  haveI : Module.Free E A.L := Module.Free.of_equiv j.symm
  have hb : IsBaseChange A.K (IsScalarTower.toAlgHom F E A.L).toLinearMap := A.push.symm.out
  haveI : Module.Free A.K A.L := Module.Free.of_equiv hb.equiv
  haveI : Module.Finite A.K A.L := Module.Finite.equiv hb.equiv
  rw [hj y' y]
  unfold Et.kerL Et.psiK
  congr 1
  rw [← Algebra.smul_def, smul_mul_assoc, Algebra.trace_trace (R := F) (S := E), ← smul_eq_mul,
    ← LinearMap.map_smul, Algebra.trace_trace]
end GlobalTheory.JR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemInvLSIffTendsto
section
open GlobalTheory.BK PowerSeries Filter Topology

namespace GlobalTheory.BK

theorem mem_invL_S_iff_tendsto (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
    [CompleteSpace K] (f : K⟦X⟧) :
    f ∈ invL l (S O K e) ↔ Tendsto (fun n => ‖coeff n f‖ * wS K e n) atTop (𝓝 0) := by
  have h2 : (((l : S O K e) : K⟦X⟧)) = C (l : K) := by simp
  have hl : 0 < ‖(l : K)‖ := norm_pos_iff.2 (l_ne_zero l)
  have key : ∀ m n : ℕ, ‖coeff n ((((l : S O K e) : K⟦X⟧)) ^ m * f)‖ * wS K e n =
      ‖(l : K)‖ ^ m * (‖coeff n f‖ * wS K e n) := fun m n => by
    rw [h2, ← map_pow, coeff_C_mul, norm_mul, norm_pow, mul_assoc]
  constructor
  · rintro ⟨m, hm⟩
    have h := (mem_S.1 hm).2.const_mul (‖(l : K)‖ ^ m)⁻¹
    rw [mul_zero] at h
    refine h.congr fun n => ?_
    rw [key, inv_mul_cancel_left₀ (pow_pos hl m).ne']
  · intro hf
    obtain ⟨b, hb⟩ := hf.bddAbove_range
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
      (norm_l_lt_one (K := K) l)).mul_const b
    rw [zero_mul] at h
    obtain ⟨m, hm⟩ := (h.eventually (gt_mem_nhds zero_lt_one)).exists
    refine ⟨m, mem_S.2 ⟨fun n => ?_, ?_⟩⟩
    · rw [key]
      exact (mul_le_mul_of_nonneg_left (hb ⟨n, rfl⟩) (pow_pos hl m).le).trans hm.le
    · have h3 := hf.const_mul (‖(l : K)‖ ^ m)
      rw [mul_zero] at h3
      exact h3.congr fun n => (key m n).symm

end GlobalTheory.BK
end

