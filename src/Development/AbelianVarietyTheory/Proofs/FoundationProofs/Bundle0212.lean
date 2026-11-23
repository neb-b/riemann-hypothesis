module

public import Mathlib
public import Development.AutomorphicArithmetic.WeightCongruences.ProdCMTypeEmbeddingsRootOfUnityEqOne
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0208
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.TauLatticeLatticeHolds
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0207
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0005
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassTermBoundBetaOfToricDenominator
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds

namespace GlobalTheory.ToricDenomBridge

theorem exists_int_of_isIntegral {r : ℚ} (h : IsIntegral ℤ (r : ℂ)) : ∃ n : ℤ, (n : ℚ) = r := by
  have h' : IsIntegral ℤ (algebraMap ℚ ℂ r) := h
  exact IsIntegrallyClosed.isIntegral_iff.1 ((isIntegral_algebraMap_iff ).1 h')

theorem isIntLattice_of {d : ℕ} (hd : d.Prime) (h4 : d % 4 = 3) {Λ : PeriodPair} (h1 : Λ.ω₁ = 1)
    (h2 : Λ.ω₂ = (1 + Complex.I * (Real.sqrt d : ℝ)) / 2) : IsIntLattice d Λ := by
  set w : ℂ := Complex.I * (Real.sqrt d : ℝ) with hw
  have hw2 : w ^ 2 = -(d : ℂ) := by
    rw [hw, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    simp
  have hwc : starRingEnd ℂ w = -w := by simp [hw]
  have hZ : ∀ n : ℤ, IsIntegral ℤ (n : ℂ) := fun n => isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := n)
  obtain ⟨c, hc⟩ : ∃ c : ℕ, d + 1 = 4 * c := ⟨(d + 1) / 4, by omega⟩
  have hcC : (d : ℂ) + 1 = 4 * c := by exact_mod_cast hc
  intro x
  rw [PeriodPair.mem_lattice, h1, h2]
  constructor
  · rintro ⟨m, n, rfl⟩
    refine ⟨((hZ m).mul isIntegral_one).add ((hZ n).mul ?_), m + n / 2, n / 2, by push_cast; ring⟩
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (c : ℤ), by monicity!, ?_⟩
    rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
      algebraMap_int_eq, eq_intCast, Int.cast_natCast]
    linear_combination (1 / 4 : ℂ) * hw2 - (1 / 4 : ℂ) * hcC
  · rintro ⟨hx, a, b, rfl⟩
    have hx' : IsIntegral ℤ ((a : ℂ) - (b : ℂ) * w) := by
      have := hx.map_of_comp_eq (RingHom.id ℤ) (starRingEnd ℂ) (RingHom.ext_int _ _)
      simpa [hwc, sub_eq_add_neg] using this
    obtain ⟨t, ht⟩ := exists_int_of_isIntegral (r := 2 * a) (by
      refine (congrArg (IsIntegral ℤ) ?_).mpr (hx.add hx')
      push_cast; ring)
    obtain ⟨n, hn⟩ := exists_int_of_isIntegral (r := a ^ 2 + d * b ^ 2) (by
      refine (congrArg (IsIntegral ℤ) ?_).mpr (hx.mul hx')
      push_cast
      linear_combination (b : ℂ) ^ 2 * hw2)
    have hm2 : ((d : ℚ) * (2 * b)) ^ 2 = ((d * (4 * n - t ^ 2) : ℤ) : ℚ) := by
      push_cast
      rw [hn, ht]; ring
    obtain ⟨m, hm⟩ := exists_int_of_isIntegral (r := d * (2 * b)) (IsIntegral.of_pow two_pos (by
      rw [← Rat.cast_pow, hm2, Rat.cast_intCast]
      exact hZ _))
    have hm3 : m ^ 2 = d * (4 * n - t ^ 2) := by
      rw [← hm] at hm2
      exact_mod_cast hm2
    obtain ⟨u, rfl⟩ : (d : ℤ) ∣ m := (Nat.prime_iff_prime_int.1 hd).dvd_of_dvd_pow ⟨_, hm3⟩
    have hd0 : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne_zero
    have hu : (u : ℚ) = 2 * b := by
      push_cast at hm
      exact mul_left_cancel₀ hd0 hm
    have hn4 : 4 * n = t ^ 2 + d * u ^ 2 := by
      have : (4 : ℚ) * n = t ^ 2 + d * u ^ 2 := by rw [hn, ht, hu]; ring
      exact_mod_cast this
    have hcZ : (d : ℤ) = 4 * c - 1 := by omega
    have hpar : Even (t - u) := by
      have h5 : Even ((t - u) * (t - u)) :=
        ⟨2 * n - 2 * c * u ^ 2 + u ^ 2 - t * u, by rw [hcZ] at hn4; linear_combination -hn4⟩
      exact (Int.even_mul.1 h5).elim id id
    obtain ⟨k, hk⟩ := hpar
    refine ⟨k, u, ?_⟩
    have e1 : (t : ℂ) = 2 * a := by exact_mod_cast congrArg (Rat.cast : ℚ → ℂ) ht
    have e2 : (u : ℂ) = 2 * b := by exact_mod_cast congrArg (Rat.cast : ℚ → ℂ) hu
    have e3 : (t : ℂ) - u = k + k := by exact_mod_cast congrArg (Int.cast : ℤ → ℂ) hk
    linear_combination (-1 / 2 : ℂ) * e3 + (1 / 2 : ℂ) * e1 + (w / 2) * e2

variable {R : Ranks} (H : Host R)

theorem host_isAbelianGalois : IsAbelianGalois ℚ H.E := by
  have := H.hostE_isGalois
  have : IsMulCommutative Gal(H.E/ℚ) :=
    ⟨⟨fun σ τ => (H.gal).injective (by rw [map_mul, map_mul, mul_comm])⟩⟩
  exact {}

theorem host_unramFin : UnramFin H.E := by
  have : IsCMField H.E := H.isCMField_hostE
  have h : discr H.E = discr (maximalRealSubfield H.E) ^ 2 := H.der.discr_sq
  have h2 := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    (maximalRealSubfield H.E) (OF H.E) H.E (𝓞 H.E)
  rw [Algebra.IsQuadraticExtension.finrank_eq_two, h, Int.natAbs_pow] at h2
  have h0 : (discr (maximalRealSubfield H.E)).natAbs ^ 2 ≠ 0 := pow_ne_zero _ (Int.natAbs_ne_zero.2 (discr_ne_zero _))
  exact Ideal.absNorm_eq_one_iff.1 (mul_right_cancel₀ h0 (h2.symm.trans (one_mul _).symm))

theorem two_dvd_discr_host : (2 : ℤ) ∣ discr H.E := H.der.discr_primes.2.1

theorem finrank_le_of_isCMType {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (h : IsCMType φ) : Module.finrank ℚ E ≤ 2 * Fintype.card I := by
  have := Fintype.card_le_of_surjective (Sum.elim φ fun i => ComplexEmbedding.conjugate (φ i)) fun σ => by
    obtain ⟨i, hi | hi, -⟩ := h σ
    · exact ⟨Sum.inl i, hi.symm⟩
    · exact ⟨Sum.inr i, hi.symm⟩
  rwa [Embeddings.card, Fintype.card_sum, ← two_mul] at this

theorem isFieldData_host {I : Type} [Fintype I] {φ : I → H.E →+* ℂ} (h : IsCMType φ)
    (h' : ∀ τ τ', φ τ H.sqrtMinusD = φ τ' H.sqrtMinusD) : IsFieldData H.d φ := by
  have hcard : 2 ≤ Fintype.card I := by
    have h1 := finrank_le_of_isCMType h
    have h2 : Module.finrank ℚ H.E = 4 * R.ord := H.finrank_cmField
    have h3 : 0 < R.ord := R.ord_pos
    rw [h2] at h1
    omega
  refine ⟨H.hyp.2.1, by have := H.hyp.2.2.2.1; omega, host_unramFin H, fun x hx => ?_, two_dvd_discr_host H, hcard, h, ?_⟩
  · exact UpperTheory.prod_CMType_embeddings_root_of_unity_eq_one R H I φ h h' x (isOfFinOrder_iff_pow_eq_one.1 hx)
  · obtain ⟨i⟩ : Nonempty I := Fintype.card_pos_iff.1 (by omega)
    have hb : H.sqrtMinusD ^ 2 = -(H.d : H.E) := H.sqrtMinusD_sq
    have hsq : φ i H.sqrtMinusD ^ 2 = (Complex.I * (Real.sqrt H.d : ℝ)) ^ 2 := by
      rw [← map_pow, hb, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with e | e
    · exact ⟨_, hb, fun j => (h' j i).trans e⟩
    · exact ⟨-H.sqrtMinusD, by rw [neg_sq, hb], fun j => by rw [map_neg, h' j i, e, neg_neg]⟩

theorem classTermBoundBeta_of_toricDenominator (h : ToricDenominator) : GlobalTheory.ToricDenom.ClassTermBoundBeta := by
  intro R H I _ φ s κ 𝔣 χ hD Λ h1 h2 l hl
  have : IsCMField H.E := H.isCMField_hostE
  have := host_isAbelianGalois H
  obtain ⟨z, -, hz⟩ := h H.E I H.d φ s (isFieldData_host H hD.1 hD.2.1) hD.2.2.1
  have hΛ := isIntLattice_of H.hyp.2.1 (by have := H.hyp.2.2.2.1; omega) h1 h2
  refine ⟨⌈betaBound_vp H.d s κ 𝔣 z l⌉₊, fun Q hQ hQl y T hT => ?_⟩
  have := (hz κ 𝔣 Λ χ hD.2.2.2.2.1 hΛ hD.2.2.2.2.2 l hl Q hQ hQl).1 y T hT (⌈betaBound_vp H.d s κ 𝔣 z l⌉₊ : ℕ) 1 one_pos
    (by simpa using Nat.le_ceil _)
  simpa using this

theorem classTermBound_of_toricDenominator (h : ToricDenominator) : GlobalTheory.ToricDenom.ClassTermBound :=
  GlobalTheory.ToricDenom.classTermBound_of_beta (classTermBoundBeta_of_toricDenominator h)

end GlobalTheory.ToricDenomBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CrystallineCocycleTransportConjugation
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open scoped TensorProduct

namespace GlobalTheory.TwistedSelmerCompare

theorem natCast_mem_maximalIdeal {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] : (l : O) ∈ IsLocalRing.maximalIdeal O := by
  have h : ((IsLocalRing.maximalIdeal O).comap (algebraMap ℤ_[l] O)).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ_[l]) _
  have h2 := IsLocalRing.eq_maximalIdeal h
  have h3 : (l : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
    rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
  rw [← h2, Ideal.mem_comap, map_natCast] at h3
  exact h3

theorem padicInt_hom_ext {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (f g : ℤ_[l] →+* O) : f = g := by
  ext z
  rw [← sub_eq_zero, ← Ideal.mem_bot,
    ← Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal O).ne_top, Ideal.mem_iInf]
  intro n
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n z)
  have hz : z = (z.appr n : ℤ_[l]) + c * (l : ℤ_[l]) ^ n := by rw [hc]; ring
  have : f z - g z = (f c - g c) * (l : O) ^ n := by
    rw [hz]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
    ring
  rw [this]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hl n)

theorem crystallineCocycle_transport_conjugation {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K₁ K₂ L₁ L₂ : FinExt l)
    (θ : ↥(GK K₂) →* ↥(GK K₁)) (hθ : Continuous θ) (σ : GQ l)
    (hσ : ∀ g : ↥(GK K₂), (g : GQ l) = σ * (θ g : GQ l) * σ⁻¹) {k : ℕ}
    (M₁ : ↥(GK K₁) →* Matrix (Fin k) (Fin k) ↥L₁.1) (M₂ : ↥(GK K₂) →* Matrix (Fin k) (Fin k) ↥L₂.1)
    (p : ↥L₁.1 →ₗ[ℚ_[l]] ↥L₂.1)
    (hp : ∀ g (v : Fin k → ↥L₁.1), (fun j => p ((M₁ (θ g)).mulVec v j)) = (M₂ g).mulVec fun j => p (v j))
    (c : ↥(GK K₁) → Fin k → ↥L₁.1) (hc : c ∈ finiteCocycles (P.PD K₁) (matRep M₁)) :
    (fun g j => p (c (θ g) j)) ∈ finiteCocycles (P.PD K₂) (matRep M₂) := by
  obtain ⟨⟨hc1, hc2⟩, x, hx⟩ := hc
  have := L₁.2
  have hpc : Continuous p := p.continuous_of_finiteDimensional
  let q : (Fin k → ↥L₁.1) →ₗ[ℚ_[l]] (Fin k → ↥L₂.1) := LinearMap.compLeft p (Fin k)
  have hq : ∀ g v, q (matRep M₁ (θ g) v) = matRep M₂ g (q v) := fun g v => hp g v
  let T := TensorProduct.map q (P.actQ σ).toLinearMap
  have hT : ∀ g y, T (actVB (P.PD K₁) (matRep M₁) (θ g) y) = actVB (P.PD K₂) (matRep M₂) g (T y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul v b =>
      change q (matRep M₁ (θ g) v) ⊗ₜ[ℚ_[l]] P.actQ σ ((P.PD K₁).actB (θ g) b) =
        matRep M₂ g (q v) ⊗ₜ[ℚ_[l]] (P.PD K₂).actB g (P.actQ σ b)
      rw [hq, P.PD_actB, P.PD_actB, ← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, ← map_mul, ← map_mul]
      congr 3
      rw [hσ g]; group
  refine ⟨⟨continuous_pi fun j => hpc.comp ((continuous_apply j).comp (hc1.comp hθ)), fun g h => ?_⟩,
    T x, fun g => ?_⟩
  · change q (c (θ (g * h))) = q (c (θ g)) + matRep M₂ g (q (c (θ h)))
    rw [map_mul, hc2, map_add (f := _), hq]
  · rw [← hT, ← map_sub, ← hx]
    change q (c (θ g)) ⊗ₜ[ℚ_[l]] (1 : P.R.B) = q (c (θ g)) ⊗ₜ[ℚ_[l]] P.actQ σ 1
    rw [map_one]

section Coef

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O₀ O : Type} [CommRing O₀] [IsDomain O₀] [Algebra ℤ_[l] O₀] [TopologicalSpace O₀]
  [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O]

theorem toLLK_bijective (B : LocBridge l E Ω Gw O) : Function.Bijective (Br.toLLK B) := by
  refine ⟨(Br.toLLK B).injective, fun x => ?_⟩
  have := B.LL.2
  have : Algebra.IsAlgebraic ℤ_[l] ↥B.LL.1 := IsFractionRing.comap_isAlgebraic_iff.2
    (inferInstance : Algebra.IsAlgebraic ℚ_[l] ↥B.LL.1)
  obtain ⟨d, hd, hx⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ_[l]) x).exists_integral_multiple
  obtain ⟨n, hn⟩ := B.eO.surjective ⟨d • x, hx⟩
  refine ⟨algebraMap O _ n / algebraMap O _ (algebraMap ℤ_[l] O d), ?_⟩
  rw [map_div₀, Br.toLLK_alg, Br.toLLK_alg, hn, B.eO_alg, ← IsScalarTower.algebraMap_apply, div_eq_iff]
  · change d • x = _
    rw [Algebra.smul_def, mul_comm]
  · rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥B.LL.1]
    simpa using hd

theorem exists_coefMap (B₀ : LocBridge l E Ω Gw O₀) (B : LocBridge l E Ω Gw O) (f : O₀ →+* O)
    (hf : Function.Injective f) (hz : ∀ z : ℤ_[l], f (algebraMap ℤ_[l] O₀ z) = algebraMap ℤ_[l] O z) :
    ∃ φ : ↥B₀.LL.1 →ₐ[ℚ_[l]] ↥B.LL.1,
      ∀ x : FractionRing O₀, φ (Br.toLLK B₀ x) = Br.toLLK B (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap f hf x) := by
  let e := RingEquiv.ofBijective _ (toLLK_bijective B₀)
  let φ : ↥B₀.LL.1 →+* ↥B.LL.1 := (Br.toLLK B).comp ((GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap f hf).comp e.symm.toRingHom)
  have hφ : ∀ x, φ (Br.toLLK B₀ x) = Br.toLLK B (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap f hf x) := fun x =>
    congrArg (fun y => Br.toLLK B (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap f hf y)) (e.symm_apply_apply x)
  have hc : φ.comp (algebraMap ℚ_[l] ↥B₀.LL.1) = algebraMap ℚ_[l] ↥B.LL.1 := by
    refine IsFractionRing.ringHom_ext (A := ℤ_[l]) fun z => ?_
    have h := hφ (algebraMap O₀ _ (algebraMap ℤ_[l] O₀ z))
    rw [GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap_alg, hz, Br.toLLK_alg, Br.toLLK_alg, B.eO_alg, B₀.eO_alg,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h
    rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, h]
  exact ⟨{ φ with commutes' := fun q => DFunLike.congr_fun hc q }, hφ⟩

end Coef

end GlobalTheory.TwistedSelmerCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualFormIntegralOnDualFr
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

theorem star_mem_one_of_mem_one {K : Type} [Field K] [NumberField K] [StarRing K] {z : K}
    (hz : z ∈ (1 : Submodule (𝓞 K) K)) : star z ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨a, rfl⟩ := Submodule.mem_one.mp hz
  have ha : IsIntegral ℤ (algebraMap (𝓞 K) K a) := a.isIntegral_coe
  have hb : IsIntegral ℤ (star (algebraMap (𝓞 K) K a)) :=
    ha.map (starRingEnd K).toIntAlgHom
  exact Submodule.mem_one.mpr ⟨⟨_, hb⟩, rfl⟩

theorem inv_mulVec_star_mem_hdualFr {K : Type} [Field K] [NumberField K] [StarRing K] {N : ℕ}
    {H : Matrix (Fin N) (Fin N) K} (hd : IsUnit H.det) {M : Submodule (𝓞 K) (Fin N → K)} {x : Fin N → K}
    (hx : x ∈ dualFr M) : H⁻¹ *ᵥ star x ∈ hdualFr H M := by
  intro m hm
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec]
  have h := star_mem_one_of_mem_one (hx m hm)
  rw [← Matrix.star_dotProduct_star] at h
  exact h

theorem dualForm_integral_on_dualFr : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (N : ℕ) (H : Matrix (Fin N) (Fin N) K), Hᴴ = H → IsUnit H.det → ∀ (M : Submodule (𝓞 K) (Fin N → K)) (s : ℕ), (∀ x ∈ hdualFr H M, ∀ y ∈ hdualFr H M, (s : K) * (star x ⬝ᵥ H *ᵥ y) ∈ (algebraMap (𝓞 K) K).range) → ∀ x ∈ dualFr M, ∀ y ∈ dualFr M, (s : K) * (star x ⬝ᵥ (H⁻¹)ᵀ *ᵥ y) ∈ (algebraMap (𝓞 K) K).range := by
  intro K _ _ _ N H hH hd M s h x hx y hy
  have key := h _ (inv_mulVec_star_mem_hdualFr hd hy) _ (inv_mulVec_star_mem_hdualFr hd hx)
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec, Matrix.star_mulVec, star_star,
    Matrix.conjTranspose_nonsing_inv, hH, ← Matrix.mulVec_transpose, dotProduct_comm] at key
  exact key

end GlobalTheory.TestLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualLatticeIsLatticeAndHermitianDual
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.DualLat

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem mem_one_iff (x : K) : x ∈ (1 : Submodule (𝓞 K) K) ↔ IsIntegral ℤ x := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

theorem star_mem_one [StarRing K] {x : K} (h : x ∈ (1 : Submodule (𝓞 K) K)) :
    star x ∈ (1 : Submodule (𝓞 K) K) := by
  rw [mem_one_iff] at h ⊢
  exact map_isIntegral_int (starRingEnd K) h

theorem exists_den_finset (s : Finset K) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ x ∈ s, d • x ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨⟨d, hd⟩, hy⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K)) s
  exact ⟨d, nonZeroDivisors.ne_zero hd, fun x hx => Submodule.mem_one.2 (hy x hx)⟩

theorem exists_smul_mem {M : Submodule (𝓞 K) (Fin n → K)}
    {x : Fin n → K} (hx : x ∈ Submodule.span K (M : Set (Fin n → K))) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ M := by
  first
  | exact @_root_.GlobalTheory.DeterminantSimpLemma.main
  | exact _root_.GlobalTheory.DeterminantSimpLemma.main
  | (apply _root_.GlobalTheory.DeterminantSimpLemma.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.DeterminantSimpLemma.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DeterminantSimpLemma.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DeterminantSimpLemma.main ..)

theorem isLattice_dualFr (M : Submodule (𝓞 K) (Fin n → K)) (hM : Submodule.IsFullLattice K M) :
    Submodule.IsFullLattice K (dualFr M) :=
  du_dualFr_lattice latticeBasisExists_holds M hM

theorem isLattice_hdualFr [StarRing K] (G : Matrix (Fin n) (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K))
    (hG : IsUnit G.det) (hM : Submodule.IsFullLattice K M) : Submodule.IsFullLattice K (hdualFr G M) :=
  (dualFrameLattice_holds K n G M hG hM).2

omit [NumberField K] in
theorem star_dot [StarRing K] (x y : Fin n → K) : star (x ⬝ᵥ y) = star y ⬝ᵥ star x := by
  simp [dotProduct, mul_comm]

theorem hdualFr_dualFr [StarRing K] (G : Matrix (Fin n) (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K))
    (hG : IsUnit G.det) : hdualFr (G⁻¹)ᵀ (dualFr M) = dualFr (hdualFr G M) := by
  have key : ∀ φ ψ : Fin n → K, star φ ⬝ᵥ ((G⁻¹)ᵀ *ᵥ ψ) = ψ ⬝ᵥ (G⁻¹ *ᵥ star φ) := by
    intro φ ψ
    rw [Matrix.mulVec_transpose, dotProduct_comm, Matrix.dotProduct_mulVec]
  ext ψ
  constructor
  · intro h x hx
    have hφ : star (G *ᵥ x) ∈ dualFr M := by
      intro y hy
      have := star_mem_one (hx y hy)
      rwa [star_dot, star_star] at this
    have := h _ hφ
    rwa [key, star_star, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul G hG, Matrix.one_mulVec] at this
  · intro h φ hφ
    rw [key]
    refine h _ fun y hy => ?_
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G hG, Matrix.one_mulVec, ← star_dot]
    exact star_mem_one (hφ y hy)

theorem dualFr_lattice_and_hdual :
    (∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (G : Matrix (Fin n) (Fin n) K)
      (M : Submodule (𝓞 K) (Fin n → K)), IsUnit G.det → Submodule.IsFullLattice K M →
      Submodule.IsFullLattice K (dualFr M) ∧ Submodule.IsFullLattice K (hdualFr G M)) ∧ DualFrHdual :=
  ⟨fun _ _ _ _ _ G M hG hM => ⟨isLattice_dualFr M hM, isLattice_hdualFr G M hG hM⟩,
    fun _ _ _ _ _ G M _ hG _ => hdualFr_dualFr G M hG⟩

end GlobalTheory.DualLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLocalConjugationSelfDualLatticesHostStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_conjugation_selfDual_lattices_host : ∀ (D : D7) (V : HSp D) (L : Submodule (𝓞 D.host.E) V.V) (h1 : Submodule.IsLattice D.host.E L) (h2 : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L), ∃ γ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), HA (Fv D.host.F v) D.sp.cm.sig V.gram, {v | γ v ≠ 1}.Finite ∧ ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (y : Fin V.rank → Fv D.host.F v ⊗[D.host.F] D.host.E), y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := D.host.F) V v ↔ (HA.mat (Fv D.host.F v) D.sp.cm.sig V.gram (γ v)).1.mulVec y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := D.host.F) (GlobalTheory.VolRatioCompare.reLat V L h1 h2) v := by
  first | exact @GlobalTheory.LocalConjugacy.exists_local_conjugation | exact GlobalTheory.LocalConjugacy.exists_local_conjugation | (intros; apply GlobalTheory.LocalConjugacy.exists_local_conjugation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMapEqOfMemNabStd
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.LocInt

variable {K : Type} [Field K] [NumberField K]

theorem vw_eq_zero_of_notMem (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K} (hs : s ∉ w.asIdeal) :
    vw w (s : K) = 0 := by
  classical
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hs w.asIdeal.zero_mem
  have hJ : (Ideal.span {s} : Ideal (𝓞 K)) ≠ 0 := by
    rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  unfold vw
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K w hJ]
  have hm : Associates.mk (Ideal.span {s} : Ideal (𝓞 K)) ≠ 0 := by rwa [ne_eq, Associates.mk_eq_zero]
  by_contra h
  have h1 : 1 ≤ (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {s} : Ideal (𝓞 K))).factors := by
    apply Nat.one_le_iff_ne_zero.2
    intro h0
    exact h (by rw [h0]; rfl)
  rw [← Associates.prime_pow_dvd_iff_le hm w.associates_irreducible, pow_one,
    Associates.mk_le_mk_iff_dvd, Ideal.dvd_span_singleton] at h1
  exact hs h1

theorem exists_map_eq_of_mem_nabStd {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) {F : Pol K ι n}
    (hF : F ∈ nabStd K lam) : F ∈ LinearMap.range (toK K (ι × Fin n × Fin n)) := by
  refine (Submodule.span_le.2 ?_ : nabStd K lam ≤ _) hF
  rintro P ⟨G, hG, rfl⟩
  choose Q _ hQ using fun τ => Submodule.mem_map.1 (hG τ)
  refine ⟨∏ τ, Formalism.GradedWeylDivisibility.blockEmb (𝓞 K) τ (Q τ), ?_⟩
  change MvPolynomial.map (algebraMap (𝓞 K) K) _ = _
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← hQ τ]
  simp only [Formalism.GradedWeylDivisibility.blockEmb]
  exact map_rename _ _ _

theorem localIntegrality : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], (∀ a : K, (∀ w : HeightOneSpectrum (𝓞 K), 0 ≤ vw w a) → a ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (w : HeightOneSpectrum (𝓞 K)) (F : Pol K ι n), F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) → ∀ mo, 0 ≤ vw w (AddMonoidAlgebra.coeff F mo) := by
  intro K _ _ _
  refine ⟨fun a h => ?_, fun ι _ n lam w F hF mo => ?_⟩
  · by_cases ha : a = 0
    · subst ha
      exact zero_mem _
    · exact DualLatticeDivisor.mem_range_of_vw_nonneg a ha h
  · obtain ⟨s, hs, hsF⟩ := hF
    obtain ⟨Q, hQ⟩ := exists_map_eq_of_mem_nabStd lam hsF
    by_cases hc : AddMonoidAlgebra.coeff F mo = 0
    · rw [hc, ValuationRepresentative.vw_zero]
    have hs' : s ∉ w.asIdeal := hs
    have hs0 : (s : K) ≠ 0 := by
      intro h0
      have : s = 0 := RingOfIntegers.ext h0
      exact hs' (this ▸ w.asIdeal.zero_mem)
    have hco : (s : K) * AddMonoidAlgebra.coeff F mo = ((AddMonoidAlgebra.coeff Q mo : 𝓞 K) : K) := by
      have h1 := congrArg (AddMonoidAlgebra.coeff · mo) hQ
      rw [coeff_smul] at h1
      have h2 : AddMonoidAlgebra.coeff (toK K _ Q) mo = ((AddMonoidAlgebra.coeff Q mo : 𝓞 K) : K) := coeff_map _ _ _
      rw [← h2, h1, Algebra.smul_def]
    have h3 := ValuationRepresentative.vw_int_nonneg w (AddMonoidAlgebra.coeff Q mo)
    rwa [← hco, ValuationRepresentative.vw_mul w _ _ hs0 hc, vw_eq_zero_of_notMem w hs', zero_add] at h3

end GlobalTheory.LocInt
end

