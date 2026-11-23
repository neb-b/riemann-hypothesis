module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumUnipotentConjEqZeroOfConstantTermZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0823
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0859
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupOperatorDepthMulDisjointColumns
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryDoubledBlockDiagOne
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

namespace GlobalTheory

theorem unitary_diag_one_mem_dbl : ∀ (R E : Type) [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) (β : Type)
    [Fintype β] [DecidableEq β] (J : Matrix β β E) (g : UG c J), ∃ gd : UG c (dbl J),
    ((gd : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E) = Matrix.fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1 := by
  intro R E _ _ _ c β _ _ J g
  have hg : ((g : GL β E) : Matrix β β E)ᵀ * J * ((g : GL β E) : Matrix β β E).map c = J := g.2
  have h1 : ((g : GL β E) : Matrix β β E) * (((g : GL β E)⁻¹ : GL β E) : Matrix β β E) = 1 := Units.mul_inv _
  have h2 : (((g : GL β E)⁻¹ : GL β E) : Matrix β β E) * ((g : GL β E) : Matrix β β E) = 1 := Units.inv_mul _
  have hm1 : (1 : Matrix β β E).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)
  have hm0 : (0 : Matrix β β E).map c = 0 := Matrix.map_zero _ (map_zero c)
  refine ⟨⟨⟨Matrix.fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1,
    Matrix.fromBlocks (((g : GL β E)⁻¹ : GL β E) : Matrix β β E) 0 0 1, ?_, ?_⟩, ?_⟩, rfl⟩
  · rw [Matrix.fromBlocks_multiply]; simp [h1, Matrix.fromBlocks_one]
  · rw [Matrix.fromBlocks_multiply]; simp [h2, Matrix.fromBlocks_one]
  · show (Matrix.fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1)ᵀ * dbl J *
        (Matrix.fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1).map c = dbl J
    rw [dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, hm0, hm1, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp [hg]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicGLMemIntegralCofinitePlaces
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix

namespace GlobalTheory.GLFinPlaces

theorem gl_mem_int_cofinite (E : Type) [Field E] [NumberField E] (a : ℕ) (k : GL (Fin a) (Af E)) :
    {w : HeightOneSpectrum (𝓞 E) | GeneralLinearGroup.map (pLoc E w) k ∉ KGL w (n := a)}.Finite := by
  have hent : ∀ M : Matrix (Fin a) (Fin a) (Af E), ∀ᶠ w in Filter.cofinite,
      ∀ i j, (M i j) w ∈ w.adicCompletionIntegers E := by
    intro M
    rw [Filter.eventually_all]; intro i
    rw [Filter.eventually_all]; intro j
    exact (M i j).2
  have h := (hent (k : Matrix (Fin a) (Fin a) (Af E))).and (hent ((k⁻¹ : GL (Fin a) (Af E)) : Matrix (Fin a) (Fin a) (Af E)))
  rw [Filter.eventually_cofinite] at h
  refine h.subset ?_
  intro w hw
  simp only [Set.mem_setOf_eq] at hw ⊢
  intro hg
  apply hw
  have key : ∀ M : Matrix (Fin a) (Fin a) (Af E), (∀ i j, (M i j) w ∈ w.adicCompletionIntegers E) →
      M.map (pLoc E w) ∈ (RingHom.mapMatrix (m := Fin a) (Ov E w).subtype).range := by
    intro M hM
    exact ⟨Matrix.of fun i j => (⟨(M i j) w, hM i j⟩ : Ov E w), by ext i j; rfl⟩
  refine P.glint_mem_range_of_integral _ _ ?_ ?_
  · exact key _ hg.1
  · rw [← map_inv]
    exact key _ hg.2

end GlobalTheory.GLFinPlaces
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeUnimodular
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf

theorem rat_valuation_le_one_eventually (x : ℚ) :
    ∀ᶠ w : HeightOneSpectrum ℤ in Filter.cofinite, w.valuation ℚ x ≤ 1 := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := ℤ) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hI : Ideal.span {b} ≠ (0 : Ideal ℤ) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hb0
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors hI).subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq] at hw ⊢
  by_contra hd
  apply hw
  have h1 : w.valuation ℚ (algebraMap ℤ ℚ b) = 1 :=
    le_antisymm (w.valuation_le_one b) (not_lt.1 fun h => hd ((w.valuation_lt_one_iff_dvd b).1 h))
  rw [map_div₀, h1, div_one]
  exact w.valuation_le_one a

variable {p : ℕ} [Fact p.Prime]

theorem rat_mem_integers_eventually (x : ℚ) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), algebraMap ℚ (Qv v) x ∈ v.1.adicCompletionIntegers ℚ := by
  have h := (Function.Injective.tendsto_cofinite (f := fun v : AwayP p => v.1) Subtype.val_injective).eventually
    (rat_valuation_le_one_eventually x)
  filter_upwards [h] with v hv
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v.1 x).trans_le hv

def starLin (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] : (R ⊗[ℚ] G.C) →ₗ[R] (R ⊗[ℚ] G.C) where
  toFun a := (starT G.star R a).unop
  map_add' x y := by rw [map_add (f := _), MulOpposite.unop_add]
  map_smul' r x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s y =>
      rw [TensorProduct.smul_tmul', starT_tmul, starT_tmul, TensorProduct.smul_tmul', RingHom.id_apply]
    | add x y hx hy =>
      rw [smul_add, map_add (f := _), MulOpposite.unop_add, hx, hy, map_add (f := _), MulOpposite.unop_add, smul_add]

theorem starLin_apply (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (a : R ⊗[ℚ] G.C) :
    starLin G R a = (starT G.star R a).unop := rfl

theorem isIntV_star_eventually : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p),
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a : Qv v ⊗[ℚ] G.C, IsIntV G v a →
      IsIntV G v (starT G.star (Qv v) a).unop := by
  intro p _ G
  have hs : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      ∀ ij : Fin (Module.finrank ℚ G.C) × Fin (Module.finrank ℚ G.C),
        algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr (G.star (Module.finBasis ℚ G.C ij.2)).unop ij.1)
          ∈ v.1.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun ij => rat_mem_integers_eventually _
  filter_upwards [hs] with v hv a ha i
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← starLin_apply, ← (basV G v).sum_repr a, map_sum, map_sum, Finsupp.finsetSum_apply]
  refine sum_mem fun j _ => ?_
  rw [map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
  refine mul_mem (ha j) ?_
  have hb : basV G v j = (1 : Qv v) ⊗ₜ Module.finBasis ℚ G.C j := by
    simp [basV, Algebra.TensorProduct.basis_apply]
  rw [hb, starLin_apply, starT_tmul, basV, Algebra.TensorProduct.basis_repr_tmul, one_smul,
    Finsupp.mapRange_apply]
  exact hv (i, j)

end GlobalTheory.OrbFinAf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfBoundedImageInFinitelyGeneratedSubgroup
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

theorem finite_of_bounded_image_closure_finset :
    ∀ {V E : Type} [AddCommGroup V] [Module ℚ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] (Φ : V →+ E),
      (∀ (k : ℕ) (e : Fin k → V), LinearIndependent ℚ e → LinearIndependent ℝ (fun j => Φ (e j))) →
      ∀ (S : Finset V) (Y : Set V), Y ⊆ (AddSubgroup.closure (S : Set V) : Set V) →
        ∀ R : ℝ, (∀ y ∈ Y, ‖Φ y‖ ≤ R) → Y.Finite := by
  intro V E _ _ _ _ _ Φ hΦ S Y hY R hR
  set M : Submodule ℤ V := Submodule.span ℤ (S : Set V) with hMdef
  have hMY : Y ⊆ (M : Set V) := by
    intro y hy
    have := hY hy
    rw [← Submodule.span_int_eq_addSubgroupClosure] at this
    exact this
  haveI : Module.Finite ℤ M := Module.Finite.span_of_finite ℤ S.finite_toSet
  haveI : Module.IsTorsionFree ℤ V := .trans_faithfulSMul ℤ ℚ V
  haveI : Module.Free ℤ M := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ M
  set n := Module.finrank ℤ M
  let e : Fin n → V := fun j => (b j : V)
  have heZ : LinearIndependent ℤ e := b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have heQ : LinearIndependent ℚ e := (LinearIndependent.iff_fractionRing ℤ ℚ).1 heZ
  have heR := hΦ n e heQ
  let T : (Fin n → ℝ) →ₗ[ℝ] E := Fintype.linearCombination ℝ (fun j => Φ (e j))
  have hT : LinearMap.ker T = ⊥ :=
    LinearMap.ker_eq_bot.2 (linearIndependent_iff_injective_fintypeLinearCombination.1 heR)
  obtain ⟨K, -, hK⟩ := T.exists_antilipschitzWith hT

  let f : V → (Fin n → ℤ) := fun y => if h : y ∈ M then fun j => b.repr ⟨y, h⟩ j else 0
  have hfy : ∀ y (h : y ∈ M), f y = fun j => b.repr ⟨y, h⟩ j := fun y h => by simp [f, h]
  have hinj : Set.InjOn f Y := by
    intro y hy z hz hyz
    have h1 := hMY hy
    have h2 := hMY hz
    rw [hfy y h1, hfy z h2] at hyz
    have : b.repr ⟨y, h1⟩ = b.repr ⟨z, h2⟩ := by
      ext j; exact congrFun hyz j
    have := b.repr.injective this
    simpa using congrArg Subtype.val this
  have hΦy : ∀ y (h : y ∈ M), Φ y = T (fun j => ((b.repr ⟨y, h⟩ j : ℤ) : ℝ)) := by
    intro y h
    have hs' : y = ∑ j, b.repr ⟨y, h⟩ j • e j := by
      have := congrArg (Subtype.val : M → V) (b.sum_repr ⟨y, h⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    conv_lhs => rw [hs']
    set_option synthInstance.maxHeartbeats 100000 in
      simp [T, Fintype.linearCombination_apply, map_sum, map_zsmul, Int.cast_smul_eq_zsmul]
  set N : ℤ := ⌈(K : ℝ) * R⌉
  have hsub : f '' Y ⊆ Set.Icc (fun _ => -N) (fun _ => N) := by
    rintro _ ⟨y, hy, rfl⟩
    have h := hMY hy
    rw [hfy y h]
    set c : Fin n → ℝ := fun j => ((b.repr ⟨y, h⟩ j : ℤ) : ℝ)
    have hc : ‖c‖ ≤ (K : ℝ) * R := by
      have h1 := ZeroHomClass.bound_of_antilipschitz T hK c
      rw [← hΦy y h] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left (hR y hy) K.2)
    have hcj : ∀ j, |c j| ≤ (K : ℝ) * R := fun j => by
      have h0 : ‖c j‖ ≤ ‖c‖ := norm_le_pi_norm c j
      rw [Real.norm_eq_abs] at h0
      exact h0.trans hc
    constructor <;> intro j
    · have h3 : -((K : ℝ) * R) ≤ c j := (abs_le.1 (hcj j)).1
      have h4 : (-(N : ℝ)) ≤ c j := le_trans (neg_le_neg (Int.le_ceil _)) h3
      have h5 : ((-N : ℤ) : ℝ) ≤ ((b.repr ⟨y, h⟩ j : ℤ) : ℝ) := by push_cast; exact h4
      exact Int.cast_le.1 h5
    · have h4 : c j ≤ (N : ℝ) := ((abs_le.1 (hcj j)).2).trans (Int.le_ceil _)
      exact Int.cast_le.1 h4
  exact Set.Finite.of_finite_image ((Set.finite_Icc _ _).subset hsub) hinj

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingNormFormSurjective
section
open IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.FinRingNorm

theorem field_case (F : Type) [Field F] [Finite F] (h2 : (2 : F) ≠ 0) (d s : F) (hd : d ≠ 0) :
    ∃ a b : F, a ^ 2 - d * b ^ 2 = s := by
  classical
  cases nonempty_fintype F
  have hc : ringChar F ≠ 2 := by
    intro h; apply h2
    have := ringChar.Nat.cast_ringChar (R := F)
    rw [h] at this; exact_mod_cast this
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic (R := F) (f := X ^ 2)
    (g := -(C d * X ^ 2) - C s) (by simp) (by compute_degree!) (FiniteField.odd_card_of_char_ne_two hc)
  refine ⟨a, b, ?_⟩
  simp only [eval_pow, eval_X, eval_sub, eval_neg, eval_mul, eval_C] at hab
  linear_combination hab

theorem reduced_case (S : Type) [CommRing S] [Finite S] [IsReduced S] (h2 : IsUnit (2 : S))
    (d s : S) (hd : IsUnit d) : ∃ a b : S, a ^ 2 - d * b ^ 2 = s := by
  classical
  have key : ∀ I : MaximalSpectrum S, ∃ a b : S ⧸ I.asIdeal,
      a ^ 2 - (Ideal.Quotient.mk I.asIdeal d) * b ^ 2 = Ideal.Quotient.mk I.asIdeal s := by
    intro I
    letI : Field (S ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : Finite (S ⧸ I.asIdeal) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
    have h2' : (2 : S ⧸ I.asIdeal) ≠ 0 := by
      have := (h2.map (Ideal.Quotient.mk I.asIdeal)).ne_zero
      rwa [map_ofNat] at this
    exact field_case _ h2' _ _ (hd.map (Ideal.Quotient.mk I.asIdeal)).ne_zero
  choose A B hAB using key
  refine ⟨(IsArtinianRing.equivPi S).symm A, (IsArtinianRing.equivPi S).symm B, ?_⟩
  apply (IsArtinianRing.equivPi S).injective
  funext I
  simp only [map_sub, map_mul, map_pow, AlgEquiv.apply_symm_apply, Pi.sub_apply, Pi.mul_apply,
    Pi.pow_apply]
  exact hAB I

theorem finiteRing_sq_sub_mul_sq_eq_of_card (n : ℕ) : ∀ (S : Type) [CommRing S] [Finite S], Nat.card S = n → IsUnit (2 : S) →
    ∀ d s : S, IsUnit d → IsUnit s → ∃ a b : S, a ^ 2 - d * b ^ 2 = s := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S _ _ hn h2 d s hd hs
  by_cases hred : IsReduced S
  · exact reduced_case S h2 d s hd

  obtain ⟨x, hx0, hx2⟩ : ∃ x : S, x ≠ 0 ∧ x ^ 2 = 0 := by
    rw [isReduced_iff] at hred
    push_neg at hred
    obtain ⟨y, ⟨k, hk⟩, hy⟩ := hred
    classical
    have hex : ∃ m, y ^ m = 0 := ⟨k, hk⟩
    let m := Nat.find hex
    have hm : y ^ m = 0 := Nat.find_spec hex
    have hm0 : m ≠ 0 := by
      intro h
      have : y ^ m = 1 := by rw [h, pow_zero]
      apply hy
      rw [← mul_one y, ← this, hm, mul_zero]
    have hm1 : m ≠ 1 := by
      intro h; apply hy; rw [← pow_one y, ← h, hm]
    obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    refine ⟨y ^ j, ?_, ?_⟩
    · exact Nat.find_min hex (by omega)
    · rw [← pow_mul]
      obtain ⟨t, ht⟩ : ∃ t, j * 2 = m + t := ⟨j * 2 - m, by omega⟩
      rw [ht, pow_add, hm, zero_mul]
  set I : Ideal S := Ideal.span {x} with hI
  have hlt : Nat.card (S ⧸ I) < n := by
    rw [← hn]
    classical
    cases nonempty_fintype S
    haveI : Finite (S ⧸ I) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
    cases nonempty_fintype (S ⧸ I)
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    apply Fintype.card_lt_of_surjective_not_injective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    intro hinj
    apply hx0
    apply hinj
    rw [map_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  haveI : Finite (S ⧸ I) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨a', b', hab'⟩ := ih _ hlt (S ⧸ I) rfl (h2.map (Ideal.Quotient.mk I)) _ _
    (hd.map (Ideal.Quotient.mk I)) (hs.map (Ideal.Quotient.mk I))
  obtain ⟨a0, rfl⟩ := Ideal.Quotient.mk_surjective a'
  obtain ⟨b0, rfl⟩ := Ideal.Quotient.mk_surjective b'
  have hmem : a0 ^ 2 - d * b0 ^ 2 - s ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [map_sub, map_mul, map_pow]
    rw [hab', sub_self]
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
  obtain ⟨u, hu⟩ := h2.exists_right_inv
  obtain ⟨t, ht⟩ := hs.exists_right_inv
  set iv := t - t ^ 2 * r * x with hiv
  have hv : (s + r * x) * iv - 1 = 0 := by
    rw [hiv]; linear_combination (1 - t * r * x) * ht - t ^ 2 * r ^ 2 * hx2
  refine ⟨a0 - r * a0 * iv * u * x, b0 - r * b0 * iv * u * x, ?_⟩
  linear_combination (1 - r * x * 2 * u * iv) * hr.symm - r * x * 2 * u * hv - r * x * hu + (r * iv * u) ^ 2 * (a0 ^ 2 - d * b0 ^ 2) * hx2

theorem exists_sq_sub_mul_sq_eq : ∀ (S : Type) [CommRing S] [Finite S], IsUnit (2 : S) →
    ∀ d s : S, IsUnit d → IsUnit s → ∃ a b : S, a ^ 2 - d * b ^ 2 = s :=
  fun S _ _ h2 d s hd hs => finiteRing_sq_sub_mul_sq_eq_of_card _ S rfl h2 d s hd hs

end GlobalTheory.FinRingNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRatHomology
section
open CategoryTheory Limits TensorProduct

namespace GlobalTheory.RatHomology

theorem finrank_rat_tensor (M : Type) [AddCommGroup M] [Module ℤ M] :
    Module.finrank ℚ (ℚ ⊗[ℤ] M) = Module.finrank ℤ M := by
  rw [← IsLocalizedModule.finrank_eq (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ M 1) le_rfl,
    ← IsFractionRing.finrank_right_eq ℤ ℚ]

theorem finrank_rat_homology (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    (_ : Module.Finite ℤ (C.homology n)) :
    Module.finrank ℚ ((((ModuleCat.extendScalars (Int.castRingHom ℚ)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj C).homology n) = Module.finrank ℤ (C.homology n) := by
  obtain ⟨e⟩ := GlobalTheory.FieldChangeInter.nonempty_homology_equiv ℚ C n
  have h := e.finrank_eq
  have hφ : algebraMap ℤ ℚ = Int.castRingHom ℚ := rfl
  rw [hφ] at h
  rw [h]
  exact finrank_rat_tensor (C.homology n)

end GlobalTheory.RatHomology
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumUnipotentConjEqZeroOfConstantTermZeroStatement
section
open MeasureTheory Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_unipotentConj_eq_zero_of_constantTerm_zero : ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (ι : Type) [Fintype ι] [DecidableEq ι] (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b) (f : GL ι K → ℂ),
  IsLocallyConstant f → HasCompactSupport f →
  (∀ (μ : Measure (Fin a → Fin b → K)), μ.IsAddHaarMeasure →
    ∀ g h : GL ι K, ∫ X, f (g * (h⁻¹ * GlobalTheory.OrbDesc.uGL e X * h)) ∂μ = 0) →
  ∀ K' : Subgroup (GL ι K), IsOpen (K' : Set (GL ι K)) → IsCompact (K' : Set (GL ι K)) →
  (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f (k * g * k') = f g) →
  ∀ γ ∈ GlobalTheory.OrbDesc.blockPar e, (γ : Matrix ι ι K).charpoly.Separable →
  ∑ᶠ q : GL ι K ⧸ (GlobalTheory.OrbDesc.blockUni e ⊓ (GlobalTheory.OrbDesc.blockPar e ⊓ K')),
    (if Quotient.out q ∈ GlobalTheory.OrbDesc.blockUni e then f ((Quotient.out q)⁻¹ * γ * Quotient.out q) else 0) = 0 := by
  first | (exact @GlobalTheory.OrbDesc.NSum.finsum_conj_eq_zero) | (exact GlobalTheory.OrbDesc.NSum.finsum_conj_eq_zero) | (intros; apply GlobalTheory.OrbDesc.NSum.finsum_conj_eq_zero  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixLineConjIff
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx

theorem fixLine_conj_iff {n : Type} [Fintype n] [DecidableEq n] (A B : GL n ℂ) (z : n → ℂ) :
    (∃ c : ℂ, (A : Matrix n n ℂ) *ᵥ z = c • z) ↔
      ∃ c : ℂ, ((B * A * B⁻¹ : GL n ℂ) : Matrix n n ℂ) *ᵥ ((B : Matrix n n ℂ) *ᵥ z) =
        c • ((B : Matrix n n ℂ) *ᵥ z) := by
  have key : ((B * A * B⁻¹ : GL n ℂ) : Matrix n n ℂ) *ᵥ ((B : Matrix n n ℂ) *ᵥ z) =
      (B : Matrix n n ℂ) *ᵥ ((A : Matrix n n ℂ) *ᵥ z) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_right, Units.val_mul, ← Matrix.mulVec_mulVec]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [key, hc, Matrix.mulVec_smul]⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [key, ← Matrix.mulVec_smul] at hc
    have h := congrArg (fun w => ((B⁻¹ : GL n ℂ) : Matrix n n ℂ) *ᵥ w) hc
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h
    rwa [inv_mul_cancel_left] at h

theorem fixL_conj_iff : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ)
    (y g : grp G β) (z : Fin G.n → ℂ),
    FixL G v β y z ↔ FixL G v β (g * y * g⁻¹) ((toV G v β g : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) := by
  intro p _ G v β y g z
  unfold FixL
  rw [map_mul, map_mul, map_inv]
  exact fixLine_conj_iff _ _ z

end GlobalTheory.LKCx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTheoremOfResolutionGaga
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

namespace GlobalTheory

theorem exists_left_basis_through_algHom : ∀ (L : Type) [Field L] [NumberField L] (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C]
    (ι : L →ₐ[ℚ] C), ∃ (r : ℕ) (e : Fin r → C), ∀ x : C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i := by
  intro L _ _ C _ _ _ ι
  letI : Module L C := Module.compHom C ι.toRingHom
  have hsmul : ∀ (l : L) (x : C), l • x = ι l * x := fun _ _ => rfl
  haveI : IsScalarTower ℚ L C := ⟨fun q l x => by
    rw [hsmul, hsmul, map_smul, smul_mul_assoc]⟩
  haveI : Module.Finite L C := Module.Finite.of_restrictScalars_finite ℚ L C
  let b := Module.finBasis L C
  refine ⟨Module.finrank L C, b, fun x => ⟨b.repr x, ?_, ?_⟩⟩
  · simp only [← hsmul]
    exact (b.sum_repr x).symm
  · intro c hc
    simp only [← hsmul] at hc
    rw [hc, b.repr_sum_self]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupOperatorDepthMulDisjointColumnsStatement
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupOperatorDepth_mul_disjoint_columns : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (κ : Type) [Fintype κ] [DecidableEq κ] (d : κ → ℕ) (G : ∀ b, LogFGL v (d b)) (ι : κ → Type) [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)] (u : ∀ b, ι b → Fin (d b) → C) (S : Set κ) (P Q : MvPolynomial (Σ b, ι b) C), (∀ x ∈ P.vars, x.1 ∈ S) → (∀ x ∈ Q.vars, x.1 ∉ S) → depth G u (P * Q) = depth G u P + depth G u Q := by
  first | exact @GlobalTheory.FGDepth.depth_mul_of_disjoint_columns | exact GlobalTheory.FGDepth.depth_mul_of_disjoint_columns | (intros; apply GlobalTheory.FGDepth.depth_mul_of_disjoint_columns <;> assumption)
end

