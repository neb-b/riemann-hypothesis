module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedQuadraticDatumAtInertPlace
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFramedPointMoveUniversalTriple
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0023

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyUnitaryConjOfSameEllipticCharpolyInert
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.UnitInert

section Local

variable {O : Type} [CommRing O] [IsNoetherianRing O] {r : ℕ}

theorem exists_unitary_conj (I : Ideal O) [IsAdicComplete I O] [Finite (O ⧸ I)] {σ : O →+* O}
    (hσ : ∀ a, σ (σ a) = a) (hI : ∀ x ∈ I, σ x ∈ I) (hω : ∃ ω, IsUnit (ω - σ ω))
    {g h : Matrix (Fin r) (Fin r) O} (hg : cT σ g * g = 1) (hh : cT σ h * h = 1)
    (hs : g.charpoly.Separable) (e : h.charpoly = g.charpoly) :
    ∃ u : GL (Fin r) O, cT σ u.1 * u.1 = 1 ∧ g * u = u * h := by
  have hjac := IsAdicComplete.le_jacobson_bot I
  obtain ⟨v, hv⟩ := GlobalTheory.Orb.exists_cyclic_of_finite_quotient I hjac (g := g) hs
  obtain ⟨w, hw⟩ := GlobalTheory.Orb.exists_cyclic_of_finite_quotient I hjac (g := h) (show h.charpoly.Separable by rwa [e])
  obtain ⟨a, ha⟩ := (isUnit_iff_isUnit_det _).2 hv
  obtain ⟨b, hb⟩ := (isUnit_iff_isUnit_det _).2 hw
  have hy : g * (a * b⁻¹ : GL (Fin r) O) = (a * b⁻¹ : GL (Fin r) O) * h := by
    have h1 := GlobalTheory.Orb.mul_krylov_eq g v
    have h2 := GlobalTheory.Orb.mul_krylov_eq h w
    rw [← ha] at h1
    rw [← hb, e] at h2
    rw [Units.val_mul, ← mul_assoc, h1, Units.mul_inv_eq_iff_eq_mul, mul_assoc, mul_assoc, h2,
      Units.inv_mul_cancel_left]
  generalize a * b⁻¹ = y at hy
  set s : Matrix (Fin r) (Fin r) O → Matrix (Fin r) (Fin r) O := cT σ with hsdef
  have hm : ∀ a b, s (a * b) = s b * s a := fun a b => cT_mul σ a b
  have hadd : ∀ a b, s (a + b) = s a + s b := fun a b => Matrix.ext fun i j => by simp [s, cT]
  have hss : ∀ a, s (s a) = a := fun a => Matrix.ext fun i j => by simp [s, cT, hσ]
  have hsc : ∀ c : O, s (algebraMap O _ c) = algebraMap O _ (σ c) := fun c => by
    ext i j
    simp only [s, cT, transpose_apply, map_apply, algebraMap_matrix_apply, eq_comm (a := j)]
    split_ifs <;> simp
  have h1 : s 1 = 1 := by simpa using hsc 1
  change s g * g = 1 at hg
  change s h * h = 1 at hh
  let C := Subalgebra.centralizer O ({h} : Set (Matrix (Fin r) (Fin r) O))
  have hC : ∀ {a}, a ∈ C ↔ a * h = h * a := by simp [C, Subalgebra.mem_centralizer_iff, eq_comm]
  let _ : CommRing C :=
    { (inferInstance : Ring C) with
      mul_comm := fun a b => Subtype.ext (by
        obtain ⟨p, hp⟩ := GlobalTheory.Orb.exists_aeval_of_cyclic hw (hC.1 a.2)
        obtain ⟨q, hq⟩ := GlobalTheory.Orb.exists_aeval_of_cyclic hw (hC.1 b.2)
        rw [C.coe_mul, C.coe_mul, hp, hq, ← map_mul, ← map_mul, mul_comm]) }
  have : Module.Finite O (Matrix (Fin r) (Fin r) O) := inferInstanceAs (Module.Finite O (Fin r → Fin r → O))
  have : Module.Finite O C := Module.Finite.of_injective C.val.toLinearMap Subtype.val_injective
  have := GlobalTheory.InertNorm.isAdicComplete_map_of_finite I C
  have := GlobalTheory.InertNorm.finite_quotient_map_of_finite I C
  have hsC : ∀ a ∈ C, s a ∈ C := fun a ha => hC.2 (by
    have h2 := congrArg s (hC.1 ha)
    rw [hm, hm] at h2
    calc s a * h = h * (s h * s a) * h := by rw [← mul_assoc, mul_eq_one_comm.1 hh, one_mul]
      _ = h * s a := by rw [h2, mul_assoc, mul_assoc, hh, mul_one])
  let t : C →+* C :=
    { toFun := fun a => ⟨s a, hsC _ a.2⟩
      map_one' := Subtype.ext h1
      map_mul' := fun a b => by rw [mul_comm a b]; exact Subtype.ext (hm _ _)
      map_zero' := Subtype.ext (by simpa using hsc 0)
      map_add' := fun a b => Subtype.ext (hadd _ _) }
  have hιR : ∀ c, t (algebraMap O C c) = algebraMap O C (σ c) := fun c => Subtype.ext (hsc c)
  have hl : s y * y ∈ C := hC.2 (by
    have h2 : s h * (s y * y) * h = s y * y := by
      rw [← mul_assoc, ← hm, mul_assoc, ← hy, hm, mul_assoc, ← mul_assoc (s g), hg, one_mul]
    conv_rhs => rw [← h2, ← mul_assoc, ← mul_assoc, mul_eq_one_comm.1 hh, one_mul])
  have hlu : (s y * y) * ((y⁻¹ : GL (Fin r) O) * s (y⁻¹ : GL (Fin r) O)) = 1 := by
    rw [mul_assoc, Units.mul_inv_cancel_left, ← hm, Units.inv_mul, h1]
  have hl' : ((y⁻¹ : GL (Fin r) O) * s (y⁻¹ : GL (Fin r) O)) ∈ C := hC.2 (by
    have h2 := mul_eq_one_comm.1 hlu
    exact (Commute.units_inv_left (u := ⟨_, _, hlu, h2⟩) (hC.1 hl)).eq)
  obtain ⟨ω, hω⟩ := hω
  obtain ⟨z, hz⟩ := GlobalTheory.HenselianNorm.exists_norm_eq C (I.map (algebraMap O C)) t (fun a => Subtype.ext (hss _))
    (fun x hx => (show I.map (algebraMap O C) ≤ (I.map (algebraMap O C)).comap t from Ideal.map_le_iff_le_comap.2
      fun c hc => by
        rw [Ideal.mem_comap, Ideal.mem_comap, hιR]
        exact Ideal.mem_map_of_mem _ (hI c hc)) hx)
    ⟨algebraMap O C ω, by rw [hιR, ← map_sub]; exact hω.map _⟩ ⟨_, hl'⟩ (Subtype.ext (by
      change s _ = _
      rw [hm, hss])) (IsUnit.of_mul_eq_one_right ⟨_, hl⟩ (Subtype.ext hlu))
  have hz' : z.1 * s z.1 = (y⁻¹ : GL (Fin r) O) * s (y⁻¹ : GL (Fin r) O) := congrArg Subtype.val hz
  have h3 : (y * z.1) * s (y * z.1) = 1 := by
    rw [hm, mul_assoc, ← mul_assoc z.1, hz', mul_assoc, Units.mul_inv_cancel_left, ← hm, Units.mul_inv, h1]
  refine ⟨⟨_, _, h3, mul_eq_one_comm.1 h3⟩, mul_eq_one_comm.1 h3, ?_⟩
  change g * (y * z.1) = y * z.1 * h
  rw [← mul_assoc, hy, mul_assoc, mul_assoc, hC.1 z.2]

end Local

end GlobalTheory.BCT.UnitInert

namespace GlobalTheory.BCT.UnitInert

variable {E : Type} [Field E] [NumberField E]

theorem eventually_int (x : E) :
    ∀ᶠ w : Pl E in cofinite, algebraMap E (w.adicCompletion E) x ∈ w.adicCompletionIntegers E :=
  (algebraMap E (FiniteAdeleRing (𝓞 E) E) x).2

theorem eventually_lift (p : E[X]) : ∀ᶠ w : Pl E in cofinite, ∃ q : (w.adicCompletionIntegers E)[X],
    q.map (algebraMap _ (w.adicCompletion E)) = atPl w p := by
  have h : ∀ᶠ w : Pl E in cofinite, ∀ i ∈ p.support,
      algebraMap E (w.adicCompletion E) (p.coeff i) ∈ w.adicCompletionIntegers E := by
    rw [eventually_all_finset]
    exact fun i _ => eventually_int _
  filter_upwards [h] with w hw
  refine (Polynomial.mem_lifts _).1 ((Polynomial.lifts_iff_coeff_lifts _).2 fun i => ?_)
  rw [coeff_map]
  by_cases hi : i ∈ p.support
  · exact ⟨⟨_, hw i hi⟩, rfl⟩
  · rw [notMem_support_iff.1 hi, map_zero]
    exact ⟨0, map_zero _⟩

theorem eventually_separable (P : E[X]) (hP : P.Separable) : ∀ᶠ w : Pl E in cofinite,
    ∀ q : (w.adicCompletionIntegers E)[X], q.map (algebraMap _ (w.adicCompletion E)) = atPl w P → q.Separable := by
  obtain ⟨u, v, huv⟩ := hP
  filter_upwards [eventually_lift u, eventually_lift v] with w ⟨u', hu⟩ ⟨v', hv⟩ q hq
  refine ⟨u', v', Polynomial.map_injective (algebraMap _ (w.adicCompletion E)) Subtype.val_injective ?_⟩
  rw [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map, hq, hu, hv,
    Polynomial.derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add, huv,
    Polynomial.map_one, Polynomial.map_one]

theorem conj_of_charpoly_inert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ P ∈ Ell E n, ∀ᶠ w in cofinite, ¬ IsSplitAt w → ∀ γ γ' : UL n w, γ ∈ KL n w → γ' ∈ KL n w →
      γ.1.val.charpoly = atPl w P → γ'.1.val.charpoly = atPl w P → ∃ g : UL n w, γ' = g⁻¹ * γ * g := by
  intro E _ _ _ hU n _ P hP
  filter_upwards [eventually_separable P hP.2.2.1] with w hsep hw γ γ' hγK hγ'K hγ hγ'
  let O := w.adicCompletionIntegers E
  let ι := algebraMap O (w.adicCompletion E)
  have hι : Function.Injective ι := Subtype.val_injective
  obtain ⟨y', hy'⟩ : ∃ y' : GL (Fin n) O, GeneralLinearGroup.map ι y' = γ.1 := (Subgroup.mem_subgroupOf.1 hγK)
  obtain ⟨z', hz'⟩ : ∃ z' : GL (Fin n) O, GeneralLinearGroup.map ι z' = γ'.1 := (Subgroup.mem_subgroupOf.1 hγ'K)
  obtain ⟨-, hcc, hv, h4, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
  obtain ⟨ϖ, q, ⟨-, -, -, -, ⟨x₀, hx₀, hx₁⟩, hq2, hcard⟩, -⟩ := (h4 hw).2.1
  have hcard' : Nat.card (O ⧸ IsLocalRing.maximalIdeal O) = q ^ 2 := hcard
  haveI := GlobalTheory.HenselSquare.isAdicComplete_integers E w
  haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) :=
    Nat.finite_of_card_ne_zero (by rw [hcard']; positivity)
  let c : O →+* O := (cj w).restrict _ _ (ThBasic.cj_mem_integers hU w)
  have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (hcc _)
  have hmapc : ∀ M : Matrix (Fin n) (Fin n) O, (cT c M).map ι = cT (cj w) (M.map ι) := fun M => by
    ext i j; rfl
  have hUL : ∀ x : GLw n w, x ∈ UL n w ↔ cT (cj w) x.val * x.val = 1 := fun x => by
    rw [UL, if_neg hw]
    change cT (cj w) x.val * 1 * x.val = 1 ↔ _
    rw [mul_one]
  have hmv : ∀ x : GL (Fin n) O, (GeneralLinearGroup.map ι x).val = x.val.map ι := fun x => by
    ext i j; rfl
  have hunit : ∀ (x : GL (Fin n) O), GeneralLinearGroup.map ι x ∈ UL n w → cT c x.val * x.val = 1 := fun x hx => by
    refine Matrix.map_injective hι ?_
    show (cT c x.val * x.val).map ι = (1 : Matrix (Fin n) (Fin n) O).map ι
    rw [Matrix.map_mul, hmapc, Matrix.map_one _ (map_zero ι) (map_one ι), ← hmv]
    exact (hUL _).1 hx
  have hch : ∀ x : GL (Fin n) O, x.val.charpoly.map ι = (GeneralLinearGroup.map ι x).val.charpoly := fun x =>
    (Matrix.charpoly_map _ _).symm
  have e1 : y'.val.charpoly.map ι = atPl w P := by rw [hch, hy', hγ]
  have e2 : z'.val.charpoly.map ι = atPl w P := by rw [hch, hz', hγ']
  obtain ⟨u, hu, hcu⟩ := exists_unitary_conj (IsLocalRing.maximalIdeal O) (σ := c) hc
    (fun x hx => by
      rw [GlobalTheory.InertUQ.mem_max_iff] at hx ⊢
      exact (hv _).trans_lt hx)
    ⟨⟨x₀, hx₀⟩, by
      rw [← IsLocalRing.notMem_maximalIdeal, GlobalTheory.InertUQ.mem_max_iff]
      change ¬ Valued.v (x₀ - cj w x₀) < 1
      rw [Valuation.map_sub_swap, hx₁]
      exact lt_irrefl _⟩
    (hunit y' (hy' ▸ γ.2)) (hunit z' (hz' ▸ γ'.2)) (hsep _ e1)
    (Polynomial.map_injective ι hι (e2.trans e1.symm))
  let g : GLw n w := GeneralLinearGroup.map ι u
  have hg : g ∈ UL n w := by
    rw [hUL]
    have := congrArg (fun M => M.map ι) hu
    simp only [Matrix.map_mul, hmapc, Matrix.map_one _ (map_zero ι) (map_one ι)] at this
    exact this
  have key : γ.1 * g = g * γ'.1 := by
    rw [← hy', ← hz', ← map_mul, ← map_mul]
    congr 1
    exact Units.ext hcu
  refine ⟨⟨g, hg⟩, Subtype.ext ?_⟩
  change γ'.1 = g⁻¹ * γ.1 * g
  rw [mul_assoc, key, inv_mul_cancel_left]

end GlobalTheory.BCT.UnitInert
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmEllipticCurveGaloisTorsionSections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj

namespace GlobalTheory.TorsionModel

theorem exists_galois (B : Type) [CommRing B] [Module.Finite ℤ B] :
    ∃ (N : IntermediateField ℚ ℂ) (_ : NumberField N) (_ : IsGalois ℚ N), ∀ χ : B →+* ℂ,
      ∃ χ' : B →+* 𝓞 N, ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)).comp χ' = χ := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := B)
  have hi : ∀ b : B, IsIntegral ℤ b := fun b => IsIntegral.of_finite ℤ b
  choose p hp hp' using hi
  let q : Polynomial ℚ := (∏ b ∈ s, p b).map (algebraMap ℤ ℚ)
  have hq : q.Monic := (Polynomial.monic_prod_of_monic _ _ fun b _ => hp b).map _
  let N : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (q.rootSet ℂ)
  have hN : Polynomial.IsSplittingField ℚ N q :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  have : FiniteDimensional ℚ N := Polynomial.IsSplittingField.finiteDimensional N q
  have : Normal ℚ N := Normal.of_isSplittingField q
  have : NumberField N := ⟨⟩
  refine ⟨N, inferInstance, ⟨⟩, fun χ => ?_⟩
  have hm : ∀ b, χ b ∈ N := fun b => by
    have hb : b ∈ Submodule.span ℤ (s : Set B) := hs ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem c hc =>
      refine IntermediateField.subset_adjoin ℚ _ (Polynomial.mem_rootSet.2 ⟨hq.ne_zero, ?_⟩)
      rw [Polynomial.aeval_map_algebraMap, map_prod]
      refine Finset.prod_eq_zero hc ?_
      have h := congrArg χ (hp' c)
      rw [Polynomial.hom_eval₂, map_zero] at h
      rw [Polynomial.aeval_def, ← h]
      congr 1
      exact RingHom.ext_int _ _
    | zero => rw [map_zero]; exact zero_mem _
    | add _ _ _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul r c _ hc => rw [map_zsmul]; exact zsmul_mem hc r
  let χ₁ : B →+* N := χ.codRestrict N hm
  exact ⟨χ₁.codRestrict (integralClosure ℤ N) fun b => (IsIntegral.of_finite ℤ b).map χ₁.toIntAlgHom, rfl⟩

theorem exists_finite_ring {R : Type} [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Sp R) [IsFinite q] :
    ∃ (B : Type) (_ : CommRing B) (g : R →+* B) (e : Sp B ≅ Z), g.Finite ∧ e.hom ≫ q = spMap g := by
  have : IsAffine Z := isAffine_of_isAffineHom q
  obtain ⟨g, hg⟩ := Spec.map_surjective (Z.isoSpec.inv ≫ q)
  refine ⟨Γ(Z, ⊤), inferInstance, g.hom, Z.isoSpec.symm, ?_, hg.symm⟩
  have : IsFinite (Spec.map g) := by rw [hg]; infer_instance
  exact (IsFinite.SpecMap_iff g).1 this

theorem exists_integral_points (hM : Out.MulNSt) {R : Type} [CommRing R] [Module.Finite ℤ R] (P : Out.PolAV (Sp R))
    (σ : R →+* ℂ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ (N : IntermediateField ℚ ℂ) (_ : NumberField N) (_ : IsGalois ℚ N) (f : R →+* 𝓞 N),
      ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)).comp f = σ ∧ ∀ x : Over.mk (spMap σ) ⟶ P.A, x ^ n = 1 →
        ∃ y : Over.mk (spMap f) ⟶ P.A, y ^ n = 1 ∧
          spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)) ≫ y.left = x.left := by
  have : IsNoetherianRing R := IsNoetherianRing.of_finite ℤ R
  have := (hM _ P n hn).1
  let η₀ : Sp R ⟶ P.A.left := (η[P.A]).left
  have hη : η₀ ≫ P.A.hom = 𝟙 _ := Over.w η[P.A]
  have hw : (Out.mulA P.A n).left ≫ P.A.hom = P.A.hom := Over.w _
  have key : ∀ {T : Over (Sp R)} (x : T ⟶ P.A), x ^ n = 1 ↔ x.left ≫ (Out.mulA P.A n).left = T.hom ≫ η₀ := by
    intro T x
    have e₁ : x ≫ Out.mulA P.A n = x ^ n := by rw [Out.mulA, MonObj.comp_pow, Category.comp_id]
    have e₂ : (1 : T ⟶ P.A).left = T.hom ≫ η₀ := by rw [Hom.one_def]; simp [η₀]
    rw [← Over.comp_left, e₁, ← e₂]
    exact ⟨fun h => by rw [h], Over.OverMorphism.ext⟩
  obtain ⟨B, _, g, e, hg, he⟩ := exists_finite_ring (pullback.snd (Out.mulA P.A n).left η₀)
  have : Module.Finite ℤ B := by
    have h := RingHom.Finite.comp hg (RingHom.finite_algebraMap.2 (inferInstance : Module.Finite ℤ R))
    rw [RingHom.ext_int (g.comp _) (algebraMap ℤ B)] at h
    exact RingHom.finite_algebraMap.1 h
  obtain ⟨N, _, _, hN⟩ := exists_galois B
  have main : ∀ x : Over.mk (spMap σ) ⟶ P.A, x ^ n = 1 → ∃ χ' : B →+* 𝓞 N,
      (∀ r, ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)) (χ' (g r)) = σ r) ∧
      spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)) ≫ spMap χ' ≫ e.hom ≫ pullback.fst _ _ = x.left := by
    intro x hx
    obtain ⟨χ, hχ⟩ := Spec.map_surjective (pullback.lift x.left (spMap σ) ((key x).1 hx) ≫ e.inv)
    obtain ⟨χ', h⟩ := hN χ.hom
    have e₁ : spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)) ≫ spMap χ' = Spec.map χ :=
      Ex.UnifModel.spMap_comp fun r => congr($h r)
    refine ⟨χ', fun r => ?_, by rw [reassoc_of% e₁, hχ, Category.assoc, e.inv_hom_id_assoc, pullback.lift_fst]⟩
    have e₂ : Spec.map χ ≫ spMap g = spMap σ := by
      rw [← he, hχ, Category.assoc, e.inv_hom_id_assoc, pullback.lift_snd]
    rw [← Spec.map_comp] at e₂
    exact (congr($h (g r))).trans (congrArg (fun f => f.hom r) (Spec.map_injective e₂))
  obtain ⟨χ₀, h₀, -⟩ := main 1 (one_pow n)
  refine ⟨N, inferInstance, inferInstance, χ₀.comp g, RingHom.ext h₀, fun x hx => ?_⟩
  obtain ⟨χ', h₁, h₂⟩ := main x hx
  have e₁ : spMap χ' ≫ spMap g = spMap (χ₀.comp g) := Ex.UnifModel.spMap_comp fun r =>
    RingOfIntegers.coe_injective ((algebraMap N ℂ).injective ((h₁ r).trans (h₀ r).symm))
  have e₂ : (spMap χ' ≫ e.hom ≫ pullback.fst _ _) ≫ (Out.mulA P.A n).left = spMap (χ₀.comp g) ≫ η₀ := by
    rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% he, reassoc_of% e₁]
  exact ⟨Over.homMk (spMap χ' ≫ e.hom ≫ pullback.fst _ _) (by
    rw [← hw, ← Category.assoc, e₂, Category.assoc, hη]; exact Category.comp_id _), (key _).2 e₂, h₂⟩

theorem exists_ell_fibre {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M) (ω : 𝓞 M) (C : GlobalTheory.CM.Ell H (𝓞 M) ω) (C₀ : GlobalTheory.CompRat.Curve H)
      (ψ : C₀.P.A.left ⟶ C.P.A.left), (2 * ω - 1) ^ 2 = -(H.d : 𝓞 M) ∧
      IsGrpPullback C₀.P.A C.P.A (spMap ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))) ψ := by
  have : NeZero H.d := ⟨H.d_prime.ne_zero⟩
  obtain ⟨χ, hχ⟩ := exists_isKroneckerChar (d := H.d) H.d_prime.ne_zero (Or.inr (by have := H.d_mod; omega))
  obtain ⟨M, _, ω, C, -, hω, hC, -⟩ := CM.EllExists.exists_ell cmCurve_closed thetaUnifAV_all firstFiveLaws.1
    (CM.homExtDvr_of_card_torsion GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional) E H χ hχ H.rt0 H.sqrt_neg_disc_sq
  obtain ⟨Q, ψ, hψ⟩ := exists_isPolFibre firstFiveLaws.1.polBaseChange
    ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) C.P
  obtain ⟨u, hu⟩ := PureType.exists_isThetaUnif thetaUnifAV_all Q
  obtain ⟨c, hc, hΛ⟩ := hC Q ψ hψ u
  refine ⟨M, inferInstance, ω, C, ⟨Q, hψ.1.trans C.dim, u, hu, c, hc, hΛ⟩, ψ, ?_, hψ.2.1⟩
  refine RingOfIntegers.coe_injective ((algebraMap M ℂ).injective ?_)
  rw [← RingHom.comp_apply, ← RingHom.comp_apply]
  rw [map_pow, map_sub, map_mul, map_one, map_ofNat, map_neg, map_natCast, ← H.sqrt_neg_disc_sq, ← hω]
  rfl

theorem exists_ell_torsion_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (n : ℕ), 0 < n → ∃ (N : IntermediateField ℚ ℂ) (_ : NumberField N) (_ : IsGalois ℚ N) (ω : 𝓞 N) (C : GlobalTheory.CM.Ell H (𝓞 N) ω) (C₀ : GlobalTheory.CompRat.Curve H) (ψ : C₀.P.A.left ⟶ C.P.A.left), (2 * ω - 1) ^ 2 = -(H.d : 𝓞 N) ∧ IsGrpPullback C₀.P.A C.P.A (spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N))) ψ ∧ ∀ a : ℤ × ℤ, ∃ y : Over.mk (𝟙 (Sp (𝓞 N))) ⟶ C.P.A, y ^ n = 1 ∧ C₀.pt (GlobalTheory.CompRat.wC H a / n) ≫ ψ = spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)) ≫ y.left := by
  intro E _ _ _ H n hn
  obtain ⟨M, _, ω, C, C₀, ψ, hω, hψ⟩ := exists_ell_fibre H
  obtain ⟨N, _, _, f, hf, hN⟩ := exists_integral_points firstFiveLaws.1.mulN C.P
    ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) hn
  obtain ⟨C', φ, -, ⟨-, hφ, -⟩, -⟩ := CM.exists_ellMap firstFiveLaws.1.polBaseChange E H _ ω C _ f
  have e : spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)) ≫ spMap f =
      spMap ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) := Ex.UnifModel.spMap_comp fun r => congr($hf r)
  have w : ψ ≫ C.P.A.hom = (C₀.P.A.hom ≫ spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N))) ≫ spMap f := by
    rw [Category.assoc, e, hψ.1.w]
  refine ⟨N, inferInstance, inferInstance, f ω, C', C₀, hφ.1.lift _ _ w, by simpa [map_ofNat] using congrArg f hω,
    hφ.cancel (hψ.congr e.symm (hφ.1.lift_fst _ _ w).symm) (hφ.1.lift_snd _ _ w), fun a => ?_⟩
  obtain ⟨ε, hε⟩ := exists_mulEquiv_of_isGrpPullback hψ (𝟙 (Sp ℂ)) _ (Category.id_comp _).symm
  obtain ⟨ε', hε'⟩ := exists_mulEquiv_of_isGrpPullback hφ (𝟙 (Sp (𝓞 N))) _ (Category.id_comp _).symm
  obtain ⟨y, hy, hy'⟩ := hN (ε (C₀.u.ex fun _ => C₀.c * (CompRat.wC H a / n))) (by
    rw [← map_pow]
    exact (congrArg ε (CurveField.ex_pow_eq_one C₀ hn a)).trans (map_one ε))
  obtain ⟨z, rfl⟩ := ε'.surjective y
  rw [hε, hε'] at hy'
  refine ⟨z, ε'.injective (by rw [map_pow, hy, map_one]), ?_⟩
  have ho : C₀.pt (CompRat.wC H a / n) ≫ C₀.P.A.hom = 𝟙 _ := Over.w (C₀.u.ex fun _ => C₀.c * (CompRat.wC H a / n))
  have hz : z.left ≫ C'.P.A.hom = 𝟙 (Sp (𝓞 N)) := Over.w z
  refine hφ.1.hom_ext ?_ ?_
  · rw [Category.assoc, hφ.1.lift_fst, Category.assoc]
    exact hy'.symm
  · rw [Category.assoc, hφ.1.lift_snd, Category.assoc, hz, reassoc_of% ho]
    exact (Category.comp_id _).symm

end GlobalTheory.TorsionModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulReadingOfMovedSectionAtFrame
section
set_option autoImplicit false

namespace GlobalTheory.GeoLevel

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix


set_option maxHeartbeats 1000000 in
theorem exists_const_rdU_of_moveMatch : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U U' : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → Formalism.L2.PjFree.IsUnf U' → ∀ (k : U.Comp) (k' : U'.Comp) (δ : GL (Fin r) E) (h : IsMatch (U.X k) (U'.X k') δ) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), ρ ≫ Xo.s = Xo.s → MoveMatch U U' k k' h ρ ν → (∀ (x : (U.X k).dom) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), IsUnitFr (U.X k) x.1 → FrMove ρ ν (U.un k x) y' → FrBor t (U'.un k' ⟨_, h.mem_dom x.2⟩) y' → cabs (t none : CAt σ) = 1) → ∀ n : ℕ, ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ w, Dom w n → ∀ f ∈ sec Xo c w n, ∀ f' ∈ sec Xo c w n, (∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y') → ∀ x ∈ (U.X k).dom, Formalism.L2.PjFree.rdU U f' k x = ε * Formalism.L2.PjFree.rdU U' f k' (lact δ (castFr h.psi x)) := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U U' hσ hU hU' k k' δ h ρ ν hρ hM hone n
  obtain ⟨hun1, -⟩ := GlobalTheory.FrameNorm.exists_unitFr_frBor E H Dw l Xo c σ r U hσ hU
  have hex : ∀ x : (U.X k).dom, ∃ (y' : FrPt Xo c (CAt σ)) (t₀ : (CAt σ)ˣ), FrMove ρ ν (U.un k x) y' ∧
      FrBor (fun i => Option.elim i t₀ (fun _ => 1)) (U'.un k' ⟨_, h.mem_dom x.2⟩) y' := fun x => by
    obtain ⟨y', hy'⟩ := (GlobalTheory.exists_unique_frMove E H Dw l Xo c ρ ν hρ (CAt σ) (U.un k x)).1
    obtain ⟨t₀, ht₀⟩ := exists_frBor_gen _ y' (hM x y' hy').1 (hM x y' hy').2
    exact ⟨y', t₀, hy', ht₀⟩
  choose y' t₀ hm hb using hex
  have hla : ∀ (w : (E →+* ℂ) × ℕ → ℕ) (τ : (U'.X k').Ψ) (i : Fin r),
      Formalism.L2.PjFree.laU U' w n k' τ i = Formalism.L2.PjFree.laU U w n k ⟨τ.1, h.mem τ⟩ i := fun w τ i => by
    unfold Formalism.L2.PjFree.laU
    rw [h.p0]
  have key : ∀ w, Dom w n → ∀ f ∈ sec Xo c w n, ∀ f' ∈ sec Xo c w n,
      (∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y') → ∀ x : (U.X k).dom,
      Formalism.L2.PjFree.rdU U f' k x.1 = Formalism.L2.PjFree.toC (t₀ x : CAt σ) ^ n *
        Formalism.L2.PjFree.rdU U' f k' (lact δ (castFr h.psi x.1)) := fun w hD f hf f' hf' hv x => by
    have v1 : Formalism.L2.PjFree.rdU U f' k x.1 = Formalism.L2.PjFree.toC (evR Xo c f' (U.un k x)) := dif_pos x.2
    have v2 : Formalism.L2.PjFree.rdU U' f k' (lact δ (castFr h.psi x.1)) =
      Formalism.L2.PjFree.toC (evR Xo c f (U'.un k' ⟨_, h.mem_dom x.2⟩)) := dif_pos (h.mem_dom x.2)
    have v3 := (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 (CAt σ)
        (inferInstanceAs (IsReduced ℂ)) w n f hf _ _ (y' x) (hb x)
    have v4 : Formalism.L2.PjFree.toC (wchar (ex Dw w n) (fun i => Option.elim i (t₀ x) (fun _ => 1)) : CAt σ) =
        Formalism.L2.PjFree.toC (t₀ x : CAt σ) ^ n := by
      have : Formalism.L2.PjFree.toC (wchar (ex Dw w n) (fun i => Option.elim i (t₀ x) (fun _ => 1)) : CAt σ) =
          ∏ j, Formalism.L2.PjFree.toC (((fun i => Option.elim i (t₀ x) (fun _ => 1) : Ix Dw → (CAt σ)ˣ) j : (CAt σ)ˣ) : CAt σ) ^ ex Dw w n j := rfl
      rw [this, Finset.prod_eq_single none]
      · rfl
      · rintro (_ | j) _ hj
        · exact (hj rfl).elim
        · exact one_pow _
      · intro hn; exact (hn (Finset.mem_univ _)).elim
    rw [v1, v2, hv _ _ (hm x), v3, ← v4]
    rfl
  obtain ⟨ε, hε, hc⟩ := GlobalTheory.exists_norm_one_const_ratio_of_common_ratio (Frame (U.X k).Ψ r)
    {p : ((E →+* ℂ) × ℕ → ℕ) × Rul Xo c × Rul Xo c // Dom p.1 n ∧ p.2.1 ∈ sec Xo c p.1 n ∧ p.2.2 ∈ sec Xo c p.1 n ∧
      ∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c p.2.2 y = evR Xo c p.2.1 y'}
    (U.X k).dom (FourierCoefficientDomain.isOpen_dom _) (GlobalTheory.frames_isConnected E r (U.X k)).isPreconnected
    (fun i => Formalism.L2.PjFree.rdU U i.1.2.2 k)
    (fun i x => Formalism.L2.PjFree.rdU U' i.1.2.1 k' (lact δ (castFr h.psi x)))
    (fun x => if hx : x ∈ (U.X k).dom then Formalism.L2.PjFree.toC (t₀ ⟨x, hx⟩ : CAt σ) ^ n else 0)
    (fun i => (hU.2.2.2.2.1 _ n i.2.1 _ i.2.2.2.1 k).1)
    (fun i => (hU'.2.2.2.2.1 _ n i.2.1 _ i.2.2.1 k').1.comp ((GlobalTheory.Dict.Extend.differentiable_lact δ).comp
      (GlobalTheory.Dict.Pull.cast_diff h.psi)).differentiableOn fun x hx => h.mem_dom hx)
    (fun i x hx => by
      rw [dif_pos hx]
      exact key _ i.2.1 _ i.2.2.1 _ i.2.2.2.1 i.2.2.2.2 ⟨x, hx⟩)
    (fun ⟨⟨w, f, f'⟩, hD, hf, hf', hv⟩ x hx => by
      obtain ⟨x₀, hx₀, ⟨b₀, hb₀, e₀⟩, -⟩ := hun1 k ⟨x, hx⟩
      have hsec := hU.2.2.2.2.1 w n hD f' hf' k
      have hQ := hU'.2.2.2.2.1 w n hD f hf k'
      have h1 : ‖Formalism.L2.PjFree.toC (t₀ x₀ : CAt σ)‖ = 1 := hone x₀ _ _ hx₀ (hm x₀) (hb x₀)
      have v5 := congrArg norm (key w hD f hf f' hf' hv x₀)
      rw [norm_mul, norm_pow, h1, one_pow, one_mul, e₀, hsec.2.1 x hx b₀ hb₀,
        GlobalTheory.Dict.Pull.cast_rmul, GlobalTheory.Dict.Extend.lact_rmul,
        hQ.2.1 _ (h.mem_dom hx) _ (GlobalTheory.Dict.Pull.cast_bor h.psi hb₀),
        GlobalTheory.Dict.Pull.cast_bchar h.psi (hla w), norm_mul, norm_mul] at v5
      exact mul_left_cancel₀ (norm_ne_zero_iff.2 (AR.Up.OntoE.bchar_ne _ _ hb₀)) v5)
  exact ⟨ε, hε, fun w hD f hf f' hf' hv x hx => hc ⟨⟨w, f, f'⟩, hD, hf, hf', hv⟩ x hx⟩

end GlobalTheory.GeoLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLCharpolyEq
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionEll

theorem exists_GL_charpoly_eq : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ), ∀ P ∈ Ell E n, ∃ a : GL (Fin n) E, a.val.charpoly = P := by
  intro E _ _ n P hP
  obtain ⟨hm, hn, -, hr⟩ := hP
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h0 : P.coeff 0 ≠ 0 := by
    intro h
    have hroot : (0 : ℂ) ∈ (P.map τ).roots := by
      rw [mem_roots (hm.map τ).ne_zero, IsRoot.def, ← coeff_zero_eq_eval_zero, coeff_map, h, map_zero]
    have := hr τ 0 hroot
    simp at this
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin n) (Fin n) E, N.charpoly = P := by
    subst hn
    exact ⟨_, (charpoly_leftMulMatrix (AdjoinRoot.powerBasis hm.ne_zero)).trans
      (AdjoinRoot.minpoly_powerBasis_gen_of_monic hm)⟩
  have hd : IsUnit N.det := by
    rw [Matrix.det_eq_sign_charpoly_coeff, hN]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h0)
  exact ⟨((Matrix.isUnit_iff_isUnit_det N).mpr hd).unit, hN⟩

end GlobalTheory.CompanionEll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportedAtInfinityAdeleWithComplexComponeStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_supportedAtInfinity_adele_with_complexComponents : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (emb : ∀ w : InfinitePlace F, EmbOver E w) (f : InfinitePlace F → ℂ),
    ∃ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evI F) z ∧ ∀ w, piInf (emb w) z = f w := by
  first | exact @GlobalTheory.RealLift.exists_atInf_piInf_eq | exact GlobalTheory.RealLift.exists_atInf_piInf_eq | (intros; apply GlobalTheory.RealLift.exists_atInf_piInf_eq <;> assumption)
end

