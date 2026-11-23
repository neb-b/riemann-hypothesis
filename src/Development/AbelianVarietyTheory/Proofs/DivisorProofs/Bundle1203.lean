module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasiRegularSeqSelfIffLocalizationMaximal
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1144
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1182
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
public import GroundTheory.Brauer.SkolemNoether
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0909
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0944
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0996
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0872
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedEigenvaluesClasses
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0920
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0933
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0927
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalNormOutsideFiniteSet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1173
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1186

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightedMonomialValuationOfParameters
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.MonoVal

theorem isQuasiRegularSeq_of_locModel : ∀ {L : Type} [Field L] (c : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel c Q),
    letI := hQ.isLocalRing; ∀ (r : ℕ) (z : Fin (r + 1) → Q),
    IsLocalRing.maximalIdeal Q = Ideal.span (Set.range z) → ringKrullDim Q = r + 1 →
    IsNoetherianRing Q ∧ IsQuasiRegularSeq Q z := by
  intro L _ c Q hQ
  letI := hQ.isLocalRing
  intro r z hm hd
  letI := (c.codRestrict Q hQ.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ Q := hQ.essFiniteType
  haveI : IsNoetherianRing Q := Algebra.EssFiniteType.isNoetherianRing ℂ Q
  refine ⟨inferInstance, isQuasiRegularSeq_of_isRegular ?_⟩
  refine isRegular_of_ofList_eq_maximalIdeal ?_ ?_
  · rw [ofList_ofFn_eq_span_range, hm]
  · rw [List.length_ofFn, hd]
    norm_cast

def powCoeffMatrix {A : Type} [CommRing A] (n : ℕ) (t : A) (e : Fin n → ℕ) (w : Fin n → A) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) A :=
  fun i j => Fin.cases (if j = 0 then 1 else 0)
    (fun i' => Fin.cases (w i' * ((e i' : A) * t ^ (e i' - 1)))
      (fun j' => if j' = i' then t ^ e i' else 0) j) i

theorem powCoeffMatrix_det {A : Type} [CommRing A] (n : ℕ) (t : A) (e : Fin n → ℕ)
    (w : Fin n → A) : (powCoeffMatrix n t e w).det = t ^ (∑ i, e i) := by
  rw [Matrix.det_of_lowerTriangular]
  · rw [Fin.prod_univ_succ]
    simp [powCoeffMatrix, Finset.prod_pow_eq_pow_sum]
  · intro i j hij
    change i < j at hij
    induction i using Fin.cases with
    | zero =>
      have : j ≠ 0 := (Fin.pos_iff_ne_zero.mp (lt_of_le_of_lt (Fin.zero_le _) hij))
      simp [powCoeffMatrix, this]
    | succ i' =>
      induction j using Fin.cases with
      | zero => exact absurd hij (by simp)
      | succ j' =>
        have : j' ≠ i' := by
          intro h; subst h; exact lt_irrefl _ hij
        simp [powCoeffMatrix, this]

theorem dForm_cons_pow_mul : ∀ {k A : Type} [CommRing k] [CommRing A] (α : k →+* A) (n : ℕ) (t : A)
    (e : Fin n → ℕ) (w : Fin n → A),
    dForm α (Fin.cons t (fun i => t ^ e i * w i) : Fin (n + 1) → A) =
      t ^ (∑ i, e i) • dForm α (Fin.cons t w : Fin (n + 1) → A) := by
  intro k A _ _ α n t e w
  rw [← powCoeffMatrix_det n t e w]
  apply dForm_eq_det_smul
  intro i
  rw [Fin.sum_univ_succ]
  induction i using Fin.cases with
  | zero => simp [powCoeffMatrix]
  | succ i' =>
    simp only [powCoeffMatrix, Fin.cons_succ, Fin.cases_zero, Fin.cases_succ, Fin.cons_zero,
      ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    letI := α.toAlgebra
    change KaehlerDifferential.D k A (t ^ e i' * w i') = _
    rw [Derivation.leibniz, Derivation.leibniz_pow, add_comm]
    congr 1
    rw [mul_smul, mul_smul, ← Nat.cast_smul_eq_nsmul A]

theorem monomial_place : ∀ {L : Type} [Field L] (c : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel c Q), letI := hQ.isLocalRing;
  ∀ (r N : ℕ) (z : Fin (r + 1) → Q) (wt : Fin (r + 1) → ℕ),
  IsLocalRing.maximalIdeal Q = Ideal.span (Set.range z) → ringKrullDim Q = r + 1 → wt 0 = 1 → (∀ i, 1 ≤ wt i) →
  (∃ x : Fin N → L, TrBasis c x) →
  ∃ V : Place c, V.Contains Q ∧ (∀ q : Q, IsUnit q → V.ord q = 0) ∧ (∀ i, V.ord (z i) = wt i) ∧
    (∀ (d : ℕ) (q : Q), (q : L) ≠ 0 → q ∈ IsLocalRing.maximalIdeal Q ^ d → (d : ℤ) ≤ V.ord q) ∧
    ∀ y : Fin N → Q, IsFreeGen Q (dForm (c.codRestrict Q hQ.const_mem) y) →
      V.formOrd (dForm c (fun i => (y i : L))) + 1 ≤ ∑ i, (wt i : ℤ) := by
  intro L _ c Q hQ
  letI := hQ.isLocalRing
  intro r N z wt hm hdim hw0 hw1 hx
  obtain ⟨hN, hqr⟩ := isQuasiRegularSeq_of_locModel c Q hQ r z hm hdim
  obtain ⟨V, hC, u, hu, hirr, hmV, hunit, hloc⟩ := GlobalTheory.T.exists_weightedMonomialPlace_of_isLocModel c Q hQ r z wt hN hm.symm hqr hw0 hw1
  have ht0 : (z 0 : L) ≠ 0 := fun h => hirr.ne_zero (Subtype.ext h)
  have hordt : V.ord (z 0 : L) = 1 := by
    have h := V.ord_irreducible hirr
    exact h
  have h1m : (1 : Q) ∉ IsLocalRing.maximalIdeal Q := fun h =>
    (IsLocalRing.maximalIdeal.isMaximal Q).ne_top ((Ideal.eq_top_iff_one _).mpr h)
  have huu : ∀ i, IsUnit (u i) := fun i => by
    have h := hunit (MvPolynomial.X i) ⟨Finsupp.single i 1, by rw [MvPolynomial.coeff_X, if_pos rfl]; exact h1m⟩
    rw [MvPolynomial.eval₂_X] at h
    exact h
  have hu0 : ∀ i, (u i : L) ≠ 0 := fun i h => (huu i).ne_zero (Subtype.ext h)
  have hordu : ∀ i, V.ord (u i : L) = 0 := fun i => V.ord_eq_zero (huu i)
  have hordz : ∀ i, V.ord (z i : L) = wt i := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [hordt, hw0]; rfl
    · rw [← hu i, V.ord_mul (hu0 i) (pow_ne_zero _ ht0), V.ord_pow, hordu i, hordt]
      simp

  obtain ⟨φ, hφ⟩ : ∃ φ : Q →+* V.ring, φ = Q.subtype.codRestrict V.ring fun q => hC _ q.2 :=
    ⟨_, rfl⟩
  have hφL : ∀ q : Q, ((φ q : V.ring) : L) = q := fun q => by rw [hφ]; rfl
  refine ⟨V, hC, fun q hq => ?_, hordz, ?_, ?_⟩
  · have h := V.ord_eq_zero (hq.map φ)
    rwa [hφL] at h
  · intro d q hq0 hq
    have hmap : Ideal.map φ (IsLocalRing.maximalIdeal Q) ≤ Ideal.span {(⟨z 0, hC _ (z 0).2⟩ : V.ring)} := by
      rw [← hirr.maximalIdeal_eq, Ideal.map_le_iff_le_comap]
      intro q hq
      have h := hmV q hq
      rw [Ideal.mem_comap]
      convert h using 1
      exact Subtype.ext (hφL q)
    have h2 : φ q ∈ Ideal.span {(⟨z 0, hC _ (z 0).2⟩ : V.ring) ^ d} := by
      rw [← Ideal.span_singleton_pow]
      refine (Ideal.pow_right_mono hmap d) ?_
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem φ hq
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h2
    have haL : (q : L) = (a : L) * (z 0 : L) ^ d := by
      rw [← hφL q, ← ha]
      rfl
    have ha0 : (a : L) ≠ 0 := fun h => hq0 (by rw [haL, h, zero_mul])
    rw [haL, V.ord_mul ha0 (pow_ne_zero _ ht0), V.ord_pow, hordt, mul_one]
    have := (V.ord_nonneg_iff ha0).2 a.2
    omega

  · intro y hy
    obtain ⟨xT, hxT⟩ := hx
    obtain ⟨j, s, hjN, hsu⟩ := GlobalTheory.T.exists_residue_coordinates_of_localModel_below_place c Q hQ N r V hC u ⟨xT, hxT⟩ hmV hunit hloc
    subst hjN
    obtain ⟨w, hw⟩ : ∃ w : Fin (r + j) → V.ring,
        w = Fin.append u fun i => (⟨s i, hC _ (s i).2⟩ : V.ring) := ⟨_, rfl⟩
    rw [← hw] at hsu
    have hG : IsFreeGen V.ring
        (dForm V.const (Fin.cons ⟨z 0, hC _ (z 0).2⟩ w : Fin (r + j + 1) → V.ring)) := by
      letI := V.const.toAlgebra
      letI := c.toAlgebra
      haveI : IsScalarTower ℂ V.ring L := IsScalarTower.of_algebraMap_eq' rfl
      haveI : Algebra.EssFiniteType ℂ V.ring := V.essFiniteType
      haveI := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ V.ring
      obtain ⟨m, z', b, -, hb⟩ := exists_basis_kaehler_uniformiser ℂ hirr
      have h1 := trdeg_eq_of_basis_kaehler ℂ L b
      have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hxT
      rw [h1, Cardinal.mk_fin] at h2
      obtain rfl : r + j = m := by
        have : r + j + 1 = m + 1 := by exact_mod_cast h2
        omega
      exact isFreeGen_dForm_uniformiser_cons ℂ V.ring V.const (r + j) _ w V.essFiniteType hirr
        ⟨b⟩ hsu
    have e1 : dForm c (Fin.cons (z 0 : L) (fun i => (w i : L)) : Fin (r + j + 1) → L) =
        V.toRat (r + j + 1)
          (dForm V.const (Fin.cons ⟨z 0, hC _ (z 0).2⟩ w : Fin (r + j + 1) → V.ring)) := by
      have h := TopForm.formMap_dForm (D := r + j + 1) (α := V.const) (β := c) V.ring.subtype rfl
        (Fin.cons ⟨z 0, hC _ (z 0).2⟩ w : Fin (r + j + 1) → V.ring)
      refine Eq.trans ?_ h.symm
      congr 1
      funext i
      cases i using Fin.cases <;> rfl
    have hθ0 : dForm c (Fin.cons (z 0 : L) (fun i => (w i : L)) : Fin (r + j + 1) → L) ≠ 0 := by
      rw [e1]; exact V.toRat_ne_zero hG
    have hθ : V.formOrd
        (dForm c (Fin.cons (z 0 : L) (fun i => (w i : L)) : Fin (r + j + 1) → L)) = 0 := by
      rw [e1]; exact V.formOrd_toRat hG
    obtain ⟨a, ha⟩ := hy.2 (dForm (c.codRestrict Q hQ.const_mem)
      (Fin.cons (z 0) (Fin.append (fun i => z i.succ) s) : Fin (r + j + 1) → Q))
    have e2 : dForm c (fun i => ((Fin.cons (z 0) (Fin.append (fun i => z i.succ) s) :
          Fin (r + j + 1) → Q) i : L)) = (a : L) • dForm c (fun i => (y i : L)) := by
      have h := congrArg (TopForm.formMap (r + j + 1) Q.subtype
        (α := c.codRestrict Q hQ.const_mem) (β := c) rfl) ha
      have f1 := TopForm.formMap_dForm (D := r + j + 1) (α := c.codRestrict Q hQ.const_mem) (β := c)
        Q.subtype rfl y
      have f2 := TopForm.formMap_dForm (D := r + j + 1) (α := c.codRestrict Q hQ.const_mem) (β := c)
        Q.subtype rfl (Fin.cons (z 0) (Fin.append (fun i => z i.succ) s) : Fin (r + j + 1) → Q)
      rw [map_smulₛₗ] at h
      exact f2.symm.trans (h.symm.trans (congrArg (Q.subtype a • ·) f1))
    obtain ⟨e, he⟩ : ∃ e : Fin (r + j) → ℕ,
        e = Fin.append (fun i => wt i.succ) (fun _ : Fin j => 0) := ⟨_, rfl⟩
    have e3 : (fun i => ((Fin.cons (z 0) (Fin.append (fun i => z i.succ) s) :
          Fin (r + j + 1) → Q) i : L)) =
        (Fin.cons (z 0 : L) (fun i => (z 0 : L) ^ e i * (w i : L)) : Fin (r + j + 1) → L) := by
      funext i
      refine Fin.cases rfl (fun i => ?_) i
      simp only [Fin.cons_succ]
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [he, hw, Fin.append_left]
        rw [← hu i, mul_comm]
      · simp only [he, hw, Fin.append_right, pow_zero, one_mul]
    have hsum : ∑ i, e i = ∑ i : Fin r, wt i.succ := by
      rw [he, Fin.sum_univ_add]
      simp
    have e4 : dForm c (fun i => ((Fin.cons (z 0) (Fin.append (fun i => z i.succ) s) :
          Fin (r + j + 1) → Q) i : L)) =
        (z 0 : L) ^ (∑ i : Fin r, wt i.succ) •
          dForm c (Fin.cons (z 0 : L) (fun i => (w i : L)) : Fin (r + j + 1) → L) := by
      rw [e3, dForm_cons_pow_mul, hsum]
    have hpow0 : ((z 0 : L) ^ (∑ i : Fin r, wt i.succ)) ≠ 0 := pow_ne_zero _ ht0
    have hne : dForm c (fun i => ((Fin.cons (z 0) (Fin.append (fun i => z i.succ) s) :
          Fin (r + j + 1) → Q) i : L)) ≠ 0 := by
      rw [e4]
      exact smul_ne_zero hpow0 hθ0
    have ha0 : (a : L) ≠ 0 := fun h => hne (by rw [e2, h, zero_smul])
    have hy0 : dForm c (fun i => (y i : L)) ≠ 0 := fun h => hne (by rw [e2, h, smul_zero])
    have o1 := V.formOrd_smul hxT hθ0 hpow0
    have o2 := V.formOrd_smul hxT hy0 ha0
    rw [← e4, hθ, V.ord_pow, hordt] at o1
    rw [← e2, o1] at o2
    have hnna := (V.ord_nonneg_iff ha0).2 (hC _ a.2)
    rw [Fin.sum_univ_succ, hw0]
    push_cast at o2 ⊢
    linarith

end GlobalTheory.MonoVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClassesFixedGammaIrr
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKIrr
variable {p : ℕ} [Fact p.Prime]

theorem irreducible_minpoly_inv (G : HTGroup p) (γ : G.Cˣ) (hirr : Irreducible (minpoly G.F (γ : G.C))) :
    Irreducible (minpoly G.F ((γ⁻¹ : G.Cˣ) : G.C)) := by
  have hi : IsIntegral G.F (γ : G.C) := Algebra.IsIntegral.isIntegral _
  set m := minpoly G.F (γ : G.C) with hmdef
  haveI : Fact (Irreducible m) := ⟨hirr⟩
  have hm0 : m ≠ 0 := minpoly.ne_zero hi
  haveI : FiniteDimensional G.F (AdjoinRoot m) := (AdjoinRoot.powerBasis hm0).finite
  have hz : ∀ a : Polynomial G.F, a ∈ Ideal.span {m} → Polynomial.aeval (γ : G.C) a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 ha
    rw [map_mul, minpoly.aeval, zero_mul]
  let f : AdjoinRoot m →ₐ[G.F] G.C := Ideal.Quotient.liftₐ (Ideal.span {m}) (Polynomial.aeval (γ : G.C)) hz
  have ef : f (AdjoinRoot.root m) = γ := by
    show Ideal.Quotient.liftₐ (Ideal.span {m}) (Polynomial.aeval (γ : G.C)) hz
      (Ideal.Quotient.mk _ Polynomial.X) = _
    exact Polynomial.aeval_X _
  have hinj : Function.Injective f := f.toRingHom.injective
  have hr0 : AdjoinRoot.root m ≠ 0 := by
    intro h
    have : (γ : G.C) = 0 := by rw [← ef, h, map_zero]
    exact γ.ne_zero this
  have hinv : f ((AdjoinRoot.root m)⁻¹) = ((γ⁻¹ : G.Cˣ) : G.C) := by
    have h1 : f ((AdjoinRoot.root m)⁻¹) * γ = 1 := by
      rw [← ef, ← map_mul, inv_mul_cancel₀ hr0, map_one]
    calc f ((AdjoinRoot.root m)⁻¹) = f ((AdjoinRoot.root m)⁻¹) * γ * ((γ⁻¹ : G.Cˣ) : G.C) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [h1, one_mul]
  rw [← hinv, minpoly.algHom_eq f hinj]
  exact minpoly.irreducible (Algebra.IsIntegral.isIntegral _)
end GlobalTheory.LKIrr

namespace GlobalTheory.LKIrr
open Polynomial GlobalTheory.GlobEig

theorem exists_emb_isRoot_irr {F C E : Type} [Field F] [NumberField F] [Ring C] [Algebra F C]
    [Algebra ℚ C] [IsScalarTower ℚ F C] [FiniteDimensional F C] [Field E] [Algebra ℚ E] [IsAlgClosed E]
    (y : C) (hirr : Irreducible (minpoly F y)) (μ : E) (h : ((minpoly ℚ y).map (algebraMap ℚ E)).IsRoot μ) :
    ∃ τ : F →+* E, ((minpoly F y).map τ).IsRoot μ := by
  have hyi : IsIntegral F y := IsIntegral.of_finite F y
  haveI : Fact (Irreducible (minpoly F y)) := ⟨hirr⟩
  haveI : FiniteDimensional F (AdjoinRoot (minpoly F y)) :=
    (AdjoinRoot.powerBasis (minpoly.ne_zero hyi)).finite
  haveI : FiniteDimensional ℚ (AdjoinRoot (minpoly F y)) := Module.Finite.trans F _
  haveI : Algebra.IsAlgebraic ℚ (AdjoinRoot (minpoly F y)) := Algebra.IsAlgebraic.of_finite ℚ _
  set r := AdjoinRoot.root (minpoly F y)
  have hdvd : minpoly ℚ y ∣ minpoly ℚ r := by
    apply minpoly.dvd
    have h1 : minpoly F y ∣ (minpoly ℚ r).map (algebraMap ℚ F) := by
      rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.aeval_eq, aeval_map_algebraMap, minpoly.aeval]
    obtain ⟨k, hk⟩ := h1
    rw [← aeval_map_algebraMap F, hk, map_mul, minpoly.aeval, zero_mul]
  have hne : minpoly ℚ r ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral r)
  have hμ' : μ ∈ (minpoly ℚ r).rootSet E := by
    rw [mem_rootSet]
    refine ⟨hne, ?_⟩
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, map_mul, aeval_def, eval₂_eq_eval_map, h.eq_zero, zero_mul]
  rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly] at hμ'
  obtain ⟨ψ, hψ⟩ := hμ'
  refine ⟨(ψ : AdjoinRoot (minpoly F y) →+* E).comp (algebraMap F _), ?_⟩
  rw [← hψ, IsRoot.def, eval_map]
  change eval₂ ((ψ : AdjoinRoot (minpoly F y) →+* E).comp (algebraMap F _))
    ((ψ : AdjoinRoot (minpoly F y) →+* E) r) (minpoly F y) = 0
  rw [← hom_eval₂, ← aeval_def, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]

theorem root_norm_le_irr {p : ℕ} [Fact p.Prime] (G : HTGroup p) (β y : G.Cˣ) (c : ℚˣ)
    (hirr : Irreducible (minpoly G.F (y : G.C)))
    (hyc : (y : G.C) * β * sh G y = algebraMap ℚ G.C c * β) (B : ℝ) (hc : ‖((c : ℚ) : ℚ_[p])‖ ≤ B)
    (hc' : ‖(((c⁻¹ : ℚˣ) : ℚ) : ℚ_[p])‖ ≤ B)
    (hy : ∀ (w : Fin G.m) (μ : PadicAlgCl p),
      ((G.rho w (y : G.C)).charpoly.map (algebraMap (G.Fw w) (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ B)
    (hyi : ∀ (w : Fin G.m) (μ : PadicAlgCl p),
      ((G.rho w ((y⁻¹ : G.Cˣ) : G.C)).charpoly.map (algebraMap (G.Fw w) (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ B)
    (μ : PadicAlgCl p) (hμ : ((LinearMap.mulLeft ℚ (y : G.C)).charpoly.map (algebraMap ℚ (PadicAlgCl p))).IsRoot μ) :
    ‖μ‖ ≤ B * B := by
  have h0 := isRoot_minpoly_of_isRoot_charpoly (y : G.C) μ hμ
  obtain ⟨τ, hτ⟩ := exists_emb_isRoot_irr (F := G.F) (y : G.C) hirr μ h0
  have hcpos : 0 < ‖((c : ℚ) : ℚ_[p])‖ := norm_pos_iff.2 (by simp)
  have hprod : ‖((c : ℚ) : ℚ_[p])‖ * ‖(((c⁻¹ : ℚˣ) : ℚ) : ℚ_[p])‖ = 1 := by
    rw [← norm_mul, ← Rat.cast_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Rat.cast_one, norm_one]
  have hB0 : 0 ≤ B := hcpos.le.trans hc
  have hB1 : 1 ≤ B := by
    have h1 : 1 ≤ B * B := by
      rw [← hprod]
      exact mul_le_mul hc hc' (norm_nonneg _) hB0
    nlinarith
  rcases liesOver_or_conj G τ with hu | hu
  · obtain ⟨i, ν, hνμ, hν⟩ := exists_root_rho G τ hu y μ hτ
    have h1 := hy i ν hν
    rw [hνμ] at h1
    nlinarith
  · have h2 := isRoot_minpoly_sh G y τ μ hτ
    obtain ⟨i, ν, hνμ, hν⟩ := exists_root_rho G _ hu (sh G y) μ h2
    have h3 := isRoot_inv G i β y c hyc ν hν
    have h4 := hyi i _ h3
    have hs : ‖((c : ℚ) : PadicAlgCl p)‖ = ‖((c : ℚ) : ℚ_[p])‖ := by
      rw [← PadicAlgCl.norm_extends, map_ratCast]
    rw [norm_mul, norm_inv, hs, hνμ, ← div_eq_mul_inv, div_le_iff₀ hcpos] at h4
    calc ‖μ‖ ≤ B * ‖((c : ℚ) : ℚ_[p])‖ := h4
      _ ≤ B * B := mul_le_mul_of_nonneg_left hc hB0

end GlobalTheory.LKIrr

namespace GlobalTheory.LKIrr

end GlobalTheory.LKIrr

namespace GlobalTheory.LKIrr
open GlobalTheory.LKMid.Northcott

end GlobalTheory.LKIrr

namespace GlobalTheory.LKIrr

variable {p : ℕ} [Fact p.Prime]

end GlobalTheory.LKIrr

namespace GlobalTheory.LKIrr

end GlobalTheory.LKIrr

namespace GlobalTheory.LKIrr

end GlobalTheory.LKIrr

namespace GlobalTheory.LKIrr

end GlobalTheory.LKIrr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedIsotropicFlagLeviLeLeviSubgroup
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct

namespace GlobalTheory.TieStd

theorem sum_castLE_of_zero {M : Type*} [AddCommMonoid M] {m s : ℕ} (hm : m ≤ s) (g : Fin s → M)
    (hg : ∀ i : Fin s, m ≤ i.val → g i = 0) : ∑ i : Fin s, g i = ∑ i : Fin m, g (Fin.castLE hm i) := by
  symm
  refine Eq.trans (Finset.sum_map Finset.univ (Fin.castLEEmb hm) g).symm ?_
  refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => hg i (not_lt.1 fun h => hi ?_)
  exact Finset.mem_map.2 ⟨⟨i.val, h⟩, Finset.mem_univ _, Fin.ext rfl⟩

theorem mul_submatrix_castLE {R ι' κ : Type*} [CommRing R] {m s : ℕ} (hm : m ≤ s) (C : Matrix ι' (Fin s) R)
    (B : Matrix (Fin s) (Fin s) R) (hB : ∀ i j : Fin s, m ≤ i.val → j.val < m → B i j = 0) (f : κ → ι') :
    (C * B).submatrix f (Fin.castLE hm) =
      C.submatrix f (Fin.castLE hm) * B.submatrix (Fin.castLE hm) (Fin.castLE hm) := by
  ext a j
  simp only [submatrix_apply, Matrix.mul_apply]
  exact sum_castLE_of_zero hm _ fun i hi => by rw [hB i _ hi j.2, mul_zero]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem mem_frameStab_of_mem_parFlag {s m : ℕ} (hm : m ≤ s) (C : Matrix (Fin n) (Fin s) E)
    (L : Matrix (Fin s) (Fin n) E) (hL : L * C = 1) (d : Fin s → ℕ)
    (hd : ∀ i j : Fin s, m ≤ i.val → j.val < m → d j < d i) {g : GAd σ J} (hg : g ∈ GlobalTheory.UAut.parFlag σ J C d) :
    g ∈ GlobalTheory.StdPar.frameStab σ J (C.submatrix id (Fin.castLE hm)) ⊤ := by
  obtain ⟨⟨B, hB, e⟩, B', hB', e'⟩ := hg
  have hL' : adMat F L * adMat F C = 1 := by rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  have hMM : (matHom _ σ J g).1 * (matHom _ σ J g⁻¹).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hBB : B * B' = 1 := by
    calc B * B' = adMat F L * (adMat F C * B) * B' := by rw [← Matrix.mul_assoc, hL', Matrix.one_mul]
      _ = adMat F L * ((matHom _ σ J g).1 * ((matHom _ σ J g⁻¹).1 * adMat F C)) := by
          simp only [← e, e', Matrix.mul_assoc]
      _ = 1 := by rw [← Matrix.mul_assoc (matHom _ σ J g).1, hMM, Matrix.one_mul, hL']
  have hz : ∀ {A : Matrix (Fin s) (Fin s) (AF F ⊗[F] E)}, A.BlockTriangular d →
      ∀ i j : Fin s, m ≤ i.val → j.val < m → A i j = 0 := fun hA i j hi hj => hA (hd i j hi hj)
  have hU : B.submatrix (Fin.castLE hm) (Fin.castLE hm) * B'.submatrix (Fin.castLE hm) (Fin.castLE hm) = 1 := by
    rw [← mul_submatrix_castLE hm B B' (hz hB') (Fin.castLE hm), hBB, Matrix.submatrix_one _ (Fin.castLE_injective hm)]
  refine ⟨⟨_, _, hU, mul_eq_one_comm.1 hU⟩, Subgroup.mem_top _, ?_⟩
  show (matHom _ σ J g).1 * (adMat F C).submatrix id (Fin.castLE hm) =
    (adMat F C).submatrix id (Fin.castLE hm) * B.submatrix (Fin.castLE hm) (Fin.castLE hm)
  rw [← mul_submatrix_castLE hm _ B (hz hB) id, ← e]
  ext a j
  simp [Matrix.mul_apply]

end GlobalTheory.TieStd

namespace GlobalTheory.TieStd

theorem leviFlag_le_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E),
    IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r), (∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) →
    ∀ d : Fin s → ℕ, (∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) →
    GlobalTheory.UAut.leviFlag σ J (X.submatrix id (Fin.castLE hs)) (Y.submatrix id (Fin.castLE hs)) d ≤
      GlobalTheory.StdPar.levi σ J X Y S := by
  intro F E _ _ _ _ _ σ hσ n J hJ r X Y hW S s hs hS d hd g hg
  obtain ⟨hgX, hgY⟩ := Subgroup.mem_inf.1 hg
  have hyx := GlobalTheory.StdPar.yx hσ hJ hW
  have hLX : Formalism.UG.cT (σ : E →+* E) (Y.submatrix id (Fin.castLE hs)) * J * X.submatrix id (Fin.castLE hs) = 1 := by
    rw [cT_submatrix_mul, hyx, Matrix.submatrix_one _ (Fin.castLE_injective hs)]
  have hLY : Formalism.UG.cT (σ : E →+* E) (X.submatrix id (Fin.castLE hs)) * J * Y.submatrix id (Fin.castLE hs) = 1 := by
    rw [cT_submatrix_mul, hW.xy, Matrix.submatrix_one _ (Fin.castLE_injective hs)]
  rw [GlobalTheory.StdPar.levi, Subgroup.mem_iInf]
  intro k
  rw [Subgroup.mem_iInf]
  intro hk
  have hm : k.val + 1 ≤ s := (hS k).2 ⟨k, hk, le_rfl⟩
  have hdk : ∀ i j : Fin s, k.val + 1 ≤ i.val → j.val < k.val + 1 → d j < d i := fun i j hi hj =>
    (depth_lt_iff S s hs d hd i j).2 ⟨k, hk, Fin.le_iff_val_le_val.2 (Nat.lt_succ_iff.1 hj), Fin.lt_iff_val_lt_val.2 hi⟩
  exact Subgroup.mem_inf.2 ⟨mem_frameStab_of_mem_parFlag σ J hm _ _ hLX d hdk hgX,
    mem_frameStab_of_mem_parFlag σ J hm _ _ hLY d hdk hgY⟩

end GlobalTheory.TieStd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviElementPreservesWittColumnSpan
section
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.IdTorus

end GlobalTheory.IdTorus
end
end

