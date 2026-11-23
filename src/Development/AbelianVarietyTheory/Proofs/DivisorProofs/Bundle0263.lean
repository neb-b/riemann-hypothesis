module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0234
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOneTmulOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0055

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJetExtensionSquareZero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts

theorem exists_jet_factor {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F) {k : K.K} {T : K.Obj} (f₁ f₂ : K.triv k ⟶ T) (n : Fin g → T.C) (hd : f₁.deg = f₂.deg)
    (hJ : ∀ a, n a ∈ T.J) (hn : ∀ a b, n a * n b = 0)
    (hf : ∀ x : Hol (K.W k), f₂.φ x = f₁.φ x + ∑ a, f₁.φ (dw a x : Hol (K.W k)) * n a) :
    ∃ χ : K.jet k ⟶ T, χ.deg = f₁.deg ∧ jet0 k ≫ χ = f₁ ∧ jet1 k ≫ χ = f₂ ∧
      ∀ x : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)),
        χ.φ x = f₁.φ (x.fst : Hol (K.W k)) + ∑ a, f₁.φ (x.snd a : Hol (K.W k)) * n a := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet
  | exact @_root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet
  | exact _root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet
  | (apply _root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet <;> assumption)
  | (intros; apply _root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet ..)

end GlobalTheory.AnPer.Charts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearIndependentIterates
section
open Polynomial Matrix

namespace GlobalTheory.ConjLocal

variable {R : Type} [CommRing R] {n : ℕ}

def iterMat (Y : Matrix (Fin n) (Fin n) R) (v : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => (Y ^ (j : ℕ) *ᵥ v) i

def compMat (Q : R[X]) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if (j : ℕ) + 1 < n then (if (i : ℕ) = (j : ℕ) + 1 then 1 else 0) else -Q.coeff i

theorem exists_linearIndependent_iterates {K : Type} [Field K] (M : Matrix (Fin n) (Fin n) K)
    (hs : M.charpoly.Separable) :
    ∃ v : Fin n → K, LinearIndependent K (fun j : Fin n => (M ^ (j : ℕ)) *ᵥ v) := by
  obtain ⟨e, -, he⟩ := Formalism.IrreducibleCountingLemmas.Z.exists_annihilator_eq (toLin' M) (by rw [charpoly_toLin']; exact hs)
    (toLin' M).charpoly dvd_rfl
  refine ⟨e, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let q : K[X] := ∑ j : Fin n, monomial (j : ℕ) (c j)
  have ha : ∀ p : K[X], aeval (toLin' M) p = toLin' (aeval M p) := fun p =>
    aeval_algHom_apply (toLinAlgEquiv' (R := K) (n := Fin n)) M p
  have hq0 : aeval (toLin' M) q e = 0 := by
    rw [ha, toLin'_apply]
    have haq : aeval M q = ∑ j : Fin n, c j • M ^ (j : ℕ) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [q, map_sum, aeval_monomial, Algebra.smul_def]
    rw [haq, Matrix.sum_mulVec]
    simpa [Matrix.smul_mulVec] using hc
  have hdvd := he q hq0
  rw [charpoly_toLin'] at hdvd
  have hdeg : q.degree < M.charpoly.degree := by
    rw [degree_eq_natDegree M.charpoly_monic.ne_zero, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun j _ => ?_
    exact lt_of_le_of_lt (degree_monomial_le _ _) (by exact_mod_cast j.2)
  have hq : q = 0 := eq_zero_of_dvd_of_degree_lt hdvd hdeg
  intro j
  have := congrArg (fun p : K[X] => p.coeff j) hq
  simp only [q, Polynomial.finsetSum_coeff, coeff_monomial_apply, Fin.val_inj,
    coeff_zero] at this
  simpa using this

end GlobalTheory.ConjLocal

namespace GlobalTheory.ConjLocal

variable {R : Type} [CommRing R] {n : ℕ}

theorem pow_dim_mulVec [Nontrivial R] (Y : Matrix (Fin n) (Fin n) R) (v : Fin n → R) (i : Fin n) :
    (Y ^ n *ᵥ v) i = -∑ k : Fin n, Y.charpoly.coeff k * (Y ^ (k : ℕ) *ᵥ v) i := by
  have h0 := Matrix.aeval_self_charpoly Y
  have hm := Y.charpoly_monic.as_sum
  rw [charpoly_natDegree_eq_dim, Fintype.card_fin] at hm
  rw [hm] at h0
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_pow, aeval_X, map_sum, map_mul, aeval_C] at h0
  have := congrArg (fun M => (M *ᵥ v) i) h0
  simp only [add_mulVec, sum_mulVec, Pi.add_apply, Finset.sum_apply, zero_mulVec, Pi.zero_apply] at this
  rw [eq_neg_iff_add_eq_zero, ← this, ← Fin.sum_univ_eq_sum_range]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mulVec_mulVec, algebraMap_eq_diagonal, mulVec_diagonal]
  rfl

theorem mul_iterMat [Nontrivial R] (Y : Matrix (Fin n) (Fin n) R) (v : Fin n → R) :
    Y * iterMat Y v = iterMat Y v * compMat Y.charpoly := by
  ext i j
  have hl : (Y * iterMat Y v) i j = (Y ^ ((j : ℕ) + 1) *ᵥ v) i := by
    rw [pow_succ', ← mulVec_mulVec]; rfl
  rw [hl, Matrix.mul_apply]
  simp only [iterMat, compMat, Matrix.of_apply]
  split_ifs with hj
  · rw [Finset.sum_eq_single ⟨(j : ℕ) + 1, hj⟩]
    · simp
    · intro b _ hb
      rw [if_neg (fun h => hb (Fin.ext h)), mul_zero]
    · simp
  · have : (j : ℕ) + 1 = n := by omega
    rw [this, pow_dim_mulVec, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

theorem exists_isUnit_det_iterMat [IsLocalRing R] (Y : Matrix (Fin n) (Fin n) R) (hs : Y.charpoly.Separable) :
    ∃ v : Fin n → R, IsUnit (iterMat Y v).det := by
  let f := IsLocalRing.residue R
  have hs' : (Y.map f).charpoly.Separable := by rw [Matrix.charpoly_map]; exact hs.map
  obtain ⟨w, hw⟩ := exists_linearIndependent_iterates (Y.map f) hs'
  choose v hv using fun i => IsLocalRing.residue_surjective (w i)
  refine ⟨v, ?_⟩
  have hmap : (iterMat Y v).map f = iterMat (Y.map f) w := by
    ext i j
    simp only [iterMat, Matrix.map_apply, Matrix.of_apply, ← Matrix.map_pow, RingHom.map_mulVec]
    congr 1
    funext k
    exact hv k
  have hunit : IsUnit (iterMat (Y.map f) w) := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    convert hw using 1
    funext j
    ext i
    rfl
  apply isUnit_of_map_unit f
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap]
  exact (Matrix.isUnit_iff_isUnit_det _).1 hunit

end GlobalTheory.ConjLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalStageTensorPolynomialOriginStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localStage_tensor_polynomial_origin : ∀ (T O : Type) [CommRing T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O],
    (maximalIdeal O).comap (algebraMap (Polynomial T) O) = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (A : Type) [CommRing A] [IsLocalRing A] (i : A →+* T), IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (A' : Type) [CommRing A'] [IsLocalRing A'] (ι : A →+* A') (α : A' →+* T), α.comp ι = i → IsLocalHom α →
    ∃ (E' : Type) (_ : CommRing E') (_ : Algebra (Polynomial A') E') (_ : Algebra.Etale (Polynomial A') E')
      (Q' : Ideal E') (_ : Q'.IsPrime),
      Q'.comap (algebraMap (Polynomial A') E') = GlobalTheory.KeyOriginCut.originIdeal A' ∧
      ∃ (β : Localization.AtPrime QA →+* Localization.AtPrime Q') (γ : Localization.AtPrime Q' →+* O),
        ((algebraMap (Polynomial A') (Localization.AtPrime Q')).comp Polynomial.C).comp ι =
          β.comp ((algebraMap (Polynomial A) (Localization.AtPrime QA)).comp Polynomial.C) ∧
        γ.comp β = jA ∧
        γ.comp ((algebraMap (Polynomial A') (Localization.AtPrime Q')).comp Polynomial.C) =
          (algebraMap T O).comp α := by
  first | (exact @GlobalTheory.LocalStage.localStage) | (exact GlobalTheory.LocalStage.localStage) | (intros; apply GlobalTheory.LocalStage.localStage  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalOverClosedPointClosedFibreStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_maximal_over_closedPoint_closedFibre : ∀ (T E : Type) [CommRing T] [IsLocalRing T] [CommRing E] [Algebra (Polynomial T) E]
    [Algebra.FiniteType (Polynomial T) E] (Q : Ideal E) [Q.IsPrime],
    Q.comap (algebraMap (Polynomial T) E) =
      (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) →
    ∃ y : Ideal E, y.IsMaximal ∧ Q ≤ y ∧
      y.comap (algebraMap (Polynomial T) E) ≠
        (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) ∧
      (y.comap (algebraMap (Polynomial T) E)).comap (Polynomial.C : T →+* Polynomial T) =
        IsLocalRing.maximalIdeal T := by
  first | (exact @GlobalTheory.exists_maximal_over_closedPt) | (exact GlobalTheory.exists_maximal_over_closedPt) | (intros; apply GlobalTheory.exists_maximal_over_closedPt  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulMemIntegralClosureOverGenericFibre
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.KeyOriginNoeth

theorem exists_common_multiple_mem_closure :
    ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] (s : Finset D),
    ∃ a : A, a ≠ 0 ∧ ∀ d ∈ s,
      GlobalTheory.KeyOriginNoeth.baseHom A R D (algebraMap A R a) * d ∈ GlobalTheory.KeyOriginNoeth.closure A R D := by
  intro A R _ _ _ _ D _ _ _ s
  classical
  letI : Algebra R D := (baseHom A R D).toAlgebra
  haveI : IsScalarTower R (GlobalTheory.LocAcyc.GenFib A R) D :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have key : ∀ d : D, ∃ a : A, a ≠ 0 ∧ IsIntegral R (baseHom A R D (algebraMap A R a) * d) := by
    intro d
    have hd : IsIntegral (GlobalTheory.LocAcyc.GenFib A R) d := Algebra.IsIntegral.isIntegral d
    obtain ⟨⟨m, hm⟩, hmi⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (Algebra.algebraMapSubmonoid R (nonZeroDivisors A)) (Rₘ := GlobalTheory.LocAcyc.GenFib A R) d hd
    obtain ⟨a, ha, rfl⟩ := hm
    refine ⟨a, nonZeroDivisors.ne_zero ha, ?_⟩
    exact hmi
  have hmem : ∀ x : D, IsIntegral R x → x ∈ closure A R D := fun x hx => hx
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert d s hds ih =>
    obtain ⟨a₂, ha₂, h₂⟩ := ih
    obtain ⟨a₁, ha₁, h₁⟩ := key d
    refine ⟨a₁ * a₂, mul_ne_zero ha₁ ha₂, ?_⟩
    intro e he
    apply hmem
    rw [Finset.mem_insert] at he
    rcases he with rfl | he
    · have : baseHom A R D (algebraMap A R (a₁ * a₂)) * e =
          algebraMap R D (algebraMap A R a₂) * (baseHom A R D (algebraMap A R a₁) * e) := by
        simp only [map_mul]; show _ = baseHom A R D _ * _; ring
      rw [this]
      exact isIntegral_algebraMap.mul h₁
    · have : baseHom A R D (algebraMap A R (a₁ * a₂)) * e =
          algebraMap R D (algebraMap A R a₁) * (baseHom A R D (algebraMap A R a₂) * e) := by
        simp only [map_mul]; show _ = baseHom A R D _ * _; ring
      rw [this]
      exact isIntegral_algebraMap.mul (h₂ e he)

end GlobalTheory.KeyOriginNoeth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenAffineHilbertChartBasicLocusStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_affineHilbertChartBasic_locus : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ) (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)), ∃ W : Z.Opens, (∀ (Z' : Scheme.{0}) (a : Z' ⟶ Z), Set.range a ⊆ (W : Set Z) ↔ GlobalTheory.HilbAff.Basic A B e σ ((GlobalTheory.HilbAff.functor A B r).map a.op y)) ∧ (CompactSpace Z → IsCompact (W : Set Z)) := by
  first | (exact @GlobalTheory.HilbAff.Locus.exists_basic_locus) | (exact GlobalTheory.HilbAff.Locus.exists_basic_locus) | (intros; apply GlobalTheory.HilbAff.Locus.exists_basic_locus  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqMulOfQuadraticBoundNormalLocal
section
open IsLocalRing ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory


open IsDiscreteValuationRing in
theorem mul_dvd_pow_of_quadratic_bound_dvr {V : Type} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] {X : Type} [AddCommGroup X] (h h' : X →+ X) (C : ℕ)
    (hq : ∀ q : X → ℤ, (∀ y, 0 ≤ q y) → q 0 = 0 → (∀ y, q (-y) = q y) →
      (∀ x y z, q (x + y + z) + q x + q y + q z = q (x + y) + q (x + z) + q (y + z)) →
      (∀ y z, q (h y + z) + q y + q (h' z) = q (y + h' z) + q (h y) + q z) →
      ∀ y, q (h y) ≤ C * q y) {N : ℕ} (hN : C + 1 ≤ N) (k : X → V) (hk0 : ∀ y, k y ≠ 0)
    (h1 : ∀ y, k (-y) = k y) (h2 : k 0 = 1)
    (h3 : ∀ x y z, k (x + y + z) * k x * k y * k z = k (x + y) * k (x + z) * k (y + z))
    (h4 : ∀ y z, ∃ u : V, IsUnit u ∧
      k (h y + z) * k y * k (h' z) = u * (k (y + h' z) * k (h y) * k z)) (y : X) :
    k y * k (h y) ∣ k y ^ N := by
  have hn : ∀ z, ∃ n : ℕ, addVal V (k z) = n := fun z =>
    (ENat.ne_top_iff_exists.1 (mt addVal_eq_top_iff.1 (hk0 z))).imp fun _ e => e.symm
  choose n hn using hn
  have key := hq (fun z => (n z : ℤ)) (fun _ => Int.natCast_nonneg _)
    (by
      have := hn 0
      rw [h2, addVal_one] at this
      exact_mod_cast this.symm)
    (fun z => by
      have := hn (-z)
      rw [h1, hn] at this
      exact_mod_cast this.symm)
    (fun a b c => by
      have := congrArg (addVal V) (h3 a b c)
      simp only [addVal_mul, hn] at this
      exact_mod_cast this)
    (fun a b => by
      obtain ⟨u, hu, e⟩ := h4 a b
      have := congrArg (addVal V) e
      simp only [addVal_mul, hn, addVal_eq_zero_iff.2 hu, zero_add] at this
      exact_mod_cast this) y
  have key' : n (h y) ≤ C * n y := by exact_mod_cast key
  rw [← addVal_le_iff_dvd, addVal_mul, addVal_pow, hn, hn, nsmul_eq_mul]
  have : n y + n (h y) ≤ N * n y := by nlinarith [Nat.mul_le_mul_right (n y) hN]
  exact_mod_cast this

theorem exists_pow_eq_mul_of_quadratic_bound :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (X : Type) [AddCommGroup X] (h h' : X →+ X) (C : ℕ), (∀ q : X → ℤ, (∀ y, 0 ≤ q y) → q 0 = 0 → (∀ y, q (-y) = q y) → (∀ x y z, q (x + y + z) + q x + q y + q z = q (x + y) + q (x + z) + q (y + z)) → (∀ y z, q (h y + z) + q y + q (h' z) = q (y + h' z) + q (h y) + q z) → ∀ y, q (h y) ≤ C * q y) → ∀ N : ℕ, C + 1 ≤ N → ∀ (κ : X → (FractionRing R)ˣ), (∀ y, κ (-y) = κ y) → κ 0 = 1 → (∀ x y z, κ (x + y + z) * κ x * κ y * κ z = κ (x + y) * κ (x + z) * κ (y + z)) → (∀ y, ∃ r : R, (κ y : FractionRing R) = algebraMap R _ r) → (∀ y z, ∃ u : Rˣ, ((κ (h y + z) * κ y * κ (h' z) : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ (u : R) * ((κ (y + h' z) * κ (h y) * κ z : (FractionRing R)ˣ) : FractionRing R)) → ∀ y, ∃ r : R, ((κ y ^ N : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ r * κ y * κ (h y) := by
  intro R _ _ _ hR X _ h h' C hq N hN κ h1 h2 h3 hκ h4 y
  obtain ⟨hno, -, hic, -⟩ := hR
  have hx : ∃ r : R, algebraMap R (FractionRing R) r =
      ((κ y ^ N * (κ y * κ (h y))⁻¹ : (FractionRing R)ˣ) : FractionRing R) := by
    refine exists_algebraMap_eq_of_forall_discreteValuationSubring fun V hV hRV _ => ?_
    have hm : ∀ z, (κ z : FractionRing R) ∈ V := fun z => by
      obtain ⟨r, e⟩ := hκ z
      exact e ▸ hRV r
    obtain ⟨c, hc⟩ := mul_dvd_pow_of_quadratic_bound_dvr (V := V) h h' C hq hN
      (fun z => ⟨κ z, hm z⟩) (fun z e => (κ z).ne_zero (congrArg Subtype.val e))
      (fun z => Subtype.ext (congrArg Units.val (h1 z)))
      (Subtype.ext (congrArg Units.val h2))
      (fun a b c => Subtype.ext (congrArg Units.val (h3 a b c)))
      (fun a b => by
        obtain ⟨u, e⟩ := h4 a b
        exact ⟨(algebraMap R (FractionRing R)).codRestrict V hRV u, u.isUnit.map _,
          Subtype.ext e⟩) y
    have hc' : (κ y : FractionRing R) ^ N = κ y * κ (h y) * (c : FractionRing R) := by
      simpa using congrArg Subtype.val hc
    have : ((κ y ^ N * (κ y * κ (h y))⁻¹ : (FractionRing R)ˣ) : FractionRing R) = c := by
      rw [Units.val_mul, Units.mul_inv_eq_iff_eq_mul, Units.val_pow_eq_pow_val, hc', Units.val_mul, mul_comm]
    exact this ▸ c.2
  obtain ⟨r, hr⟩ := hx
  refine ⟨r, ?_⟩
  rw [hr, mul_assoc, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuaternionNormOneNearReSqNeOne
section
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
open Filter

namespace GlobalTheory.QSA

theorem exists_nrm_one_re_sq_ne_one : ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K], (2 : K) ≠ 0 → (𝓝[≠] (0 : K)).NeBot → ∀ a b : K, a ≠ 0 → ∀ g : ℍ[K, a, b], nrm g = 1 → ∀ W : Set ℍ[K, a, b], W ∈ 𝓝 g → ∃ g' : ℍ[K, a, b], nrm g' = 1 ∧ g'.re ^ 2 ≠ 1 ∧ W ∈ 𝓝 g' := by
  intro K _ _ _ _ h2 hne a b ha g hg W hW
  by_cases hre : g.re ^ 2 = 1
  swap
  · exact ⟨g, hg, hre, hW⟩
  have hs0 : g.re ≠ 0 := by
    intro h
    rw [h] at hre
    simp at hre
  let X0 : K → K := fun τ => (1 + a * τ ^ 2) / (1 - a * τ ^ 2)
  let X1 : K → K := fun τ => 2 * τ / (1 - a * τ ^ 2)
  let x : K → ℍ[K, a, b] := fun τ => ⟨X0 τ, X1 τ, 0, 0⟩
  have hD : Tendsto (fun τ : K => 1 - a * τ ^ 2) (𝓝 0) (𝓝 1) := by
    have : Continuous (fun τ : K => 1 - a * τ ^ 2) := by fun_prop
    simpa using this.tendsto 0
  have hx0 : Tendsto X0 (𝓝 0) (𝓝 1) := by
    have h1 : Continuous (fun τ : K => 1 + a * τ ^ 2) := by fun_prop
    have := (h1.tendsto 0).div hD one_ne_zero
    simpa [Pi.div_def] using this
  have hx1 : Tendsto X1 (𝓝 0) (𝓝 0) := by
    have h1 : Continuous (fun τ : K => 2 * τ) := by fun_prop
    have := (h1.tendsto 0).div hD one_ne_zero
    simpa [Pi.div_def] using this
  have key : ∀ c d : K, Tendsto (fun τ => c * X0 τ + d * X1 τ) (𝓝 0) (𝓝 c) := by
    intro c d
    simpa using (hx0.const_mul c).add (hx1.const_mul d)
  have hf : Tendsto (fun τ => g * x τ) (𝓝 0) (𝓝 g) := by
    rw [(Topology.IsInducing.induced coords).tendsto_nhds_iff, tendsto_pi_nhds]
    intro i
    fin_cases i
    · refine (key g.re (a * g.imI)).congr fun τ => ?_
      simp [coords, x]
    · refine (key g.imI g.re).congr fun τ => ?_
      simp [coords, x, add_comm]
    · refine (key g.imJ (-(a * g.imK))).congr fun τ => ?_
      simp [coords, x, sub_eq_add_neg]
    · refine (key g.imK (-g.imJ)).congr fun τ => ?_
      simp [coords, x, add_comm]
  have e1 : ∀ᶠ τ in 𝓝[≠] (0 : K), τ ≠ 0 := self_mem_nhdsWithin
  have e2 : ∀ᶠ τ in 𝓝[≠] (0 : K), 1 - a * τ ^ 2 ≠ 0 :=
    (hD.eventually_ne one_ne_zero).filter_mono nhdsWithin_le_nhds
  have e3 : ∀ᶠ τ in 𝓝[≠] (0 : K), g.re + a * τ * g.imI ≠ 0 := by
    have h1 : Continuous (fun τ : K => g.re + a * τ * g.imI) := by fun_prop
    exact ((h1.tendsto 0).eventually_ne (by simpa using hs0)).filter_mono nhdsWithin_le_nhds
  have e4 : ∀ᶠ τ in 𝓝[≠] (0 : K), g.re * τ + g.imI ≠ 0 := by
    by_cases hI : g.imI = 0
    · filter_upwards [e1] with τ hτ
      simpa [hI] using ⟨hs0, hτ⟩
    · have h1 : Continuous (fun τ : K => g.re * τ + g.imI) := by fun_prop
      exact ((h1.tendsto 0).eventually_ne (by simpa using hI)).filter_mono nhdsWithin_le_nhds
  have e5 : ∀ᶠ τ in 𝓝[≠] (0 : K), g * x τ ∈ interior W :=
    (hf.eventually (interior_mem_nhds.2 hW)).filter_mono nhdsWithin_le_nhds
  obtain ⟨τ, h1, h2', h3, h4, h5⟩ := (e1.and (e2.and (e3.and (e4.and e5)))).exists
  refine ⟨g * x τ, ?_, ?_, mem_interior_iff_mem_nhds.1 h5⟩
  · rw [nrm_mul, hg, one_mul]
    simp only [nrm, x, X0, X1]
    field_simp
    ring
  · have hr : (g * x τ).re = g.re * X0 τ + a * g.imI * X1 τ := by simp [x]
    rw [hr]
    intro h
    have hm : g.re * X0 τ + a * g.imI * X1 τ - g.re
        = 2 * a * τ * (g.re * τ + g.imI) / (1 - a * τ ^ 2) := by
      simp only [X0, X1]
      field_simp
      ring
    have hp : g.re * X0 τ + a * g.imI * X1 τ + g.re
        = 2 * (g.re + a * τ * g.imI) / (1 - a * τ ^ 2) := by
      simp only [X0, X1]
      field_simp
      ring
    have hz : (g.re * X0 τ + a * g.imI * X1 τ - g.re) * (g.re * X0 τ + a * g.imI * X1 τ + g.re) = 0 := by
      linear_combination h - hre
    rw [hm, hp] at hz
    exact mul_ne_zero (div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h2 ha) h1) h4) h2')
      (div_ne_zero (mul_ne_zero h2 h3) h2') hz

end GlobalTheory.QSA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictHenselisationOfHenselian
section
open IsLocalRing

namespace GlobalTheory

open StrictHensOfHens

theorem exists_strictHenselisation_of_henselian : ∀ (R : Type) [CommRing R] [HenselianLocalRing R] (Ω : Type) [Field Ω] [Algebra (ResidueField R) Ω] [IsSepClosure (ResidueField R) Ω], ∃ (S : Type) (_ : CommRing S) (_ : Algebra R S) (_ : HenselianLocalRing S) (_ : IsLocalHom (algebraMap R S)), IsSepClosed (ResidueField S) ∧ Module.Flat R S ∧ (maximalIdeal R).map (algebraMap R S) = maximalIdeal S ∧ Nonempty (ResidueField S ≃ₐ[ResidueField R] Ω) ∧ (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) := by
  intro R _ _ Ω _ _ _
  have hflat : Module.Flat R (SH R Ω) := by
    refine _root_.GlobalTheory.flat_of_forall_finset_subset_flat R (SH R Ω) fun s => ?_
    obtain ⟨E, hE⟩ := StrictHensOfHens.exists_ofA_finset (R := R) (Ω := Ω) s
    let e := AlgEquiv.ofInjective (ofA (R := R) (Ω := Ω) E) (ofA_injective E)
    haveI : Module.Flat R (Lift R Ω E) := Algebra.Smooth.flat _ _
    refine ⟨Subalgebra.toSubmodule (ofA (R := R) (Ω := Ω) E).range, fun x hx => ?_,
      Module.Flat.of_linearEquiv e.symm.toLinearEquiv⟩
    obtain ⟨a, rfl⟩ := hE x hx
    exact ⟨a, rfl⟩
  refine ⟨SH R Ω, inferInstance, inferInstance, inferInstance, inferInstance,
    isSepClosed_residueField, hflat, map_maximalIdeal, ⟨resAlgEquiv⟩, Idx R Ω, inferInstance,
    inferInstance, inferInstance, fun E => (ofA (R := R) (Ω := Ω) E).range, ?_, ?_, fun E => ?_⟩
  · intro E F h x hx
    obtain ⟨a, rfl⟩ := hx
    exact ⟨trans R Ω E F h a, ofA_trans h a⟩
  · intro s
    obtain ⟨E, a, rfl⟩ := StrictHensOfHens.exists_ofA (R := R) (Ω := Ω) s
    exact ⟨E, a, rfl⟩
  · refine ⟨Lift R Ω E, inferInstance, inferInstance, inferInstance, maximalIdeal _, inferInstance, ⟨?_⟩⟩
    have hu : (maximalIdeal (Lift R Ω E)).primeCompl ≤ IsUnit.submonoid (Lift R Ω E) :=
      fun x hx => by simpa [IsUnit.mem_submonoid_iff, mem_maximalIdeal, mem_nonunits_iff] using hx
    exact ((IsLocalization.atUnits (Lift R Ω E) (maximalIdeal (Lift R Ω E)).primeCompl
      (S := Localization.AtPrime (maximalIdeal (Lift R Ω E))) hu).restrictScalars R).symm.trans
      (AlgEquiv.ofInjective (ofA (R := R) (Ω := Ω) E) (ofA_injective E))

end GlobalTheory
end

