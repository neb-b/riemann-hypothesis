module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
public import GroundTheory.AutomorphicForms.AdelicGLn

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceLevelIffLatticeStable
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLat.Lv

open IsDedekindDomain.HeightOneSpectrum

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ} (b : Module.Basis (Fin m) K.E B.A)

def col (Z : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (j : Fin m) : B.A := ∑ i, e.symm (Z i j) • b i

theorem repr_col (Z : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (j i : Fin m) :
    b.repr (col e b Z j) i = e.symm (Z i j) := by
  rw [col, Module.Basis.repr_sum_self]

theorem repr_sum_smul_col (Z : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (c : Fin m → K.E) (i : Fin m) :
    b.repr (∑ l, c l • col e b Z l) i = e.symm ((Z *ᵥ fun l => e (c l)) i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, repr_col,
    smul_eq_mul, Matrix.mulVec, dotProduct, map_mul, RingEquiv.symm_apply_apply]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

theorem mul_col (a : B.A) (Z : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (j : Fin m) :
    a * col e b Z j = col e b (GlobalTheory.TwLat.mulMat e b a * Z) j := by
  apply b.repr.injective
  ext i
  rw [repr_col]
  have h2 := congrFun (LinearMap.toMatrix_mulVec_repr b b (LinearMap.mulLeft K.E a) (col e b Z j)) i
  simp only [LinearMap.mulLeft_apply] at h2
  rw [← h2]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, GlobalTheory.TwLat.mulMat, Matrix.mul_apply, Matrix.map_apply, repr_col, map_sum,
    map_mul, RingEquiv.symm_apply_apply]

theorem mulMat_one_add (t : K.E) (x : B.A) :
    GlobalTheory.TwLat.mulMat e b (1 + algebraMap K.E B.A t * x) = 1 + e t • GlobalTheory.TwLat.mulMat e b x := by
  ext i j
  simp only [GlobalTheory.TwLat.mulMat, Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.mulLeft_apply, add_mul, one_mul,
    mul_assoc, ← Algebra.smul_def, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, map_mul,
    Matrix.add_apply, Matrix.smul_apply, Module.Basis.repr_self, Matrix.one_apply, Finsupp.single_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

theorem sum_smul_col_inj (g : GLw m w) (c c' : Fin m → K.E)
    (h : ∑ l, c l • col e b g.val l = ∑ l, c' l • col e b g.val l) : c = c' := by
  have h1 : g.val *ᵥ (fun l => e (c l)) = g.val *ᵥ (fun l => e (c' l)) := by
    funext i
    have := congrArg (fun x => b.repr x i) h
    simp only [repr_sum_smul_col] at this
    exact e.symm.injective this
  have h2 := congrArg (fun v => (g⁻¹).val *ᵥ v) h1
  simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h2
  funext l
  exact e.injective (congrFun h2 l)

theorem mul_le_self_iff (a b : WithZero (Multiplicative ℤ)) (ha : a ≠ 0) : a * b ≤ a ↔ b ≤ 1 := by
  constructor
  · intro h
    have : a⁻¹ * (a * b) ≤ a⁻¹ * a := by gcongr
    rwa [← mul_assoc, inv_mul_cancel₀ ha, one_mul] at this
  · intro h
    exact mul_le_of_le_one_right' h

end GlobalTheory.TwLat.Lv

namespace GlobalTheory.TwLat.Lv

open IsDedekindDomain.HeightOneSpectrum

theorem valued_uniformizerPower_completion_eq_exp_neg {E : Type} [Field E] [NumberField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
    (e : K.E ≃+* w.adicCompletion E) (hval : ∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) (t : K.O) (k : ℕ)
    (ht : t ≠ 0) (hk : GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k) :
    Valued.v (e (algebraMap K.O K.E t)) = WithZero.exp (-(k : ℤ)) := by
  have hne : e (algebraMap K.O K.E t) ≠ 0 := by
    intro h
    apply ht
    have h1 : algebraMap K.O K.E t = 0 := e.injective (h.trans (map_zero e).symm)
    exact IsFractionRing.injective K.O K.E (h1.trans (map_zero _).symm)
  have hv : Valued.v (e (algebraMap K.O K.E t)) ≠ 0 := (Valuation.ne_zero_iff _).mpr hne
  rw [hval, ordL, dite_eq_right hv] at hk
  rw [← WithZero.coe_unzero hv, WithZero.exp]
  congr 1
  rw [← ofAdd_toAdd (WithZero.unzero hv)]
  congr 1
  omega

theorem level_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ (t : K.O) (k : ℕ), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ g N : GLw m w, N.val = GlobalTheory.TwLat.mulMat e b (1 + algebraMap K.O B.A t * B.g) → ((g⁻¹ * N * g ∈ GlobalTheory.LFun.KGL w (n := m) ∧ ∀ i j, Valued.v ((g⁻¹ * N * g).val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))) ↔ ∀ y ∈ GlobalTheory.TwLat.lat e b g, B.g * y ∈ GlobalTheory.TwLat.lat e b g) := by
  intro E _ _ _ _ w _ K e he hint hval B m b t k hs hk g N hN
  have hv := valued_uniformizerPower_completion_eq_exp_neg e hval t k hs.1 hk
  obtain ⟨c, hc⟩ : ∃ c, c = e (algebraMap K.O K.E t) := ⟨_, rfl⟩
  rw [← hc] at hv
  obtain ⟨Y, hY⟩ : ∃ Y : Matrix (Fin m) (Fin m) (w.adicCompletion E),
      Y = (g⁻¹).val * GlobalTheory.TwLat.mulMat e b B.g * g.val := ⟨_, rfl⟩
  have hA : (g⁻¹ * N * g).val = 1 + c • Y := by
    rw [Units.val_mul, Units.val_mul, hN, IsScalarTower.algebraMap_apply K.O K.E B.A, mulMat_one_add, ← hc, hY,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one]
  have hent : ∀ i j, (g⁻¹ * N * g).val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j = c * Y i j := by
    intro i j
    rw [hA]
    simp
  have hexp : WithZero.exp (-(k : ℤ)) ≠ 0 := WithZero.exp_ne_zero
  have hcoef : (∀ i j, Valued.v ((g⁻¹ * N * g).val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤
      WithZero.exp (-(k : ℤ))) ↔ ∀ i j, Valued.v (Y i j) ≤ 1 := by
    simp only [hent, map_mul, hv]
    exact forall_congr' fun i => forall_congr' fun j => mul_le_self_iff _ _ hexp

  have hgY : g.val * Y = GlobalTheory.TwLat.mulMat e b B.g * g.val := by
    rw [hY, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hgcol : ∀ j, B.g * col e b g.val j = ∑ l, e.symm (Y l j) • col e b g.val l := by
    intro j
    rw [mul_col, ← hgY]
    apply b.repr.injective
    ext i
    rw [repr_sum_smul_col, repr_col]
    simp only [RingEquiv.apply_symm_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply]
  have hlat : (∀ y ∈ GlobalTheory.TwLat.lat e b g, B.g * y ∈ GlobalTheory.TwLat.lat e b g) ↔ ∀ i j, Valued.v (Y i j) ≤ 1 := by
    constructor
    · intro hst i j
      have hmem : B.g * col e b g.val j ∈ GlobalTheory.TwLat.lat e b g :=
        hst _ (Submodule.subset_span ⟨j, rfl⟩)
      obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun K.O).mp hmem
      have ho' : ∑ l, algebraMap K.O K.E (o l) • col e b g.val l = ∑ l, e.symm (Y l j) • col e b g.val l := by
        rw [← hgcol j, ← ho]
        exact Finset.sum_congr rfl fun l _ => algebraMap_smul K.E (o l) _
      have := congrFun (sum_smul_col_inj e b g _ _ ho') i
      have hi := (hint (algebraMap K.O K.E (o i))).mp ⟨o i, rfl⟩
      rw [this, RingEquiv.apply_symm_apply] at hi
      exact hi
    · intro hYi y hy
      have hle : GlobalTheory.TwLat.lat e b g ≤ (GlobalTheory.TwLat.lat e b g).comap (LinearMap.mulLeft K.O B.g) := by
        rw [GlobalTheory.TwLat.lat, Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        show B.g * col e b g.val j ∈ GlobalTheory.TwLat.lat e b g
        rw [hgcol j]
        refine Submodule.sum_mem _ fun l _ => ?_
        obtain ⟨o, ho⟩ := (hint (e.symm (Y l j))).mpr (by rw [RingEquiv.apply_symm_apply]; exact hYi l j)
        rw [← ho, algebraMap_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
      exact hle hy

  have hK : (∀ i j, Valued.v (Y i j) ≤ 1) → g⁻¹ * N * g ∈ GlobalTheory.LFun.KGL w (n := m) := by
    intro hYi
    haveI : IsLocalRing (Ov E w) := inferInstanceAs (IsLocalRing (w.adicCompletionIntegers E))
    have hcS : c ∈ Ov E w := by
      show c ∈ w.adicCompletionIntegers E
      rw [mem_adicCompletionIntegers, hv]
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
    let c' : Ov E w := ⟨c, hcS⟩
    let Y' : Matrix (Fin m) (Fin m) (Ov E w) := fun i j =>
      ⟨Y i j, by show Y i j ∈ w.adicCompletionIntegers E; rw [mem_adicCompletionIntegers]; exact hYi i j⟩
    let A' : Matrix (Fin m) (Fin m) (Ov E w) := 1 + c' • Y'
    have hmap : A'.map (Ov E w).subtype = (g⁻¹ * N * g).val := by
      rw [hA]
      ext i j
      simp only [A', Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
        map_add, map_mul]
      split_ifs <;> simp [c', Y']
    have hc'nu : ¬ IsUnit c' := by
      rintro ⟨u, hu⟩
      have h1 : c * ((u⁻¹ : (Ov E w)ˣ) : Ov E w) = 1 := by
        have := congrArg Subtype.val (Units.mul_inv u)
        rw [hu] at this
        exact this
      obtain ⟨o, ho⟩ := (hint (e.symm ((u⁻¹ : (Ov E w)ˣ) : Ov E w))).mpr (by
        rw [RingEquiv.apply_symm_apply]
        exact (mem_adicCompletionIntegers _ _ _).mp ((u⁻¹ : (Ov E w)ˣ) : Ov E w).2)
      have h2 : algebraMap K.O K.E (t * o) = 1 := by
        apply e.injective
        rw [map_mul, map_mul, ho, RingEquiv.apply_symm_apply, ← hc, h1, map_one]
      have h3 : t * o = 1 := IsFractionRing.injective K.O K.E (h2.trans (map_one _).symm)
      exact (IsLocalRing.mem_maximalIdeal t).mp hs.2.1 ⟨⟨t, o, h3, by rw [mul_comm]; exact h3⟩, rfl⟩
    have hres0 : IsLocalRing.residue (Ov E w) c' = 0 :=
      (IsLocalRing.residue_eq_zero_iff c').mpr ((IsLocalRing.mem_maximalIdeal c').mpr hc'nu)
    have hdet : IsUnit A'.det := by
      apply (isUnit_map_iff (IsLocalRing.residue (Ov E w)) _).mp
      rw [RingHom.map_det]
      have : (IsLocalRing.residue (Ov E w)).mapMatrix A' = 1 := by
        ext i j
        simp [A', hres0, Matrix.one_apply]
      rw [this, Matrix.det_one]
      exact isUnit_one
    have hU : IsUnit A' := (Matrix.isUnit_iff_isUnit_det A').mpr hdet
    refine ⟨hU.unit, ?_⟩
    apply Units.ext
    rw [← hmap]
    rfl
  constructor
  · rintro ⟨-, h⟩
    exact hlat.2 (hcoef.1 h)
  · intro h
    have h' := hlat.1 h
    exact ⟨hK h', hcoef.2 h'⟩

end GlobalTheory.TwLat.Lv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdFormulaSqrtNormalizedAbsValuesCMField
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ProdForm

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem absHalf_eq_sqrt_norm (w : Pl E) {y : w.adicCompletion E} (hy : y ≠ 0) :
    absHalf w y = ((Real.sqrt ‖y‖ : ℝ) : ℂ) := by
  have hv : (Valued.v y : WithZero (Multiplicative ℤ)) ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
  unfold absHalf
  congr 2
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv, ordL, dite_eq_right hv, neg_neg]
  simp [qV, WithZero.toAdd_unzero_eq_log]

theorem absHalf_prodFormula : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (x : E), x ≠ 0 →
    (Function.mulSupport fun w : Pl E => absHalf w (algebraMap E (w.adicCompletion E) x)).Finite ∧
      (∏ᶠ w : Pl E, absHalf w (algebraMap E (w.adicCompletion E) x)) * ∏ v : InfinitePlace E, (‖v.embedding x‖ : ℂ) = 1 := by
  intro E _ _ _ x hx
  have key : ∀ w : Pl E, absHalf w (algebraMap E (w.adicCompletion E) x) =
      ((Real.sqrt (FinitePlace.mk w x) : ℝ) : ℂ) := fun w =>
    absHalf_eq_sqrt_norm w ((_root_.map_ne_zero _).mpr hx)
  have hfin : (Function.mulSupport fun w : Pl E => FinitePlace.mk w x).Finite := by
    have h0 := FinitePlace.hasFiniteMulSupport (K := E) hx
    have he : (fun w : Pl E => FinitePlace.mk w x) =
        (fun u : FinitePlace E => u x) ∘ FinitePlace.equivHeightOneSpectrum.symm := rfl
    rw [he, Function.mulSupport_comp_eq_preimage]
    exact Set.Finite.preimage (FinitePlace.equivHeightOneSpectrum.symm.injective.injOn) h0
  have hsup : (Function.mulSupport fun w : Pl E => Real.sqrt (FinitePlace.mk w x)) =
      Function.mulSupport fun w : Pl E => FinitePlace.mk w x := by
    ext w
    simp [Real.sqrt_eq_one]
  refine ⟨?_, ?_⟩
  · have hs : (Function.mulSupport fun w : Pl E => absHalf w (algebraMap E (w.adicCompletion E) x)) =
        Function.mulSupport fun w : Pl E => Real.sqrt (FinitePlace.mk w x) := by
      ext w
      simp only [Function.mem_mulSupport, key, ne_eq, Complex.ofReal_eq_one]
    rw [hs, hsup]
    exact hfin
  · have hA : (∏ᶠ w : Pl E, Real.sqrt (FinitePlace.mk w x)) ^ 2 = ∏ᶠ w : Pl E, FinitePlace.mk w x := by
      have hfs : Function.HasFiniteMulSupport fun w : Pl E => Real.sqrt (FinitePlace.mk w x) := by
        unfold Function.HasFiniteMulSupport; rw [hsup]; exact hfin
      rw [finprod_pow hfs]
      congr 1
      funext w
      exact Real.sq_sqrt (apply_nonneg _ _)
    have hF : ∏ᶠ w : Pl E, FinitePlace.mk w x = ∏ᶠ u : FinitePlace E, u x :=
      finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm (f := fun u : FinitePlace E => u x)
    have hP : (∏ v : InfinitePlace E, ‖v.embedding x‖) ^ 2 = ∏ v : InfinitePlace E, v x ^ v.mult := by
      rw [← Finset.prod_pow]
      congr 1
      funext v
      rw [InfinitePlace.norm_embedding_eq, InfinitePlace.mult,
        if_neg (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex v))]
    have hprod := prod_abs_eq_one (K := E) hx
    have hsq : ((∏ᶠ w : Pl E, Real.sqrt (FinitePlace.mk w x)) * ∏ v : InfinitePlace E, ‖v.embedding x‖) ^ 2 = 1 := by
      rw [mul_pow, hA, hP, hF, mul_comm]
      exact hprod
    have h1 : (∏ᶠ w : Pl E, Real.sqrt (FinitePlace.mk w x)) * ∏ v : InfinitePlace E, ‖v.embedding x‖ = 1 :=
      (pow_eq_one_iff_of_nonneg (mul_nonneg (finprod_nonneg fun w => Real.sqrt_nonneg _)
        (Finset.prod_nonneg fun v _ => norm_nonneg _)) two_ne_zero).mp hsq
    have hc : ∏ᶠ w : Pl E, absHalf w (algebraMap E (w.adicCompletion E) x) =
        ((∏ᶠ w : Pl E, Real.sqrt (FinitePlace.mk w x) : ℝ) : ℂ) := by
      simp_rw [key]
      exact (Complex.ofRealHom.toMonoidHom.map_finprod_of_injective Complex.ofReal_injective _).symm
    rw [hc]
    exact_mod_cast h1

end GlobalTheory.ProdForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.GlobLev

open GlobalTheory.SplitPts GroundTheory.Automorphic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}


omit [IsCMField E] in
theorem mem_KGL_iff_val (w : Pl E) (g : GLw n w) :
    g ∈ GlobalTheory.LFun.KGL w (n := n) ↔ (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1 := by
  have hO : GLnLocal.integralGL (w.adicCompletion E) n = GlobalTheory.LFun.KGL w (n := n) := by
    have h : (ValuativeRel.valuation (w.adicCompletion E)).integer = Formalism.UG.Ov E w :=
      Subring.ext fun x => GroundTheory.Global.mem_valuationInteger_iff w x
    rw [GlobalTheory.LFun.KGL, ← h]; rfl
  rw [← hO, GLnLocal.mem_integralGL_iff]
  simp only [GroundTheory.Global.mem_valuationInteger_iff]
  rfl

theorem eq_or_eq_conjSrc {w u : Pl E}
    (h : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) :
    u = w ∨ u = conjSrc (conjE E) w := by
  by_cases huw : u = w
  · exact Or.inl huw
  · exact (over_split ⟨u, huw, h⟩).2.2 u h

theorem conjSrc_eq_of_not_split {w : Pl E} (hw : ¬ IsSplitAt w) : conjSrc (conjE E) w = w := by
  by_contra hne
  exact hw ⟨_, hne, (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) w _).2
      (Or.inr (conjPl_self_conjSrc w))⟩

theorem conjLoc_eq_cj {w : Pl E} (hw : ¬ IsSplitAt w) (a : Af E) :
    conjLoc (conjE E) w (pLoc E (conjSrc (conjE E) w) a) = cj w (pLoc E w a) := by
  have key : ∀ (v : Pl E) (_ : v = w) (f : v.adicCompletion E →+* w.adicCompletion E), Continuous f →
      (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (conjE E k)) → f (pLoc E v a) = cj w (pLoc E w a) := by
    rintro v rfl f hf h
    have hex : ∃ s : v.adicCompletion E →+* v.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := ⟨f, hf, h⟩
    rw [cj, dite_eq_left hex]
    exact congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf hex.choose_spec.1
      (funext fun k => (h k).trans (hex.choose_spec.2 k).symm)) _
  exact key _ (conjSrc_eq_of_not_split hw) _ (conjLoc_spec (conjE E) _).1 (conjLoc_spec (conjE E) _).2.1

theorem cLoc_mem_UL (w : Pl E) (x : UA E n) : cLoc w x ∈ UL n w := by
  unfold UL
  split_ifs with hw
  · exact Subgroup.mem_top _
  · have h := comp_eq x w
    have e : (cLoc (conjSrc (conjE E) w) x).val.map (conjLoc (conjE E) w) = (cLoc w x).val.map (cj w) :=
      Matrix.ext fun i j => conjLoc_eq_cj hw _
    rw [e] at h
    change ((cLoc w x).val.map (cj w))ᵀ * 1 * (cLoc w x).val = 1
    rw [Matrix.mul_one]
    exact h

theorem val_inv_entry (x : UA E n) (u : Pl E) (i j : Fin n) :
    Valued.v (((cLoc u x)⁻¹).val i j) = Valued.v ((cLoc (conjSrc (conjE E) u) x).val j i) := by
  have h := comp_eq x u
  have e : ((cLoc u x)⁻¹).val = ((cLoc (conjSrc (conjE E) u) x).val.map (conjLoc (conjE E) u))ᵀ :=
    (Units.eq_inv_of_mul_eq_one_right h).symm
  rw [e]
  exact (conjLoc_spec (conjE E) u).2.2 _

theorem integral_conjSrc (x : UA E n) (u : Pl E) (h : cLoc u x ∈ GlobalTheory.LFun.KGL u (n := n)) :
    cLoc (conjSrc (conjE E) u) x ∈ GlobalTheory.LFun.KGL (conjSrc (conjE E) u) (n := n) := by
  rw [mem_KGL_iff_val] at h ⊢
  refine ⟨fun i j => (val_inv_entry x u j i) ▸ h.2 j i, fun i j => ?_⟩
  have h2 := val_inv_entry x⁻¹ u j i
  rw [map_inv, map_inv, inv_inv] at h2
  exact h2 ▸ h.1 j i

theorem mem_globLev (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (k : finU (E := E) (n := n)) :
    k ∈ globLev S K' ↔ ∀ w ∈ S, (⟨cLoc w k.1, cLoc_mem_UL w k.1⟩ : UL n w) ∈ K' w := by
  simp only [globLev, Subgroup.mem_iInf, Subgroup.mem_comap]
  refine forall₂_congr fun w _ => ⟨?_, fun h => ⟨_, h, rfl⟩⟩
  rintro ⟨a, ha, e⟩
  have : a = ⟨cLoc w k.1, cLoc_mem_UL w k.1⟩ := Subtype.ext e
  exact this ▸ ha


variable (E n) in
def finPart : finU (E := E) (n := n) →* GL (Fin n) (Af E) :=
  (GeneralLinearGroup.map (pFin E)).comp ((UA E n).subtype.comp (finU (E := E) (n := n)).subtype)

theorem continuous_finPart : Continuous (finPart E n) :=
  (Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))).comp
    (continuous_subtype_val.comp continuous_subtype_val)

theorem globLev_KL_eq {S : Set (Pl E)} (hS : IsSection S) :
    globLev S (KL n) = (AdelicGLn.integralFiniteGL E n).comap (finPart E n) := by
  ext k
  have e : k ∈ (AdelicGLn.integralFiniteGL E n).comap (finPart E n) ↔ ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u (n := n) := by
    rw [Subgroup.mem_comap, AdelicGLn.mem_integralFiniteGL_iff, ← map_inv]
    simp only [mem_KGL_iff_val, ← map_inv, GroundTheory.Global.mem_integralFiniteAdeles]
    exact ⟨fun h u => ⟨fun i j => h.1 i j u, fun i j => h.2 i j u⟩,
      fun h => ⟨fun i j u => (h u).1 i j, fun i j u => (h u).2 i j⟩⟩
  rw [e, mem_globLev]
  refine ⟨fun h u => ?_, fun h w _ => h w⟩
  obtain ⟨w, ⟨hw, hwu⟩, -⟩ := hS u
  rcases eq_or_eq_conjSrc hwu.symm with rfl | rfl
  · exact h u hw
  · exact integral_conjSrc k.1 w (h w hw)

theorem continuous_pInf_ad : Continuous (pInf E) :=
  continuous_pi fun w =>
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst

theorem continuous_conj_ad : Continuous (conjAd E) :=
  ((continuous_infEq E).comp (continuous_star.comp continuous_pInf_ad)).prodMk
    ((continuous_conjFin _).comp continuous_snd)

theorem isClosedEmbedding_finU : Topology.IsClosedEmbedding (fun x : finU (E := E) (n := n) => ((x : UA E n) : GA E n)) := by
  haveI : T2Space (FiniteAdeleRing (𝓞 E) E) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) Filter.cofinite))
  haveI : T2Space (InfiniteAdeleRing E) := inferInstanceAs (T2Space ((v : InfinitePlace E) → v.Completion))
  haveI : T2Space (Ad E) := inferInstanceAs (T2Space (InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E))
  have h1 : IsClosed ((UA E n : Subgroup (GA E n)) : Set (GA E n)) := by
    show IsClosed {g : GA E n | ((g : Matrix (Fin n) (Fin n) (Ad E)).map (conjAd E))ᵀ * 1 *
      (g : Matrix (Fin n) (Fin n) (Ad E)) = 1}
    exact isClosed_eq (((Units.continuous_val.matrix_map continuous_conj_ad).matrix_transpose.matrix_mul
      continuous_const).matrix_mul Units.continuous_val) continuous_const
  have h2 : IsClosed ((finU (E := E) (n := n) : Subgroup (UA E n)) : Set (UA E n)) := by
    haveI : T2Space (GL (Fin n) (Cinf E)) := Units.isEmbedding_embedProduct.t2Space
    have hc : Continuous (cInf (E := E) (n := n)) :=
      (Continuous.units_map _ (continuous_id.matrix_map continuous_pInf_ad)).comp continuous_subtype_val
    exact isClosed_eq hc continuous_const
  exact h1.isClosedEmbedding_subtypeVal.comp h2.isClosedEmbedding_subtypeVal

theorem continuous_finGL_ad : Continuous (finGL E n) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
    (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))))

theorem continuous_cLoc (w : Pl E) : Continuous (cLoc (n := n) w) :=
  (Continuous.units_map _ (continuous_id.matrix_map
    ((RestrictedProduct.continuous_eval w).comp continuous_snd))).comp continuous_subtype_val

theorem globLev_isOpen_isCompact_isLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' →
    IsOpen (globLev S (KL n) : Set (finU (E := E) (n := n))) ∧ IsCompact (globLev S (KL n) : Set (finU (E := E) (n := n))) ∧
      IsLevel (MonoidHom.id _) (globLev S (KL n)) (globLev S K') := by
  intro E _ _ _ _ n _ S hS K' hK
  have hO : IsOpen (globLev S (KL n) : Set (finU (E := E) (n := n))) := by
    rw [globLev_KL_eq hS]
    exact (AdelicGLn.isOpen_integralFiniteGL E n).preimage continuous_finPart
  have hle : globLev S K' ≤ globLev S (KL n) := fun k hk =>
    (mem_globLev S _ k).2 fun w hw => (hK.1 w).2.1 ((mem_globLev S _ k).1 hk w hw)
  refine ⟨hO, ?_, ?_, hle, fun k hk => hk⟩
  · refine IsCompact.of_isClosed_subset (isClosedEmbedding_finU.isCompact_preimage
      ((AdelicGLn.isCompact_integralFiniteGL E n).image continuous_finGL_ad))
      (Subgroup.isClosed_of_isOpen _ hO) fun x hx => ⟨finPart E n x, ?_, ?_⟩
    · rw [globLev_KL_eq hS] at hx
      exact hx
    · have h1 : GeneralLinearGroup.map (pInf E) ((x : UA E n) : GA E n) = 1 := x.2
      exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)
  · have hfin : {w | w ∈ S ∧ K' w ≠ KL n w}.Finite := (Filter.eventually_cofinite.1 hK.2).subset fun w hw => hw.2
    have e : (globLev S K' : Set (finU (E := E) (n := n))) = (globLev S (KL n) : Set (finU (E := E) (n := n))) ∩
        ⋂ w ∈ {w | w ∈ S ∧ K' w ≠ KL n w},
          (fun k : finU (E := E) (n := n) => (⟨cLoc w k.1, cLoc_mem_UL w k.1⟩ : UL n w)) ⁻¹' (K' w : Set (UL n w)) := by
      ext k
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
      refine ⟨fun hk => ⟨hle hk, fun w hw => (mem_globLev S _ k).1 hk w hw.1⟩, fun hk => ?_⟩
      refine (mem_globLev S _ k).2 fun w hw => ?_
      by_cases h : K' w = KL n w
      · rw [h]; exact (mem_globLev S _ k).1 hk.1 w hw
      · exact hk.2 w ⟨hw, h⟩
    rw [e]
    exact hO.inter (hfin.isOpen_biInter fun w _ => (hK.1 w).1.preimage
      (Continuous.subtype_mk ((continuous_cLoc w).comp continuous_subtype_val) _))

end GlobalTheory.BCT.GlobLev
end
end

