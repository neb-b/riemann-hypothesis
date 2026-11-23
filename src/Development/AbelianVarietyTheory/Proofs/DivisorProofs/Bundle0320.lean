module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgClosedFractionRing
section
open Polynomial

namespace GlobalTheory.FractionRingRootRange

theorem root_mem_range {A B : Type} [CommRing A] [Nontrivial A] [CommRing B] [IsDomain B] [Algebra A B]
    (h : GlobalTheory.EtC.AIC A) (z : B) :
    ∀ (n : ℕ) (p : A[X]), p.natDegree = n → p.Monic → aeval z p = 0 → ∃ a : A, algebraMap A B a = z := by
  intro n
  induction n with
  | zero =>
    intro p hdeg hmon hz
    rw [Polynomial.eq_one_of_monic_natDegree_zero hmon hdeg, map_one] at hz
    exact absurd hz one_ne_zero
  | succ n ih =>
    intro p hdeg hmon hz
    obtain ⟨a, ha⟩ := h p hmon (by omega)
    have hmul : (X - C a) * (p /ₘ (X - C a)) = p := mul_divByMonic_eq_iff_isRoot.mpr ha
    have hqmon : (p /ₘ (X - C a)).Monic :=
      (monic_X_sub_C a).of_mul_monic_left (by rw [hmul]; exact hmon)
    have hqdeg : (p /ₘ (X - C a)).natDegree = n := by
      rw [natDegree_divByMonic p (monic_X_sub_C a), natDegree_X_sub_C, hdeg]
      omega
    rw [← hmul, map_mul] at hz
    simp only [map_sub, aeval_X, aeval_C] at hz
    rcases mul_eq_zero.mp hz with h1 | h1
    · exact ⟨a, (sub_eq_zero.mp h1).symm⟩
    · exact ih _ hqdeg hqmon h1

theorem isAlgClosed_fractionRing (A : Type) [CommRing A] [IsDomain A] (h : GlobalTheory.EtC.AIC A) :
    IsAlgClosed (FractionRing A) := by
  refine IsAlgClosed.of_exists_root _ fun p hmon hirr => ?_
  have hdeg : p.degree ≠ 0 := (Polynomial.degree_pos_of_irreducible hirr).ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (p.map (algebraMap (FractionRing A) (AlgebraicClosure (FractionRing A))))
    (by rwa [degree_map])
  have hpz : aeval z p = 0 := by
    rw [aeval_def, ← eval_map]
    exact hz
  obtain ⟨b, hbM, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A) p
  have hbK : algebraMap A (FractionRing A) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hbM
  have hq0 : IsLocalization.integerNormalization (nonZeroDivisors A) p ≠ 0 := by
    intro h0
    have h1 := congrArg (fun r => r.coeff p.natDegree) hb
    simp only [h0, Polynomial.map_zero, coeff_zero] at h1
    rw [Algebra.smul_def] at h1
    change 0 = (C (algebraMap A (FractionRing A) b) * p).coeff p.natDegree at h1
    rw [coeff_C_mul, hmon.coeff_natDegree, mul_one] at h1
    exact hbK h1.symm
  have hqz : aeval z (IsLocalization.integerNormalization (nonZeroDivisors A) p) = 0 := by
    rw [← aeval_map_algebraMap (FractionRing A), hb, Algebra.smul_def, map_mul, hpz, mul_zero]
  have inj : ∀ x : A, algebraMap A (AlgebraicClosure (FractionRing A)) x = 0 → x = 0 := by
    intro x hx
    rw [IsScalarTower.algebraMap_apply A (FractionRing A), map_eq_zero] at hx
    exact IsFractionRing.to_map_eq_zero_iff.mp hx
  have hw := integralNormalization_aeval_eq_zero hqz inj
  have hmon' : (integralNormalization (IsLocalization.integerNormalization (nonZeroDivisors A) p)).Monic := by
    exact monic_integralNormalization hq0
  obtain ⟨a, ha⟩ := root_mem_range (B := AlgebraicClosure (FractionRing A)) h _ _ _ rfl hmon' hw
  set c := (IsLocalization.integerNormalization (nonZeroDivisors A) p).leadingCoeff
  have hc : algebraMap A (FractionRing A) c ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]
    exact leadingCoeff_ne_zero.mpr hq0
  have ha' : algebraMap A (AlgebraicClosure (FractionRing A)) a =
      algebraMap A (AlgebraicClosure (FractionRing A)) c * z := by
    rw [ha]
  refine ⟨algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) c, ?_⟩
  have hcB : algebraMap (FractionRing A) (AlgebraicClosure (FractionRing A)) (algebraMap A (FractionRing A) c) ≠ 0 :=
    (_root_.map_ne_zero _).mpr hc
  have hx : algebraMap (FractionRing A) (AlgebraicClosure (FractionRing A))
      (algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) c) = z := by
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ha']
    rw [← IsScalarTower.algebraMap_apply] at hcB
    field_simp
  apply (algebraMap (FractionRing A) (AlgebraicClosure (FractionRing A))).injective
  rw [map_zero, ← eval₂_hom, ← eval_map, hx]
  exact hz

end GlobalTheory.FractionRingRootRange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactPseudoUnitaryOffDiagNormSublevel
section
open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

namespace GlobalTheory.UJOffDiag

open Formalism.REAL

def sgn (e : Bool) : ℝ := if e then 1 else -1

def ind (e : Bool) : ℝ := if e then 1 else 0

lemma term_left (z : ℂ) (e : Bool) :
    star z * (if e then (1 : ℂ) else -1) * z = ((sgn e * ‖z‖ ^ 2 : ℝ) : ℂ) := by
  have h : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']; push_cast; ring
  cases e
  · rw [show star z * (if false = true then (1 : ℂ) else -1) * z = -(star z * z) by simp, h]
    simp [sgn]
  · rw [show star z * (if true = true then (1 : ℂ) else -1) * z = star z * z by simp, h]
    simp [sgn]

lemma term_right (z : ℂ) (e : Bool) :
    z * (if e then (1 : ℂ) else -1) * star z = ((sgn e * ‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [show z * (if e then (1 : ℂ) else -1) * star z = star z * (if e then (1 : ℂ) else -1) * z by ring]
  exact term_left z e

lemma col_id {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) (b : Fin n) :
    ∑ a, sgn (ε a) * ‖g a b‖ ^ 2 = sgn (ε b) := by
  unfold inUJ at hg
  have h := congrFun (congrFun hg b) b
  rw [Matrix.mul_apply] at h
  simp only [Jm, Matrix.mul_diagonal, Matrix.conjTranspose_apply] at h
  simp only [term_left] at h
  have h2 : ((∑ a, sgn (ε a) * ‖g a b‖ ^ 2 : ℝ) : ℂ) = ((sgn (ε b) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, h, Matrix.diagonal_apply_eq]; cases ε b <;> simp [sgn]
  exact_mod_cast h2

lemma row_id {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) (a : Fin n) :
    ∑ b, sgn (ε b) * ‖g a b‖ ^ 2 = sgn (ε a) := by
  have h1 := (indefinite_unitary_inv_closed n ε g hg).1
  have hJ : g * Jm ε * gᴴ = Jm ε := by
    calc g * Jm ε * gᴴ = g * (Jm ε * gᴴ * Jm ε) * Jm ε := by
          simp only [Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]
      _ = Jm ε := by rw [h1, Matrix.one_mul]
  have h := congrFun (congrFun hJ a) a
  rw [Matrix.mul_apply] at h
  simp only [Jm, Matrix.mul_diagonal, Matrix.conjTranspose_apply] at h
  simp only [term_right] at h
  have h2 : ((∑ b, sgn (ε b) * ‖g a b‖ ^ 2 : ℝ) : ℂ) = ((sgn (ε a) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, h, Matrix.diagonal_apply_eq]; cases ε a <;> simp [sgn]
  exact_mod_cast h2

end GlobalTheory.UJOffDiag

namespace GlobalTheory.UJOffDiag

open Formalism.REAL

lemma off_sum_eq {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖M z.1.1 z.1.2‖ ^ 2 =
      ∑ a, ∑ b, ind (ε a) * ind (!ε b) * ‖M a b‖ ^ 2 := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun z : Fin n × Fin n => ε z.1 = true ∧ ε z.2 = false)
    (fun x => by simp) (fun z => ‖M z.1 z.2‖ ^ 2), Finset.sum_filter, ← Finset.univ_product_univ,
    Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  cases ε a <;> cases ε b <;> simp [ind]

lemma hs_eq {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) :
    hs g = n + 4 * ∑ a, ∑ b, ind (ε a) * ind (!ε b) * ‖g a b‖ ^ 2 := by
  have key : ∀ a b, ‖g a b‖ ^ 2 = 4 * (ind (ε a) * ind (!ε b) * ‖g a b‖ ^ 2) +
      (-(sgn (ε a) * ‖g a b‖ ^ 2) + 2 * (ind (ε a) * (sgn (ε b) * ‖g a b‖ ^ 2))) := by
    intro a b; cases ε a <;> cases ε b <;> simp [ind, sgn] <;> ring
  have hcol : ∑ a, ∑ b, sgn (ε a) * ‖g a b‖ ^ 2 = ∑ b, sgn (ε b) := by
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun b _ => col_id ε g hg b
  have hrow : ∑ a, ind (ε a) * ∑ b, sgn (ε b) * ‖g a b‖ ^ 2 = ∑ a, ind (ε a) * sgn (ε a) :=
    Finset.sum_congr rfl fun a _ => by rw [row_id ε g hg a]
  have hn : ∑ a : Fin n, (-(sgn (ε a)) + 2 * (ind (ε a) * sgn (ε a))) = n := by
    rw [show (n : ℝ) = ∑ _a : Fin n, (1 : ℝ) by simp]
    exact Finset.sum_congr rfl fun a _ => by cases ε a <;> simp [ind, sgn] <;> norm_num
  calc hs g = ∑ a, ∑ b, (4 * (ind (ε a) * ind (!ε b) * ‖g a b‖ ^ 2) +
      (-(sgn (ε a) * ‖g a b‖ ^ 2) + 2 * (ind (ε a) * (sgn (ε b) * ‖g a b‖ ^ 2)))) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => key a b
    _ = 4 * (∑ a, ∑ b, ind (ε a) * ind (!ε b) * ‖g a b‖ ^ 2) +
        (-(∑ a, ∑ b, sgn (ε a) * ‖g a b‖ ^ 2) +
          2 * ∑ a, ind (ε a) * ∑ b, sgn (ε b) * ‖g a b‖ ^ 2) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_neg_distrib]
    _ = n + 4 * ∑ a, ∑ b, ind (ε a) * ind (!ε b) * ‖g a b‖ ^ 2 := by
        rw [hcol, hrow, ← hn, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
        ring

end GlobalTheory.UJOffDiag

namespace GlobalTheory

open Formalism.REAL

theorem isCompact_offDiag_sublevel : ∀ (n : ℕ) (ε : Fin n → Bool) (C : ℝ),
    IsCompact {g : UJ ε | ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false},
      ‖(toM g) z.1.1 z.1.2‖ ^ 2 ≤ C} := by
  intro n ε C
  set F : Matrix (Fin n) (Fin n) ℂ → ℝ := fun M =>
    ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖M z.1.1 z.1.2‖ ^ 2 with hF
  have hFc : Continuous F :=
    continuous_finsetSum _ fun z _ => (continuous_norm.comp (continuous_id.matrix_elem z.1.1 z.1.2)).pow 2
  have hK : IsCompact {M : Matrix (Fin n) (Fin n) ℂ | inUJ ε M ∧ F M ≤ C} := by
    refine IsCompact.of_isClosed_subset ((hermitian_small_ball n ε).1 (n + 4 * C)) ?_ ?_
    · exact (indefinite_unitary_closed n ε).inter (isClosed_le hFc continuous_const)
    · rintro M ⟨hM, hFM⟩
      refine ⟨hM, ?_⟩
      rw [UJOffDiag.hs_eq ε M hM, ← UJOffDiag.off_sum_eq]
      have : F M = ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖M z.1.1 z.1.2‖ ^ 2 := rfl
      linarith
  have h := (isClosedEmbeddingMatrix n ε).1.isCompact_preimage hK
  convert h using 1
  ext g
  exact ⟨fun hg => ⟨g.2, hg⟩, fun hg => hg.2⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjOfIsConjGlFieldExtensionInclusion
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.ConjDesc

noncomputable section

theorem smul_of_X {F : Type} [Field F] {M N : Type} [AddCommGroup M] [Module F M] [Module F[X] M]
    [IsScalarTower F F[X] M] [AddCommGroup N] [Module F N] [Module F[X] N] [IsScalarTower F F[X] N]
    (e : M ≃ₗ[F] N) (h : ∀ m, e ((X : F[X]) • m) = (X : F[X]) • e m) (p : F[X]) (m : M) :
    e (p • m) = p • e m := by
  revert m
  induction p using Polynomial.induction_on with
  | C a =>
    intro m
    rw [← Polynomial.algebraMap_eq, algebraMap_smul, algebraMap_smul]
    exact e.map_smul a m
  | add p q hp hq =>
    intro m
    rw [add_smul, add_smul, map_add (f := _), hp, hq]
  | monomial k a ih =>
    intro m
    rw [pow_succ, ← mul_assoc, mul_smul (C a * X ^ k) X m, ih, h, ← mul_smul]

def equivOfX {F : Type} [Field F] {M N : Type} [AddCommGroup M] [Module F M] [Module F[X] M]
    [IsScalarTower F F[X] M] [AddCommGroup N] [Module F N] [Module F[X] N] [IsScalarTower F F[X] N]
    (e : M ≃ₗ[F] N) (h : ∀ m, e ((X : F[X]) • m) = (X : F[X]) • e m) : M ≃ₗ[F[X]] N :=
  { e with
    map_smul' := fun p m => smul_of_X e h p m }

def swapE (F : Type) [Field F] (a b : ℕ) : (Fin a → Fin b → F) ≃ₗ[F] (Fin b → Fin a → F) :=
  { Equiv.piComm (fun (_ : Fin a) (_ : Fin b) => F) with map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

def coordE {F F' : Type} [Field F] [Field F'] [Algebra F F'] {l : ℕ} (b : Module.Basis (Fin l) F F') (n : ℕ) :
    (Fin n → F') ≃ₗ[F] (Fin l → Fin n → F) :=
  (LinearEquiv.piCongrRight fun _ : Fin n => b.equivFun).trans (swapE F n l)

theorem coordE_apply {F F' : Type} [Field F] [Field F'] [Algebra F F'] {l : ℕ} (b : Module.Basis (Fin l) F F') (n : ℕ)
    (v : Fin n → F') (k : Fin l) (i : Fin n) : coordE b n v k i = b.equivFun (v i) k := rfl

theorem coordE_mulVec {F F' : Type} [Field F] [Field F'] [Algebra F F'] {l : ℕ} (b : Module.Basis (Fin l) F F') (n : ℕ)
    (A : Matrix (Fin n) (Fin n) F) (v : Fin n → F') :
    coordE b n (Matrix.mulVec (A.map (algebraMap F F')) v) = fun k => Matrix.mulVec A (coordE b n v k) := by
  funext k i
  rw [coordE_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, ← Algebra.smul_def, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, coordE_apply]

end

end GlobalTheory.Shin.ConjDesc

namespace GlobalTheory.Shin


open ConjDesc in
theorem isConj_of_isConj_incl : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (n : ℕ)
    (γ γ' : GL (Fin n) F), IsConj (incl F F' n γ) (incl F F' n γ') → IsConj γ γ' := by
  intro F F' _ _ _ _ n γ γ' hc
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  have hcA : (c : Matrix (Fin n) (Fin n) F') * ((γ : Matrix (Fin n) (Fin n) F).map (algebraMap F F')) =
      ((γ' : Matrix (Fin n) (Fin n) F).map (algebraMap F F')) * (c : Matrix (Fin n) (Fin n) F') := by
    have h2 : c * incl F F' n γ = incl F F' n γ' * c := by rw [← hc]; group
    exact congrArg (fun x : GL (Fin n) F' => (x : Matrix (Fin n) (Fin n) F')) h2
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  haveI : FiniteDimensional F F' := inferInstance
  have hl : 0 < Module.finrank F F' := Module.finrank_pos
  let b := Module.finBasis F F'
  let f := Matrix.toLin' (γ : Matrix (Fin n) (Fin n) F)
  let g := Matrix.toLin' (γ' : Matrix (Fin n) (Fin n) F)
  let Fc : (Fin n → F') ≃ₗ[F] (Fin n → F') :=
    (LinearEquiv.ofLinear (Matrix.toLin' (c : Matrix (Fin n) (Fin n) F'))
      (Matrix.toLin' ((c⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F'))
      (by rw [← Matrix.toLin'_mul, Units.mul_inv, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, Units.inv_mul, Matrix.toLin'_one])).restrictScalars F
  have hFc : ∀ w, Fc w = Matrix.mulVec (c : Matrix (Fin n) (Fin n) F') w := fun w => rfl
  let core : (Fin (Module.finrank F F') → Fin n → F) ≃ₗ[F] (Fin (Module.finrank F F') → Fin n → F) :=
    (coordE b n).symm.trans (Fc.trans (coordE b n))
  have hcore : ∀ x, core (fun k => f (x k)) = fun k => g (core x k) := by
    intro x
    obtain ⟨v, rfl⟩ := (coordE b n).surjective x
    have h1 : (fun k => f (coordE b n v k)) =
        coordE b n (Matrix.mulVec ((γ : Matrix (Fin n) (Fin n) F).map (algebraMap F F')) v) := by
      rw [coordE_mulVec]; rfl
    rw [h1]
    show coordE b n (Fc ((coordE b n).symm (coordE b n
        (Matrix.mulVec ((γ : Matrix (Fin n) (Fin n) F).map (algebraMap F F')) v)))) =
      fun k => g (coordE b n (Fc ((coordE b n).symm (coordE b n v))) k)
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, hFc, hFc, Matrix.mulVec_mulVec, hcA,
      ← Matrix.mulVec_mulVec, coordE_mulVec]
    rfl
  let Θ : (Fin (Module.finrank F F') → Module.AEval' f) ≃ₗ[F] (Fin (Module.finrank F F') → Module.AEval' g) :=
    (LinearEquiv.piCongrRight fun _ => (Module.AEval'.of f).symm).trans
      (core.trans (LinearEquiv.piCongrRight fun _ => Module.AEval'.of g))
  have hΘ : ∀ x, Θ ((X : F[X]) • x) = (X : F[X]) • Θ x := by
    intro x
    have h3 : (fun k => (Module.AEval'.of f).symm (((X : F[X]) • x) k)) =
        fun k => f ((Module.AEval'.of f).symm (x k)) :=
      funext fun k => Module.AEval'.of_symm_X_smul f (x k)
    funext k
    show Module.AEval'.of g (core (fun k => (Module.AEval'.of f).symm (((X : F[X]) • x) k)) k) =
      (X : F[X]) • Module.AEval'.of g (core (fun k => (Module.AEval'.of f).symm (x k)) k)
    rw [h3, hcore, Module.AEval'.X_smul_of]
  haveI : Finite (Module.AEval' f) := Finite.of_equiv _ (Module.AEval'.of f).toEquiv
  haveI : Finite (Module.AEval' g) := Finite.of_equiv _ (Module.AEval'.of g).toEquiv
  obtain ⟨ψ⟩ := GlobalTheory.T.nonempty_linearEquiv_of_pi_fin_pow_finite F[X] (Module.AEval' f) (Module.AEval' g) (Module.finrank F F') hl
    ⟨equivOfX Θ hΘ⟩
  let e : (Fin n → F) ≃ₗ[F] (Fin n → F) :=
    (Module.AEval'.of f).trans ((ψ.restrictScalars F).trans (Module.AEval'.of g).symm)
  have he : ∀ v, e (f v) = g (e v) := by
    intro v
    have h1 : Module.AEval'.of f (f v) = (X : F[X]) • Module.AEval'.of f v :=
      (Module.AEval'.X_smul_of f v).symm
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply, h1, map_smul]
    exact Module.AEval'.of_symm_X_smul g _
  let P : GL (Fin n) F := ⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap,
    by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩
  refine isConj_iff.mpr ⟨P, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  have h4 : e.toLinearMap ∘ₗ f = g ∘ₗ e.toLinearMap := LinearMap.ext he
  have h5 := congrArg LinearMap.toMatrix' h4
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp] at h5
  simpa [P, f, g, LinearMap.toMatrix'_toLin'] using h5

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdAwayOfIsUnitMod
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem isExcisionNbhd_away_of_isUnit_mod : ∀ (B A' : Type) [CommRing B] [CommRing A'] [Algebra B A'] (f s : B),
    IsExcisionNbhd B A' f → IsUnit (Ideal.Quotient.mk (Ideal.span {f}) s) →
    IsExcisionNbhd B (Localization.Away (algebraMap B A' s)) f := by
  intro B A' _ _ _ f s hA hs
  obtain ⟨hEt, h2, h3⟩ := hA
  obtain ⟨σ, hσ⟩ : ∃ σ : A', σ = algebraMap B A' s := ⟨_, rfl⟩
  rw [← hσ]

  obtain ⟨t, ht⟩ : ∃ t : B, s * t - 1 ∈ Ideal.span {f} := by
    obtain ⟨v, hv⟩ := hs.exists_right_inv
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective v
    refine ⟨t, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hv, map_one, sub_self]
  have hpow : ∀ n : ℕ, (s * t) ^ n - 1 ∈ Ideal.span {f} := by
    intro n
    obtain ⟨c, hc⟩ := (sub_dvd_pow_sub_pow (s * t) 1 n)
    rw [one_pow] at hc
    rw [hc]
    exact Ideal.mul_mem_right _ _ ht
  haveI : Algebra.Etale A' (Localization.Away σ) := Algebra.Etale.of_isLocalizationAway σ
  haveI : Algebra.Etale B (Localization.Away σ) := Algebra.Etale.comp B A' (Localization.Away σ)
  refine ⟨inferInstance, ?_, ?_⟩
  · intro x
    obtain ⟨⟨a', m⟩, hx⟩ := IsLocalization.mk'_surjective (Submonoid.powers σ) x
    have hxs : x * algebraMap A' (Localization.Away σ) m = algebraMap A' _ a' := by
      rw [← hx]; exact IsLocalization.mk'_spec _ _ _
    obtain ⟨n, hn⟩ := m.2
    rw [← hn] at hxs
    obtain ⟨b, hb⟩ := h2 (a' * algebraMap B A' t ^ n)
    refine ⟨b, ?_⟩
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hb
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 (hpow n)
    have hc' := congrArg (algebraMap A' (Localization.Away σ)) hc
    have hv' := congrArg (algebraMap A' (Localization.Away σ)) (congrArg (algebraMap B A') hv)
    rw [Ideal.mem_span_singleton']
    refine ⟨-(x * algebraMap A' _ (algebraMap B A' v)) + algebraMap A' _ c, ?_⟩
    simp only [IsScalarTower.algebraMap_apply B A' (Localization.Away σ), map_mul, map_sub, map_pow, map_one,
      ← hσ] at hxs hc' hv' ⊢
    linear_combination hc' - x * hv' - (algebraMap A' (Localization.Away σ) (algebraMap B A' t)) ^ n * hxs
  · intro a ha
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 ha
    obtain ⟨⟨c, _, n, rfl⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers σ) y
    have hys := IsLocalization.mk'_spec (Localization.Away σ) c (⟨σ ^ n, n, rfl⟩ : Submonoid.powers σ)
    have key : algebraMap A' (Localization.Away σ) (algebraMap B A' a * σ ^ n) =
        algebraMap A' (Localization.Away σ) (c * algebraMap B A' f) := by
      rw [map_mul, map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ← hy]
      simp only at hys
      rw [← hys]; ring
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers σ) _).1 key
    have hmem : algebraMap B A' (s ^ (k + n) * a) ∈ Ideal.span {algebraMap B A' f} := by
      rw [Ideal.mem_span_singleton']
      refine ⟨σ ^ k * c, ?_⟩
      simp only at hk
      rw [map_mul, map_pow, ← hσ, pow_add]
      linear_combination -hk
    have h1 := h3 _ hmem
    have h4 := hpow (k + n)
    obtain ⟨p, hp⟩ := Ideal.mem_span_singleton'.1 h1
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.1 h4
    rw [Ideal.mem_span_singleton']
    refine ⟨t ^ (k + n) * p - a * q, ?_⟩
    linear_combination t ^ (k + n) * hp - a * hq

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIndEtaleAlgebraOfStrictlyHenselianEtaleStalkAf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC

theorem isIndEtale_comp_etale {A B O : Type} [CommRing A] [CommRing B] [CommRing O] (φ : A →+* B)
    (hφ : φ.Etale) (g : B →+* O) (hg : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale g) :
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (g.comp φ) := by
  obtain ⟨J, _, _, D, s, t, hs, hj⟩ := hg
  refine ⟨J, inferInstance, inferInstance, D, (Functor.const J).map (CommRingCat.ofHom φ) ≫ s, t, hs,
    fun j => ⟨?_, ?_⟩⟩
  · show RingHom.Etale ((s.app j).hom.comp φ)
    exact RingHom.Etale.stableUnderComposition _ _ hφ (hj j).1
  · have h2 := (hj j).2
    show CommRingCat.ofHom φ ≫ s.app j ≫ t.app j = CommRingCat.ofHom (g.comp φ)
    rw [h2]
    rfl

theorem isStalk_affine : ∀ (A : Type) [CommRing A] (O : Type) [CommRing O]
    (s : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of A)), IsStalk O s →
    ∃ _ : Algebra A O, SH O ∧ IndEt A O ∧ s = Spec.map (CommRingCat.ofHom (algebraMap A O)) := by
  intro A _ O _ s hs
  obtain ⟨hSH, A', _, _, j, hj, hind, rfl⟩ := hs
  set φ := Spec.preimage j with hφdef
  have hjφ : Spec.map φ = j := Spec.map_preimage j
  have hφ : φ.hom.Etale := by
    rw [← hjφ] at hj
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp hj
  letI : Algebra A O := ((algebraMap A' O).comp φ.hom).toAlgebra
  refine ⟨this, hSH, ?_, ?_⟩
  · exact isIndEtale_comp_etale φ.hom hφ (algebraMap A' O) hind
  · rw [← hjφ, ← Spec.map_comp]
    rfl

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictlyHenselianOfIsFieldMonicRoots
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem isField_aic_sh : ∀ (T : Type) [CommRing T], IsField T → AIC T → SH T := by
  intro T _ hF hA
  letI : Field T := hF.toField
  refine ⟨Field.henselian T, ?_⟩
  haveI hT : IsAlgClosed T := by
    refine IsAlgClosed.of_exists_root T ?_
    intro p hm hirr
    obtain ⟨a, ha⟩ := hA p hm (Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible hirr))
    exact ⟨a, by simpa [Polynomial.IsRoot] using ha⟩
  have hinj : Function.Injective (IsLocalRing.residue T) := (IsLocalRing.residue T).injective
  have hbij : Function.Bijective (IsLocalRing.residue T) := ⟨hinj, IsLocalRing.residue_surjective⟩
  haveI : IsAlgClosed (IsLocalRing.ResidueField T) :=
    IsAlgClosed.of_ringEquiv T _ (RingEquiv.ofBijective _ hbij)
  infer_instance

end GlobalTheory.EtC
end

