module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRegular
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PProjIdealFormValue
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace ProjIdealFormValue

theorem weight_blockWeight_apply {K : Type*} [DecidableEq K] {ι : K → Type*} (m : (Σ k, ι k) →₀ ℕ)
    (k : K) : Finsupp.weight (blockWeight ι) m k = Finsupp.mapDomain Sigma.fst m k := by
  rw [Finsupp.weight_apply, Finsupp.mapDomain, Finsupp.sum, Finsupp.sum, Finset.sum_apply,
    Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : v.1 = k
  · simp [blockWeight, h]
  · simp [blockWeight, Ne.symm h]

theorem eval₂_monomial_cone {F Φ : Type*} [CommRing F] [CommRing Φ] (α : F →+* Φ) {K : Type*}
    {ι : K → Type*} (z : (Σ k, ι k) → Φ) (m : (Σ k, ι k) →₀ ℕ) (c : F) :
    eval₂ (C.comp α) (fun p => C (z p) * X p.1) (monomial m c) =
      C (eval₂ α z (monomial m c)) * monomial (Finsupp.mapDomain Sigma.fst m) (1 : Φ) := by
  rw [eval₂_monomial, eval₂_monomial, monomial_eq, C_1, one_mul,
    Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  simp only [mul_pow, Finsupp.prod_mul, map_mul, RingHom.coe_comp, Function.comp_apply,
    map_finsuppProd, map_pow, mul_assoc]

theorem proof : ProjIdealFormValue.Statement := by
  intro F _ Ω _ _ K _ ι y N E _ _ w M φ Φ _ _ t d x hx
  have hx' : IsWeightedHomogeneous (blockWeight (bundleIdx ι M)) x d := hx
  rw [projIdeal, RingHom.mem_ker, coe_eval₂Hom]
  by_cases hx0 : x = 0
  · subst hx0
    simp
  obtain ⟨m₀, hm₀⟩ : x.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty]
    exact hx0
  have hD : ∀ m ∈ x.support, Finsupp.mapDomain Sigma.fst m = Finsupp.mapDomain Sigma.fst m₀ := by
    intro m hm
    ext o
    rw [← weight_blockWeight_apply, ← weight_blockWeight_apply, hx' (mem_support_iff.mp hm),
      hx' (mem_support_iff.mp hm₀)]
  have key : eval₂ (C.comp ((algebraMap Ω Φ).comp (algebraMap F Ω)))
      (fun p => C (projCoord y w φ t p) * X p.1) x =
      C (eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ t) x) *
        monomial (Finsupp.mapDomain Sigma.fst m₀) 1 := by
    conv_lhs => rw [x.as_sum]
    conv_rhs => rw [x.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [eval₂_sum, eval₂_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [eval₂_monomial_cone, hD m hm]
  rw [key, mul_eq_zero, C_eq_zero, monomial_eq_zero]
  simp

end ProjIdealFormValue

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpanBundleDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem SpanBundleDim.proof (h : PointIdealMultiProj.Statement) (hge : SpanBundleTrdegGe.Statement)
    (hle : SpanBundleTrdegLe.Statement) : SpanBundleDim.Statement := by
  intro F _ Ω _ _ K _ _ ι _ y e hy hdim M i G hi hG c a H hc hH hGH Φ _ _ s hs
  have hprime : IsMultiProjPrime (projIdeal F y (Pi.basisFun Ω (Fin i))
      (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s) := by
    let : Algebra F Φ := ((algebraMap Ω Φ).comp (algebraMap F Ω)).toAlgebra
    refine h F Φ (Option K) (bundleIdx ι M) _ ?_
    rintro (_ | k)
    · obtain ⟨l, hl⟩ : ∃ l, G l ⟨0, hi⟩ ≠ 0 := by
        by_contra! h0
        exact hG.ne_zero ⟨0, hi⟩ (funext h0)
      refine ⟨l, fun h0 => hl ?_⟩
      have hsum : ∑ j, G l j • s j = 0 := by
        rw [← h0]
        simp only [projCoord]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [Algebra.smul_def, mul_comm, Matrix.mulVec, dotProduct, Pi.single_apply]
      exact Fintype.linearIndependent_iff.1 hs.linearIndependent _ hsum ⟨0, hi⟩
    · obtain ⟨j, hj⟩ := hy.relevant k
      refine ⟨j, fun h0 => hj ?_⟩
      have hy0 : y ⟨k, j⟩ = 0 := (FaithfulSMul.algebraMap_injective Ω Φ) (by simpa [projCoord] using h0)
      simp [pointIdeal, RingHom.mem_ker, pointConeMap, hy0]
  refine ⟨hprime, ?_⟩
  have := hprime.isPrime
  have := hy.isPrime
  have hty : Algebra.trdeg F (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : Cardinal) := by
    rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F] at hdim
    exact Cardinal.toENat_eq_natCast.1 (WithBot.coe_injective (by simpa using hdim))
  have htz : Algebra.trdeg F (MRing (bundleIdx ι M) F ⧸ projIdeal F y (Pi.basisFun Ω (Fin i))
      (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s) =
      ((e + Fintype.card K + i : ℕ) : Cardinal) := by
    apply le_antisymm
    · simpa [hty] using hle F Ω K ι y M i G c a H hc hH hGH Φ s
    · simpa [hty] using hge F Ω K ι y M i G hG Φ s hs
  apply (FieldNumbers.CutRegular.relDim_eq_natCast_iff _ (e + i - 1)).2
  rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F, htz, Fintype.card_option,
    show e + i - 1 + (Fintype.card K + 1) = e + Fintype.card K + i by omega]
  simp

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpanBundleTrdegGe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

theorem SpanBundleTrdegGe.algebraicIndependent_linComb {Ω Φ : Type*} [Field Ω] [Field Φ] [Algebra Ω Φ]
    {i : ℕ} (s : Fin i → Φ) (hs : AlgebraicIndependent Ω s) (A : Matrix (Fin i) (Fin i) Ω)
    (hA : IsUnit A) : AlgebraicIndependent Ω (fun r => ∑ j, s j * algebraMap Ω Φ (A r j)) := by
  classical
  let L : Matrix (Fin i) (Fin i) Ω → MvPolynomial (Fin i) Ω →ₐ[Ω] MvPolynomial (Fin i) Ω :=
    fun B => aeval fun r => ∑ j, C (B r j) * X j
  have hcomp : ∀ B B', (L B').comp (L B) = L (B * B') := by
    intro B B'
    apply MvPolynomial.algHom_ext
    intro r
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [L, AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq,
      Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  have hid : L 1 = AlgHom.id Ω _ := by
    apply MvPolynomial.algHom_ext
    intro r
    simp [L, Matrix.one_apply]
  have heq : (aeval fun r => ∑ j, s j * algebraMap Ω Φ (A r j)) = (aeval s).comp (L A) := by
    apply MvPolynomial.algHom_ext
    intro r
    simp [L, mul_comm]
  have hAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).1 hA)
  have hinj : Function.Injective (L A) := Function.LeftInverse.injective (g := L A⁻¹) fun p => by
    rw [← AlgHom.comp_apply, hcomp, hAinv, hid, AlgHom.id_apply]
  rw [algebraicIndependent_iff_injective_aeval, heq]
  exact (algebraicIndependent_iff_injective_aeval.1 hs).comp hinj

theorem SpanBundleTrdegGe.injective_aeval_mul_X {Ω Φ : Type*} [Field Ω] [Field Φ] [Algebra Ω Φ] {i : ℕ}
    (σ : Fin i → Φ) (hσ : AlgebraicIndependent Ω σ) :
    Function.Injective (aeval (fun r => Polynomial.C (σ r) * Polynomial.X) :
      MvPolynomial (Fin i) Ω →ₐ[Ω] Polynomial Φ) := by
  let H : MvPolynomial (Fin i) Ω →ₐ[Ω] Polynomial (MvPolynomial (Fin i) Ω) :=
    aeval fun r => Polynomial.C (X r) * Polynomial.X
  have hH : Function.Injective H := by
    have h1 : ((Polynomial.aeval (1 : MvPolynomial (Fin i) Ω)).restrictScalars Ω).comp H =
        AlgHom.id Ω _ := by
      apply MvPolynomial.algHom_ext
      intro r
      simp [H]
    exact Function.LeftInverse.injective (g := (Polynomial.aeval (1 : MvPolynomial (Fin i) Ω)).restrictScalars Ω)
      fun p => by rw [← AlgHom.comp_apply, h1, AlgHom.id_apply]
  have heq : (aeval (fun r => Polynomial.C (σ r) * Polynomial.X) :
      MvPolynomial (Fin i) Ω →ₐ[Ω] Polynomial Φ) = (Polynomial.mapAlgHom (aeval σ)).comp H := by
    apply MvPolynomial.algHom_ext
    intro r
    simp [H]
  rw [heq]
  exact (Polynomial.map_injective _ (algebraicIndependent_iff_injective_aeval.1 hσ)).comp hH

theorem SpanBundleTrdegGe.exists_injective_cone {Ω Φ : Type*} [Field Ω] [Field Φ] [Algebra Ω Φ]
    (K : Type*) {i : ℕ} (σ : Fin i → Φ) (hσ : AlgebraicIndependent Ω σ) :
    ∃ Ψ : MvPolynomial (Fin i) (MvPolynomial K Ω) →+* MvPolynomial (Option K) Φ, Function.Injective Ψ ∧
      (∀ p, Ψ (C p) = rename some (map (algebraMap Ω Φ) p)) ∧ ∀ r, Ψ (X r) = C (σ r) * X none := by
  let θ : MvPolynomial (Fin i) Ω →+* Polynomial Φ :=
    (aeval (fun r => Polynomial.C (σ r) * Polynomial.X) :
      MvPolynomial (Fin i) Ω →ₐ[Ω] Polynomial Φ).toRingHom
  have hθ : Function.Injective θ := SpanBundleTrdegGe.injective_aeval_mul_X σ hσ
  let e := (optionEquivRight Φ K).symm
  have heC : ∀ a : Φ, e (C (Polynomial.C a)) = C a := fun a =>
    (AlgEquiv.symm_apply_eq _).2 (optionEquivRight_C Φ K a).symm
  have heX : ∀ k, e (X k) = X (some k) := fun k =>
    (AlgEquiv.symm_apply_eq _).2 (optionEquivRight_X_some Φ K k).symm
  have heN : e (C Polynomial.X) = X none :=
    (AlgEquiv.symm_apply_eq _).2 (optionEquivRight_X_none Φ K).symm
  refine ⟨e.toRingEquiv.toRingHom.comp ((map θ).comp (commAlgEquiv Ω (Fin i) K).toRingEquiv.toRingHom),
    e.injective.comp ((map_injective θ hθ).comp (commAlgEquiv Ω (Fin i) K).injective), ?_, ?_⟩
  · intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      have h1 : θ (C a) = Polynomial.C (algebraMap Ω Φ a) := by simp [θ]
      simp [h1, heC]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p k hp =>
      rw [C_mul, map_mul, hp, map_mul, map_mul]
      have h2 : (e.toRingEquiv.toRingHom.comp ((map θ).comp (commAlgEquiv Ω (Fin i) K).toRingEquiv.toRingHom))
          (C (X k)) = X (some k) := by
        simp [heX]
      rw [h2, map_X, rename_X]
  · intro r
    have h3 : θ (X r) = Polynomial.C (σ r) * Polynomial.X := by simp [θ]
    have h4 : e (C (Polynomial.C (σ r) * Polynomial.X)) = C (σ r) * X none := by
      rw [C_mul, map_mul, heC, heN]
    simp [h3, heC, heN]

theorem SpanBundleTrdegGe.proof : SpanBundleTrdegGe.Statement := by
  intro F _ Ω _ _ K ι y M i G hG Φ _ _ s hs
  classical
  let : Algebra F Φ := ((algebraMap Ω Φ).comp (algebraMap F Ω)).toAlgebra
  have : IsScalarTower F Ω Φ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  set z := projCoord y (Pi.basisFun Ω (Fin i))
    (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s with hz
  change Algebra.trdeg F (MRing ι F ⧸ pointIdeal F y) + i ≤
    Algebra.trdeg F (MRing (bundleIdx ι M) F ⧸ pointIdeal F z)
  have hzn : ∀ m, z ⟨none, m⟩ = ∑ j, s j * algebraMap Ω Φ (G m j) := by
    intro m
    simp [hz, projCoord, Matrix.col]
    rfl
  have hzs : ∀ k (q : ι k), z ⟨some k, q⟩ = algebraMap Ω Φ (y ⟨k, q⟩) := fun _ _ => rfl

  obtain ⟨l, hl⟩ : ∃ l : Fin i → Fin M, IsUnit (Matrix.of fun r j => G (l r) j) := by
    have hrk : (Matrix.of G).rank = i := by
      rw [← Matrix.rank_transpose]
      simpa using LinearIndependent.rank_matrix (M := Matrix.transpose (Matrix.of G)) hG
    obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' Ω (Matrix.of G).row
    have : Finite κ := hli.finite
    let : Fintype κ := Fintype.ofFinite κ
    have hcard : Fintype.card κ = i := by
      rw [← finrank_span_eq_card hli, hsp, ← Matrix.rank_eq_finrank_span_row, hrk]
    let e : Fin i ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
    refine ⟨a ∘ e, Matrix.linearIndependent_rows_iff_isUnit.1 ?_⟩
    exact hli.comp e e.injective
  set σ : Fin i → Φ := fun r => ∑ j, s j * algebraMap Ω Φ (G (l r) j) with hσdef
  have hσ : AlgebraicIndependent Ω σ :=
    SpanBundleTrdegGe.algebraicIndependent_linComb s hs _ hl

  have : (pointIdeal F y).IsPrime := RingHom.ker_isPrime _
  have : (pointIdeal F z).IsPrime := RingHom.ker_isPrime _
  set Ay := MRing ι F ⧸ pointIdeal F y
  set Az := MRing (bundleIdx ι M) F ⧸ pointIdeal F z
  let qy : Ay →ₐ[F] MvPolynomial K Ω := Ideal.kerLiftAlg (pointConeMap F y)
  have hqy : Function.Injective qy := Ideal.kerLiftAlg_injective _
  let qz : Az →ₐ[F] MvPolynomial (Option K) Φ := Ideal.kerLiftAlg (pointConeMap F z)
  let emb : MvPolynomial K Ω →+* MvPolynomial (Option K) Φ :=
    (rename (R := Φ) some).toRingHom.comp (map (algebraMap Ω Φ))
  let σ' : (Σ k, ι k) → (Σ o, bundleIdx ι M o) := fun p => ⟨some p.1, p.2⟩
  have hE1 : ∀ g : MRing ι F, pointConeMap F z (rename σ' g) = emb (pointConeMap F y g) := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp [pointConeMap, emb, MvPolynomial.algebraMap_eq, RingHom.algebraMap_toAlgebra]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p q hp =>
      simp only [map_mul, hp, rename_X]
      simp [pointConeMap, emb, σ', hzs]
  have hle : pointIdeal F y ≤ (pointIdeal F z).comap (rename σ' : MRing ι F →ₐ[F] _) := by
    intro g hg
    simp only [Ideal.mem_comap, pointIdeal, RingHom.mem_ker] at hg ⊢
    rw [hE1, hg, map_zero]
  let fy : Ay →ₐ[F] Az := Ideal.quotientMapₐ (pointIdeal F z) (rename σ') hle
  let Θ : MvPolynomial (Fin i) Ay →ₐ[F] Az :=
    aevalTower fy fun r => Ideal.Quotient.mk _ (X ⟨none, l r⟩)

  obtain ⟨Ψ, hΨ, hΨC, hΨX⟩ := SpanBundleTrdegGe.exists_injective_cone K σ hσ
  have key : ∀ a, qz (Θ a) = Ψ (map qy.toRingHom a) := by
    intro a
    induction a using MvPolynomial.induction_on with
    | C c =>
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective c
      simp only [Θ, aevalTower_C, map_C]
      rw [hΨC]
      change qz (Ideal.Quotient.mk _ (rename σ' g)) = emb (qy (Ideal.Quotient.mk _ g))
      simp only [qz, qy]
      exact hE1 g
    | add p q hp hq =>
      rw [map_add Θ, map_add qz, (map qy.toRingHom : MvPolynomial (Fin i) Ay →+* _).map_add, map_add Ψ, hp, hq]
    | mul_X p r hp =>
      simp only [map_mul, hp, map_X, hΨX]
      congr 1
      simp only [Θ, aevalTower_X]
      refine (Ideal.kerLiftAlg_mk (pointConeMap F z) _).trans ?_
      simp only [pointConeMap, aeval_X]
      exact congrArg (fun a => C a * X none) (hzn (l r))
  have hΘ : Function.Injective Θ := by
    intro a b hab
    apply map_injective qy.toRingHom hqy
    apply hΨ
    rw [← key, ← key, hab]

  have : FaithfulSMul F Ay :=
    (faithfulSMul_iff_algebraMap_injective F Ay).2 (algebraMap F Ay).injective
  have : FaithfulSMul Ay (MvPolynomial (Fin i) Ay) :=
    (faithfulSMul_iff_algebraMap_injective Ay _).2 (C_injective _ _)
  have e1 := trdeg_add_eq F Ay (A := MvPolynomial (Fin i) Ay)
  rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fin] at e1
  rw [e1]
  exact trdeg_le_of_injective Θ hΘ

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTruncSpecialize
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section Ring

variable {K : Type*} {ι : K → Type} {Ω : Type*} [Field Ω] {N M : ℕ} {E : Type*} [AddCommGroup E]
  [Module Ω E]

def projCoordRing {B : Type*} [CommRing B] [Algebra Ω B] (y : (Σ k, ι k) → Ω)
    (w : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E) (u : Fin N → B) :
    (Σ o, bundleIdx ι M o) → B
  | ⟨none, l⟩ => ∑ i, u i * algebraMap Ω B (φ l (w i))
  | ⟨some k, i⟩ => algebraMap Ω B (y ⟨k, i⟩)

theorem projCoordRing_map {B B' : Type*} [CommRing B] [Algebra Ω B] [CommRing B'] [Algebra Ω B']
    (g : B →ₐ[Ω] B') (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (u : Fin N → B) (p : Σ o, bundleIdx ι M o) :
    g (projCoordRing y w φ u p) = projCoordRing y w φ (g ∘ u) p := by
  rcases p with ⟨_ | k, l⟩ <;> simp [projCoordRing, map_sum]

theorem projCoord_eq_projCoordRing {Φ : Type*} [Field Φ] [Algebra Ω Φ] (y : (Σ k, ι k) → Ω)
    (w : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) :
    projCoord y w φ t = projCoordRing y w φ t := by
  funext p
  rcases p with ⟨_ | k, l⟩ <;> rfl

end Ring

theorem map_coneMap {σ τ R B B' : Type*} [CommRing R] [CommRing B] [CommRing B'] (f : R →+* B)
    (g : B →+* B') (c : σ → B) (q : σ → τ) (x : MvPolynomial σ R) :
    map g (eval₂ (C.comp f) (fun p => C (c p) * X (q p)) x) =
      eval₂ (C.comp (g.comp f)) (fun p => C (g (c p)) * X (q p)) x := by
  rw [eval₂_comp_left]
  congr 1
  · exact RingHom.ext fun a => by simp
  · funext p
    simp

theorem TruncSpecialize.proof : TruncSpecialize.Statement := by
  intro F _ Ω _ _ K ι y N E _ _ w M φ Φ _ _ t ht i
  let ev : MvPolynomial (Fin N) Ω →ₐ[Ω] Φ := aeval t
  have hev : Function.Injective ev := ht
  let sub : MvPolynomial (Fin N) Ω →ₐ[Ω] MvPolynomial (Fin N) Ω := aeval fun k => if k = i then 0 else X k
  have hevT : ∀ j : ℕ, ev ∘ truncCoord (X : Fin N → MvPolynomial (Fin N) Ω) j = truncCoord t j := by
    intro j
    funext k
    by_cases hk : (k : ℕ) < j <;> simp [truncCoord, hk, ev]
  have hsubT : sub ∘ truncCoord (X : Fin N → MvPolynomial (Fin N) Ω) ((i : ℕ) + 1) = truncCoord X i := by
    funext k
    simp only [Function.comp_apply, truncCoord]
    rcases lt_trichotomy (k : ℕ) i with h | h | h
    · have hki : k ≠ i := fun e => by subst e; exact lt_irrefl _ h
      simp [h, Nat.lt_succ_of_lt h, sub, hki]
    · have hki : k = i := Fin.ext h
      subst hki
      simp [sub]
    · have h1 : ¬ (k : ℕ) < i + 1 := by omega
      have h2 : ¬ (k : ℕ) < i := by omega
      simp [h1, h2]
  let cA : ℕ → (Σ o, bundleIdx ι M o) → MvPolynomial (Fin N) Ω :=
    fun j => projCoordRing y w φ (truncCoord X j)
  have hcoord : ∀ j : ℕ, projCoord y w φ (truncCoord t j) = fun p => ev (cA j p) := by
    intro j
    funext p
    rw [projCoord_eq_projCoordRing, ← hevT, projCoordRing_map]
  have hsubc : ∀ p, sub (cA ((i : ℕ) + 1) p) = cA i p := by
    intro p
    simp only [cA]
    rw [projCoordRing_map, hsubT]
  let algA : F →+* MvPolynomial (Fin N) Ω := (algebraMap Ω (MvPolynomial (Fin N) Ω)).comp (algebraMap F Ω)
  have hevA : (ev : MvPolynomial (Fin N) Ω →+* Φ).comp algA = (algebraMap Ω Φ).comp (algebraMap F Ω) :=
    RingHom.ext fun a => by simp [algA]
  have hsubA : (sub : MvPolynomial (Fin N) Ω →+* MvPolynomial (Fin N) Ω).comp algA = algA :=
    RingHom.ext fun a => by simp [algA]
  refine ⟨fun x hx => ?_, fun x z hxz => ?_⟩
  · have key : ∀ j : ℕ, eval₂Hom (C.comp ((algebraMap Ω Φ).comp (algebraMap F Ω)))
        (fun p => C (projCoord y w φ (truncCoord t j) p) * X p.1) x =
        map (ev : MvPolynomial (Fin N) Ω →+* Φ) (eval₂ (C.comp algA) (fun p => C (cA j p) * X p.1) x) := by
      intro j
      rw [map_coneMap, hevA, hcoord]
      rfl
    have ksub : map (sub : MvPolynomial (Fin N) Ω →+* MvPolynomial (Fin N) Ω)
        (eval₂ (C.comp algA) (fun p => C (cA ((i : ℕ) + 1) p) * X p.1) x) =
        eval₂ (C.comp algA) (fun p => C (cA i p) * X p.1) x := by
      rw [map_coneMap, hsubA]
      simp only [AlgHom.coe_toRingHom, hsubc]
    simp only [projIdeal, RingHom.mem_ker] at hx ⊢
    rw [key] at hx ⊢
    have h0 : eval₂ (C.comp algA) (fun p => C (cA ((i : ℕ) + 1) p) * X p.1) x = 0 :=
      map_injective _ hev (hx.trans (map_zero _).symm)
    rw [← ksub, h0, map_zero, map_zero]
  · have val : ∀ (j : ℕ) (v : MRing (bundleIdx ι M) F),
        eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t j)) v =
          ev (eval₂ algA (cA j) v) := by
      intro j v
      rw [← AlgHom.coe_toRingHom, eval₂_comp_left, hevA, hcoord]
      rfl
    have vsub : ∀ v : MRing (bundleIdx ι M) F,
        sub (eval₂ algA (cA ((i : ℕ) + 1)) v) = eval₂ algA (cA i) v := by
      intro v
      rw [← AlgHom.coe_toRingHom, eval₂_comp_left, hsubA]
      congr 1
      funext p
      exact hsubc p
    rw [val, val] at hxz
    have hx' : eval₂ algA (cA ((i : ℕ) + 1)) x = X i * eval₂ algA (cA ((i : ℕ) + 1)) z :=
      hev (by rw [hxz, map_mul]; simp [ev])
    rw [val, ← vsub, hx', map_mul]
    simp [sub]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsGenericProjClosureDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def GenericProjClosureDim.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ), 0 < N → ∀ (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
      IsModelOver (pointIdeal O (pairProjCoord y e φ φ' t)) (d + (N - 1))

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

