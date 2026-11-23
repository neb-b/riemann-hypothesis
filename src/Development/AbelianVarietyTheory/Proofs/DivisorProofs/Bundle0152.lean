module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0062
public import Formalism.DegreeFormula.FlagDegFormula
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianUnitaryGroupOneParameterChart
section
open Matrix
open scoped Topology

noncomputable section

namespace GlobalTheory.UnitaryGroupChart

open Filter

theorem chart_general {E : Type} [NormedRing E] [NormedAlgebra ℝ E] [FiniteDimensional ℝ E]
    (σ : E →ₗ[ℝ] E) (hσ : ∀ a, σ (σ a) = a) (hm : ∀ a b, σ (a * b) = σ b * σ a) (h1 : σ 1 = 1)
    {d e : ℕ} (Z : Fin d → E) (j : Fin e → Fin d) (hZσ : ∀ a, σ (Z a) = -Z a)
    (hli : LinearIndependent ℝ (fun i => Z (j i)))
    (hsp : ∀ X, σ X = -X → X ∈ Submodule.span ℝ (Set.range fun i => Z (j i))) :
    ∃ s : E → (Fin d → ℝ), ContinuousAt s 1 ∧
      ∀ᶠ g in 𝓝 (1 : E), σ g * g = 1 →
        g = (List.ofFn fun a => NormedSpace.exp (s g a • Z a)).prod := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : NormedAlgebra ℚ E := NormedAlgebra.restrictScalars ℚ ℝ E
  have hexp : ∀ a, σ (NormedSpace.exp a) = NormedSpace.exp (σ a) := fun a => by
    have hp : ∀ m : ℕ, σ (a ^ m) = σ a ^ m := fun m => by
      induction m with
      | zero => simpa using h1
      | succ m ih => rw [pow_succ, hm, ih, pow_succ']
    have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a).map σ.toAddMonoidHom
      σ.continuous_of_finiteDimensional
    refine h2.unique ?_
    convert NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (σ a) using 1
    funext m
    simp [hp]
  let cL : (Fin e → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
    Fintype.linearCombination ℝ (fun i => Pi.single (j i) (1 : ℝ))
  let cC : (Fin e → ℝ) →L[ℝ] (Fin d → ℝ) := LinearMap.toContinuousLinearMap cL
  have hcC : ∀ t, cC t = cL t := fun _ => rfl
  have hsum : ∀ t : Fin e → ℝ, ∑ a, cL t a • Z a = ∑ i, t i • Z (j i) := fun t => by
    simp only [cL, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [ite_smul]
  set Θ : (Fin e → ℝ) → E :=
    fun t => (List.ofFn fun a => NormedSpace.exp (cL t a • Z a)).prod with hΘ
  have hU : ∀ t, σ (Θ t) * Θ t = 1 ∧ Θ t * σ (Θ t) = 1 := fun t =>
    GlobalTheory.UnitaryChart.unitary_list_prod σ hm h1 _ (fun u hu => by
      obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hu
      rw [hexp, map_smul, hZσ, smul_neg, ← NormedSpace.exp_add_of_commute (Commute.refl _).neg_left,
        ← NormedSpace.exp_add_of_commute (Commute.refl _).neg_right]
      simp)
  let T : (Fin e → ℝ) →L[ℝ] E :=
    ∑ a, (ContinuousLinearMap.toSpanSingleton ℝ (Z a)).comp ((ContinuousLinearMap.proj a).comp cC)
  have hT : ∀ t, T t = ∑ i, t i • Z (j i) := fun t => by
    rw [← hsum]
    simp [T, hcC]
  obtain ⟨h0, hD⟩ : Θ 0 = 1 ∧ HasStrictFDerivAt Θ T 0 :=
    GlobalTheory.UnitaryChart.hasStrictFDerivAt_ofFn_prod d
      (fun a (t : Fin e → ℝ) => NormedSpace.exp (cL t a • Z a)) _ (fun a => by
        refine ⟨by simp, ?_⟩
        have hd : HasStrictFDerivAt (fun s : ℝ => NormedSpace.exp (s • Z a))
            (ContinuousLinearMap.toSpanSingleton ℝ (Z a))
            (((ContinuousLinearMap.proj a).comp cC) 0) := by
          rw [map_zero]
          simpa using (hasStrictDerivAt_exp_smul_const (𝕂 := ℝ) (Z a) (0 : ℝ)).hasStrictFDerivAt
        exact hd.comp (0 : Fin e → ℝ) ((ContinuousLinearMap.proj a).comp cC).hasStrictFDerivAt)
  obtain ⟨P, hP1, hP2, hP3⟩ := GlobalTheory.UnitaryChart.exists_skew_coord σ (fun i => Z (j i)) hσ hli
    (fun i => hZσ (j i)) hsp
  have hΨ : HasStrictFDerivAt (fun t => P (Θ t))
      ((ContinuousLinearEquiv.refl ℝ (Fin e → ℝ) : (Fin e → ℝ) →L[ℝ] (Fin e → ℝ))) 0 := by
    refine (P.hasStrictFDerivAt.comp 0 hD).congr_fderiv ?_
    ext1 t
    simp [hT, hP1]
  have hP0 : P 1 = 0 := hP2 _ h1
  have hΨ0 : P (Θ 0) = 0 := by rw [h0, hP0]
  have p1 := hΨ.localInverse_continuousAt
  have p2 := hΨ.localInverse_apply_image
  have p3 := hΨ.eventually_right_inverse
  simp only [hΨ0] at p1 p2 p3
  set Ψ := hΨ.localInverse _ _ _
  have hσc : Continuous σ := σ.continuous_of_finiteDimensional
  have hnear : ∀ᶠ m in 𝓝 (1 : E), ‖1 - σ m‖ ≤ 1 / 2 := by
    have : ContinuousAt (fun m => ‖1 - σ m‖) 1 := (continuous_const.sub hσc).norm.continuousAt
    exact this.eventually_le_const (by simp [h1])
  have hPt : Tendsto P (𝓝 1) (𝓝 0) := hP0 ▸ P.continuous.tendsto 1
  have hcont : ContinuousAt (fun g => Ψ (P g)) 1 :=
    ContinuousAt.comp_of_eq p1 P.continuous.continuousAt hP0
  have ht : Tendsto (fun g => Θ (Ψ (P g))) (𝓝 1) (𝓝 1) := by
    have h3 : Tendsto (fun g => Ψ (P g)) (𝓝 1) (𝓝 0) := by
      have := hcont.tendsto
      simp only [hP0, p2] at this
      exact this
    have := hD.continuousAt.tendsto.comp h3
    rwa [h0] at this
  refine ⟨fun g => cL (Ψ (P g)), cC.continuous.continuousAt.comp hcont, ?_⟩
  filter_upwards [hPt.eventually p3, hnear, ht.eventually hnear] with g q1 q2 q3 hg1
  haveI : IsArtinianRing E := IsArtinianRing.of_finite ℝ E
  exact (GlobalTheory.UnitaryChart.eq_of_skew_eq (hU _).1 (mul_eq_one_comm.1 hg1) (hP3 _ _ q1) q3 q2).symm

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem chart_matrix (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hdet : IsUnit H.det)
    (d e : ℕ) (Z : Fin d → Matrix (Fin n) (Fin n) ℂ) (j : Fin e → Fin d)
    (hZ : ∀ a, (Z a)ᴴ * H + H * Z a = 0) (hli : LinearIndependent ℝ (fun i => Z (j i)))
    (hsp : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * H + H * X = 0 →
      X ∈ Submodule.span ℝ (Set.range fun i => Z (j i))) :
    ∃ s : Matrix (Fin n) (Fin n) ℂ → (Fin d → ℝ), ContinuousAt s 1 ∧
      ∀ᶠ g in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), gᴴ * H * g = H →
        g = (List.ofFn fun a => NormedSpace.exp (s g a • Z a)).prod := by
  have hHi : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H hdet
  have hHi' : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H hdet
  have hHih : (H⁻¹)ᴴ = H⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hH]
  let σ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun x => H⁻¹ * xᴴ * H
      map_add' := fun x y => by rw [conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c x => by simp [conjTranspose_smul] }
  have hs : ∀ x, σ x = H⁻¹ * xᴴ * H := fun _ => rfl
  have hσ : ∀ a, σ (σ a) = a := fun a => by
    simp only [hs, conjTranspose_mul, conjTranspose_conjTranspose, hH, hHih, Matrix.mul_assoc]
    rw [hHi, Matrix.mul_one, ← Matrix.mul_assoc, hHi, Matrix.one_mul]
  have hm : ∀ a b, σ (a * b) = σ b * σ a := fun a b => by
    simp only [hs, conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc H, hHi', Matrix.one_mul]
  have h1 : σ 1 = 1 := by simp [hs, hHi]
  have hZσ : ∀ a, σ (Z a) = -Z a := fun a => by
    rw [hs, Matrix.mul_assoc, eq_neg_of_add_eq_zero_left (hZ a), Matrix.mul_neg, ← Matrix.mul_assoc,
      hHi, Matrix.one_mul]
  have hsp' : ∀ X, σ X = -X → X ∈ Submodule.span ℝ (Set.range fun i => Z (j i)) := fun X hX => by
    apply hsp
    have h2 : H * σ X = Xᴴ * H := by
      rw [hs, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hHi', Matrix.one_mul]
    rw [← h2, hX, Matrix.mul_neg, neg_add_cancel]
  obtain ⟨s, hs1, hs2⟩ := chart_general σ hσ hm h1 Z j hZσ hli hsp'
  refine ⟨s, hs1, ?_⟩
  filter_upwards [hs2] with g hg hgu
  apply hg
  simp only [Matrix.mul_assoc] at hgu
  rw [hs, Matrix.mul_assoc, Matrix.mul_assoc, hgu, hHi]

end

theorem unitary_chart : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ), Hᴴ = H → IsUnit H.det →
    ∀ (d e : ℕ) (Z : Fin d → Matrix (Fin n) (Fin n) ℂ) (j : Fin e → Fin d), Function.Injective j →
      (∀ a, a ∉ Set.range j → Z a = 0) → (∀ a, (Z a)ᴴ * H + H * Z a = 0) →
      LinearIndependent ℝ (fun i => Z (j i)) →
      (∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * H + H * X = 0 → X ∈ Submodule.span ℝ (Set.range fun i => Z (j i))) →
      ∃ V ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), ∃ s : Matrix (Fin n) (Fin n) ℂ → (Fin d → ℝ), ContinuousAt s 1 ∧
        ∀ g ∈ V, gᴴ * H * g = H → g = (List.ofFn fun a => NormedSpace.exp (s g a • Z a)).prod := by
  intro n H hH hdet d e Z j _ _ hZ hli hsp
  obtain ⟨s, hs1, hs2⟩ := chart_matrix n H hH hdet d e Z j hZ hli hsp
  exact ⟨_, hs2, s, hs1, fun g hg => hg⟩

end GlobalTheory.UnitaryGroupChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomExtSpecProdSelfOfBasicOpenPreimageEq
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.AlgConn

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AlgConn

theorem hom_eq_toSpecΓ_comp {T : Scheme.{0}} {A : CommRingCat.{0}} (h : T ⟶ Spec A) :
    h = T.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso A).inv ≫ h.appTop) := by
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem hom_ext_of_twoπ_of_basicOpen : ∀ (O : Type) [CommRing O] (T : Scheme.{0})
    (h h' : T ⟶ Spec (.of (O × O))), h ≫ twoπ O = h' ≫ twoπ O →
    h ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) = h' ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) →
    h = h' := by
  intro O _ T h h' hπ hb
  rw [hom_eq_toSpecΓ_comp h, hom_eq_toSpecΓ_comp h']
  congr 2

  have h1 : ∀ a : O, ((Scheme.ΓSpecIso (.of (O × O))).inv ≫ h.appTop).hom (algebraMap O (O × O) a) =
      ((Scheme.ΓSpecIso (.of (O × O))).inv ≫ h'.appTop).hom (algebraMap O (O × O) a) := by
    intro a
    have key : ∀ g : T ⟶ Spec (.of (O × O)),
        ((Scheme.ΓSpecIso (.of (O × O))).inv ≫ g.appTop).hom (algebraMap O (O × O) a) =
          ((Scheme.ΓSpecIso (.of O)).inv ≫ (g ≫ twoπ O).appTop).hom a := by
      intro g
      rw [Scheme.Hom.comp_appTop, ← Category.assoc]
      have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap O (O × O)))
      have n' : CommRingCat.ofHom (algebraMap O (O × O)) ≫ (Scheme.ΓSpecIso (.of (O × O))).inv =
          (Scheme.ΓSpecIso (.of O)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap O (O × O)))).appTop := by
        rw [Iso.eq_inv_comp, ← Category.assoc, ← n, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rw [← n']
      rfl
    rw [key h, key h', hπ]

  have h2 : ((Scheme.ΓSpecIso (.of (O × O))).inv ≫ h.appTop).hom ((1, 0) : O × O) =
      ((Scheme.ΓSpecIso (.of (O × O))).inv ≫ h'.appTop).hom ((1, 0) : O × O) := by
    change h.appTop (fst1 O) = h'.appTop (fst1 O)
    have hid : fst1 O * fst1 O = fst1 O := by
      rw [fst1, ← map_mul]; congr 1; ext <;> simp
    apply GlobalTheory.idempotent_eq_of_basicOpen_eq T
    · rw [← map_mul, hid]
    · rw [← map_mul, hid]
    · rw [← Scheme.preimage_basicOpen_top, ← Scheme.preimage_basicOpen_top, hb]

  ext1
  ext x
  obtain ⟨a, b⟩ := x
  have hx : ((a, b) : O × O) = algebraMap O (O × O) a * (1, 0) + algebraMap O (O × O) b * (1 - (1, 0)) := by
    ext <;> simp
  rw [hx, map_add (f := _), map_mul, map_mul, map_sub, map_one, map_add (f := _), map_mul, map_mul, map_sub, map_one, h1 a, h1 b, h2]

end GlobalTheory.AlgConn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousMemSpanLinearRoots
section
open MvPolynomial

namespace GlobalTheory

namespace PowLinSpan

variable {σ : Type} [Fintype σ] [DecidableEq σ]

theorem sum_C_mul_X_pow (u : σ → ℝ) (d : ℕ) :
    (∑ x, C (u x) * X x : MvPolynomial σ ℝ) ^ d =
      ∑ k ∈ Finset.piAntidiag Finset.univ d,
        ((Nat.multinomial Finset.univ k : ℝ) * ∏ x, u x ^ k x) •
          monomial (Finsupp.equivFunOnFinite.symm k) (1 : ℝ) := by
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_eq_C_mul, monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod, map_mul, map_natCast, C_1, one_mul,
    Finsupp.coe_equivFunOnFinite_symm]
  ring

noncomputable def polOf (φ : Module.Dual ℝ (MvPolynomial σ ℝ)) (d : ℕ) : MvPolynomial σ ℝ :=
  ∑ k ∈ Finset.piAntidiag Finset.univ d,
    monomial (Finsupp.equivFunOnFinite.symm k)
      ((Nat.multinomial Finset.univ k : ℝ) * φ (monomial (Finsupp.equivFunOnFinite.symm k) 1))

theorem eval_polOf (φ : Module.Dual ℝ (MvPolynomial σ ℝ)) (d : ℕ) (u : σ → ℝ) :
    eval u (polOf φ d) = φ ((∑ x, C (u x) * X x) ^ d) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [sum_C_mul_X_pow, map_sum, polOf, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, eval_monomial, smul_eq_mul, Finsupp.prod_fintype _ _ (by simp)]
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  ring

theorem coeff_polOf (φ : Module.Dual ℝ (MvPolynomial σ ℝ)) (d : ℕ) (m : σ →₀ ℕ) (hm : ∑ x, m x = d) :
    AddMonoidAlgebra.coeff (polOf φ d) m = (Nat.multinomial Finset.univ m : ℝ) * φ (monomial m 1) := by
  rw [polOf, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_eq_single (⇑m)]
  · simp
  · intro k _ hk
    rw [if_neg]
    intro h
    apply hk
    rw [← h]
    simp
  · intro h
    exfalso
    apply h
    rw [Finset.mem_piAntidiag]
    simp [hm]

theorem degreeOf_polOf_le (φ : Module.Dual ℝ (MvPolynomial σ ℝ)) (d : ℕ) (x : σ) :
    (polOf φ d).degreeOf x ≤ d := by
  refine (degreeOf_le_totalDegree _ _).trans ?_
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun k hk => ?_)
  refine (totalDegree_monomial_le _ _).trans ?_
  rw [Finset.mem_piAntidiag] at hk
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simpa [Finsupp.coe_equivFunOnFinite_symm] using hk.1.le

theorem monomial_kill (φ : Module.Dual ℝ (MvPolynomial σ ℝ)) (d : ℕ) (hP : polOf φ d = 0)
    (m : σ →₀ ℕ) (hm : ∑ x, m x = d) : φ (monomial m 1) = 0 := by
  have h := coeff_polOf φ d m hm
  rw [hP, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h
  have hne : (Nat.multinomial Finset.univ m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.multinomial_pos _ _).ne'
  rcases mul_eq_zero.mp h.symm with h1 | h1
  · exact absurd h1 hne
  · exact h1

theorem homog_kill (φ : Module.Dual ℝ (MvPolynomial σ ℝ)) (d : ℕ) (hP : polOf φ d = 0)
    (Q : MvPolynomial σ ℝ) (hQ : Q.IsHomogeneous d) : φ Q = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Q.as_sum, map_sum]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hdeg : ∑ x, m x = d := by
    have := hQ (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  have : monomial m (AddMonoidAlgebra.coeff Q m) = AddMonoidAlgebra.coeff Q m • monomial m (1 : ℝ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this, map_smul, monomial_kill φ d hP m hdeg, smul_zero]

end PowLinSpan
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafComapIdealAffineOpenOfIsAffine
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory

theorem IdealSheafData.ideal_comap_affineOpen_of_isAffine {X Y : Scheme.{0}} [IsAffine Y]
    (f : X ⟶ Y) (K : Y.IdealSheafData) (W : X.affineOpens) :
    (K.comap f).ideal W = Ideal.map (f.appLE ⊤ W (by simp)).hom (K.ideal ⟨⊤, isAffineOpen_top Y⟩) := by
  haveI : IsAffine (W.1 : Scheme) := W.2
  have h1 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion (K.comap f) W.1.ι
    ⟨⊤, isAffineOpen_top _⟩
  rw [← Scheme.IdealSheafData.comap_comp, IdealSheafData.ideal_comap_top_of_isAffine] at h1
  have hc : (W.1.ι ≫ f).appTop ≫ (W.1.ι.appIso ⊤).inv = f.appLE ⊤ (W.1.ι ''ᵁ ⊤) (by simp) := by
    simp [Scheme.Hom.appLE]; exact Category.comp_id _
  have hs : Function.Surjective (W.1.ι.appIso ⊤).inv.hom :=
    (W.1.ι.appIso ⊤).commRingCatIsoToRingEquiv.symm.surjective
  have h2 : (K.comap f).ideal ⟨W.1.ι ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion W.1.ι⟩ =
      Ideal.map (f.appLE ⊤ (Subtype.val (⟨W.1.ι ''ᵁ ⊤,
        (isAffineOpen_top _).image_of_isOpenImmersion W.1.ι⟩ : X.affineOpens)) (by simp)).hom
        (K.ideal ⟨⊤, isAffineOpen_top Y⟩) := by
    rw [← hc, CommRingCat.hom_comp, ← Ideal.map_map, h1, Ideal.map_comap_of_surjective _ hs]
  have hW : (⟨W.1.ι ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion W.1.ι⟩ : X.affineOpens) = W :=
    Subtype.ext (by simp)
  have key : ∀ V : X.affineOpens, V = W →
      (K.comap f).ideal V = Ideal.map (f.appLE ⊤ V.1 (fun _ _ => trivial)).hom
        (K.ideal ⟨⊤, isAffineOpen_top Y⟩) →
      (K.comap f).ideal W = Ideal.map (f.appLE ⊤ W (fun _ _ => trivial)).hom
        (K.ideal ⟨⊤, isAffineOpen_top Y⟩) := by
    rintro V rfl h; exact h
  exact key _ hW h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafDataExtOfOpenCover
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u

namespace GlobalTheory.HilbAff

theorem idealSheafData_ext_of_openCover {X : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0})
    (f : ∀ i, V i ⟶ X) (hf : ∀ i, IsOpenImmersion (f i)) (hcov : ∀ x : X, ∃ i y, f i y = x)
    (I I' : X.IdealSheafData) (h : ∀ i, I.comap (f i) = I'.comap (f i)) : I = I' := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (ι := Σ i, (V i).affineOpens)
    (fun p => ⟨(f p.1) ''ᵁ p.2.1, p.2.2.image_of_isOpenImmersion (f p.1)⟩) ?_ ?_
  · refine top_le_iff.mp fun x _ => ?_
    obtain ⟨i, y, rfl⟩ := hcov x
    have hy : y ∈ (⊤ : (V i).Opens) := trivial
    rw [← iSup_affineOpens_eq_top (V i)] at hy
    obtain ⟨W, hW⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, W⟩, ⟨y, hW, rfl⟩⟩
  · rintro ⟨i, W⟩
    have e := congrArg (fun J => J.ideal W) (h i)
    simp only [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at e
    exact Ideal.comap_injective_of_surjective _
      ((ConcreteCategory.bijective_of_isIso ((f i).appIso W).inv).2) e

end GlobalTheory.HilbAff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafGlueOfOpenImmersionsStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idealSheafData_glue_of_openImmersions : (∀ {X : Scheme.{0}} (𝒜 : Set X.affineOpens), (∀ W ∈ 𝒜, ∀ W' : X.affineOpens, W' ≤ W → W' ∈ 𝒜) → (∀ x : X, ∃ W ∈ 𝒜, x ∈ W.1) → ∀ (k : ∀ W : X.affineOpens, Ideal Γ(X, W)), (∀ W ∈ 𝒜, ∀ (W' : X.affineOpens) (h : W' ≤ W), (k W).map (X.presheaf.map (homOfLE h).op).hom = k W') → ∃ I : X.IdealSheafData, ∀ W ∈ 𝒜, I.ideal W = k W) → ∀ {X : Scheme.{0}} {ι : Type*} (P : ι → Scheme.{0}) (e : ∀ i, P i ⟶ X), (∀ i, IsOpenImmersion (e i)) → (∀ x : X, ∃ i, x ∈ Set.range (e i)) → ∀ (K : ∀ i, (P i).IdealSheafData), (∀ i j (Q : Scheme.{0}) (a : Q ⟶ P i) (b : Q ⟶ P j), a ≫ e i = b ≫ e j → (K i).comap a = (K j).comap b) → ∃ I : X.IdealSheafData, ∀ i, I.comap (e i) = K i := by
  first | (exact @GlobalTheory.IdealGlue.idealSheaf_glue_of_openImmersions) | (exact GlobalTheory.IdealGlue.idealSheaf_glue_of_openImmersions) | (intros; apply GlobalTheory.IdealGlue.idealSheaf_glue_of_openImmersions  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentTensorEqZeroOrOneOfIsPurelyInseparable
section
open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory

theorem pow_mem_range_includeRight_of_isPurelyInseparable (k K B : Type) [Field k] [Field K]
    [Algebra k K] [IsPurelyInseparable k K] [CommRing B] [Nontrivial B] [Algebra k B]
    (q : ℕ) [ExpChar k q] (z : K ⊗[k] B) :
    ∃ n : ℕ, z ^ q ^ n ∈
      (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B).range := by
  first
  | exact @_root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight
  | exact _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight
  | (apply _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight ..)

theorem idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable (k K B : Type) [Field k] [Field K]
    [Algebra k K] [IsPurelyInseparable k K] [CommRing B] [IsLocalRing B] [Algebra k B]
    (e : K ⊗[k] B) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hinj : Function.Injective (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap k K).injective
  obtain ⟨n, b, hb⟩ :=
    pow_mem_range_includeRight_of_isPurelyInseparable k K B (ringExpChar k) e
  have hpos : ringExpChar k ^ n ≠ 0 := (pow_pos (expChar_pos k _) n).ne'
  have h1 : e ^ (ringExpChar k ^ n) = e := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos
    rw [hm]; exact he.pow_succ_eq m
  rw [h1] at hb
  have hb' : (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B) b = e := hb
  have hbi : b * b = b := by
    apply hinj
    rw [map_mul, hb']; exact he
  rcases isUnit_or_isUnit_one_sub_self b with hu | hu
  · right
    have : b = 1 := hu.mul_left_cancel (by rw [hbi, mul_one])
    rw [← hb', this, map_one]
  · left
    have : b = 0 := hu.mul_left_cancel (by rw [sub_mul, hbi, one_mul, sub_self, mul_zero])
    rw [← hb', this, map_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndEtalePrimeComparison
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ind_etale_prime_comparison : ∀ (B O : Type) [CommRing B] [CommRing O] [Algebra B O], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra B O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra B E) (_ : Algebra.Etale B E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[B] Si i)) → ∀ p p' : Ideal O, p.IsPrime → p'.IsPrime → p ≤ p' → p.comap (algebraMap B O) = p'.comap (algebraMap B O) → p = p' := by
  first | (exact @GlobalTheory.eq_of_le_of_comap_eq_of_indEtale) | (exact GlobalTheory.eq_of_le_of_comap_eq_of_indEtale) | (intros; apply GlobalTheory.eq_of_le_of_comap_eq_of_indEtale  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
section
noncomputable section

namespace GlobalTheory.InertUnitOrb

open GlobalTheory.UnitLemma Matrix

def stdH (K : UQ) (n : ℕ) (y z : Fin n → K.E) : K.E := ∑ k, y k * K.c (z k)

def IsModel {K : UQ} (B : InvAlg K) {n : ℕ} (γ : Matrix (Fin n) (Fin n) K.E) (x : B.Aˣ)
    (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)) : Prop :=
  B.σ (x : B.A) = x ∧ (∀ y, ψ (B.g * y) = γ *ᵥ ψ y) ∧ ∀ y z, stdH K n (ψ y) (ψ z) = B.herm x y z

end GlobalTheory.InertUnitOrb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMulConvolutionEqStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_mul_convolution_eq_alt : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H), μ.IsHaarMeasure → ∀ K : Set H, IsCompact K → ∀ κ a : H → ℂ, Continuous κ → HasCompactSupport κ → Measurable a → Integrable a μ → (∀ x ∉ K, a x = 0) → ∀ f : H → ℂ, Continuous f → ∫ z, f z * (∫ x, κ x * a (x⁻¹ * z) ∂μ) ∂μ = ∫ x, κ x * ∫ y, f (x * y) * a y ∂μ ∂μ := by
  first | exact @GlobalTheory.integral_mul_convolution_eq | exact GlobalTheory.integral_mul_convolution_eq | (intros; apply GlobalTheory.integral_mul_convolution_eq <;> assumption)
end

