module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0005
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0093
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZetaEulerProductNeZeroOneAddMulI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0535

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLinearMapTensorOfPairing
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

namespace GlobalTheory.PairingTensor

open TensorProduct

variable {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

noncomputable def contrR (l : B →ₗ[ℂ] ℂ) : TensorProduct ℂ A B →ₗ[ℂ] A :=
  (TensorProduct.rid ℂ A).toLinearMap ∘ₗ LinearMap.lTensor A l

noncomputable def contrL (l : A →ₗ[ℂ] ℂ) : TensorProduct ℂ A B →ₗ[ℂ] B :=
  (TensorProduct.lid ℂ B).toLinearMap ∘ₗ LinearMap.rTensor B l

@[simp] theorem contrR_tmul (l : B →ₗ[ℂ] ℂ) (a : A) (b : B) :
    contrR l (a ⊗ₜ[ℂ] b) = l b • a := by
  simp [contrR]

@[simp] theorem contrL_tmul (l : A →ₗ[ℂ] ℂ) (a : A) (b : B) :
    contrL l (a ⊗ₜ[ℂ] b) = l a • b := by
  simp [contrL]

theorem apply_contrR (l : A →ₗ[ℂ] ℂ) (m : B →ₗ[ℂ] ℂ) (z : TensorProduct ℂ A B) :
    l (contrR m z) = m (contrL l z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [mul_comm]
  | add x y hx hy => simp [hx, hy]

theorem contrR_map (m : B →ₗ[ℂ] ℂ) (a : Module.End ℂ A) (z : TensorProduct ℂ A B) :
    contrR m (TensorProduct.map a LinearMap.id z) = a (contrR m z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp [hx, hy]

theorem contrL_map (l : A →ₗ[ℂ] ℂ) (b : Module.End ℂ B) (z : TensorProduct ℂ A B) :
    contrL l (TensorProduct.map LinearMap.id b z) = b (contrL l z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp [hx, hy]

theorem eq_zero_of_contrR {ι : Type} (m : ι → B →ₗ[ℂ] ℂ) (hm : ∀ b, (∀ y, m y b = 0) → b = 0)
    (z : TensorProduct ℂ A B) (hz : ∀ y, contrR (m y) z = 0) : z = 0 := by
  classical
  let bA := Module.Basis.ofVectorSpace ℂ A
  have key : ∀ (w : TensorProduct ℂ A B) i,
      TensorProduct.equivFinsuppOfBasisLeft bA w i = contrL (bA.coord i) w := by
    intro w i
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp [hx, hy]
  apply (TensorProduct.equivFinsuppOfBasisLeft bA).injective
  ext i
  rw [key, map_zero, Finsupp.zero_apply]
  apply hm
  intro y
  rw [← apply_contrR, hz, map_zero]

theorem inner_separates {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (i : A →ₗ[ℂ] H) (hi : Function.Injective i) (a : A) (h : ∀ x, inner ℂ x (i a) = 0) :
    a = 0 := by
  apply hi
  rw [map_zero]
  exact inner_self_eq_zero.mp (h (i a))

theorem exists_linearMap_tensor :
    ∀ (V A B H₁ H₂ : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] (i₁ : A →ₗ[ℂ] H₁) (i₂ : B →ₗ[ℂ] H₂), Function.Injective i₁ → Function.Injective i₂ → ∀ (φ : H₂ → V →ₗ[ℂ] A) (ψ : H₁ → V →ₗ[ℂ] B), (∀ x y P, inner ℂ x (i₁ (φ y P)) = inner ℂ y (i₂ (ψ x P))) → (∀ P, ∃ E : Submodule ℂ A, FiniteDimensional ℂ E ∧ ∀ y, φ y P ∈ E) → ∃ f : V →ₗ[ℂ] TensorProduct ℂ A B, (∀ P, f P = 0 → ∀ y, φ y P = 0) ∧ (∀ (c : Module.End ℂ V) (a : Module.End ℂ A), (∀ y P, φ y (c P) = a (φ y P)) → f ∘ₗ c = TensorProduct.map a LinearMap.id ∘ₗ f) ∧ (∀ (c : Module.End ℂ V) (b : Module.End ℂ B), (∀ x P, ψ x (c P) = b (ψ x P)) → f ∘ₗ c = TensorProduct.map LinearMap.id b ∘ₗ f) := by
  intro V A B H₁ H₂ _ _ _ _ _ _ _ _ _ _ i₁ i₂ h₁ h₂ φ ψ hφψ hE
  let m : H₂ → B →ₗ[ℂ] ℂ := fun y => (innerₛₗ ℂ y) ∘ₗ i₂
  let l : H₁ → A →ₗ[ℂ] ℂ := fun x => (innerₛₗ ℂ x) ∘ₗ i₁
  have hm : ∀ y b, m y b = inner ℂ y (i₂ b) := fun _ _ => rfl
  have hl : ∀ x a, l x a = inner ℂ x (i₁ a) := fun _ _ => rfl
  have sepm : ∀ b, (∀ y, m y b = 0) → b = 0 := fun b h => inner_separates i₂ h₂ b h
  have sepl : ∀ a, (∀ x, l x a = 0) → a = 0 := fun a h => inner_separates i₁ h₁ a h
  have sepR : ∀ z w : TensorProduct ℂ A B, (∀ y, contrR (m y) z = contrR (m y) w) → z = w := by
    intro z w h
    rw [← sub_eq_zero]
    exact eq_zero_of_contrR m sepm _ (fun y => by rw [map_sub, h, sub_self])
  have sepL : ∀ z w : TensorProduct ℂ A B, (∀ x, contrL (l x) z = contrL (l x) w) → z = w := by
    intro z w h
    apply sepR
    intro y
    rw [← sub_eq_zero]
    apply sepl
    intro x
    rw [map_sub, apply_contrR, apply_contrR, h, sub_self]
  have ex : ∀ P, ∃ z : TensorProduct ℂ A B, ∀ y, contrR (m y) z = φ y P := by
    intro P
    obtain ⟨E, hfin, hmem⟩ := hE P
    let e := stdOrthonormalBasis ℂ (E.map i₁)
    have ha : ∀ j, ∃ a : A, i₁ a = (e j : H₁) := fun j => by
      obtain ⟨a, -, ha⟩ := (e j).2
      exact ⟨a, ha⟩
    choose a ha using ha
    refine ⟨∑ j, a j ⊗ₜ[ℂ] ψ (e j) P, fun y => ?_⟩
    apply h₁
    have := congrArg (fun v : E.map i₁ => (v : H₁))
      (e.sum_repr' ⟨i₁ (φ y P), Submodule.mem_map_of_mem (hmem y)⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← this, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [contrR_tmul, map_smul, ha, hm, ← hφψ]
  choose g hg using ex
  let f : V →ₗ[ℂ] TensorProduct ℂ A B :=
    { toFun := g
      map_add' := fun P Q => sepR _ _ fun y => by rw [map_add (f := _), hg, hg, hg, map_add (f := _)]
      map_smul' := fun s P => sepR _ _ fun y => by
        rw [map_smul, hg, hg, map_smul, RingHom.id_apply] }
  have hf : ∀ P y, contrR (m y) (f P) = φ y P := hg
  have hf' : ∀ P x, contrL (l x) (f P) = ψ x P := by
    intro P x
    rw [← sub_eq_zero]
    apply sepm
    intro y
    rw [map_sub, ← apply_contrR, hf, hl, hm, hφψ, sub_self]
  refine ⟨f, fun P hP y => by rw [← hf, hP, map_zero], fun c a h => ?_, fun c b h => ?_⟩
  · ext P
    refine sepR _ _ fun y => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, contrR_map, hf, hf, h]
  · ext P
    refine sepL _ _ fun x => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, contrL_map, hf', hf', h]

end GlobalTheory.PairingTensor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialKFiniteBothMembers
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

namespace GlobalTheory.FockKFin

theorem sameBlock_iff_isLeft {p q : ℕ} (a b : Ix p q) : sameBlock a b ↔ a.isLeft = b.isLeft := by
  cases a <;> cases b <;> simp [sameBlock]

theorem isKC_one {p q : ℕ} : IsKC (1 : Mat p q) := by
  intro a b h
  apply Matrix.one_apply_ne
  rintro rfl
  exact h ((sameBlock_iff_isLeft a a).2 rfl)

theorem isKC_kronecker {p q r s : ℕ} (A : Mat p q) (B : Mat r s) (hA : IsKC A) (hB : IsKC B) :
    IsKC (Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s)
      (Matrix.kroneckerMap (· * ·) A B)) := by
  intro x y hxy
  obtain ⟨⟨a, c⟩, rfl⟩ := (lineEquiv p q r s).surjective x
  obtain ⟨⟨b, d⟩, rfl⟩ := (lineEquiv p q r s).surjective y
  rw [sameBlock_iff_isLeft, lineEquiv_isLeft, lineEquiv_isLeft] at hxy
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.kroneckerMap_apply]
  by_cases h1 : sameBlock a b
  · by_cases h2 : sameBlock c d
    · exfalso
      apply hxy
      cases a <;> cases b <;> cases c <;> cases d <;> simp_all [sameBlock, linePos]
    · rw [hB c d h2, mul_zero]
  · rw [hA a b h1, zero_mul]

theorem emb_mem_Kset {p q r s : ℕ} {T0 : GrpData (p * r + q * s) (p * s + q * r)}
    {T1 : GrpData p q} {T2 : GrpData r s} (F : FockData T0 T1 T2) {g : T1.G} {h : T2.G}
    (hg : g ∈ T1.Kset) (hh : h ∈ T2.Kset) : F.emb (g, h) ∈ T0.Kset := by
  change IsKC _
  rw [F.emb_cov]
  exact isKC_kronecker _ _ hg hh

theorem one_mem_Kset {p q : ℕ} (T : GrpData p q) : (1 : T.G) ∈ T.Kset := by
  change IsKC _
  rw [map_one, Units.val_one]
  exact isKC_one

theorem exists_finite {p q r s : ℕ} {T0 : GrpData (p * r + q * s) (p * s + q * r)}
    {T1 : GrpData p q} {T2 : GrpData r s} (F : FockData T0 T1 T2)
    (H : ∀ k ∈ T0.Kset, ∀ (d : ℕ), ∀ P ∈ homog (Ix p q × Ix r s) d,
      ∃ Q ∈ homog (Ix p q × Ix r s) d, F.Om k (F.ι P) = F.ι Q) (P : Pol p q r s) :
    ∃ W : Submodule ℂ F.H, FiniteDimensional ℂ W ∧ ∀ k ∈ T0.Kset, F.Om k (F.ι P) ∈ W := by
  refine ⟨(MvPolynomial.restrictTotalDegree (Ix p q × Ix r s) ℂ P.totalDegree).map F.ι,
    inferInstance, fun k hk => ?_⟩
  conv_rhs => rw [← MvPolynomial.sum_homogeneousComponent P]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  obtain ⟨Q, hQ, e⟩ := H k hk d _ (MvPolynomial.homogeneousComponent_mem d P)
  rw [e]
  refine Submodule.mem_map_of_mem ?_
  rw [MvPolynomial.mem_restrictTotalDegree]
  have h1 : Q.totalDegree ≤ d := MvPolynomial.IsHomogeneous.totalDegree_le hQ
  have h2 := Finset.mem_range.1 hd
  omega

theorem kfin_fock : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s) (F : FockData T0 T1 T2), (∀ k ∈ T0.Kset, ∀ (d : ℕ), ∀ P ∈ homog (Ix p q × Ix r s) d, ∃ Q ∈ homog (Ix p q × Ix r s) d, F.Om k (F.ι P) = F.ι Q) → ∀ P : Pol p q r s, KFin T1 (fun g => F.π (g, 1)) (F.ι P) ∧ KFin T2 (fun h => F.π (1, h)) (F.ι P) := by
  intro p q r s T0 T1 T2 F H P
  obtain ⟨W, hW, hmem⟩ := exists_finite F H P
  constructor
  · refine Submodule.finiteDimensional_of_le (S₂ := W) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact hmem _ (emb_mem_Kset F k.2 (one_mem_Kset T2))
  · refine Submodule.finiteDimensional_of_le (S₂ := W) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact hmem _ (emb_mem_Kset F (one_mem_Kset T1) k.2)

end GlobalTheory.FockKFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeLEntireAndNonzeroAtOneHolds
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff
open Formalism.L2.Host (HChar)

namespace GlobalTheory.HeckeOne
open GlobalTheory.CMVal (eulerFactor IsHeckeL)
variable {K : Type} [Field K] [NumberField K]

theorem two_le_N (P : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm P.asIdeal :=
  NumberField.HeightOneSpectrum.one_lt_absNorm P

theorem sumN (σ : ℝ) (hσ : 1 < σ) : Summable fun P : HeightOneSpectrum (𝓞 K) => (Ideal.absNorm P.asIdeal : ℝ) ^ (-σ) :=
  ((GlobalTheory.countable_ideal_and_summable_absNorm_rpow K).2 σ hσ).2

theorem nonemptyN : Nonempty (HeightOneSpectrum (𝓞 K)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 K)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩⟩

noncomputable def cf (χ : HChar K) (P : HeightOneSpectrum (𝓞 K)) : ℂ := if χ.UnrAt P then ((χ.val P : ℂˣ) : ℂ) else 0

theorem norm_cf {χ : HChar K} (h : χ.IsUnitary) (P : HeightOneSpectrum (𝓞 K)) : ‖cf χ P‖ ≤ 1 := by
  unfold cf; split_ifs
  · exact (h _).le
  · simp

theorem hasProd_exp {χ : HChar K} (h : χ.IsUnitary) {s : ℂ} (hs : 1 < s.re) : HasProd (eulerFactor χ s)
    (Complex.exp (∑' P : HeightOneSpectrum (𝓞 K), -Complex.log (1 - cf χ P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)))) := by
  refine (((GlobalTheory.eulerProduct_eq_exp_and_pos _ (fun P : HeightOneSpectrum (𝓞 K) => Ideal.absNorm P.asIdeal) (cf χ) two_le_N
    (norm_cf h) sumN).1 s hs).2).congr_fun fun P => ?_
  unfold eulerFactor cf; split_ifs <;> simp

theorem eulerFactor_mul_normChar (χ : HChar K) (t : ℝ) (s : ℂ) :
    eulerFactor (χ * normChar K t) s = eulerFactor χ (s + (t : ℂ) * Complex.I) := by
  funext v
  have hiff : (χ * normChar K t).UnrAt v ↔ χ.UnrAt v :=
    ⟨fun h => by simpa using h.mul (unrAt_normChar t v).inv, fun h => h.mul (unrAt_normChar t v)⟩
  have hN := two_le_N v
  unfold eulerFactor
  by_cases h : χ.UnrAt v
  · rw [if_pos h, if_pos (hiff.2 h), Formalism.L2.Host.HChar.val_mul, Units.val_mul, val_normChar, mul_assoc,
      ← Complex.cpow_add _ _ (by exact_mod_cast (by omega : Ideal.absNorm v.asIdeal ≠ 0))]
    congr 4; ring
  · rw [if_neg h, if_neg (mt hiff.1 h)]

theorem entire_of_not_normPow {χ : HChar K} (hu : χ.IsUnitary) (hχ : ¬ ∃ t : ℝ, IsNormPow χ t) :
    ∃ Λ : ℂ → ℂ, IsHeckeL χ Λ := by
  obtain ⟨t, φ, hφ1, hφ2, hφ3, hφ4, hφ5⟩ := GlobalTheory.HeckeOne.exists_normChar_smooth_homogeneous_inf K χ hu
  set χ₀ := χ * normChar K (-t) with hχ₀
  have he : χ = χ₀ * normChar K t := by
    rw [hχ₀, mul_assoc, ← normChar_add, neg_add_cancel, normChar_zero, mul_one]
  have hu₀ : χ₀.IsUnitary := hu.mul (isUnitary_normChar _)
  obtain ⟨m, X, hm, hX0, hX1, hXm, hXn, hXz, hXP, hXβ⟩ := _root_.GlobalTheory.exists_ideal_character_of_unitary_hchar K χ₀ hu₀
  have hβ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = φ (mixedEmbedding K β) := fun β h0 h1 => by
    have h0' : (β : K) ≠ 0 := by exact_mod_cast h0
    rw [hXβ β (Units.mk0 _ h0') rfl h1, ← hφ5]; rfl
  have hJ : ∃ J, J ≠ ⊥ ∧ J ⊔ m = ⊤ ∧ X J ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hφ := GlobalTheory.eq_one_of_homogeneous_of_eq_one_on_class K m φ hm hφ3.continuousOn hφ2 (fun β h0 h1 => by
      rw [← hβ β h0 h1]
      refine hcon _ (by rwa [Ne, Ideal.span_singleton_eq_bot]) ?_
      rw [Ideal.eq_top_iff_one, show (1 : 𝓞 K) = β - (β - 1) by ring]
      exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self β)) (Ideal.mem_sup_right h1))
    have h1 : χ₀ = 1 := GlobalTheory.HeckeUnrTrivial.eq_one_of_inf_of_val K χ₀ (fun k => by
      have := hφ (mixedEmbedding K (k : K)) (by
        rw [mixedEmbedding.norm_eq_norm]
        exact_mod_cast abs_ne_zero.2 (Algebra.norm_ne_zero_iff.2 k.ne_zero))
      rw [hφ5, inv_eq_one] at this
      exact Units.ext this) fun v hv => by
      have h2 := hXP v
      rw [if_pos hv] at h2
      refine Units.ext (h2.symm.trans (hcon _ v.ne_bot ?_))
      by_contra h3
      exact (χ₀.val v).ne_zero (h2.symm.trans (hXz _ h3))
    exact hχ ⟨t, (isNormPow_iff _ _).2 (by rw [he, h1, one_mul])⟩
  have hle : ∀ I, ‖X I‖ ≤ 1 := fun I => by
    by_cases hI : I = ⊥
    · simp [hI, hX0]
    by_cases hI' : I ⊔ m = ⊤
    · exact (hXn I hI hI').le
    · simp [hXz I hI']
  obtain ⟨Z, hZd, hZ, hZ1⟩ := GlobalTheory.idealCharacter_LSeries_continuation K m X φ hm hX0 hXm hXn hXz hφ1 hφ2 hφ3 hφ4 hβ
  have hd : Differentiable ℂ (dslope Z 1) := by
    rw [← differentiableOn_univ] at hZd ⊢
    exact (Complex.differentiableOn_dslope Filter.univ_mem).mpr hZd
  refine ⟨fun s => dslope Z 1 (s + (t : ℂ) * Complex.I), hd.comp (by fun_prop), fun s hs => ?_⟩
  have hs' : 1 < (s + (t : ℂ) * Complex.I).re := by simpa using hs
  rw [he, eulerFactor_mul_normChar]
  convert hasProd_exp hu₀ hs' using 1
  have hs1 : s + (t : ℂ) * Complex.I ≠ 1 := fun h => by rw [h] at hs'; simp at hs'
  have hs2 := sub_ne_zero.mpr hs1
  beta_reduce
  rw [dslope_of_ne _ hs1, slope_def_field, hZ1 hJ, hZ _ hs',
    GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum K X hX0 hX1 hXm hle _ hs', sub_zero, mul_div_cancel_left₀ _ hs2]
  simp only [hXP, cf]

theorem _root_.GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne_holds : GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne := by
  intro K _ _ χ hu
  refine ⟨entire_of_not_normPow hu, fun h1 => ?_⟩
  obtain ⟨Z, hZd, hZ⟩ := GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire K
  by_cases hχ : ∃ t : ℝ, IsNormPow χ t
  · obtain ⟨t, ht⟩ := hχ
    rw [isNormPow_iff] at ht
    subst ht
    have ht0 : t ≠ 0 := fun h => h1 (h ▸ normChar_zero)
    have ht1 : (1 : ℂ) + (t : ℂ) * Complex.I - 1 ≠ 0 := by simpa using ht0
    refine ⟨fun s => Z (s + (t : ℂ) * Complex.I) / (s + (t : ℂ) * Complex.I - 1), ⟨?_, fun s hs => ?_⟩,
      div_ne_zero (GlobalTheory.zetaEulerProduct_ne_zero_one_add_mul_I _ _ two_le_N sumN nonemptyN Z hZd hZ t ht0) ht1⟩
    · exact ((hZd.comp (f := fun s : ℂ => s + (t : ℂ) * Complex.I) (by fun_prop)).analyticAt 1).div (by fun_prop) ht1
    · have hs' : 1 < (s + (t : ℂ) * Complex.I).re := by simpa using hs
      have hs1 : s + (t : ℂ) * Complex.I ≠ 1 := fun h => by rw [h] at hs'; simp at hs'
      rw [← one_mul (normChar K t), eulerFactor_mul_normChar]
      convert hasProd_exp (χ := 1) (fun _ => by simp) hs' using 1
      have hc : ∀ P : HeightOneSpectrum (𝓞 K), cf 1 P = 1 := fun P => if_pos fun _ _ => rfl
      simp only [hc]
      rw [hZ _ hs', mul_div_cancel_left₀ _ (sub_ne_zero.mpr hs1)]
  · obtain ⟨Λ, hΛ⟩ := entire_of_not_normPow hu hχ
    exact ⟨Λ, isContAtOne_of_isHeckeL hΛ, GlobalTheory.eulerProduct_ne_zero_one_of_entire _ _ (cf χ) two_le_N (norm_cf hu) sumN
      nonemptyN Z Λ hZd hΛ.1 hZ fun s hs => (hΛ.2 s hs).unique (hasProd_exp hu hs)⟩

end GlobalTheory.HeckeOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestLeastDegreeMirror
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

namespace GlobalTheory.LeastDegree

theorem lamA_ne_zero {t : ℕ} {al be ga de : List ℚ} (h : HypA t al be ga de)
    (a : Ix (al.length + be.length) (ga.length + de.length)) : lamA al be ga de a ≠ 0 := by
  obtain ⟨ht, -, -, -, -, -, -, -, -, -, habs⟩ := h
  have key : ∀ e ∈ al ++ be ++ ga ++ de, e ≠ 0 := by
    intro e he h0
    have hle := habs e he
    rw [h0, abs_zero] at hle
    have ht' : (1 : ℚ) ≤ t := by exact_mod_cast ht
    linarith
  rcases a with ⟨i, hi⟩ | ⟨j, hj⟩
  · have hi' : i < (al ++ be).length := by simpa using hi
    have hm : (al ++ be)[i] ∈ al ++ be := List.getElem_mem hi'
    simp only [lamA, ofBlocks, List.getD_eq_getElem _ _ hi']
    apply key
    simp only [List.mem_append] at hm ⊢
    tauto
  · have hj' : j < (ga ++ de).length := by simpa using hj
    have hm : (ga ++ de)[j] ∈ ga ++ de := List.getElem_mem hj'
    simp only [lamA, ofBlocks, List.getD_eq_getElem _ _ hj']
    apply key
    simp only [List.mem_append] at hm ⊢
    tauto

theorem coneTypes_ds (X : ProvA) (hX : DiscreteSeriesBlattner X) {p q : ℕ} {lam : Ix p q → ℚ}
    (h : IsParam lam) : ConeTypes (X.ds p q lam).HK lam := by
  intro μ v hv
  exact (hX p q lam h).2.2 μ v hv

theorem lowest_least_degree : ∀ X : ProvA, DiscreteSeriesBlattner X → ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → (∀ μ v, IsHW (X.ds _ _ (lamA al be ga de)).HK.act μ v → degW (cPair (al.length + de.length + t) (ga.length + be.length)) (blattner (lamA al be ga de)) ≤ degW (cPair (al.length + de.length + t) (ga.length + be.length)) μ) ∧ (∀ μ v, IsHW (X.ds _ _ (lamA' t al be ga de)).HK.act μ v → degW (cPair (al.length + be.length) (ga.length + de.length)) (blattner (lamA' t al be ga de)) ≤ degW (cPair (al.length + be.length) (ga.length + de.length)) μ) := by
  intro X hX t al be ga de hA
  obtain ⟨-, hP, hP', hs, hs'⟩ := _root_.GlobalTheory.LowestTypes.lowest_types t al be ga de hA
  refine ⟨?_, ?_⟩
  · refine GlobalTheory.T.degW_blattner_le_of_blattnerCone _ _ _ _ _ 0 (coneTypes_ds X hX hP) ?_
    intro a
    refine ⟨(hs a).1, fun hle => (hs a).2 ?_⟩
    exact lt_of_le_of_ne hle (lamA_ne_zero hA a)
  · exact GlobalTheory.T.degW_blattner_le_of_blattnerCone _ _ _ _ _ ((t : ℚ) / 2) (coneTypes_ds X hX hP') hs'

theorem lowest_least_degree_mirror : ∀ X : ProvA, DiscreteSeriesBlattner X → ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → (∀ μ v, IsHW (X.ds _ _ (lamA al be ga de)).HK.act μ v → degW (cPair (al.length + de.length) (ga.length + be.length + t)) (blattner (lamA al be ga de)) ≤ degW (cPair (al.length + de.length) (ga.length + be.length + t)) μ) ∧ (∀ μ v, IsHW (X.ds _ _ (lamM' t al be ga de)).HK.act μ v → degW (cPair (al.length + be.length) (ga.length + de.length)) (blattner (lamM' t al be ga de)) ≤ degW (cPair (al.length + be.length) (ga.length + de.length)) μ) := by
  intro X hX t al be ga de hA
  obtain ⟨-, hP, -, -, -⟩ := _root_.GlobalTheory.LowestTypes.lowest_types t al be ga de hA
  obtain ⟨-, hM, hs, hs'⟩ := _root_.GlobalTheory.TypesMirror.types_mirror t al be ga de hA
  refine ⟨?_, ?_⟩
  · refine GlobalTheory.T.degW_blattner_le_of_blattnerCone _ _ _ _ _ 0 (coneTypes_ds X hX hP) ?_
    intro a
    refine ⟨(hs a).1, fun hle => (hs a).2 ?_⟩
    exact lt_of_le_of_ne hle (lamA_ne_zero hA a)
  · exact GlobalTheory.T.degW_blattner_le_of_blattnerCone _ _ _ _ _ ((t : ℚ) / 2) (coneTypes_ds X hX hM) hs'

end GlobalTheory.LeastDegree
end

