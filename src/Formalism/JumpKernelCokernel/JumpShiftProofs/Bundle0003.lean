module

public import Formalism.JumpKernelCokernel.Statement
public import Formalism.JumpKernelCokernel.JumpShiftProofs.Bundle0001
public import Formalism.JumpKernelCokernel.JumpShiftProofs.Bundle0002
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.Bundle0002
public import Formalism.JumpKernelCokernel.LemmaDJoint

@[expose] public section

-- bundled from Formalism.JumpKernelCokernel.JumpShiftProofs.CokerTors
section
open Polynomial Module

namespace Formalism.KernelCokernelLengths.CokernelTorsionLemmas

theorem charpoly_of_range_le {R : Type} [CommRing R] [IsDomain R] {M : Type} [AddCommGroup M]
    [Module R M] [Module.Free R M] [Module.Finite R M]
    (S : Submodule R M) [Module.Free R S] [Module.Finite R S] [Module.Free R (M ⧸ S)]
    [Module.Finite R (M ⧸ S)] (d : Module.End R M) (hd : ∀ m, d m ∈ S) :
    d.charpoly = (d.restrict (p := S) (q := S) (fun x _ => hd x)).charpoly *
      X ^ finrank R (M ⧸ S) := by
  classical
  obtain ⟨g, hg⟩ := Module.projective_lifting_property S.mkQ LinearMap.id
    (Submodule.mkQ_surjective S)
  have hg' : ∀ x, S.mkQ (g x) = x := fun x => LinearMap.congr_fun hg x
  let pr : M →ₗ[R] M := LinearMap.id - g ∘ₗ S.mkQ
  have hmem : ∀ m, pr m ∈ S := by
    intro m
    rw [← Submodule.Quotient.mk_eq_zero]
    simp only [pr, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
    rw [Submodule.Quotient.mk_sub]
    have := hg' (S.mkQ m)
    simp only [Submodule.mkQ_apply] at this ⊢
    rw [this, sub_self]
  let F : M →ₗ[R] S × (M ⧸ S) :=
    LinearMap.prod (pr.codRestrict S hmem) S.mkQ
  let G : S × (M ⧸ S) →ₗ[R] M := S.subtype.coprod g
  have h1 : F ∘ₗ G = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨s, c⟩
    have hs : S.mkQ (s : M) = 0 := by simp
    have hs' : (Submodule.Quotient.mk (s : M) : M ⧸ S) = 0 := hs
    have hg'' : (Submodule.Quotient.mk (g c) : M ⧸ S) = c := hg' c
    apply Prod.ext
    · apply Subtype.ext
      simp [F, G, pr, hg', hs]
    · simp [F, G, pr, hs', hg'']
  have h2 : G ∘ₗ F = LinearMap.id := by
    apply LinearMap.ext
    intro m
    simp [F, G, pr]
  let e : M ≃ₗ[R] S × (M ⧸ S) := LinearEquiv.ofLinearMap (f := F) (g := G) h1 h2
  let dS := d.restrict (p := S) (q := S) (fun x _ => hd x)
  let bS := Module.Free.chooseBasis R S
  let bQ := Module.Free.chooseBasis R (M ⧸ S)
  let b := bS.prod bQ
  have hconj : ∀ x, e.conj d x = (⟨d (G x), hd _⟩, 0) := by
    intro x
    rw [LinearEquiv.conj_apply]
    have hq : S.mkQ (d (G x)) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hd _
    apply Prod.ext
    · apply Subtype.ext
      simp [e, F, pr, hq]
    · simp [e, F, pr, hq]
  have hM : LinearMap.toMatrix b b (e.conj d) =
      Matrix.fromBlocks (LinearMap.toMatrix bS bS dS) (LinearMap.toMatrix b b (e.conj d)).toBlocks₁₂
        0 0 := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (LinearMap.toMatrix b b (e.conj d))]
    congr 1
    · ext i j
      simp only [Matrix.toBlocks₁₁, Matrix.of_apply, LinearMap.toMatrix_apply, b,
        Module.Basis.prod_apply, Sum.elim_inl, hconj, Module.Basis.prod_repr_inl]
      congr 2
      apply Subtype.ext
      simp [G, dS]
    · ext i j
      simp [Matrix.toBlocks₂₁, LinearMap.toMatrix_apply, b, hconj]
    · ext i j
      simp [Matrix.toBlocks₂₂, LinearMap.toMatrix_apply, b, hconj]
  rw [← e.charpoly_conj d, ← LinearMap.charpoly_toMatrix (e.conj d) b, hM,
    Matrix.charpoly_fromBlocks_zero₂₁, LinearMap.charpoly_toMatrix, Matrix.charpoly_zero,
    Module.finrank_eq_card_chooseBasisIndex]

end Formalism.KernelCokernelLengths.CokernelTorsionLemmas

namespace Formalism.KernelCokernelLengths.CokernelTorsionLemmas

theorem eq_of_mul_X_pow {R : Type} [CommRing R] [IsDomain R] (P Q : R[X]) (k r : ℕ)
    (hP : P.coeff 0 ≠ 0) (hQ : Q.coeff 0 ≠ 0) (h : P * X ^ r = X ^ k * Q) : P = Q := by
  have hP0 : P ≠ 0 := fun h0 => hP (by simp [h0])
  have hQ0 : Q ≠ 0 := fun h0 => hQ (by simp [h0])
  have tP : P.natTrailingDegree = 0 := Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hP)
  have tQ : Q.natTrailingDegree = 0 := Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hQ)
  have hrk : r = k := by
    have h1 := congrArg Polynomial.natTrailingDegree h
    rw [mul_comm (X ^ k) Q, Polynomial.natTrailingDegree_mul_X_pow hP0,
      Polynomial.natTrailingDegree_mul_X_pow hQ0, tP, tQ] at h1
    omega
  subst hrk
  rw [mul_comm (X ^ r) Q] at h
  exact mul_right_cancel₀ (pow_ne_zero _ Polynomial.X_ne_zero) h

end Formalism.KernelCokernelLengths.CokernelTorsionLemmas

theorem Formalism.KernelCokernelLengths.cokernel_torsion_holds : Formalism.KernelCokernelLengths.CokerTors := by
  intro O _ _ _ M _ _ _ _ d k Q hQ0 hchar hann
  classical
  have hQc : Q.coeff 0 ≠ 0 := by rwa [Polynomial.coeff_zero_eq_eval_zero]

  have hdQ : ∀ m, d (aeval d Q m) = 0 := by
    intro m
    have := LinearMap.congr_fun hann m
    simpa [map_mul, aeval_X] using this
  have hQd : ∀ m, aeval d Q (d m) = 0 := by
    intro m
    have h0 : aeval d (Q * X) = 0 := by rw [mul_comm]; exact hann
    have := LinearMap.congr_fun h0 m
    simpa [map_mul, aeval_X] using this

  have hsplit : ∀ m, aeval d Q m = Q.coeff 0 • m + d (aeval d Q.divX m) := by
    intro m
    conv_lhs => rw [← Polynomial.X_mul_divX_add Q]
    rw [map_add (f := _), map_mul, aeval_X, aeval_C, LinearMap.add_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, add_comm]
  have hcommR : ∀ m, d (aeval d Q.divX m) = aeval d Q.divX (d m) := by
    intro m
    have h0 : aeval d (X * Q.divX) = aeval d (Q.divX * X) := by rw [mul_comm]
    have := LinearMap.congr_fun h0 m
    simpa [map_mul, aeval_X] using this
  let S : Submodule O M := LinearMap.ker (aeval d Q)
  have hdS : ∀ m, d m ∈ S := fun m => hQd m

  have htf : Module.IsTorsionFree O (M ⧸ S) := by
    refine Module.IsTorsionFree.of_smul_eq_zero (fun a x hx => ?_)
    induction x using Submodule.Quotient.induction_on with
    | H m =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
      by_cases ha : a = 0
      · exact Or.inl ha
      · right
        rw [Submodule.Quotient.mk_eq_zero]
        have : a • aeval d Q m = 0 := by
          rw [← map_smul]; exact hx
        exact (smul_eq_zero.mp this).resolve_left ha
  have : Module.Free O (M ⧸ S) := Module.free_of_finite_type_torsion_free'
  let dS := d.restrict (p := S) (q := S) (fun x _ => hdS x)
  have hc := Formalism.KernelCokernelLengths.CokernelTorsionLemmas.charpoly_of_range_le S d hdS

  have hker : LinearMap.ker dS = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro s hs
    have hs1 : d (s : M) = 0 := by
      have := congrArg Subtype.val hs
      simpa [dS] using this
    have hs2 : aeval d Q (s : M) = 0 := s.2
    rw [hsplit, hcommR, hs1, map_zero (aeval d Q.divX), add_zero] at hs2
    exact Subtype.ext ((smul_eq_zero.mp hs2).resolve_left hQc)
  have hdet : LinearMap.det dS ≠ 0 := fun h => (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h) hker
  have hPc : dS.charpoly.coeff 0 ≠ 0 := by
    intro h; apply hdet; rw [LinearMap.det_eq_sign_charpoly_coeff, h, mul_zero]
  have hPQ : dS.charpoly = Q :=
    Formalism.KernelCokernelLengths.CokernelTorsionLemmas.eq_of_mul_X_pow _ _ k _ hPc hQc (hc.symm.trans hchar)
  have hspan : Ideal.span {LinearMap.det dS} = Ideal.span {Q.eval 0} := by
    rw [LinearMap.det_eq_sign_charpoly_coeff, hPQ, Polynomial.coeff_zero_eq_eval_zero]
    exact Ideal.span_singleton_mul_left_unit ((isUnit_neg_one).pow _) _
  have hlen := Formalism.KernelCokernelLengths.determinant_length_formula O S dS hdet
  rw [hspan] at hlen
  rw [← hlen]

  have hmemT : ∀ s : S, (LinearMap.range d).mkQ (s : M) ∈
      Submodule.torsion O (M ⧸ LinearMap.range d) := by
    intro s
    rw [Submodule.mem_torsion_iff]
    refine ⟨⟨Q.coeff 0, mem_nonZeroDivisors_of_ne_zero hQc⟩, ?_⟩
    show Q.coeff 0 • (Submodule.Quotient.mk (s : M) : M ⧸ LinearMap.range d) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    have hs2 : aeval d Q (s : M) = 0 := s.2
    rw [hsplit] at hs2
    rw [eq_neg_of_add_eq_zero_left hs2]
    exact Submodule.neg_mem _ (LinearMap.mem_range_self d _)
  let φ : S →ₗ[O] Submodule.torsion O (M ⧸ LinearMap.range d) :=
    ((LinearMap.range d).mkQ ∘ₗ S.subtype).codRestrict _ hmemT
  have hφ : LinearMap.range dS ≤ LinearMap.ker φ := by
    rintro _ ⟨s, rfl⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    show (LinearMap.range d).mkQ (d (s : M)) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self d _
  refine Module.length_le_of_surjective ((LinearMap.range dS).liftQ φ hφ) ?_
  rintro ⟨x, hx⟩
  induction x using Submodule.Quotient.induction_on with
  | H m =>
    rw [Submodule.mem_torsion_iff] at hx
    obtain ⟨a, ha⟩ := hx
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at ha
    obtain ⟨m', hm'⟩ := ha
    have h1 : (a : O) • aeval d Q m = 0 := by
      rw [← map_smul]
      show aeval d Q ((a : O) • m) = 0
      rw [show (a : O) • m = d m' from hm'.symm]; exact hQd m'
    have hmS : m ∈ S := (smul_eq_zero.mp h1).resolve_left (nonZeroDivisors.coe_ne_zero a)
    refine ⟨Submodule.Quotient.mk ⟨m, hmS⟩, ?_⟩
    rw [Submodule.liftQ_apply]
    rfl
end

-- bundled from Formalism.JumpKernelCokernel.JumpShiftProofs.ExpRowD
section
namespace Formalism.KernelCokernelLengths

theorem row_degree_exponent : ExpRowD := by
  intro ℓ hℓ h η S b a s₁ E e₂ hη hb ha hs hE he
  have key := Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.expBound_statement ℓ hℓ h η S b a s₁ E e₂ hb ha hs hE he
  have hℓ0 : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast (by omega : 0 < ℓ)
  have hℓ2 : (0 : ℝ) < (ℓ : ℝ) ^ 2 := by positivity
  have hη' : (2 * (η : ℝ)) ≤ h := by exact_mod_cast hη
  have hc : 32 * ((h + η : ℕ) : ℝ) / (ℓ : ℝ) ^ 2 ≤ 50 * (h : ℝ) / (ℓ : ℝ) ^ 2 := by
    apply div_le_div_of_nonneg_right _ hℓ2.le
    push_cast
    nlinarith [(Nat.cast_nonneg η : (0 : ℝ) ≤ η)]
  linarith

end Formalism.KernelCokernelLengths
end

-- bundled from Formalism.JumpKernelCokernel.JumpShiftProofs.LemmaDJoint
section
namespace Formalism.KernelCokernelLengths.QuotientLengthJointLemmas

theorem quot_le (O : Type) [CommRing O] (R : Type) [AddCommGroup R] [Module O R]
    (π : Module.End O R) (R' R'' : Submodule O R) (B : Type) [AddCommGroup B] [Module O B]
    (πB : Module.End O B) (j : ↥R'' →ₗ[O] B)
    (hstab : R''.map π ≤ R'') (hker : LinearMap.ker j = R'.comap R''.subtype)
    (hj : ∀ (x : ↥R'') (hx : π x ∈ R''), j ⟨π x, hx⟩ = πB (j x)) :
    Module.length O (↥R'' ⧸ (R' ⊔ R''.map π).comap R''.subtype) ≤
      Module.length O (↥(LinearMap.range j) ⧸
        ((LinearMap.range j).map πB).comap (LinearMap.range j).subtype) := by
  set K := (R' ⊔ R''.map π).comap R''.subtype with hK
  set L := ((LinearMap.range j).map πB).comap (LinearMap.range j).subtype with hL
  have hkerK : LinearMap.ker j ≤ K := by
    rw [hker]; exact Submodule.comap_mono le_sup_left
  let ψ : ↥(LinearMap.range j) →ₗ[O] ↥R'' ⧸ K :=
    (Submodule.factor hkerK).comp (j.quotKerEquivRange.symm : ↥(LinearMap.range j) →ₗ[O] ↥R'' ⧸ LinearMap.ker j)
  have hψ : ∀ y : ↥R'', ψ (j.rangeRestrict y) = K.mkQ y := by
    intro y
    have e : j.quotKerEquivRange.symm (j.rangeRestrict y) = Submodule.Quotient.mk y := by
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext (LinearMap.quotKerEquivRange_apply_mk j y).symm
    show Submodule.factor hkerK (j.quotKerEquivRange.symm (j.rangeRestrict y)) = K.mkQ y
    rw [e]
    exact Submodule.factor_mk hkerK y
  have hLψ : L ≤ LinearMap.ker ψ := by
    intro m hm
    obtain ⟨b, ⟨x, rfl⟩, hbm⟩ := hm
    have hpx : π x ∈ R'' := hstab ⟨x, x.2, rfl⟩
    have hy : j.rangeRestrict ⟨π x, hpx⟩ = m := Subtype.ext ((hj x hpx).trans hbm)
    rw [LinearMap.mem_ker, ← hy, hψ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_sup_right ⟨x, x.2, rfl⟩
  have hsurj : Function.Surjective (L.liftQ ψ hLψ) := by
    intro z
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective K z
    exact ⟨L.mkQ (j.rangeRestrict y), by rw [Submodule.mkQ_apply, Submodule.liftQ_apply, hψ]⟩
  exact Module.length_le_of_surjective _ hsurj

end Formalism.KernelCokernelLengths.QuotientLengthJointLemmas

theorem Formalism.KernelCokernelLengths.lemma_D_joint_form : Formalism.KernelCokernelLengths.LemmaDJoint := by
  intro O _ R _ _ π R' R'' B _ _ πB j hle hstab hB hker hj
  have hN : (LinearMap.range j).map πB ≤ LinearMap.range j := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨⟨π x, hstab ⟨x, x.2, rfl⟩⟩, hj x _⟩
  calc _ ≤ _ := Formalism.KernelCokernelLengths.LengthSplittingLemmas.main O R π R' R'' hle
    _ ≤ _ := add_le_add le_rfl ((Formalism.KernelCokernelLengths.QuotientLengthJointLemmas.quot_le O R π R' R'' B πB j hstab hker hj).trans
          (Formalism.KernelCokernelLengths.KernelCokernelLemmas.main O B hB πB _ hN))
end

