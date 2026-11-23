module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.IsStarRep
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.TensorFormCoordinates.CoordConjAtEmb
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL
open scoped Classical

namespace PositivityTheory.Rg.Cz.J

section
variable {E : Type} [Field E]

lemma coord_atEmb_ne {τ τ' : E →+* ℂ} (h : InfinitePlace.mk τ' ≠ InfinitePlace.mk τ) (z : ℂ) :
    coord τ' (atEmb τ z) = 0 := by
  have h0 := congrArg (coord τ') (atEmb_mul_of_ne h 1 z)
  rwa [map_mul, coord_atEmb, map_zero, one_mul] at h0

lemma coord_conj_atEmb [_root_.NumberField.IsTotallyComplex E] (τ : E →+* ℂ) (z : ℂ) :
    coord (ComplexEmbedding.conjugate τ) (atEmb τ z) = starRingEnd ℂ z := by
  have : atEmb τ z = atEmb (ComplexEmbedding.conjugate τ) (starRingEnd ℂ z) := by
    rw [atEmb_conj, Complex.conj_conj]
  rw [this, coord_atEmb]

lemma cxkey [_root_.NumberField.IsTotallyComplex E] (τ τ' : E →+* ℂ) :
    (1 / 2 : ℂ) * (coord τ' (atEmb τ 1) - Complex.I * coord τ' (atEmb τ Complex.I)) =
      if τ' = τ then 1 else 0 := by
  by_cases hm : InfinitePlace.mk τ' = InfinitePlace.mk τ
  · rcases InfinitePlace.mk_eq_iff.mp hm with h | h
    · subst h
      rw [if_pos rfl, coord_atEmb, coord_atEmb, Complex.I_mul_I]
      norm_num
    · have h' : τ' = ComplexEmbedding.conjugate τ := by
        rcases InfinitePlace.mk_eq_iff.mp hm.symm with h2 | h2
        · exfalso
          apply IsTotallyComplex.complexEmbedding_not_isReal τ'
          rw [ComplexEmbedding.isReal_iff, h, h2]
        · exact h2.symm
      have hne : τ' ≠ τ := by
        intro e
        apply IsTotallyComplex.complexEmbedding_not_isReal τ'
        rw [ComplexEmbedding.isReal_iff, h, e]
      rw [if_neg hne, h', coord_conj_atEmb, coord_conj_atEmb, map_one, Complex.conj_I, mul_neg,
        Complex.I_mul_I]
      norm_num
  · have hne : τ' ≠ τ := fun e => hm (by rw [e])
    rw [if_neg hne, coord_atEmb_ne hm, coord_atEmb_ne hm]
    simp

end

lemma half_comb (ι : Type) [Fintype ι] (x x' : ι → ℂ) (y y' : ℂ) :
    (1 / 2 : ℂ) * ((∑ p, x p - y) - Complex.I * (∑ p, x' p - y')) =
      ∑ p, (1 / 2 : ℂ) * (x p - Complex.I * x' p) - (1 / 2 : ℂ) * (y - Complex.I * y') := by
  simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  ring

lemma half_ite (P : Prop) [Decidable P] (u v : ℂ) :
    (1 / 2 : ℂ) * ((if P then u else 0) - Complex.I * (if P then v else 0)) =
      if P then (1 / 2 : ℂ) * (u - Complex.I * v) else 0 := by
  split_ifs <;> simp

theorem bigCx_holds : BigCx := by
  intro E _ _ _ a Q _ _ lab s
  refine ⟨fun τ i j f => ?_, fun y p p' hp f => ?_⟩
  · have hD : ∀ (z : ℂ) (I J : Q → Fin a), bigD lab s (toL (Matrix.single i j (atEmb τ z))) I J =
        (∑ p, if (∀ r, r ≠ p → I r = J r) ∧ I p = i ∧ J p = j then coord (lab p) (atEmb τ z) else 0) -
          if I = J ∧ i = j then (s : ℂ) * ∑ τ' : E →+* ℂ, coord τ' (atEmb τ z) else 0 := by
      intro z I J
      simp only [bigD, Matrix.of_apply, toL, Matrix.of_symm_apply, Matrix.single_apply]
      congr 1
      · refine Finset.sum_congr rfl fun p _ => ?_
        rw [apply_ite (coord (lab p)), map_zero]
        by_cases h1 : ∀ r, r ≠ p → I r = J r
        · rw [if_pos h1]
          by_cases h4 : i = I p ∧ j = J p
          · rw [if_pos h4, if_pos ⟨h1, h4.1.symm, h4.2.symm⟩]
          · rw [if_neg h4, if_neg (fun h => h4 ⟨h.2.1.symm, h.2.2.symm⟩)]
        · rw [if_neg h1, if_neg (fun h => h1 h.1)]
      · by_cases h1 : I = J
        · by_cases h2 : i = j
          · subst h2
            rw [if_pos h1, if_pos ⟨h1, rfl⟩]
            congr 1
            refine Finset.sum_congr rfl fun τ' _ => ?_
            simp only [and_self, apply_ite (coord τ'), map_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
          · rw [if_pos h1, if_neg (fun h => h2 h.2)]
            rw [Finset.sum_eq_zero fun τ' _ => Finset.sum_eq_zero fun k _ => by
              rw [if_neg (fun h => h2 (h.1.trans h.2.symm)), map_zero]]
            simp
        · rw [if_neg h1, if_neg (fun h => h1 h.1)]
    have hS : (1 / 2 : ℂ) * (∑ τ' : E →+* ℂ, coord τ' (atEmb τ 1) -
        Complex.I * ∑ τ' : E →+* ℂ, coord τ' (atEmb τ Complex.I)) = 1 := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
      simp only [cxkey, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hE : ∀ I J : Q → Fin a, cx τ (bigD lab s) i j I J =
        (∑ p, if (∀ r, r ≠ p → I r = J r) ∧ I p = i ∧ J p = j then (if lab p = τ then (1 : ℂ) else 0) else 0) -
          if I = J ∧ i = j then (s : ℂ) else 0 := by
      intro I J
      simp only [cx, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, hD, half_comb, half_ite, cxkey]
      congr 1
      split_ifs
      · linear_combination (s : ℂ) * hS
      · rfl
    have hT : ∀ I : Q → Fin a, tE (fib lab τ) (0 : Fin a → Fin a → Module.End ℂ ℂ) i j f I =
        ∑ p, if lab p = τ then (if I p = i then f (Function.update I p j) else 0) else 0 := by
      intro I
      simp [tE, lift, eAt, fib, Finset.sum_filter]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hl : lab p = τ <;> by_cases hi : I p = i <;> simp [hl, hi]
    funext I
    simp only [mulVec, dotProduct, hE, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Pi.sub_apply, hT]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hl : lab p = τ
      · by_cases hi : I p = i
        · rw [Finset.sum_eq_single (Function.update I p j)]
          · have hc : (∀ r, r ≠ p → I r = Function.update I p j r) ∧ I p = i ∧ Function.update I p j p = j :=
              ⟨fun r hr => by rw [Function.update_of_ne hr], hi, by simp⟩
            rw [if_pos hc, if_pos hl, if_pos hl, if_pos hi, one_mul]
          · intro J _ hJ
            rw [if_neg, zero_mul]
            intro h
            exact hJ (Function.eq_update_iff.mpr ⟨h.2.2, fun r hr => (h.1 r hr).symm⟩)
          · intro h
            exact absurd (Finset.mem_univ _) h
        · simp only [if_pos hl, if_neg hi]
          refine Finset.sum_eq_zero fun J _ => ?_
          rw [if_neg (fun h => hi h.2.1), zero_mul]
      · simp only [if_neg hl]
        simp
    · by_cases h : i = j
      · simp [h]
      · simp [h]
  · have hlab : ∀ r, lab (Equiv.swap p p' r) = lab r := by
      intro r
      rw [Equiv.swap_apply_def]
      split_ifs with h1 h2
      · rw [h1, hp]
      · rw [h2, hp]
      · rfl
    have hM : ∀ I J : Q → Fin a,
        bigM lab s y (I ∘ Equiv.swap p p') (J ∘ Equiv.swap p p') = bigM lab s y I J := by
      intro I J
      simp only [bigM, Matrix.of_apply, Function.comp_apply]
      congr 1
      exact Fintype.prod_equiv (Equiv.swap p p') _ _ (fun r => by rw [hlab])
    let e : (Q → Fin a) ≃ (Q → Fin a) :=
      ⟨fun J => J ∘ Equiv.swap p p', fun J => J ∘ Equiv.swap p p',
        fun J => by funext r; simp, fun J => by funext r; simp⟩
    funext I
    simp only [mulVec, dotProduct, pm, LinearMap.pi_apply, LinearMap.proj_apply]
    exact Fintype.sum_equiv e _ _ (fun J => by simp only [e, Equiv.coe_fn_mk, hM])

end PositivityTheory.Rg.Cz.J
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.TensorFormCoordinates.TensForm
section
open scoped TensorProduct MatrixOrder ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Cz.J

section
variable {V : Type} [AddCommGroup V] [Module ℂ V] {d : ℕ}

noncomputable abbrev ec (d : ℕ) : V ⊗[ℂ] (Fin d → ℂ) →ₗ[ℂ] (Fin d → V) :=
  TensorProduct.piScalarRightHom ℂ ℂ V (Fin d)

lemma ec_injective : Function.Injective (ec (V := V) d) := by
  intro x y h
  apply (TensorProduct.piScalarRight ℂ ℂ V (Fin d)).injective
  simpa using h

lemma ec_lTensor (T : Matrix (Fin d) (Fin d) ℂ) (x : V ⊗[ℂ] (Fin d → ℂ)) (k : Fin d) :
    ec d ((Matrix.toLin' T).lTensor V x) k = ∑ j, T k j • ec d x j := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v =>
    simp [Matrix.mulVec, dotProduct, Finset.sum_smul, mul_smul]
  | add x y hx hy =>
    simp only [map_add (f := _), Pi.add_apply, hx, hy, smul_add, Finset.sum_add_distrib]

end

private theorem re_sum_posSemidef_mul_H_nonneg {V : Type} [AddCommGroup V] [Module ℂ V] {d : ℕ}
    (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hnn : ∀ φ : V, 0 ≤ (H φ φ).re)
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosSemidef) (u : Fin d → V) :
    0 ≤ (∑ k, ∑ j, A k j * H (u k) (u j)).re := by
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hA
  have e : ∑ k, ∑ j, (∑ i, Matrix.vecMulVec (v i) (star (v i))) k j * H (u k) (u j) =
      ∑ i, H (∑ k, star (v i k) • u k) (∑ k, star (v i k) • u k) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, map_sum, map_smulₛₗ,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Pi.star_apply,
      starRingEnd_apply, star_star, RingHom.id_apply, Finset.sum_mul, Finset.mul_sum]
    calc _ = ∑ k, ∑ i, ∑ j, v i k * star (v i j) * H (u k) (u j) :=
          Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = _ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
          ring
  rw [e, Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => hnn _

theorem tensForm_holds : TensForm := by
  intro V _ _ d H hsym hpos
  have hnn : ∀ φ : V, 0 ≤ (H φ φ).re := fun φ => by
    by_cases h : φ = 0
    · simp [h]
    · exact (hpos φ h).le
  let B : V ⊗[ℂ] (Fin d → ℂ) →ₗ[ℂ] V ⊗[ℂ] (Fin d → ℂ) →ₗ⋆[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
      (fun x y => ∑ k, H (ec (V := V) d y k) (ec (V := V) d x k))
      (by intros; simp [Finset.sum_add_distrib])
      (by intros; simp [Finset.mul_sum])
      (by intros; simp [Finset.sum_add_distrib])
      (by intros; simp [Finset.mul_sum])
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · intro x y
    simp only [B, LinearMap.mk₂'ₛₗ_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsym]
  · intro x hx
    simp only [B, LinearMap.mk₂'ₛₗ_apply]
    rw [Complex.re_sum]
    have hne : ec (V := V) d x ≠ 0 := fun h => hx (ec_injective (by rw [h, map_zero]))
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hne
    exact Finset.sum_pos' (fun j _ => hnn _) ⟨k, Finset.mem_univ _, hpos _ hk⟩
  · intro φ ψ v w
    simp only [B, LinearMap.mk₂'ₛₗ_apply, ec, TensorProduct.piScalarRightHom_tmul, map_smulₛₗ,
      LinearMap.smul_apply, map_smul, smul_eq_mul, dotProduct, Finset.mul_sum, Pi.star_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [starRingEnd_apply, RingHom.id_apply]
    ring
  · intro T c hT hle x
    have hH : ((c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - T).IsHermitian := by
      refine Matrix.IsHermitian.sub ?_ hT
      simp [Matrix.IsHermitian, Matrix.conjTranspose_smul]
    have hA : ((c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - T).PosSemidef := by
      rw [Matrix.posSemidef_iff_dotProduct_mulVec]
      refine ⟨hH, fun v => ?_⟩
      rw [Complex.nonneg_iff]
      constructor
      · simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
          dotProduct_sub, dotProduct_smul, smul_eq_mul, Complex.sub_re, Complex.re_ofReal_mul]
        linarith [hle v]
      · have h0 := hH.im_star_dotProduct_mulVec_self v
        simpa using h0.symm
    have key := re_sum_posSemidef_mul_H_nonneg H hnn _ hA (ec (V := V) d x)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [B, LinearMap.mk₂'ₛₗ_apply, ec_lTensor, map_sum, map_smul, smul_eq_mul]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, sub_mul,
      Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, Complex.sub_re, Complex.re_sum,
      Complex.re_ofReal_mul] at key
    rw [Complex.re_sum, Complex.re_sum, Finset.mul_sum]
    simp only [Complex.re_sum]
    linarith

end PositivityTheory.Rg.Cz.J
end

