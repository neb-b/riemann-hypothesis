module

public import Development.AutomorphicArithmetic.Foundations.Convolution.OrbitNormCounting.NormCount
public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaConstantMulOfCoprimeEllipticPolynomials
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.OrbitNormCounting.CptInt
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

private theorem nrmL_locEl {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ) (w : Pl E)
    (δ : GL (Fin n) E) :
    nrmL n w (locEl n w δ) = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (δ * thE E n δ) := by
  unfold nrmL locEl
  split_ifs with hs
  · rfl
  · have hm : thetaGL n (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ) =
        GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (thE E n δ) :=
      (GlobalTheory.ThetaPull.map_thetaGL _ _ _ (fun x => ((_root_.GlobalTheory.ConjAtPlace.main E hU w).2.2.2.1 hs).1 x |>.symm) δ).symm
    rw [hm, ← map_mul]

theorem UpperTheory.ConvolutionTheory.G3.cptInt :
    UpperTheory.ConvolutionTheory.G3.CptInt := by
  intro E _ _ _ hU n δ hs
  have hs' : (δ * thE E n δ).val.charpoly.Separable := hs
  filter_upwards [GlobalTheory.BCT.SepBezout.bezout_eventually E _ hs', GlobalTheory.BCT.GoodInt.eventually_mem_KGL (δ * thE E n δ)] with w hb hK
  obtain ⟨-, hinv, -, -, -, hKc, -⟩ := GlobalTheory.BCT.ThBasic.twist_basic E hU n w
  have hNe := nrmL_locEl hU n w δ
  have hNK : nrmL n w (locEl n w δ) ∈ GlobalTheory.LFun.KGL w (n := n) := hNe ▸ hK
  have hgood : ∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧
      u * (nrmL n w (locEl n w δ)).val.charpoly + v * derivative (nrmL n w (locEl n w δ)).val.charpoly = 1 := by
    have e : (nrmL n w (locEl n w δ)).val.charpoly =
        (δ * thE E n δ).val.charpoly.map (algebraMap E (w.adicCompletion E)) := by
      rw [hNe]; exact Matrix.charpoly_map _ _
    rw [e]; exact hb
  have hcomm : ∀ t ∈ twCent (thL n w) (locEl n w δ),
      t * nrmL n w (locEl n w δ) = nrmL n w (locEl n w δ) * t := by
    intro t ht
    have ht' : t * locEl n w δ = locEl n w δ * thL n w t := ht
    generalize locEl n w δ = y at ht' ⊢
    by_cases hsp : IsSplitAt w
    · have hθ1 : thL n w = MonoidHom.id _ := by unfold thL; rw [if_pos hsp]
      have hn1 : nrmL n w y = y := by unfold nrmL; rw [if_pos hsp]
      rw [hn1]; rw [hθ1] at ht'; simpa using ht'
    · have hn1 : nrmL n w y = y * thL n w y := by
        unfold nrmL; rw [if_neg hsp]; unfold thL; rw [if_neg hsp]
      rw [hn1]
      calc t * (y * thL n w y) = y * thL n w t * thL n w y := by rw [← mul_assoc, ht']
        _ = y * thL n w (t * y) := by simp only [map_mul, mul_assoc]
        _ = y * thL n w (y * thL n w t) := by rw [ht']
        _ = y * thL n w y * t := by simp only [map_mul, hinv, mul_assoc]
  refine le_antisymm (le_inf ((Subgroup.closure_le _).2 fun t ht => ht.1) ((Subgroup.closure_le _).2 fun t ht => ?_)) ?_
  · exact GlobalTheory.StabInt.mem_KGL_of_commute E n w _ t hNK hgood (hcomm t ht.1) ht.2
  · intro t ht
    refine Subgroup.subset_closure ⟨ht.1, ?_⟩
    refine hKc.of_isClosed_subset isClosed_closure (closure_minimal ?_ hKc.isClosed)
    exact (Subgroup.zpowers_le.2 ht.2 : _)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.OrbitNormCounting.Transl
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

private theorem phi_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (a : ℕ) :
    (GlobalTheory.Tw.Phi a R).map f = GlobalTheory.Tw.Phi a S := by
  ext i j
  simp only [Matrix.map_apply, GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

private theorem phi_mul_transpose {R : Type} [CommRing R] (a : ℕ) :
    GlobalTheory.Tw.Phi a R * (GlobalTheory.Tw.Phi a R)ᵀ = 1 := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, GlobalTheory.Tw.Phi, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single i.rev]
  · have h1 : (i : ℕ) + (i.rev : ℕ) + 1 = a := by rw [Fin.val_rev]; omega
    rw [if_pos h1]
    by_cases h : i = k
    · subst h
      rw [if_pos h1, if_pos rfl, ← mul_pow]
      simp
    · rw [if_neg (fun h2 => h (Fin.ext (by rw [Fin.val_rev] at h2; omega))), if_neg h, mul_zero]
  · intro j _ hj
    rw [if_neg (fun h => hj (Fin.ext (by rw [Fin.val_rev]; omega))), zero_mul]
  · simp

private theorem exists_scalar (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    ∃ z : E, z ≠ 0 ∧ z = (-1) ^ (n - 1) * IsCMField.complexConj E z := by
  rcases Nat.even_or_odd (n - 1) with h | h
  · exact ⟨1, one_ne_zero, by simp [h.neg_one_pow]⟩
  · have hx : ∃ x : E, IsCMField.complexConj E x ≠ x := by
      by_contra hc
      push_neg at hc
      exact IsCMField.complexConj_ne_one E (AlgEquiv.ext hc)
    obtain ⟨x, hx⟩ := hx
    refine ⟨x - IsCMField.complexConj E x, sub_ne_zero.mpr hx.symm, ?_⟩
    rw [h.neg_one_pow, map_sub, IsCMField.complexConj_apply_apply]
    ring

private def uMat {E : Type} [Field E] (n : ℕ) (z : E) (hz : z ≠ 0) : GL (Fin n) E where
  val := z • GlobalTheory.Tw.Phi n E
  inv := z⁻¹ • (GlobalTheory.Tw.Phi n E)ᵀ
  val_inv := by
    rw [Matrix.smul_mul, Matrix.mul_smul, phi_mul_transpose, smul_smul, mul_inv_cancel₀ hz, one_smul]
  inv_val := by
    rw [Matrix.smul_mul, Matrix.mul_smul, mul_eq_one_comm.mp (phi_mul_transpose n), smul_smul,
      inv_mul_cancel₀ hz, one_smul]

theorem UpperTheory.ConvolutionTheory.G3.transl :
    UpperTheory.ConvolutionTheory.G3.Transl := by
  intro E _ _ _ _ n
  obtain ⟨z, hz0, hz⟩ := exists_scalar E n
  have hΦΦ : GlobalTheory.Tw.Phi n E * GlobalTheory.Tw.Phi n E = ((-1 : E) ^ (n - 1)) • (1 : Matrix (Fin n) (Fin n) E) :=
    GlobalTheory.LocTwist.Phi_mul_self n
  refine ⟨uMat n z hz0, ?_, ?_, ?_⟩
  · intro g
    apply Units.ext
    have hL : (thE E n g).val = GlobalTheory.Tw.Phi n E *
        ((g⁻¹ : GL (Fin n) E).val.map (IsCMField.complexConj E))ᵀ * (GlobalTheory.Tw.Phi n E)ᵀ :=
      GlobalTheory.LocTwist.thetaGL_val n _ g
    have hR : ((uMat n z hz0) * UpperTheory.ConvolutionTheory.D.th (IsCMField.complexConj E) g * (uMat n z hz0)⁻¹).val =
        (z • GlobalTheory.Tw.Phi n E) * ((g⁻¹ : GL (Fin n) E).val.map (IsCMField.complexConj E))ᵀ *
          (z⁻¹ • (GlobalTheory.Tw.Phi n E)ᵀ) := rfl
    rw [hL, hR, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hz0, one_smul]
  · apply Units.ext
    have hc : (IsCMField.complexConj E z)⁻¹ * z * (-1) ^ (n - 1) = 1 := by
      have hcz : IsCMField.complexConj E z ≠ 0 := (_root_.map_ne_zero _).mpr hz0
      have hs : ((-1 : E) ^ (n - 1)) * (-1) ^ (n - 1) = 1 := by rw [← mul_pow]; simp
      have e : (IsCMField.complexConj E z)⁻¹ * z * (-1) ^ (n - 1) =
          ((IsCMField.complexConj E z)⁻¹ * IsCMField.complexConj E z) * (((-1 : E) ^ (n - 1)) * (-1) ^ (n - 1)) := by
        rw [show (IsCMField.complexConj E z)⁻¹ * z * (-1) ^ (n - 1) =
          (IsCMField.complexConj E z)⁻¹ * ((-1) ^ (n - 1) * IsCMField.complexConj E z) * (-1) ^ (n - 1) by rw [← hz]]
        ring
      rw [e, inv_mul_cancel₀ hcz, hs, one_mul]
    have hm : ((GlobalTheory.Tw.Phi n E)ᵀ.map (IsCMField.complexConj E))ᵀ = GlobalTheory.Tw.Phi n E := by
      rw [Matrix.transpose_map, Matrix.transpose_transpose]
      exact phi_map ((IsCMField.complexConj E : E →+* E)) n
    have hL : ((uMat n z hz0) * UpperTheory.ConvolutionTheory.D.th (IsCMField.complexConj E) (uMat n z hz0)).val =
        (z • GlobalTheory.Tw.Phi n E) * (((z⁻¹ • (GlobalTheory.Tw.Phi n E)ᵀ)).map (IsCMField.complexConj E))ᵀ := rfl
    have hs : ((z⁻¹ • (GlobalTheory.Tw.Phi n E)ᵀ)).map (IsCMField.complexConj E) =
        (IsCMField.complexConj E z)⁻¹ • ((GlobalTheory.Tw.Phi n E)ᵀ.map (IsCMField.complexConj E)) := by
      ext i j
      simp
    rw [hL, hs, Matrix.transpose_smul, hm, Matrix.smul_mul, Matrix.mul_smul, hΦΦ, smul_smul, smul_smul,
      Units.val_one, mul_comm z, hc, one_smul]
  · intro w hw g
    have ht : thL n w = thetaGL n (cj w) := by rw [thL, if_neg hw]
    have hf : algebraMap E (w.adicCompletion E) z ≠ 0 := (_root_.map_ne_zero _).mpr hz0
    have h1 : (uMat n z hz0).val.map (algebraMap E (w.adicCompletion E)) =
        algebraMap E (w.adicCompletion E) z • GlobalTheory.Tw.Phi n (w.adicCompletion E) := by
      rw [← phi_map (algebraMap E (w.adicCompletion E)) n]
      ext i j
      simp [uMat]
    have h2 : ((uMat n z hz0)⁻¹ : GL (Fin n) E).val.map (algebraMap E (w.adicCompletion E)) =
        (algebraMap E (w.adicCompletion E) z)⁻¹ • (GlobalTheory.Tw.Phi n (w.adicCompletion E))ᵀ := by
      rw [← phi_map (algebraMap E (w.adicCompletion E)) n]
      ext i j
      simp [uMat]
    rw [ht, GlobalTheory.LocTwist.thetaGL_val, h1, h2, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
      inv_mul_cancel₀ hf, one_smul]
    rfl
end

