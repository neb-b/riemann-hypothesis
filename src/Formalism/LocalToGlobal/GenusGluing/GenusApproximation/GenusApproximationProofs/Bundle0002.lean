module

public import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.FactsW
public import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.Bundle0001

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.ApproximationAdelicHolds
section
noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

theorem approximationAdelic_holds : ApproxA := by
  intro F E _ _ _ _ _ D hD u
  obtain ⟨d, hd, hdu⟩ := Formalism.UG.P.levelaf_denom (F := F) (E := E) u
  obtain ⟨b0, t, ht, heq⟩ :=
    Formalism.UG.P.csGlob_approx Formalism.UG.P.integral_adele_approximation_holds (d * D) (mul_ne_zero hd hD) _ hdu
  have hlevel (a : 𝓞 F) : Formalism.UG.P.levelafC E a = iA F E (algebraMap (𝓞 F) E a) := by
    have h := Formalism.UG.P.csGlob_tmul_int (F := F) (E := E) (1 : E) a
    rw [mul_one] at h
    exact h
  rw [hlevel, hlevel] at heq
  have hdE : algebraMap (𝓞 F) E d ≠ 0 := by
    intro h0
    apply hd
    exact (FaithfulSMul.algebraMap_injective (𝓞 F) E) (by rw [h0, map_zero])
  have hinv : iA F E (algebraMap (𝓞 F) E d)⁻¹ * iA F E (algebraMap (𝓞 F) E d) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hdE, map_one]
  refine ⟨(algebraMap (𝓞 F) E d)⁻¹ * algebraMap (𝓞 E) E b0, t, ht, ?_⟩
  calc u = iA F E (algebraMap (𝓞 F) E d)⁻¹ * (iA F E (algebraMap (𝓞 F) E d) * u) := by
        rw [← mul_assoc, hinv, one_mul]
    _ = iA F E (algebraMap (𝓞 F) E d)⁻¹ * (iA F E (algebraMap (𝓞 E) E b0) +
          iA F E (algebraMap (𝓞 F) E d) * iA F E (algebraMap (𝓞 F) E D) * t) := by
        rw [heq, map_mul (algebraMap (𝓞 F) E) d D, map_mul (iA F E)]
    _ = _ := by
        rw [mul_add, ← mul_assoc, ← mul_assoc, hinv, one_mul, map_mul]

theorem unitNearOne_holds : UnitNear := by
  intro F E _ _ _ _ _ _ hc v π hπ n s hs
  classical
  set S := Formalism.L2.Herm.intAf F E with hS
  let st : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨s i j, hs i j⟩
  let et : S := Formalism.L2.DIV.adS F E (Formalism.L2.DIV.idemAd (fun w => w = v))
  let pt : S := Formalism.L2.DIV.oToS F E (algebraMap (𝓞 F) (𝓞 E) π)
  let Mt : Matrix (Fin n) (Fin n) S := et • (1 - pt • st) + (1 - et) • (1 : Matrix (Fin n) (Fin n) S)
  have hMt : IsUnit Mt := by
    refine Formalism.L2.DIV.isUnit_matrix_of_resS hc Mt fun PP => ?_
    have h1 : Mt.map (Formalism.L2.DIV.resS F PP) = 1 := by
      by_cases hw : Formalism.L2.DIV.underPl F PP = v
      · have he : Formalism.L2.DIV.resS F PP et = 1 :=
          Formalism.L2.DIV.resS_idemAd_pos PP (Formalism.L2.DIV.underPl F PP) rfl hw
        have hp : Formalism.L2.DIV.resS F PP pt = 0 := by
          show Formalism.L2.DIV.resS F PP (Formalism.L2.DIV.oToS F E (algebraMap (𝓞 F) (𝓞 E) π)) = 0
          rw [Formalism.L2.DIV.resS_oToS, Ideal.Quotient.eq_zero_iff_mem]
          have : π ∈ (Formalism.L2.DIV.underPl F PP).asIdeal := by rw [hw]; exact hπ
          exact this
        ext i j
        by_cases hij : i = j <;>
          simp [Mt, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
            he, hp, hij]
      · have he : Formalism.L2.DIV.resS F PP et = 0 :=
          Formalism.L2.DIV.resS_idemAd_neg PP (Formalism.L2.DIV.underPl F PP) rfl hw
        ext i j
        by_cases hij : i = j <;>
          simp [Mt, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
            he, hij]
    rw [h1, Matrix.det_one]
    exact one_ne_zero
  obtain ⟨U, hU⟩ := hMt
  set e := eAt E v with he_def
  have hee : e * e = e := by
    rw [he_def, show eAt E v = eP E (fun w => w = v) from rfl, (idempotentCalculation_holds F E).2.1]
    exact eP_congr (fun u => and_self_iff)
  have het : ((et : S) : E ⊗[F] Formalism.L2.Herm.Af F) = e := rfl
  have hpt : ((pt : S) : E ⊗[F] Formalism.L2.Herm.Af F) = iA F E (algebraMap (𝓞 F) E π) := by
    show algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) π) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F) = _
    rw [← IsScalarTower.algebraMap_apply]
    rfl
  let φ := (S.subtype).mapMatrix (m := Fin n)
  refine ⟨((U⁻¹ : (Matrix (Fin n) (Fin n) S)ˣ) : Matrix (Fin n) (Fin n) S).map S.subtype,
    fun i j => (((U⁻¹ : (Matrix (Fin n) (Fin n) S)ˣ) : Matrix (Fin n) (Fin n) S) i j).2, ?_⟩
  have hMR : Mt * ((U⁻¹ : (Matrix (Fin n) (Fin n) S)ˣ) : Matrix (Fin n) (Fin n) S) = 1 := by
    rw [← hU]; exact U.mul_inv
  set_option synthInstance.maxHeartbeats 200000 in
  have hφ : φ Mt = glueM e (1 - iA F E (algebraMap (𝓞 F) E π) • s) := by
    change Mt.map S.subtype = _
    ext i j
    by_cases hij : i = j <;>
      simp [Mt, glueM, st, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
        het, hpt, hij]
  have h2 := congrArg φ hMR
  rw [map_mul, map_one, hφ] at h2
  rw [← glue_smul_same hee]
  exact congrArg (fun M => e • M) h2

theorem integralAtInverse_holds : IntAtInv := by
  intro F E _ _ _ _ _ _ hc n v y hy hI
  have hJ : (1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hy' : Formalism.UG.cT (Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F))
      ((y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
      ((1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) *
      ((y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      ((1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) := hy
  rw [hJ, Matrix.mul_one] at hy'
  have hinv : (((y⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      Formalism.UG.cT (Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F))
        ((y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :=
    Units.inv_eq_of_mul_eq_one_left hy'
  have hσ : Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F) (eAt E v) = eAt E v := sigR_eP hc _
  intro i j
  rw [hinv]
  show eAt E v * Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F)
    (((y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) j i) ∈ _
  have hm := (Formalism.L2.DIV.sigS hc ⟨_, hI j i⟩).2
  rw [Formalism.L2.DIV.sigS_coe, map_mul, hσ] at hm
  exact hm

end Formalism.L2.GenusGluing.Gen
end
end

-- bundled from Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.DetAddDiagonalCons
section
noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

theorem det_add_diagonal_cons {A : Type*} [CommRing A] {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (a : A) (d : Fin n → A) :
    (M + diagonal (Fin.cons a d : Fin (n + 1) → A)).det =
      (M.submatrix Fin.succ Fin.succ + diagonal d).det * a +
        (M + diagonal (Fin.cons 0 d : Fin (n + 1) → A)).det := by
  set N := M + diagonal (Fin.cons 0 d : Fin (n + 1) → A) with hN
  have h1 : M + diagonal (Fin.cons a d : Fin (n + 1) → A) =
      N.updateRow 0 (N 0 + a • Pi.single 0 1) := by
    ext i j
    refine Fin.cases ?_ ?_ i
    · by_cases hj : j = 0
      · subst hj; simp [N]
      · simp [N, hj, Ne.symm hj]
    · intro i
      simp [N, Matrix.diagonal_apply]
  have h2 : (N.updateRow 0 (Pi.single 0 1)).det = (M.submatrix Fin.succ Fin.succ + diagonal d).det := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    have hz : ∀ k : Fin n, (N.updateRow 0 (Pi.single 0 1)) 0 k.succ = 0 := by
      intro k; simp [Fin.succ_ne_zero]
    simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
    simp only [Matrix.updateRow_self, Pi.single_eq_same, Fin.val_zero, pow_zero, one_mul,
      Fin.succAbove_zero]
    congr 1
    ext i j
    simp [N, Matrix.diagonal_apply]
  rw [h1, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self, h2]
  ring

theorem shiftDiag_of (hS : ShiftOne) : ShiftDiag := by
  intro F E _ _ _ _ _ _ hc v n
  induction n with
  | zero =>
    intro M
    refine ⟨Fin.elim0, fun i => i.elim0, 1, ?_⟩
    simp [Matrix.det_isEmpty]
  | succ n ih =>
    intro M
    obtain ⟨t', ht', w', hw'⟩ := ih (M.submatrix Fin.succ Fin.succ)
    obtain ⟨t0, ht0, w, hw⟩ := hS F E hc v _
      ((M + diagonal (Fin.cons 0 (fun i => iA F E (t' i)) : Fin (n + 1) → _)).det) ⟨w', hw'⟩
    refine ⟨Fin.cons t0 t', ?_, w, ?_⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · simpa using ht0
      · intro i; simpa using ht' i
    · have hf : (fun i => iA F E ((Fin.cons t0 t' : Fin (n + 1) → E) i)) =
          (Fin.cons (iA F E t0) (fun i => iA F E (t' i)) : Fin (n + 1) → _) := by
        funext i
        refine Fin.cases ?_ ?_ i
        · simp
        · intro i; simp
      rw [hf, det_add_diagonal_cons]
      exact hw

end Formalism.L2.GenusGluing.Gen
end
end

-- bundled from Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.EvaluationNeZeroHolds
section
noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem one_tmul_injective : Function.Injective (fun a : Formalism.L2.Herm.Af F => (1 : E) ⊗ₜ[F] a) := by
  have h := Algebra.TensorProduct.includeRight_injective (R := F) (A := E) (B := Formalism.L2.Herm.Af F)
    (algebraMap F E).injective
  intro a b hab
  apply h
  simpa [Algebra.TensorProduct.includeRight_apply] using hab

theorem eAt_eq (v : HeightOneSpectrum (𝓞 F)) :
    eAt E v = (1 : E) ⊗ₜ[F] ((Formalism.L2.DIV.idemAd (fun w => w = v) : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F) := rfl

end SlopeTestRemainingChoices

theorem evaluationNeZero_holds : EAtNeZero := by
  intro F E _ _ _ _ _ v h
  rw [eAt_eq, ← TensorProduct.tmul_zero (R := F) (Formalism.L2.Herm.Af F) (1 : E)] at h
  have h2 := one_tmul_injective h
  have h3 : ((Formalism.L2.DIV.idemAd (fun w => w = v) : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F) v =
      (0 : Formalism.L2.Herm.Af F) v := by rw [h2]
  rw [Formalism.L2.DIV.idemAd_pos (P := fun w => w = v) rfl] at h3
  exact one_ne_zero h3

theorem unitDichotomy_holds : UnitDich := by
  classical
  intro F E _ _ _ _ _ _ hc v u
  set σ := Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F) with hσ
  have hfix : σ (u * σ u) = u * σ u := by
    rw [map_mul, hσ, Formalism.L2.DIV.sigR_sigR, mul_comm]
  obtain ⟨a, ha⟩ := Formalism.L2.DIV.exists_adele_of_fixed hc _ hfix
  set idem : Formalism.L2.Herm.Af F := ((Formalism.L2.DIV.idemAd (fun w => w = v) : Formalism.UG.intAd F) : Formalism.L2.Herm.Af F)
    with hidem
  by_cases hav : a v = 0
  · left
    rw [ha, eAt_eq, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.tmul_zero (R := F)
      (Formalism.L2.Herm.Af F) (1 : E)]
    congr 1
    apply FiniteAdeleRing.ext
    intro w
    show idem w * a w = 0
    by_cases hw : w = v
    · subst hw; rw [hav, mul_zero]
    · rw [hidem, Formalism.L2.DIV.idemAd_neg (P := fun x => x = v) hw, zero_mul]
  · right
    let f : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F := fun w => if w = v then (a w)⁻¹ else 0
    have hf : ∀ᶠ w in Filter.cofinite, f w ∈ w.adicCompletionIntegers F := by
      filter_upwards [Filter.eventually_cofinite_ne v] with w hw
      simp only [f, if_neg hw]
      exact zero_mem _
    let a' : Formalism.L2.Herm.Af F := ⟨f, hf⟩
    have hprod : idem * a * a' = idem := by
      apply FiniteAdeleRing.ext
      intro w
      show idem w * a w * f w = idem w
      by_cases hw : w = v
      · subst hw
        simp only [f, if_pos rfl]
        rw [mul_assoc, mul_inv_cancel₀ hav, mul_one]
      · rw [hidem, Formalism.L2.DIV.idemAd_neg (P := fun x => x = v) hw, zero_mul, zero_mul]
    refine ⟨σ u * ((1 : E) ⊗ₜ[F] a'), ?_⟩
    rw [← mul_assoc u (σ u), ha, ← mul_assoc, eAt_eq, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul]
    simp only [one_mul]
    exact congrArg _ hprod

section Aux2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem exists_star_ne (hc : Formalism.BasicNotions.CMData F E) : ∃ θ : E, star θ ≠ θ := by
  by_contra h
  push Not at h
  have hb : Function.Bijective (algebraMap F E) :=
    ⟨(algebraMap F E).injective, fun x => by
      obtain ⟨y, hy⟩ := RingHom.mem_range.1 ((hc.fixed x).1 (h x))
      exact ⟨y, hy⟩⟩
  have h1 := Module.finrank_of_bijective_algebraMap hb
  rw [hc.deg2] at h1
  exact absurd h1 (by norm_num)

theorem exists_norm_one (hc : Formalism.BasicNotions.CMData F E) : ∃ t : E, star t * t = 1 ∧ star t - t ≠ 0 := by
  obtain ⟨θ, hθ⟩ := exists_star_ne hc
  set d : E := θ - star θ with hd_def
  have hd : star d = -d := by rw [hd_def, star_sub, star_star, neg_sub]
  have hd0 : d ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  have h2 : (2 : E) ≠ 0 := two_ne_zero
  have hs : (1 + d) ≠ 0 := by
    intro h
    have h' : star (1 + d) = 0 := by rw [h, star_zero]
    rw [star_add, star_one, hd] at h'
    exact h2 (by linear_combination h + h')
  have hsb : (1 - d) ≠ 0 := by
    intro h
    have h' : star (1 - d) = 0 := by rw [h, star_zero]
    rw [star_sub, star_one, hd] at h'
    exact h2 (by linear_combination h + h')
  have e1 : star ((1 + d) * (1 - d)⁻¹) = (1 + d)⁻¹ * (1 - d) := by
    rw [star_mul, star_inv₀, star_sub, star_add, star_one, hd, sub_neg_eq_add, ← sub_eq_add_neg]
  have hsi : (1 + d) * (1 + d)⁻¹ = 1 := mul_inv_cancel₀ hs
  have hsbi : (1 - d) * (1 - d)⁻¹ = 1 := mul_inv_cancel₀ hsb
  refine ⟨(1 + d) * (1 - d)⁻¹, ?_, ?_⟩
  · rw [e1]
    have hinv : (1 + d)⁻¹ * (1 + d) = 1 := inv_mul_cancel₀ hs
    linear_combination (1 - d) * (1 - d)⁻¹ * hinv + hsbi
  · rw [e1]
    intro h
    have h4 : (4 : E) * d = 0 := by
      linear_combination (-((1 + d) * (1 - d))) * h + (1 - d) ^ 2 * hsi - (1 + d) ^ 2 * hsbi
    rcases mul_eq_zero.1 h4 with h5 | h5
    · exact absurd h5 (by norm_num)
    · exact hd0 h5

end Aux2

theorem shiftOne_holds : ShiftOne := by
  intro F E _ _ _ _ _ _ hc v α β ⟨α', hα⟩
  set e := eAt E v with he_def
  set σ := Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F) with hσ
  have hσι : ∀ t : E, σ (iA F E t) = iA F E (star t) := fun t => rfl
  set b := β * α' with hb
  have win : ∀ t : E, star t * t = 1 → (∃ u', e * ((iA F E t + b) * u') = e) →
      ∃ t : E, star t * t = 1 ∧ ∃ w, e * ((α * iA F E t + β) * w) = e := by
    rintro t ht ⟨u', hu'⟩
    refine ⟨t, ht, α' * u', ?_⟩
    rw [hb] at hu'
    linear_combination hu' + (iA F E t * u') * hα
  obtain ⟨t3, ht3, hne⟩ := exists_norm_one hc
  rcases unitDichotomy_holds F E hc v (iA F E 1 + b) with h1 | h1
  swap
  · exact win 1 (by rw [star_one, one_mul]) h1
  rcases unitDichotomy_holds F E hc v (iA F E (-1) + b) with h2 | h2
  swap
  · exact win (-1) (by rw [star_neg, star_one, neg_mul_neg, one_mul]) h2
  rcases unitDichotomy_holds F E hc v (iA F E t3 + b) with h3 | h3
  swap
  · exact win t3 ht3 h3
  exfalso
  rw [map_add (f := _), hσι, star_one, map_one] at h1
  rw [map_add (f := _), hσι, star_neg, star_one, map_neg, map_one] at h2
  rw [map_add (f := _), hσι] at h3
  set sb := σ b
  set T := iA F E t3
  set S := iA F E (star t3)
  have hTS : S * T = 1 := by rw [← map_mul, ht3, map_one]
  set k := iA F E (star t3 - t3)⁻¹
  have hk : (S - T) * k = 1 := by rw [← map_sub, ← map_mul, mul_inv_cancel₀ hne, map_one]
  set half := iA F E (2 : E)⁻¹
  have hh : half * 2 = 1 := by
    rw [show (2 : E ⊗[F] Formalism.L2.Herm.Af F) = iA F E 2 from (map_ofNat (iA F E) 2).symm, ← map_mul,
      inv_mul_cancel₀ (two_ne_zero : (2 : E) ≠ 0), map_one]
  have A : e * (b + sb) = 0 := by linear_combination half * h1 - half * h2 - (e * (b + sb)) * hh
  have B : e * (1 + b * sb) = 0 := by linear_combination half * h1 + half * h2 - (e * (1 + b * sb)) * hh
  have C : e * b * (S - T) = 0 := by linear_combination h3 - B - T * A - e * hTS
  have D : e * b = 0 := by linear_combination k * C - (e * b) * hk
  have hE : e = 0 := by linear_combination B - sb * D
  exact evaluationNeZero_holds F E v hE

end Formalism.L2.GenusGluing.Gen
end
end

