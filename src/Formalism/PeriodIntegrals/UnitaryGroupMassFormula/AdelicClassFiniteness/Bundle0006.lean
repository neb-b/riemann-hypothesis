module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.HformSmulRight
public import Mathlib

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.SuccessiveVectorGramDet
section
noncomputable section

namespace PIW.AdelClassFin

open Formalism.UG NumberField
open scoped Matrix

section GD

variable {E : Type} [Field E] [NumberField E] [StarRing E] {m : ℕ} (J : Matrix (Fin m) (Fin m) E)

theorem gd_qsmul (q : ℚ) (x : Fin m → E) : q • x = ((q : E)) • x := by
  ext i
  simp [Rat.smul_def]

theorem gd_star_rat (q : ℚ) : star ((q : E)) = (q : E) := by
  first
    | exact star_ratCast q
    | simpa [starRingEnd_apply] using map_ratCast (starRingEnd E) q

def gdLeft (y : Fin m → E) : (Fin m → E) →ₗ[ℚ] ℚ where
  toFun x := Algebra.trace ℚ E (hform (starRingEnd E) J x y)
  map_add' x x' := by rw [hform_add_left', map_add (f := _)]
  map_smul' q x := by
    rw [gd_qsmul, hform_smul_left', gd_star_rat, RingHom.id_apply, smul_eq_mul, ← Rat.smul_def, map_smul,
      smul_eq_mul]

def gdRight (x : Fin m → E) : (Fin m → E) →ₗ[ℚ] ℚ where
  toFun y := Algebra.trace ℚ E (hform (starRingEnd E) J x y)
  map_add' y y' := by rw [hform_add_right', map_add (f := _)]
  map_smul' q y := by
    rw [gd_qsmul, hform_smul_right', RingHom.id_apply, smul_eq_mul, ← Rat.smul_def, map_smul, smul_eq_mul]

theorem gd_int_smul (c : ℤ) (x : Fin m → E) : ((c : E)) • x = ((c : ℚ)) • x := by
  rw [gd_qsmul, Rat.cast_intCast]

end GD

theorem successive_vector_gram_det : SvGramDet := by
  classical
  intro F E _ _ _ _ _ _ cm m d δ hd hδ hcod p hp e hli he hspan
  simp only [Lat, Set.mem_setOf_eq] at hp
  obtain ⟨hJh, hJdet, -, -, hMint, hMdual⟩ := hp
  set J := p.1 with hJdef
  set M := p.2 with hMdef
  have hO : ∀ b : E, b ∈ (algebraMap (𝓞 E) E).range → star b ∈ (algebraMap (𝓞 E) E).range := by
    intro b hb
    obtain ⟨β, rfl⟩ := RingHom.mem_range.mp hb
    have hint : IsIntegral ℤ (starRingEnd E (algebraMap (𝓞 E) E β)) :=
      IsIntegral.map (starRingEnd E).toIntAlgHom β.isIntegral_coe
    exact RingHom.mem_range.mpr ((IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp hint)
  have F1 : ∀ x y : Fin m → E,
      hform (starRingEnd E) J x y = (fun i => starRingEnd E (x i)) ⬝ᵥ (J *ᵥ y) := by
    intro x y
    simp only [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hsingle : ∀ (i : Fin m) (v : Fin m → E), hform (starRingEnd E) J (Pi.single i 1) v = (J *ᵥ v) i := by
    intro i v
    rw [F1]
    have hs : (fun a => starRingEnd E ((Pi.single i (1 : E) : Fin m → E) a)) = Pi.single i 1 := by
      funext a
      by_cases h : a = i
      · subst h
        simp
      · simp [Pi.single_apply, h]
    rw [hs]
    first
      | rw [single_dotProduct, one_mul]
      | simp [dotProduct, Pi.single_apply]
  have hnd : ∀ y : Fin m → E, (∀ x, hform (starRingEnd E) J x y = 0) → y = 0 := by
    intro y hy
    have hJy : J *ᵥ y = 0 := by
      funext i
      rw [← hsingle, Pi.zero_apply]
      exact hy _
    have h6 : y = J⁻¹ *ᵥ (J *ᵥ y) := by
      rw [Matrix.mulVec_mulVec y J⁻¹ J, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hJdet),
        Matrix.one_mulVec]
    rw [h6, hJy, Matrix.mulVec_zero]
  have htr : ∀ z : E, (∀ b : E, Algebra.trace ℚ E (b * z) = 0) → z = 0 := by
    intro z hz
    by_contra hne
    have h1 := hz z⁻¹
    rw [inv_mul_cancel₀ hne, ← map_one (algebraMap ℚ E), Algebra.trace_algebraMap, nsmul_eq_mul,
      mul_one, Nat.cast_eq_zero] at h1
    exact (Module.finrank_pos (R := ℚ) (M := E)).ne' h1
  have hRt : ∀ x y, gdRight J x y = Algebra.trace ℚ E (hform (starRingEnd E) J x y) := fun x y => rfl
  have hLt : ∀ x y, gdLeft J y x = Algebra.trace ℚ E (hform (starRingEnd E) J x y) := fun x y => rfl
  have Br : ∀ (x : Fin m → E) (q : Fin (m * Module.finrank ℚ E) → ℚ),
      Algebra.trace ℚ E (hform (starRingEnd E) J x (∑ k, q k • e k)) =
        ∑ k, q k * Algebra.trace ℚ E (hform (starRingEnd E) J x (e k)) := by
    intro x q
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hRt, map_sum]
    simp only [map_smul, smul_eq_mul]
    simp only [hRt]
  have Bl : ∀ (y : Fin m → E) (q : Fin (m * Module.finrank ℚ E) → ℚ),
      Algebra.trace ℚ E (hform (starRingEnd E) J (∑ k, q k • e k) y) =
        ∑ k, q k * Algebra.trace ℚ E (hform (starRingEnd E) J (e k) y) := by
    intro y q
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hLt, map_sum]
    simp only [map_smul, smul_eq_mul]
    simp only [hLt]
  have hGe : ∀ i j, gramTr J e i j = Algebra.trace ℚ E (hform (starRingEnd E) J (e i) (e j)) :=
    fun i j => rfl
  have hdetG : (gramTr J e).det ≠ 0 := by
    rcases isEmpty_or_nonempty (Fin (m * Module.finrank ℚ E)) with hE | hE
    · rw [Matrix.det_isEmpty]
      exact one_ne_zero
    have hcard : Fintype.card (Fin (m * Module.finrank ℚ E)) = Module.finrank ℚ (Fin m → E) := by
      rw [Fintype.card_fin]
      first
        | simp [Module.finrank_pi_fintype]
        | rw [Module.finrank_pi_fintype]; simp
    let bs := basisOfLinearIndependentOfCardEqFinrank hli hcard
    have hbs : ∀ i, bs i = e i := fun i => by simp [bs]
    rw [Ne, ← Matrix.exists_mulVec_eq_zero_iff]
    rintro ⟨v, hv0, hv⟩
    have hy : ∑ j, v j • e j = 0 := by
      apply hnd
      intro x
      apply htr
      intro b
      have e1 : b * hform (starRingEnd E) J x (∑ j, v j • e j) =
          hform (starRingEnd E) J (star b • x) (∑ j, v j • e j) := by
        rw [hform_smul_left', star_star]
      rw [e1]
      have hf : gdLeft J (∑ j, v j • e j) = 0 := by
        refine bs.ext fun i => ?_
        rw [hbs, LinearMap.zero_apply, hLt, Br]
        have h2 := congrFun hv i
        rw [Pi.zero_apply] at h2
        refine Eq.trans ?_ h2
        simp only [Matrix.mulVec, dotProduct]
        exact Finset.sum_congr rfl fun k _ => by rw [hGe, mul_comm]
      have h3 := LinearMap.congr_fun hf (star b • x)
      rw [LinearMap.zero_apply, hLt] at h3
      exact h3
    apply hv0
    funext i
    exact (Fintype.linearIndependent_iff.mp hli) v hy i
  refine ⟨hdetG, ?_⟩
  set Gi := (gramTr J e)⁻¹ with hGi
  have hGGi : gramTr J e * Gi = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdetG)
  obtain ⟨w, hw⟩ : ∃ w : Fin (m * Module.finrank ℚ E) → Fin m → E,
      ∀ j, w j = ∑ k, Gi k j • e k := ⟨_, fun j => rfl⟩
  have hBw : ∀ i j, Algebra.trace ℚ E (hform (starRingEnd E) J (e i) (w j)) =
      (1 : Matrix (Fin (m * Module.finrank ℚ E)) (Fin (m * Module.finrank ℚ E)) ℚ) i j := by
    intro i j
    rw [hw, Br, ← hGGi, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [hGe, mul_comm]
  have hint : ∀ x ∈ M, ∀ j, Algebra.trace ℚ E (hform (starRingEnd E) J x (w j)) ∈
      (algebraMap ℤ ℚ).range := by
    intro x hx j
    obtain ⟨c, rfl⟩ := hspan x hx
    have e2 : ∑ i, ((c i : ℤ) : E) • e i = ∑ i, ((c i : ℚ)) • e i :=
      Finset.sum_congr rfl fun i _ => gd_int_smul _ _
    rw [e2, Bl]
    simp only [hBw, Matrix.one_apply]
    refine RingHom.mem_range.mpr ⟨c j, ?_⟩
    simp
  have hdual : ∀ j, (d : E) • ((δ : E) • w j) ∈ M := by
    intro j
    apply hMdual
    intro x hx
    rw [hform_smul_right']
    apply hcod
    intro a
    have hsa : star (algebraMap (𝓞 E) E a) • x ∈ M := by
      obtain ⟨a', ha'⟩ := RingHom.mem_range.mp (hO _ (RingHom.mem_range.mpr ⟨a, rfl⟩))
      rw [← ha', algebraMap_smul]
      exact M.smul_mem a' hx
    have e3 : algebraMap (𝓞 E) E a * hform (starRingEnd E) J x (w j) =
        hform (starRingEnd E) J (star (algebraMap (𝓞 E) E a) • x) (w j) := by
      rw [hform_smul_left', star_star]
    rw [e3]
    exact hint _ hsa j
  have hn : ∀ (n : ℕ) (v : Fin m → E), (n : E) • v = (n : ℚ) • v := fun n v => by
    rw [gd_qsmul, Rat.cast_natCast]
  have hC : ∀ j, ∃ C : Fin (m * Module.finrank ℚ E) → ℤ,
      ∀ k, (C k : ℚ) = (d : ℚ) * (δ : ℚ) * Gi k j := by
    intro j
    obtain ⟨C, hCe⟩ := hspan _ (hdual j)
    refine ⟨C, ?_⟩
    have e4 : (d : E) • ((δ : E) • w j) = ∑ k, ((d : ℚ) * (δ : ℚ) * Gi k j) • e k := by
      rw [hn, hn, hw, Finset.smul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul, smul_smul, mul_assoc]
    have e5 : ∑ k, ((C k : ℚ) - (d : ℚ) * (δ : ℚ) * Gi k j) • e k = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [sub_eq_zero, ← e4, hCe]
      exact Finset.sum_congr rfl fun k _ => (gd_int_smul _ _).symm
    intro k
    exact sub_eq_zero.mp ((Fintype.linearIndependent_iff.mp hli) _ e5 k)
  choose C hCj using hC
  set C' : Matrix (Fin (m * Module.finrank ℚ E)) (Fin (m * Module.finrank ℚ E)) ℤ :=
    Matrix.of fun k j => C j k with hC'
  have hdq : (0 : ℚ) < (d : ℚ) * (δ : ℚ) := by
    have h1 : (0 : ℚ) < d := Nat.cast_pos.mpr hd
    have h2 : (0 : ℚ) < δ := Nat.cast_pos.mpr hδ
    positivity
  have hCm : C'.map (Int.cast : ℤ → ℚ) = ((d : ℚ) * (δ : ℚ)) • Gi := by
    ext k j
    simp [hC', hCj]
  have hdetC : ((C'.det : ℤ) : ℚ) =
      ((d : ℚ) * (δ : ℚ)) ^ (m * Module.finrank ℚ E) * ((gramTr J e).det)⁻¹ := by
    have h1 : ((C'.det : ℤ) : ℚ) = (C'.map (Int.cast : ℤ → ℚ)).det := (Int.castRingHom ℚ).map_det C'
    rw [h1, hCm, Matrix.det_smul, Fintype.card_fin, hGi, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have hCne : C'.det ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero] at hdetC
    exact mul_ne_zero (pow_ne_zero _ hdq.ne') (inv_ne_zero hdetG) hdetC.symm
  have h1 : (1 : ℚ) ≤ |((C'.det : ℤ) : ℚ)| := by exact_mod_cast Int.one_le_abs hCne
  have hpos : 0 < |(gramTr J e).det| := abs_pos.mpr hdetG
  set X := ((d : ℚ) * (δ : ℚ)) ^ (m * Module.finrank ℚ E) with hX
  have hXpos : 0 < X := pow_pos hdq _
  rw [hdetC, abs_mul, abs_inv, abs_of_pos hXpos] at h1
  have key : |(gramTr J e).det| ≤ X := by
    have h2 := mul_le_mul_of_nonneg_left h1 hpos.le
    rwa [mul_one, mul_comm X, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at h2
  rw [hX] at key
  push_cast
  exact key

end PIW.AdelClassFin

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.SuccessiveVectorMajorantE
section
noncomputable section

namespace PIW.AdelClassFin

open Formalism.UG NumberField Matrix
open scoped ComplexOrder

theorem svM_conj_form {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (d z : Fin n → ℂ) :
    star z ⬝ᵥ ((U * diagonal d * star U) *ᵥ z) =
      ∑ i, star ((star U *ᵥ z) i) * (d i * (star U *ᵥ z) i) := by
  rw [Matrix.star_eq_conjTranspose, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec]
  have h : star z ᵥ* U = star (Uᴴ *ᵥ z) := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
  rw [h]
  simp only [dotProduct, Pi.star_apply, Matrix.mulVec_diagonal]

theorem svM_term (r : ℝ) (w : ℂ) : star w * ((r : ℂ) * w) = ((r * ‖w‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Complex.star_def, Complex.ofReal_mul, Complex.ofReal_pow]
  rw [mul_left_comm, Complex.conj_mul']

theorem successive_vector_majorant : SvMaj := by
  intro n J hJ hdet
  set U : Matrix (Fin n) (Fin n) ℂ := (hJ.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef
  set ev := hJ.eigenvalues with hev
  have hspec : J = U * diagonal (fun i => ((ev i : ℝ) : ℂ)) * star U := by
    have h := hJ.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have hUU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hJ.eigenvectorUnitary.2
  have hUU' : U * star U = 1 := Matrix.mem_unitaryGroup_iff.1 hJ.eigenvectorUnitary.2
  have hev0 : ∀ i, ev i ≠ 0 := by
    intro i h
    apply hdet
    rw [hJ.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [← hev, h]; simp)
  refine ⟨U * diagonal (fun i => ((|ev i| : ℝ) : ℂ)) * star U, ?_, ?_, ?_⟩
  · have hD : (diagonal (fun i => ((|ev i| : ℝ) : ℂ))).PosDef := by
      rw [Matrix.posDef_diagonal_iff]
      intro i
      exact Complex.zero_lt_real.2 (abs_pos.2 (hev0 i))
    have hinj : Function.Injective (star U).mulVec := by
      intro x y hxy
      have := congrArg (fun v => U *ᵥ v) hxy
      simpa [Matrix.mulVec_mulVec, hUU'] using this
    have h2 := hD.conjTranspose_mul_mul_same hinj
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
      ← Matrix.star_eq_conjTranspose] at h2
  · have hdU : U.det * (star U).det = 1 := by rw [← Matrix.det_mul, hUU', Matrix.det_one]
    rw [Matrix.det_mul, Matrix.det_mul, mul_right_comm, hdU, one_mul, Matrix.det_diagonal,
      hJ.det_eq_prod_eigenvalues, norm_prod]
    push_cast
    apply Finset.prod_congr rfl
    intro i _
    simp [hev]
  · intro z
    rw [hspec, svM_conj_form, svM_conj_form]
    simp only [svM_term]
    rw [← Complex.ofReal_sum, ← Complex.ofReal_sum, Complex.norm_real, Complex.ofReal_re,
      Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [abs_mul, abs_sq]

theorem successive_vector_majorant_e : SvMajE := by
  intro F E _ _ _ _ _ _ hCM m J hJ hdet
  have hstar : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a) := hCM.cmUnram.2.1
  have hTC : NumberField.IsTotallyComplex E := hCM.cmUnram.1
  have hne : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ ≠ φ := by
    intro φ h
    have hc := hTC.isComplex (InfinitePlace.mk φ)
    rw [InfinitePlace.isComplex_mk_iff] at hc
    exact hc (ComplexEmbedding.isReal_iff.2 h)
  have hJe : ∀ i j, star (J j i) = J i j := by
    intro i j
    have := congrFun (congrFun hJ i) j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this
    exact this
  have hherm : ∀ φ : E →+* ℂ, (J.map φ).IsHermitian := by
    intro φ
    refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [Matrix.map_apply]
    rw [← hJe i j, hstar]
    rfl
  have hdetφ : ∀ φ : E →+* ℂ, (J.map φ).det ≠ 0 := by
    intro φ
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero φ).2 hdet
  have hmapT : ∀ M : Matrix (Fin m) (Fin m) ℂ, M.IsHermitian → M.map (starRingEnd ℂ) = Mᵀ := by
    intro M hM
    ext i j
    rw [Matrix.map_apply, Matrix.transpose_apply, ← hM.apply j i]
    rfl
  have hid : ∀ (N : Matrix (Fin m) (Fin m) ℂ) (z : Fin m → ℂ),
      star z ⬝ᵥ (N.map (starRingEnd ℂ) *ᵥ z) = starRingEnd ℂ (z ⬝ᵥ (N *ᵥ star z)) := by
    intro N z
    set_option synthInstance.maxHeartbeats 100000 in
      simp [dotProduct, mulVec, map_sum, map_mul]
  choose H0 hH0 using fun φ : E →+* ℂ => successive_vector_majorant m (J.map φ) (hherm φ) (hdetφ φ)
  let ι := Fintype.equivFin (E →+* ℂ)
  refine ⟨fun φ => if ι φ < ι (ComplexEmbedding.conjugate φ) then H0 φ
    else (H0 (ComplexEmbedding.conjugate φ)).map (starRingEnd ℂ), ?_⟩
  intro φ
  have hcc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := star_star φ
  by_cases hp : ι φ < ι (ComplexEmbedding.conjugate φ)
  · have hp' : ¬ ι (ComplexEmbedding.conjugate φ) < ι φ := lt_asymm hp
    simp only [if_pos hp]
    refine ⟨(hH0 φ).1, (hH0 φ).2.1, (hH0 φ).2.2, ?_⟩
    rw [hcc, if_neg hp']
  · set ψ := ComplexEmbedding.conjugate φ with hψ
    have hψφ : ι ψ < ι (ComplexEmbedding.conjugate ψ) := by
      rw [hψ, hcc]
      refine lt_of_le_of_ne (not_lt.1 hp) fun h => hne φ (ι.injective h.symm ▸ rfl)
    have hJφ : J.map φ = (J.map ψ).map (starRingEnd ℂ) := by
      ext i j
      simp [hψ, ComplexEmbedding.conjugate_coe_eq]
    have hM := hH0 ψ
    simp only [if_neg hp, if_pos hψφ, ← hψ]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hmapT _ hM.1.1]
      exact hM.1.transpose
    · have hdc : ∀ N : Matrix (Fin m) (Fin m) ℂ,
          (N.map (starRingEnd ℂ)).det = starRingEnd ℂ N.det := fun N => by
        rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      rw [hmapT _ hM.1.1, Matrix.det_transpose, hM.2.1, hJφ, hdc, Complex.norm_conj]
    · intro z
      have h1 := hM.2.2 (star z)
      rw [star_star] at h1
      rw [hJφ, hid, hid, Complex.norm_conj, Complex.conj_re]
      exact h1
    · rw [Matrix.map_map]
      ext i j
      simp

end PIW.AdelClassFin
end
end

