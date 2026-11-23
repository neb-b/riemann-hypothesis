module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ExistsUnipotentDiagRotationLevelDecomposition
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem kgl_of {v : H.P ℚ} (y : GL (Fin 2) (H.Kv v)) (h1 : ∀ i j, y.val i j ∈ Formalism.UG.Ov ℚ v)
    (h2 : ∀ i j, (y⁻¹).val i j ∈ Formalism.UG.Ov ℚ v) : y ∈ GlobalTheory.LFun.KGL v (n := 2) := by
  rw [GlobalTheory.LFun.KGL, Formalism.UG.GLint, MonoidHom.mem_range]
  let M : Matrix (Fin 2) (Fin 2) (Formalism.UG.Ov ℚ v) := Matrix.of fun i j => ⟨_, h1 i j⟩
  let N : Matrix (Fin 2) (Fin 2) (Formalism.UG.Ov ℚ v) := Matrix.of fun i j => ⟨_, h2 i j⟩
  have hM : M.map (Formalism.UG.Ov ℚ v).subtype = y.val := by ext i j; rfl
  have hN : N.map (Formalism.UG.Ov ℚ v).subtype = (y⁻¹).val := by ext i j; rfl
  have inj : Function.Injective (fun A : Matrix (Fin 2) (Fin 2) (Formalism.UG.Ov ℚ v) => A.map (Formalism.UG.Ov ℚ v).subtype) :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨M, N, inj ?_, inj ?_⟩, Units.ext ?_⟩
  · simp only
    rw [Matrix.map_mul, hM, hN, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  · simp only
    rw [Matrix.map_mul, hM, hN, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  · exact hM

private theorem cp_rot (v : H.P ℚ) (t : ℝ) : Matrix.GeneralLinearGroup.map (H.cp v) (rot t) = 1 := by
  have h : Matrix.GeneralLinearGroup.map (pFin ℚ) (rot t) = 1 := TR.pFin_infGL _
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h2 := congrArg (fun x : GL (Fin 2) (Af ℚ) => pLoc ℚ v (x.val i j)) h
  change H.cp v ((rot t).val i j) = _ at h2
  change H.cp v ((rot t).val i j) = _
  rw [h2]
  fin_cases i <;> fin_cases j <;> simp

private theorem lev_of (N : ℕ) (t : ℝ) (k : G1 ℚ)
    (hr : Matrix.GeneralLinearGroup.map (TR.pInf ℚ) (gl k) = Matrix.GeneralLinearGroup.map (TR.pInf ℚ) (rot t))
    (hi : ∀ v i j, Valued.v (H.cp v (k i j)) ≤ 1)
    (hd : ∀ v i j, Dv N v (k i j - (1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j)) : Lev N ((rot t)⁻¹ * gl k) := by
  have e : ∀ v, Matrix.GeneralLinearGroup.map (H.cp v) ((rot t)⁻¹ * gl k) = Matrix.GeneralLinearGroup.map (H.cp v) (gl k) := by
    intro v
    rw [map_mul, map_inv, cp_rot, inv_one, one_mul]
  refine ⟨fun i j => ?_, fun v => ⟨?_, fun i j => ?_⟩⟩
  · have h : Matrix.GeneralLinearGroup.map (TR.pInf ℚ) ((rot t)⁻¹ * gl k) = Matrix.GeneralLinearGroup.map (TR.pInf ℚ) 1 := by
      rw [map_mul, map_inv, hr, inv_mul_cancel, map_one]
    exact (TR.infEq ℚ).symm.injective (congrArg (fun x : GL (Fin 2) (TR.Rinf ℚ) => x.val i j) h)
  · unfold H.KAt
    rw [e]
    refine kgl_of _ (fun i j => hi v i j) fun i j => ?_
    rw [← map_inv, ← map_inv]
    change Valued.v (H.cp v ((k⁻¹ : G1 ℚ) i j)) ≤ 1
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    fin_cases i <;> fin_cases j <;> simp [hi]
  · have h := congrArg (fun x : GL (Fin 2) (H.Kv v) => x.val i j) (e v)
    change H.cp v (((rot t)⁻¹ * gl k).val i j) = H.cp v (k i j) at h
    have h2 := hd v i j
    unfold Dv at h2 ⊢
    rw [map_sub] at h2 ⊢
    rw [h]; exact h2

private theorem pinf_re (x : A ℚ) : TR.pInf ℚ x = fun _ => re x := by
  funext w
  rw [Subsingleton.elim w Rat.infinitePlace]; rfl

private theorem real_rot (k : G1 ℚ) (hk : InfOrth k) (t : ℝ) (hs : re (k 1 0) = Real.sin t) (hc : re (k 1 1) = Real.cos t) :
    re (k 0 0) = Real.cos t ∧ re (k 0 1) = -Real.sin t := by
  let φ : A ℚ →+* ℝ := (Pi.evalRingHom (fun _ : InfinitePlace ℚ => ℝ) Rat.infinitePlace).comp (TR.pInf ℚ)
  have hφ : ∀ x, re x = φ x := fun _ => rfl
  have h1 : φ ((k.1 * k.1ᵀ) 0 1) = φ ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) 0 1) :=
    congrArg (fun x => (TR.infEq ℚ).symm x Rat.infinitePlace) (hk 0 1)
  have h2 := congrArg φ k.det_coe
  rw [Matrix.det_fin_two] at h2
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, map_add (f := _), map_mul, map_sub, map_one,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), map_zero] at h1 h2
  simp only [hφ] at hs hc ⊢
  rw [hs, hc] at h1 h2
  have h3 := Real.sin_sq_add_cos_sq t
  constructor
  · linear_combination (Real.sin t) * h1 + (Real.cos t) * h2 - φ (k 0 0) * h3
  · linear_combination (Real.cos t) * h1 - (Real.sin t) * h2 - φ (k 0 1) * h3

private theorem rot_of (k : G1 ℚ) (t : ℝ) (h0 : re (k 0 0) = Real.cos t) (h1 : re (k 0 1) = -Real.sin t)
    (hs : re (k 1 0) = Real.sin t) (hc : re (k 1 1) = Real.cos t) :
    Matrix.GeneralLinearGroup.map (TR.pInf ℚ) (gl k) = Matrix.GeneralLinearGroup.map (TR.pInf ℚ) (rot t) := by
  rw [rot, TR.pInf_infGL]
  refine Units.ext (Matrix.ext fun i j => ?_)
  change TR.pInf ℚ (k i j) = _
  rw [pinf_re]
  fin_cases i <;> fin_cases j
  · exact congrArg (fun x _ => x) h0
  · exact congrArg (fun x _ => x) h1
  · exact congrArg (fun x _ => x) hs
  · exact congrArg (fun x _ => x) hc

private theorem loc {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ) (a b c d n : K)
    (ha : w a ≤ 1) (hb : w b ≤ 1) (hc : w c ≤ w n) (hd : w d ≤ 1) (hn : w n ≤ 1) (h : a * d - b * c = 1) :
    ∃ z z' β : K, z * z' = 1 ∧ w z = 1 ∧ w z' = 1 ∧ w β ≤ 1 ∧ w (z' * (a - β * c) - 1) ≤ w n ∧
      w (z' * (b - β * d)) ≤ w n ∧ w (z * c) ≤ w n ∧ w (z * d - 1) ≤ w n := by
  rcases hn.lt_or_eq with hn' | hn'
  · have hbc : w (b * c) ≤ w n := by
      rw [map_mul]; exact (mul_le_of_le_one_left' hb).trans hc
    have had : w a * w d = 1 := by
      rw [← map_mul, show a * d = 1 + b * c by linear_combination h]
      exact w.map_one_add_of_lt (hbc.trans_lt hn')
    have ha1 : w a = 1 := le_antisymm ha (had ▸ mul_le_of_le_one_right' hd)
    have hd1 : w d = 1 := by rwa [ha1, one_mul] at had
    have a0 : a ≠ 0 := by rintro rfl; simp at ha1
    have d0 : d ≠ 0 := by rintro rfl; simp at hd1
    refine ⟨a, a⁻¹, b / d, mul_inv_cancel₀ a0, ha1, by simp [ha1], by simpa [hd1] using hb, ?_, ?_, ?_, ?_⟩
    · rw [show a⁻¹ * (a - b / d * c) - 1 = -(b * c) / (a * d) by field_simp; ring]
      simpa [ha1, hd1] using hbc
    · rw [div_mul_cancel₀ _ d0]; simp
    · simpa [ha1] using hc
    · rw [show a * d - 1 = b * c by linear_combination h]; exact hbc
  · rw [hn'] at hc ⊢
    refine ⟨1, 1, 0, one_mul _, map_one _, map_one _, by simp, ?_, by simpa using hb, by simpa using hc, ?_⟩
    · simpa using w.map_sub_le ha (map_one w).le
    · simpa using w.map_sub_le hd (map_one w).le

theorem UpperTheory.exists_unipotent_diag_rotation_level_decomposition :
    ∀ (N : ℕ), 0 < N → ∀ k ∈ KK ℚ, k ∈ SS N → ∀ t : ℝ, re (k 1 0) = Real.sin t → re (k 1 1) = Real.cos t →
        ∃ (b : A ℚ) (ζ : (A ℚ)ˣ) (κ : GL (Fin 2) (A ℚ)), ζ ∈ UU ∧ Lev N κ ∧ gl k = gl (nU b) * gl (mD ζ) * rot t * κ := by
  intro N _ k hk hS t hs hc
  obtain ⟨h0, h1⟩ := real_rot k hk.1 t hs hc
  have hdet := k.det_coe
  rw [Matrix.det_fin_two] at hdet
  have hint : ∀ v i j, Valued.v (H.cp v (k i j)) ≤ 1 := fun v i j => hk.2 v i j
  have hN : ∀ v : H.P ℚ, Valued.v (N : H.Kv v) ≤ 1 := fun v => natCast_mem (v.adicCompletionIntegers ℚ) N
  choose z z' β hzz hz hz' hβ e00 e01 e10 e11 using fun v : H.P ℚ =>
    loc (Valued.v (R := H.Kv v)) (H.cp v (k 0 0)) (H.cp v (k 0 1)) (H.cp v (k 1 0)) (H.cp v (k 1 1)) (N : H.Kv v)
      (hint v 0 0) (hint v 0 1) (hS v) (hint v 1 1) (hN v)
      (by rw [← map_mul, ← map_mul, ← map_sub, hdet, map_one])
  let Z : A ℚ := ((1, ⟨z, Eventually.of_forall fun v => (hz v).le⟩) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ)
  let Z' : A ℚ := ((1, ⟨z', Eventually.of_forall fun v => (hz' v).le⟩) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ)
  let B : A ℚ := ((0, ⟨β, Eventually.of_forall fun v => hβ v⟩) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ)
  have hZ : ∀ v, H.cp v Z = z v := fun _ => rfl
  have hZ' : ∀ v, H.cp v Z' = z' v := fun _ => rfl
  have hB : ∀ v, H.cp v B = β v := fun _ => rfl
  have hZZ : Z * Z' = 1 := Prod.ext (mul_one _) (FiniteAdeleRing.ext _ fun v => hzz v)
  have rZ : TR.pInf ℚ Z = 1 := map_one (TR.infEq ℚ).symm
  have rZ' : TR.pInf ℚ Z' = 1 := map_one (TR.infEq ℚ).symm
  have rB : TR.pInf ℚ B = 0 := map_zero (TR.infEq ℚ).symm
  let ζ : (A ℚ)ˣ := ⟨Z, Z', hZZ, (mul_comm _ _).trans hZZ⟩
  let k' : G1 ℚ := ⟨!![Z' * (k 0 0 - B * k 1 0), Z' * (k 0 1 - B * k 1 1); Z * k 1 0, Z * k 1 1], by
    rw [Matrix.det_fin_two_of]
    linear_combination (k 0 0 * k 1 1 - k 0 1 * k 1 0) * hZZ + hdet⟩
  have hd : ∀ v i j, Dv N v (k' i j - (1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j) := by
    intro v i j
    unfold Dv
    fin_cases i <;> fin_cases j
    · simpa [k', hZ, hZ', hB] using e00 v
    · simpa [k', hZ, hZ', hB] using e01 v
    · simpa [k', hZ, hZ', hB] using e10 v
    · simpa [k', hZ, hZ', hB] using e11 v
  refine ⟨B, ζ, (rot t)⁻¹ * gl k', ⟨rfl, fun v => hz v⟩, lev_of N t k' (rot_of k' t ?_ ?_ ?_ ?_) (fun v i j => ?_) hd, ?_⟩
  · simpa [k', re, rZ, rZ', rB] using h0
  · simpa [k', re, rZ, rZ', rB] using h1
  · simpa [k', re, rZ, rZ', rB] using hs
  · simpa [k', re, rZ, rZ', rB] using hc
  · have h := (hd v i j).trans (hN v)
    rw [← sub_add_cancel (k' i j) ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j), map_add (f := _)]
    refine Valuation.map_add_le _ h ?_
    fin_cases i <;> fin_cases j <;> simp
  · rw [mul_assoc, mul_inv_cancel_left, ← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext (Matrix.ext fun i j => ?_)
    change _ = (!![1, B; 0, 1] * !![Z, 0; 0, Z'] *
      !![Z' * (k 0 0 - B * k 1 0), Z' * (k 0 1 - B * k 1 1); Z * k 1 0, Z * k 1 1] : Matrix (Fin 2) (Fin 2) (A ℚ)) i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination (-k 0 0) * hZZ
    · linear_combination (-k 0 1) * hZZ
    · linear_combination (-k 1 0) * hZZ
    · linear_combination (-k 1 1) * hZZ
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.FiniteIdeleCongruenceVolumePos
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private lemma eq_one_of_mul'' {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ}
    (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : a = 1 := by
  refine le_antisymm ha ?_
  have := mul_le_mul' (le_refl a) hb
  rwa [h, mul_one] at this

private noncomputable def ef (x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (A ℚ)ˣ := (IdeleGroup.prodEquiv ℚ).symm (1, x)

private lemma ef_fst (x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ((ef x : (A ℚ)ˣ) : A ℚ).1 = 1 := rfl

private lemma inv_mul_at (x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (v : H.P ℚ) :
    Valued.v (((x⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v) *
      Valued.v ((x : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := by
  rw [← map_mul]
  have h := congrArg (fun y : FiniteAdeleRing (𝓞 ℚ) ℚ => y v) (Units.inv_mul x)
  have h' : ((x⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v *
      (x : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1 := h
  rw [h', map_one]

private lemma natCast_ne (L : ℕ) (hL : 0 < L) (v : H.P ℚ) : (L : H.Kv v) ≠ 0 := by
  exact_mod_cast hL.ne'

private lemma v_natCast_of_not_bad (L : ℕ) (v : H.P ℚ) (h : ¬ Bad L v) : Valued.v (L : H.Kv v) = 1 := by
  have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v (L : 𝓞 ℚ)
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 h] at h2
  exact_mod_cast h2

private lemma finite_bad (L : ℕ) (hL : 0 < L) : {v : H.P ℚ | Bad L v}.Finite := by
  have hne : Ideal.span {(L : 𝓞 ℚ)} ≠ 0 := by
    simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hL.ne'
  refine (Ideal.finite_factors hne).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

private lemma nhds_cong (L : ℕ) (hL : 0 < L) (v : H.P ℚ) :
    {x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ | Valued.v ((x : FiniteAdeleRing (𝓞 ℚ) ℚ) v - 1) ≤ Valued.v (L : H.Kv v)} ∈
      𝓝 (1 : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) := by
  have hB : IsOpen {y : H.Kv v | Valued.v y ≤ Valued.v (L : H.Kv v)} := by
    have : {y : H.Kv v | Valued.v y ≤ Valued.v (L : H.Kv v)} =
        {y | Valued.v.restrict y ≤ Valued.v.restrict (L : H.Kv v)} := by
      ext y
      simp only [Set.mem_ofPred_eq, Valuation.restrict_le_iff]
    rw [this]
    exact Valued.isOpen_closedBall _ (by simp [natCast_ne L hL v])
  have he : Continuous fun y : FiniteAdeleRing (𝓞 ℚ) ℚ => y v := RestrictedProduct.continuous_eval v
  have hf : Continuous fun x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ => (x : FiniteAdeleRing (𝓞 ℚ) ℚ) v - 1 :=
    (he.comp Units.continuous_val).sub continuous_const
  refine (hB.preimage hf).mem_nhds ?_
  have h0 : ((1 : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v - 1 = 0 := sub_self _
  change Valued.v (((1 : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v - 1) ≤ _
  rw [h0, map_zero]
  exact zero_le'

theorem UpperTheory.finiteIdele_congruenceVolume_pos :
    ∀ L : ℕ, 0 < L → 0 < cT L := by
  intro L hL
  set S : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ := (fun u => (IdeleGroup.prodEquiv ℚ).symm (1, u)) ⁻¹' TT L with hS
  have hcT : cT L = (finiteIdeleMeasure ℚ S).toReal := rfl
  have hsub : S ⊆ (finiteIntegralUnits ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) := by
    intro x hx
    have hu : ∀ v : H.P ℚ, Valued.v ((x : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := fun v => hx.1.2 v
    refine (mem_finiteIntegralUnits ℚ).2 fun v => ?_
    have hi := inv_mul_at x v
    rw [hu v, mul_one] at hi
    exact ⟨(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 (hu v).le,
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hi.le⟩
  have hnhds : S ∈ 𝓝 (1 : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) := by
    have h1 : (finiteIntegralUnits ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) ∈ 𝓝 (1 : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :=
      (isOpen_finiteIntegralUnits ℚ).mem_nhds (one_mem _)
    have h2 := (Filter.biInter_mem (finite_bad L hL)).2 fun v (_ : Bad L v) => nhds_cong L hL v
    filter_upwards [h1, h2] with x hx hc
    obtain hxi := (mem_finiteIntegralUnits ℚ).1 hx
    have hle : ∀ v : H.P ℚ, Valued.v ((x : FiniteAdeleRing (𝓞 ℚ) ℚ) v) ≤ 1 := fun v =>
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 (hxi v).1
    have hle' : ∀ v : H.P ℚ, Valued.v (((x⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v) ≤ 1 :=
      fun v => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 (hxi v).2
    refine ⟨⟨ef_fst x, fun v => ?_⟩, fun v => ?_⟩
    · exact eq_one_of_mul'' (hle v) (hle' v) (by rw [mul_comm]; exact inv_mul_at x v)
    · have hcp : H.cp v ((ef x : (A ℚ)ˣ) : A ℚ) - 1 = (x : FiniteAdeleRing (𝓞 ℚ) ℚ) v - 1 := rfl
      change Valued.v (H.cp v (((ef x : (A ℚ)ˣ) : A ℚ) - 1)) ≤ _
      rw [map_sub, map_one, hcp]
      by_cases hb : Bad L v
      · exact Set.mem_iInter₂.1 hc v hb
      · rw [v_natCast_of_not_bad L v hb]
        refine (Valuation.map_sub _ _ _).trans (max_le (hle v) ?_)
        rw [map_one]
  rw [hcT]
  refine ENNReal.toReal_pos (Measure.measure_pos_of_mem_nhds _ hnhds).ne' ?_
  refine ((measure_mono hsub).trans_lt ?_).ne
  rw [finiteIdeleMeasure_finiteIntegralUnits]
  exact ENNReal.one_lt_top
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.HasDerivAtWhittakerPeriodOneParameter
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

private theorem cover : ∃ C : Set (Fin 2 → A ℚ), IsCompact C ∧ FS2 ℚ ⊆ C := by
  obtain ⟨C, hC, hEC⟩ : ∃ C, IsCompact C ∧ fundamentalSet ℚ ⊆ C :=
    ⟨closure (fundamentalSetInfinite ℚ) ×ˢ _,
      (isCompact_closure_fundamentalSetInfinite ℚ).prod (isCompact_integralFiniteAdeles ℚ),
      fun x hx => ⟨subset_closure hx.1, hx.2⟩⟩
  exact ⟨Set.univ.pi fun _ : Fin 2 => C, isCompact_univ_pi fun _ => hC, fun x hx i hi => hEC (hx i hi)⟩

private theorem cont_nE' {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) :
    Continuous fun u : Fin 2 → A ℚ => nE D u :=
  continuous_gl.comp (continuous_nU.comp ((AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 0)).add
    ((AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 1)).mul continuous_const)))

private theorem deriv_at {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (f : Sm E 2)
    (c : ℝ → GL (Fin 2) (Cinf E)) (X : Lie E 2) (x : GL (Fin 2) (A E)) (c0 : c 0 = 1)
    (cadd : ∀ s t, c (s + t) = c s * c t) (cd : HasDerivAt (fun t => toL (c t).val) X 0) (t : ℝ) :
    HasDerivAt (fun τ => f.1 (x * infGL E 2 (c τ))) ((lie E 2 X f).1 (x * infGL E 2 (c t))) t := by
  have h := hasDerivAt_curve f (x * infGL E 2 (c t)) c X c0 cd
  have h2 : HasDerivAt (fun s => f.1 (x * infGL E 2 (c t) * infGL E 2 (c s))) ((lie E 2 X f).1 (x * infGL E 2 (c t))) (t - t) := by
    rw [sub_self]; exact h
  have h3 := HasDerivAt.comp_sub_const t t h2
  refine h3.congr_of_eventuallyEq (Eventually.of_forall fun τ => ?_)
  have e : c τ = c t * c (τ - t) := by rw [← cadd]; congr 1; ring
  simp only [e, map_mul, mul_assoc]

theorem UpperTheory.hasDerivAt_whittakerPeriod_oneParameter :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (f : Sm E 2) (c : ℝ → GL (Fin 2) (Cinf E)) (X : Lie E 2)
        (g : GL (Fin 2) (A E)), c 0 = 1 → (∀ s t, c (s + t) = c s * c t) → HasDerivAt (fun t => toL (c t).val) X 0 →
        Continuous f.1 → Continuous (lie E 2 X f).1 → (∃ B : ℝ, ∀ g, ‖(lie E 2 X f).1 g‖ ≤ B) →
        HasDerivAt (fun t : ℝ => Wo D f.1 (g * infGL E 2 (c t))) (Wo D (lie E 2 X f).1 g) 0 := by
  intro E _ _ _ D f c X g c0 cadd cd hf hl ⟨B, hB⟩
  obtain ⟨C, hC, hsub⟩ := cover
  have hfin : adeleMeasurePi ℚ (FS2 ℚ) < ⊤ := (measure_mono hsub).trans_lt hC.measure_lt_top
  haveI : IsFiniteMeasure ((adeleMeasurePi ℚ).restrict (FS2 ℚ)) := ⟨by simpa using hfin⟩
  have hn := cont_nE' D
  have hψ : Continuous fun u : Fin 2 → A ℚ => ψ (u 1) := continuous_ψ.comp (continuous_apply 1)
  have hF : ∀ h : GL (Fin 2) (A E), Continuous fun u : Fin 2 → A ℚ => f.1 (nE D u * h) * ψ (u 1) :=
    fun h => (hf.comp (hn.mul continuous_const)).mul hψ
  have hF' : ∀ h : GL (Fin 2) (A E), Continuous fun u : Fin 2 → A ℚ => (lie E 2 X f).1 (nE D u * h) * ψ (u 1) :=
    fun h => (hl.comp (hn.mul continuous_const)).mul hψ
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (adeleMeasurePi ℚ).restrict (FS2 ℚ)) (x₀ := (0 : ℝ)) (s := Set.univ)
    (F := fun t u => f.1 (nE D u * (g * infGL E 2 (c t))) * ψ (u 1))
    (F' := fun t u => (lie E 2 X f).1 (nE D u * (g * infGL E 2 (c t))) * ψ (u 1))
    (bound := fun _ => B) Filter.univ_mem
    (Eventually.of_forall fun t => (hF _).aestronglyMeasurable)
    (((hF _).continuousOn.integrableOn_compact hC).mono_set hsub)
    (hF' _).aestronglyMeasurable
    (ae_of_all _ fun u t _ => by rw [norm_mul, norm_ψ, mul_one]; exact hB _)
    (integrable_const _)
    (ae_of_all _ fun u t _ => by
      have h := deriv_at f c X (nE D u * g) c0 cadd cd t
      simp only [mul_assoc] at h
      exact h.mul_const (ψ (u 1)))
  have h2 := key.2
  simp only [c0, map_one, mul_one] at h2
  exact h2
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.HasLevelOfUnitIdeleCongruentOne
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.hasLevel_of_unitIdele_congruent_one :
    ∀ (L : ℕ), 0 < L → ∀ t : (A ℚ)ˣ, t ∈ UU → (∀ v, Dv L v ((t : A ℚ) - 1)) → Lev L (aE t) := by
  intro L _ t ht hD
  have h1 : (t : A ℚ).1 = 1 := ht.1
  have hu : ∀ v : H.P ℚ, Valued.v (H.cp v (t : A ℚ)) = 1 := ht.2
  have hi : ∀ v : H.P ℚ, Valued.v (H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ)) = 1 := by
    intro v
    have hm : H.cp v (t : A ℚ) * H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have := congrArg Valued.v hm
    rwa [map_mul, hu v, one_mul, map_one] at this
  have hz : ∀ v : H.P ℚ, Dv L v 0 := by
    intro v
    simp [Dv]
  refine ⟨fun i j => ?_, fun v => ⟨?_, fun i j => ?_⟩⟩
  · fin_cases i <;> fin_cases j <;> simp [aE, h1] <;> rfl
  · rw [H.KAt, GlobalTheory.LFun.KGL, GlobalTheory.AdelicU.mem_GLint_iff]
    have e1 : (1 : H.Kv v) ∈ Formalism.UG.Ov ℚ v := one_mem _
    have e0 : (0 : H.Kv v) ∈ Formalism.UG.Ov ℚ v := zero_mem _
    have et : H.cp v (t : A ℚ) ∈ Formalism.UG.Ov ℚ v := (hu v).le
    have ei : H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ) ∈ Formalism.UG.Ov ℚ v := (hi v).le
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · fin_cases i <;> fin_cases j
      · simpa [aE, Matrix.GeneralLinearGroup.map] using et
      · simpa [aE, Matrix.GeneralLinearGroup.map] using e0
      · simpa [aE, Matrix.GeneralLinearGroup.map] using e0
      · simpa [aE, Matrix.GeneralLinearGroup.map] using e1
    · fin_cases i <;> fin_cases j
      · exact ei
      · simpa [aE, Matrix.GeneralLinearGroup.map] using e0
      · simpa [aE, Matrix.GeneralLinearGroup.map] using e0
      · simpa [aE, Matrix.GeneralLinearGroup.map] using e1
  · fin_cases i <;> fin_cases j
    · simpa [aE] using hD v
    · simpa [aE] using hz v
    · simpa [aE] using hz v
    · simpa [aE] using hz v
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.HasSumCoprimeInvPowTwoMulEqLSeries
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.hasSum_coprime_inv_pow_two_mul_eq_LSeries :
    ∀ (N : ℕ) (s : ℂ), 0 < N → 1 < s.re → HasSum (fun n : {n : ℕ // 0 < n ∧ n.Coprime N} => ((n : ℕ) : ℂ) ^ (-(2 * s))) (LSeries (sqN N) s) := by
  intro N s _ hs
  have hsum : Summable fun n : {n : ℕ // 0 < n ∧ n.Coprime N} => ((n : ℕ) : ℂ) ^ (-(2 * s)) := by
    have h : Summable fun n : ℕ => 1 / (n : ℂ) ^ (2 * s) :=
      Complex.summable_one_div_nat_cpow.2 (by simp; linarith)
    refine (h.subtype _).congr fun n => ?_
    simp [Complex.cpow_neg]
  have hinj : Function.Injective fun m : {n : ℕ // 0 < n ∧ n.Coprime N} => (m : ℕ) * m := fun a b e =>
    Subtype.ext (Nat.mul_self_inj.1 e)
  have h2 : HasSum (LSeries.term (sqN N) s) (∑' n : {n : ℕ // 0 < n ∧ n.Coprime N}, ((n : ℕ) : ℂ) ^ (-(2 * s))) := by
    refine (hinj.hasSum_iff fun x hx => ?_).1 ?_
    · rcases eq_or_ne x 0 with rfl | h0
      · simp
      · rw [LSeries.term_of_ne_zero h0, sqN, if_neg, zero_div]
        rintro ⟨m, rfl, hm⟩
        exact hx ⟨⟨m, Nat.pos_of_ne_zero fun e => h0 (by simp [e]), hm⟩, rfl⟩
    · convert hsum.hasSum using 1
      funext m
      have h0 : (m : ℕ) * m ≠ 0 := mul_ne_zero m.2.1.ne' m.2.1.ne'
      rw [Function.comp_apply, LSeries.term_of_ne_zero h0, sqN, if_pos ⟨m, rfl, m.2.2⟩, Nat.cast_mul,
        Complex.natCast_mul_natCast_cpow, Complex.cpow_neg, two_mul,
        Complex.cpow_add _ _ (Nat.cast_ne_zero.2 m.2.1.ne'), one_div]
  rw [LSeries, h2.tsum_eq]
  exact hsum.hasSum
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.IdeleCongruenceConditionMulCongruenceUnitIff
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.ideleCongruenceCondition_mul_congruenceUnit_iff :
    ∀ N : ℕ, 0 < N → ∀ τ ∈ TT N, ∀ y : (A ℚ)ˣ, ((∀ v, Bad N v → Dv N v (((y * τ : (A ℚ)ˣ) : A ℚ) - 1)) ∧ ∀ v : H.P ℚ, Valued.v (H.cp v ((y * τ : (A ℚ)ˣ) : A ℚ)) ≤ 1) ↔ ((∀ v, Bad N v → Dv N v (((y : (A ℚ)ˣ) : A ℚ) - 1)) ∧ ∀ v : H.P ℚ, Valued.v (H.cp v ((y : (A ℚ)ˣ) : A ℚ)) ≤ 1) := by
  intro N _ τ hτ y
  obtain ⟨⟨_, hu⟩, hd⟩ := hτ
  have h1 : ∀ v : H.P ℚ, Valued.v (H.cp v ((y * τ : (A ℚ)ˣ) : A ℚ)) = Valued.v (H.cp v ((y : (A ℚ)ˣ) : A ℚ)) := by
    intro v
    rw [Units.val_mul, map_mul, map_mul, hu v, mul_one]
  have h2 : ∀ v : H.P ℚ, Dv N v (((y * τ : (A ℚ)ˣ) : A ℚ) - 1) ↔ Dv N v (((y : (A ℚ)ˣ) : A ℚ) - 1) := by
    intro v
    have hv := hd v
    have he : Valued.v (H.cp v (((y : A ℚ) - 1) * (τ : A ℚ))) = Valued.v (H.cp v ((y : A ℚ) - 1)) := by
      rw [map_mul, map_mul, hu v, mul_one]
    unfold Dv at hv ⊢
    constructor
    · intro h
      have e : ((y : A ℚ) - 1) * (τ : A ℚ) = (((y * τ : (A ℚ)ˣ) : A ℚ) - 1) - ((τ : A ℚ) - 1) := by
        rw [Units.val_mul]; ring
      rw [← he, e, map_sub]
      exact Valuation.map_sub_le _ h hv
    · intro h
      have e : (((y * τ : (A ℚ)ˣ) : A ℚ) - 1) = ((y : A ℚ) - 1) * (τ : A ℚ) + ((τ : A ℚ) - 1) := by
        rw [Units.val_mul]; ring
      rw [e, map_add (f := _)]
      exact Valuation.map_add_le _ (he ▸ h) hv
  simp only [h1, h2]
end

