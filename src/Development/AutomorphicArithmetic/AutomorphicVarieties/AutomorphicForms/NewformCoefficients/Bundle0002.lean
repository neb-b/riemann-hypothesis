module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.QuantumMinorsCasimir
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.InfGLScalar
section
open NumberField Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.TR Matrix

private theorem infGL_scalar {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (u : (Rinf F)ˣ) :
    infGL F 2 (GeneralLinearGroup.scalar (Fin 2) u) = GeneralLinearGroup.scalar (Fin 2) (infId F u) := by
  have h : ∀ x, pInf F (sInf F x) = x := fun x => (infEq F).symm_apply_apply x
  have h1 : pInf F (infId F u : Ideles F) = u := by
    change pInf F (1 - sInf F 1 + sInf F _) = _
    simp [h]
  have h2 : pFin F (infId F u : Ideles F) = 1 := by
    change (1 : Af F) - 0 + 0 = 1
    simp
  refine ga_ext ?_ ?_
  · rw [TR.pInf_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h1]
  · rw [TR.pFin_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h2]

private theorem fin_expU {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {ω : HChar F} (h : IsOfFinOrder ω)
    (z : Rinf F) : ω.1 (infId F (expU z)) = 1 := by
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e1 : expU z = expU ((n : ℝ)⁻¹ • z) ^ n := by
    refine Units.ext (funext fun i => ?_)
    have : (n : ℝ) ≠ 0 := by positivity
    simp only [Units.val_pow_eq_pow_val, Pi.pow_apply, expU_val, ← Real.exp_nat_mul, Pi.smul_apply, smul_eq_mul]
    congr 1
    field_simp
  rw [e1, map_pow, map_pow]
  have e2 : ω.1 ^ n = 1 := congrArg Subtype.val e
  exact DFunLike.congr_fun e2 _

private theorem lie_scalar {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {ω : HChar F} (h : IsOfFinOrder ω)
    {φ : Sm F 2} (hφ : ∀ (z : Ideles F) (g : GA F 2), φ.1 (GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g) (z : Rinf F) : lie F 2 (toL (Matrix.scalar (Fin 2) z)) φ = 0 := by
  refine Subtype.ext (funext fun g => ?_)
  have h1 := hasDerivAt_curve φ g (fun t => GeneralLinearGroup.scalar (Fin 2) (expU (t • z)))
    (toL (Matrix.scalar (Fin 2) z)) (by simp [TR.expU_zero]) (by
      refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
      by_cases e : i = j
      · subst e
        have := ((hasDerivAt_id (0 : ℝ)).mul_const (z v)).exp
        simpa using this
      · simpa [Matrix.diagonal_apply, e] using hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have h2 : (fun t : ℝ => φ.1 (g * infGL F 2 (GeneralLinearGroup.scalar (Fin 2) (expU (t • z))))) = fun _ => φ.1 g := by
    funext t
    rw [infGL_scalar, ← GeneralLinearGroup.scalar_commute, hφ, fin_expU h]
    simp
  rw [h2] at h1
  exact h1.unique (hasDerivAt_const _ _)

private theorem qdet2 {A : Type} [Ring A] [Algebra ℂ A] (E : Fin 2 → Fin 2 → A) (u : ℂ) :
    Formalism.REAL.qdet E u = (algebraMap ℂ A u + E 0 0) * (algebraMap ℂ A (u - 1) + E 1 1) - E 1 0 * E 0 1 := by
  have h : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  rw [Formalism.REAL.qdet, Formalism.REAL.qminor, h, Finset.sum_pair (by decide)]
  simp [Formalism.REAL.Tm, List.ofFn_succ, sub_eq_add_neg]

private theorem casimir {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin 2 → Fin 2 → Module.End ℂ V)
    (hE : Formalism.REAL.GlRel E) (k : ℂ) (φ : V) (h0 : E 0 0 φ + E 1 1 φ = 0)
    (h1 : E 0 1 φ - E 1 0 φ = (Complex.I * k) • φ) (h2 : E 0 0 φ - E 1 1 φ = Complex.I • (E 0 1 φ + E 1 0 φ)) (u : ℂ) :
    Formalism.REAL.qdet E (u + 1 / 2) φ = ((u + (k - 1) / 2) * (u - (k - 1) / 2)) • φ :=
  _root_.UpperTheory.Reformulated.B.QuantumMinorsCasimir.casimir E hE k φ h0 h1 h2 u

theorem UpperTheory.V.Af.Nf.zFin :
    UpperTheory.V.Af.Nf.ZFin := by
  intro F _ _ _ k ω hω φ hc hw hl
  have hcap : ∀ v u, ∃ c : ℂ, TR.cap v u φ = c • φ := fun v u => by
    have h0 : Eop v 0 0 φ + Eop v 1 1 φ = 0 := by
      classical
      rw [← lie_scalar hω hc (Pi.single v 1), TR.Eop, TR.Eop, ← LinearMap.add_apply, ← map_add (f := _)]
      congr 2
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have := casimir _ (TR.glRel_Eop v) k φ h0 (hw v) (hl v) u
    refine ⟨_, Eq.trans ?_ this⟩
    rw [TR.cap]
    norm_num
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {φ}) (Submodule.span_le.2 ?_)
  rintro _ ⟨z, hz, rfl⟩
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨v, u, rfl⟩ := hx
    obtain ⟨c, e⟩ := hcap v u
    exact Submodule.mem_span_singleton.2 ⟨c, e.symm⟩
  | algebraMap c => exact Submodule.mem_span_singleton.2 ⟨c, rfl⟩
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy =>
    obtain ⟨c, e⟩ := Submodule.mem_span_singleton.1 hy
    have e' : c • φ = y φ := e
    change x (y φ) ∈ Submodule.span ℂ {φ}
    rw [← e', map_smul]
    exact Submodule.smul_mem _ _ hx
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.IntOfIntegers
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep

namespace UpperTheory.V.Af.Nf

private theorem memO {x : Af ℚ} :
    x ∈ Ohat ℚ ↔ ∀ v : HeightOneSpectrum (𝓞 ℚ), x v ∈ v.adicCompletionIntegers ℚ := by
  rw [Ohat, Subring.mem_iInf]
  rfl

private theorem int_of_integers (x : 𝓞 ℚ) : ∃ n : ℤ, (x : ℚ) = n :=
  ⟨Rat.ringOfIntegersEquiv x, (Rat.ringOfIntegersEquiv_apply_coe x).symm⟩

private theorem dense_int (M : ℕ) (hM : 1 ≤ M) (x : Af ℚ) (hx : x ∈ Ohat ℚ) :
    ∃ d : ℤ, ∃ y ∈ Ohat ℚ, x - d = M * y := by
  obtain ⟨r, a, ha, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat ℚ M hM).2 x (memO.1 hx)
  obtain ⟨n, hn⟩ := int_of_integers r
  refine ⟨n, a, memO.2 ha, ?_⟩
  rw [e, hn, map_intCast, nsmul_eq_mul]
  ring

private theorem exists_den (y : Af ℚ) : ∃ N : ℕ, 1 ≤ N ∧ (N : Af ℚ) * y ∈ Ohat ℚ := by
  obtain ⟨r, a, ha, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat ℚ 1 one_pos).1 y
  refine ⟨r.den, r.den_pos, ?_⟩
  have h : (r.den : Af ℚ) * algebraMap ℚ (Af ℚ) r = (r.num : Af ℚ) := by
    rw [← map_natCast (algebraMap ℚ (Af ℚ)), ← map_mul, Rat.den_mul_eq_num, map_intCast]
  rw [e, mul_add, h, one_smul]
  exact add_mem (intCast_mem _ _) (mul_mem (natCast_mem _ _) (memO.2 ha))

private theorem class_one (y : (Af ℚ)ˣ) : ∃ (r : ℚˣ) (u : (Af ℚ)ˣ), 0 < (r : ℚ) ∧ IsZU u ∧
    y = Units.map (algebraMap ℚ (Af ℚ)).toMonoidHom r * u := by
  classical
  obtain ⟨N, hN, ha⟩ := exists_den (y : Af ℚ)
  obtain ⟨M, hM, hb⟩ := exists_den ((y⁻¹ : (Af ℚ)ˣ) : Af ℚ)
  set a : Af ℚ := N * y with ha'
  set b : Af ℚ := M * ((y⁻¹ : (Af ℚ)ˣ) : Af ℚ) with hb'
  have hab : a * b = ((N * M : ℕ) : Af ℚ) := by
    rw [ha', hb', mul_mul_mul_comm, Units.mul_inv, mul_one, Nat.cast_mul]
  let I : Ideal ℤ :=
    { carrier := {n | ∃ w ∈ Ohat ℚ, (n : Af ℚ) = a * w}
      zero_mem' := ⟨0, zero_mem _, by simp⟩
      add_mem' := by
        rintro m n ⟨w, hw, e⟩ ⟨w', hw', e'⟩
        exact ⟨w + w', add_mem hw hw', by rw [Int.cast_add, e, e', mul_add]⟩
      smul_mem' := by
        rintro c n ⟨w, hw, e⟩
        exact ⟨c * w, mul_mem (intCast_mem _ _) hw, by rw [smul_eq_mul, Int.cast_mul, e]; ring⟩ }
  obtain ⟨d₀, hd₀⟩ := (IsPrincipalIdealRing.principal I).principal
  have hI : I = Ideal.span {|d₀|} := by
    rw [hd₀, Ideal.submodule_span_eq, Ideal.span_singleton_abs]
  set d : ℤ := |d₀| with hd
  have hL : ((N * M : ℕ) : ℤ) ∈ I := ⟨b, hb, by rw [hab, Int.cast_natCast]⟩
  obtain ⟨w, hw, hdw⟩ : d ∈ I := hI ▸ Ideal.mem_span_singleton_self d
  obtain ⟨n, z, hz, hn⟩ := dense_int (N * M) (Nat.mul_pos hN hM) a ha
  have hnI : n ∈ I := ⟨1 - b * z, sub_mem (one_mem _) (mul_mem hb hz), by
    rw [← hab] at hn; linear_combination -hn⟩
  rw [hI, Ideal.mem_span_singleton] at hL hnI
  obtain ⟨l, hl⟩ := hL
  obtain ⟨k, hk⟩ := hnI
  have hd0 : d ≠ 0 := by
    intro h
    rw [h, zero_mul, Nat.cast_eq_zero] at hl
    exact (Nat.mul_pos hN hM).ne' hl
  have hdpos : (0 : ℚ) < d := by exact_mod_cast lt_of_le_of_ne (abs_nonneg d₀) hd0.symm
  have hNpos : (0 : ℚ) < N := by exact_mod_cast hN
  have hl' : ((N * M : ℕ) : Af ℚ) = d * l := by
    rw [← Int.cast_natCast, hl, Int.cast_mul]
  have hau : a = d * ((k : Af ℚ) + l * z) := by
    rw [hk, hl', Int.cast_mul] at hn
    linear_combination hn
  have hdi : algebraMap ℚ (Af ℚ) (d : ℚ)⁻¹ * d = 1 := by
    rw [← map_intCast (algebraMap ℚ (Af ℚ)), ← map_mul, inv_mul_cancel₀ hdpos.ne', map_one]
  have hNi : algebraMap ℚ (Af ℚ) (N : ℚ)⁻¹ * N = 1 := by
    rw [← map_natCast (algebraMap ℚ (Af ℚ)), ← map_mul, inv_mul_cancel₀ hNpos.ne', map_one]
  have huw : ((k : Af ℚ) + l * z) * w = 1 := by
    rw [hau] at hdw
    linear_combination (-algebraMap ℚ (Af ℚ) (d : ℚ)⁻¹) * hdw + (1 - ((k : Af ℚ) + l * z) * w) * hdi
  refine ⟨Units.mk0 (d / N) (div_pos hdpos hNpos).ne', ⟨(k : Af ℚ) + l * z, w, huw, by rw [mul_comm, huw]⟩,
    div_pos hdpos hNpos, ⟨add_mem (intCast_mem _ _) (mul_mem (intCast_mem _ _) hz), hw⟩, Units.ext ?_⟩
  change (y : Af ℚ) = algebraMap ℚ (Af ℚ) ((d : ℚ) / N) * ((k : Af ℚ) + l * z)
  rw [div_eq_mul_inv, map_mul, map_intCast]
  rw [ha'] at hau
  linear_combination (algebraMap ℚ (Af ℚ) (N : ℚ)⁻¹) * hau - (y : Af ℚ) * hNi

private theorem val_le (K : Type) [Field K] [NumberField K] (r : K) (v : HeightOneSpectrum (𝓞 K))
    (h : algebraMap K (Af K) r v ∈ v.adicCompletionIntegers K) : v.valuation K r ≤ 1 :=
  (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v r).symm.trans_le h

private theorem rat_int (r : ℚ) (hr : algebraMap ℚ (Af ℚ) r ∈ Ohat ℚ) : ∃ n : ℤ, r = n := by
  obtain ⟨x, hx⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 ℚ) ℚ r fun v =>
    val_le ℚ r v (memO.1 hr v)
  obtain ⟨n, hn⟩ := int_of_integers x
  exact ⟨n, hx.symm.trans hn⟩

end UpperTheory.V.Af.Nf

theorem UpperTheory.V.Af.Nf.ratAd :
    UpperTheory.V.Af.Nf.RatAd :=
  ⟨UpperTheory.V.Af.Nf.class_one, UpperTheory.V.Af.Nf.dense_int, UpperTheory.V.Af.Nf.rat_int⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.NslMdiffPos
section
open UpperHalfPlane hiding I
open scoped Matrix MatrixGroups ModularForm Manifold

namespace UpperTheory.V.Af.Nf

private theorem nsl_pos (k : ℕ) (f : ℍ → ℂ) (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) (z : ℍ) :
    nsl k f g z = ((g.val.det ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (denom g z ^ (-(k : ℤ)) * f (g • z)) := by
  have h : (((g.val 0 0 : ℝ) : ℂ) * z + g.val 0 1) / (((g.val 1 0 : ℝ) : ℂ) * z + g.val 1 1) = ((g • z : ℍ) : ℂ) := by
    rw [coe_smul_of_det_pos (by simpa using hg)]
    rfl
  unfold nsl
  rw [h, sign_pos hg, abs_of_pos hg]
  simp only [SignType.coe_one, Complex.ofReal_one, one_mul, ofComplex_apply, mul_assoc]
  rfl

private theorem nsl_slash (k : ℕ) (f : ℍ → ℂ) (x : GL (Fin 2) ℝ) (hx : 0 < x.val.det) :
    nsl k f x = (((x.val.det ^ (1 - (k : ℝ) / 2) : ℝ) : ℂ)) • f ∣[(k : ℤ)] x := by
  funext z
  have hσ : σ x (f (x • z)) = f (x • z) := by simp [σ, hx]
  have hr : x.val.det ^ ((k : ℝ) / 2) = x.val.det ^ (1 - (k : ℝ) / 2) * x.val.det ^ ((k : ℤ) - 1) := by
    rw [← Real.rpow_intCast, ← Real.rpow_add hx]
    congr 1
    push_cast
    ring
  rw [nsl_pos k f x hx, Pi.smul_apply, ModularForm.slash_apply, hσ, Matrix.GeneralLinearGroup.val_det_apply,
    abs_of_pos hx, hr, smul_eq_mul]
  push_cast
  ring

private theorem nsl_eps (k : ℕ) (f : ℍ → ℂ) (x : Matrix (Fin 2) (Fin 2) ℝ) : nsl k f (eps * x) = nsl k f x := by
  funext z
  have hd : (eps * x).det = -x.det := by rw [Matrix.det_mul]; simp [eps]
  have h0 : ∀ j, (eps * x) 0 j = -x 0 j := fun j => by simp [eps, Matrix.mul_apply]
  have h1 : ∀ j, (eps * x) 1 j = x 1 j := fun j => by simp [eps, Matrix.mul_apply]
  unfold nsl
  rw [hd, h0, h0, h1, h1, abs_neg, Left.sign_neg]
  congr 3
  push_cast
  ring

private theorem nsl_mdiff_pos (k : ℕ) (f : ℍ → ℂ) (hf : MDiff f) (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : 0 < x.det) :
    MDiff (nsl k f x) := by
  let g : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero x hx.ne'
  have hg : 0 < g.val.det := hx
  have : nsl k f x = fun z : ℍ => ((g.val.det ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (denom g z ^ (-(k : ℤ)) * f (g • z)) :=
    funext (nsl_pos k f g hg)
  rw [this]
  exact mdifferentiable_const.mul ((mdifferentiable_denom_zpow g _).mul
    (hf.comp (mdifferentiable_smul (by simpa using hg))))

end UpperTheory.V.Af.Nf

theorem UpperTheory.V.Af.Nf.nslSl :
    UpperTheory.V.Af.Nf.NslSl := by
  intro k f
  refine ⟨fun δ => ?_, nsl_slash k f, fun hf x hx => ?_⟩
  · have hv : (δ : GL (Fin 2) ℝ).val = δ.1.map (Int.cast : ℤ → ℝ) := rfl
    have hd : (δ : GL (Fin 2) ℝ).val.det = 1 :=
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) δ).det_coe
    rw [← hv, nsl_slash k f _ (by rw [hd]; exact one_pos), hd, ModularForm.SL_slash]
    simp
  · rcases hx.lt_or_gt with h | h
    · rw [← nsl_eps]
      refine nsl_mdiff_pos k f hf _ ?_
      have hd : (eps * x).det = -x.det := by rw [Matrix.det_mul]; simp [eps]
      rw [hd]; linarith
    · exact nsl_mdiff_pos k f hf x h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.NslMul
section
open UpperHalfPlane

namespace UpperTheory.V.Af.Nf

end UpperTheory.V.Af.Nf

private theorem lower_row_mul_add_ne_zero_of_det_ne_zero (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : x.det ≠ 0) (w : ℍ) :
    (x 1 0 : ℂ) * (w : ℂ) + (x 1 1 : ℂ) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp at him hre
  rcases him with h1 | h1
  · apply hx
    rw [Matrix.det_fin_two]
    simp [h1] at hre
    simp [h1, hre]
  · exact absurd h1 w.im_pos.ne'

private theorem im_mobius_pos_of_det_pos (y : Matrix (Fin 2) (Fin 2) ℝ) (hy : 0 < y.det) (z : ℍ) :
    0 < (((y 0 0 : ℂ) * z + y 0 1) / ((y 1 0 : ℂ) * z + y 1 1)).im := by
  have hj := lower_row_mul_add_ne_zero_of_det_ne_zero y hy.ne' z
  rw [Complex.div_im]
  have hn : 0 < Complex.normSq ((y 1 0 : ℂ) * z + y 1 1) := Complex.normSq_pos.mpr hj
  rw [← sub_div]
  apply div_pos _ hn
  have hd := hy
  rw [Matrix.det_fin_two] at hd
  simp
  nlinarith [z.im_pos]

open UpperTheory.V.Af.Nf in
theorem UpperTheory.V.Af.Nf.nslMul :
    UpperTheory.V.Af.Nf.NslMul := by
  intro k f
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hx hy
    funext z
    have hjy := lower_row_mul_add_ne_zero_of_det_ne_zero y hy.ne' z
    have hm := im_mobius_pos_of_det_pos y hy z
    set m := ((y 0 0 : ℂ) * z + y 0 1) / ((y 1 0 : ℂ) * z + y 1 1) with hmdef
    simp only [nsl]
    rw [sign_pos hy, Matrix.det_mul, sign_mul, sign_pos hy, mul_one, abs_mul,
      Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
    simp only [SignType.coe_one, Int.cast_one, Complex.ofReal_one, one_mul]
    rw [← hmdef, UpperHalfPlane.ofComplex_apply_of_im_pos hm]
    simp only [UpperHalfPlane.coe_mk, Matrix.mul_apply, Fin.sum_univ_two]
    have hJ : ((↑(x 1 0 * y 0 0 + x 1 1 * y 1 0) : ℂ) * z + ↑(x 1 0 * y 0 1 + x 1 1 * y 1 1)) =
        ((x 1 0 : ℂ) * m + x 1 1) * ((y 1 0 : ℂ) * z + y 1 1) := by
      rw [hmdef, add_mul, mul_assoc, div_mul_cancel₀ _ hjy]
      push_cast
      ring
    have hN : ((↑(x 0 0 * y 0 0 + x 0 1 * y 1 0) : ℂ) * z + ↑(x 0 0 * y 0 1 + x 0 1 * y 1 1)) =
        ((x 0 0 : ℂ) * m + x 0 1) * ((y 1 0 : ℂ) * z + y 1 1) := by
      rw [hmdef, add_mul, mul_assoc, div_mul_cancel₀ _ hjy]
      push_cast
      ring
    rw [hJ, hN, mul_div_mul_right _ _ hjy, mul_zpow]
    push_cast
    ring
  · intro x
    funext z
    simp only [nsl, eps, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    simp
    have h1 : -(x 0 0 * x 1 1) + x 0 1 * x 1 0 = -(x 0 0 * x 1 1 - x 0 1 * x 1 0) := by ring
    rw [h1, abs_neg, Left.sign_neg]
    congr 3
    push_cast
    ring
  · intro t x ht
    funext z
    simp only [nsl, Matrix.det_fin_two, Matrix.smul_apply, smul_eq_mul]
    have h1 : t * x 0 0 * (t * x 1 1) - t * x 0 1 * (t * x 1 0) =
        t ^ 2 * (x 0 0 * x 1 1 - x 0 1 * x 1 0) := by ring
    rw [h1]
    set d := x 0 0 * x 1 1 - x 0 1 * x 1 0
    have h2 : SignType.sign (t ^ 2 * d) = SignType.sign d := by
      rw [sign_mul, sign_pos (by positivity), one_mul]
    have h3 : |t ^ 2 * d| ^ ((k : ℝ) / 2) = t ^ k * |d| ^ ((k : ℝ) / 2) := by
      rw [abs_mul, Real.mul_rpow (by positivity) (abs_nonneg _),
        abs_of_pos (by positivity : (0:ℝ) < t ^ 2)]
      congr 1
      rw [show (t ^ 2 : ℝ) = t ^ (2:ℝ) by norm_cast, ← Real.rpow_mul ht.le,
        show (2:ℝ) * (k / 2) = k by ring, Real.rpow_natCast]
    have hj : ((↑(t * x 1 0) : ℂ) * ↑z + ↑(t * x 1 1)) = (t : ℂ) * ((x 1 0 : ℂ) * z + x 1 1) := by
      push_cast
      ring
    have hn : ((↑(t * x 0 0) : ℂ) * ↑z + ↑(t * x 0 1)) = (t : ℂ) * ((x 0 0 : ℂ) * z + x 0 1) := by
      push_cast
      ring
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    rw [h2, h3, hj, hn, mul_div_mul_left _ _ ht']
    congr 1
    push_cast
    rw [mul_zpow, zpow_neg, zpow_neg, zpow_natCast]
    field_simp
  · intro c x
    funext z
    simp only [nsl, Pi.smul_apply, smul_eq_mul]
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Places
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V.Sd

theorem UpperTheory.V.Af.Nf.places :
    UpperTheory.V.Af.Nf.Places := by
  intro w
  have hq := Rat.HeightOneSpectrum.prime_natGenerator w
  have hspan := Rat.HeightOneSpectrum.span_natGenerator w
  have hN : normV w = Rat.HeightOneSpectrum.natGenerator w := by
    unfold normV
    rw [Nat.card_congr (Ideal.quotientEquiv w.asIdeal _
      (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hspan).toEquiv,
      Nat.card_congr (Int.quotientSpanNatEquivZMod _).toEquiv, Nat.card_zmod]
  have hP : w.asIdeal =
      Ideal.span {((Rat.HeightOneSpectrum.natGenerator w : ℕ) : 𝓞 ℚ)} := by
    ext x
    rw [Ideal.mem_span_singleton,
      ← Ideal.apply_mem_of_equiv_iff (f := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)), ← hspan,
      Ideal.mem_span_singleton,
      ← map_dvd_iff (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)), map_natCast]
  refine ⟨by rw [hN]; exact hq, by rw [hN]; exact hP, ?_, ?_⟩
  · rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  · intro M hM hndvd
    unfold UpperTheory.V.Af.Nf.lev ordI
    have hne : Ideal.span {(M : 𝓞 ℚ)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (by omega : M ≠ 0)
    by_contra hc
    rw [← Ne, Associates.count_ne_zero_iff_dvd hne w.irreducible, Ideal.dvd_iff_le,
      Ideal.span_singleton_le_iff_mem] at hc
    apply hndvd
    rw [hN, Rat.HeightOneSpectrum.natGenerator_dvd_iff,
      ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) M, Ideal.apply_mem_of_equiv_iff]
    exact hc
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.SatComp
section
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.CuspRep in
theorem UpperTheory.V.Af.Nf.satComp :
    UpperTheory.V.Af.Nf.SatComp := by
  intro F _ _ _ φ π ψ W h0 hW hd hφ w B h
  have hle : ∀ g, W ≤ W.comap (locSm F w g) := fun g x hx => hW (.fin (locGL F 2 w g)) x hx
  have hi : Function.Injective (W.mkQ ∘ₗ π.V.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_comp, Submodule.ker_mkQ]
    exact Submodule.disjoint_iff_comap_eq_bot.1 hd
  have he : W.mkQ φ = (W.mkQ ∘ₗ π.V.subtype) ψ := (Submodule.Quotient.eq W).2 hφ
  have h1 := h.map (ρ' := (locSm F w).quotient W hle) W.mkQ (fun _ _ => rfl)
    (by rw [he]; exact fun e => h0 (hi (e.trans (map_zero _).symm)))
  rw [he] at h1
  exact GlobalTheory.LFun.IsSatVecGL.of_map _ (fun _ _ => rfl) hi h1
end

