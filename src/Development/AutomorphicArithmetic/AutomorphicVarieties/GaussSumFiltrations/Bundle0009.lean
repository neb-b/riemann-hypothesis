module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.FinSupp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsAdelicLiftOfHilbertSystem
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.AdelicLift

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem sl_indep {k : ℕ} {Ψ : GL (Fin 2) (Af F) → Hn F → ℂ} (hΨ : Sys k Ψ) (h : GL (Fin 2) (InfinitePlace F → ℝ))
    (g : GL (Fin 2) (Af F)) (τ τ' : GL (Fin 2) F) (hτ : Pos (toInf τ * h)) (hτ' : Pos (toInf τ' * h)) :
    sl k (toInf τ * h) (Ψ (toFin τ * g)) = sl k (toInf τ' * h) (Ψ (toFin τ' * g)) := by
  have hinv : Pos (toInf τ' * h)⁻¹ := (SlashCocycle.slash_cocycle F k _ _ 0 hτ' hτ').2.1
  have hγ : Pos (toInf (τ * τ'⁻¹)) := by
    have e : toInf (τ * τ'⁻¹) = (toInf τ * h) * (toInf τ' * h)⁻¹ := by
      rw [map_mul, map_inv]; group
    rw [e]
    exact (SlashCocycle.slash_cocycle F k _ _ 0 hτ hinv).1
  have hTP : TP (τ * τ'⁻¹).val.det := ((GlobalTheory.T.hilbert_slash_rational_matrix_properties F k 0).2.1 _).1.1 hγ
  have e1 : toInf τ * h = toInf (τ * τ'⁻¹) * (toInf τ' * h) := by
    rw [map_mul, map_inv]; group
  have e2 : toFin τ * g = toFin (τ * τ'⁻¹) * (toFin τ' * g) := by
    rw [map_mul, map_inv]; group
  rw [e1, e2, (SlashCocycle.slash_cocycle F k _ _ _ hγ hτ').2.2.2.1, hΨ.left _ hTP]

theorem map_scalar {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (z : Rˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map f.toMonoidHom z) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [Matrix.GeneralLinearGroup.scalar]
  · simp [Matrix.GeneralLinearGroup.scalar, hij]

theorem scalar_comm {R : Type} [CommRing R] (z : Rˣ) (g : GL (Fin 2) R) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 2) z = Matrix.GeneralLinearGroup.scalar (Fin 2) z * g := by
  apply Units.ext
  exact ((Matrix.scalar_commute (z : R) (fun r => Commute.all _ r) g.val).eq).symm

theorem exists_lift : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ), Even k → ∀ (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ), Sys k Ψ → ∃ φ : GA F 2 → ℂ, IsLift k Ψ φ ∧ (∀ u ∈ KLev F 2 1, ∀ g, φ (g * finGL F 2 u) = φ g) ∧ ∀ (z : Ideles F) (g : GA F 2), φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = φ g := by
  intro F _ _ _ k hk Ψ hΨ
  choose τ hτ using (GlobalTheory.T.rational_GL2_infinite_finite_factor F 1).2
  let G : GL (Fin 2) (InfinitePlace F → ℝ) → GL (Fin 2) (Af F) → Hn F → ℂ :=
    fun h g => sl k (toInf (τ h) * h) (Ψ (toFin (τ h) * g))
  have hG : ∀ h g σ, Pos (toInf σ * h) → G h g = sl k (toInf σ * h) (Ψ (toFin σ * g)) :=
    fun h g σ hσ => sl_indep hΨ h g _ _ (hτ h) hσ
  refine ⟨fun x => G (Matrix.GeneralLinearGroup.map (TR.pInf F) x) (Matrix.GeneralLinearGroup.map (pFin F) x)
    fun _ => UpperHalfPlane.I, ⟨fun γ x => ?_, fun h hh g => ?_⟩, fun u hu x => ?_, fun z x => ?_⟩
  · rw [(GlobalTheory.T.rational_GL2_infinite_finite_factor F γ).1]
    simp only [map_mul, TR.pInf_infGL, TR.pInf_finGL, TR.pFin_infGL, pFin_finGL, mul_one, one_mul]
    generalize Matrix.GeneralLinearGroup.map (TR.pInf F) x = h
    generalize Matrix.GeneralLinearGroup.map (pFin F) x = g
    have hp : Pos (toInf (τ (toInf γ * h) * γ) * h) := by
      rw [map_mul, mul_assoc]; exact hτ _
    rw [hG h g _ hp]
    simp only [G, map_mul, mul_assoc]
  · simp only [map_mul, TR.pInf_infGL, TR.pInf_finGL, TR.pFin_infGL, pFin_finGL, mul_one, one_mul]
    rw [hG h g 1 (by simpa using hh)]
    simp only [map_one, one_mul]
  · simp only [map_mul, TR.pInf_finGL, pFin_finGL, mul_one, G]
    rw [← mul_assoc, hΨ.right _ u hu]
  · simp only [map_mul, map_scalar]
    generalize Matrix.GeneralLinearGroup.map (TR.pInf F) x = h
    generalize Matrix.GeneralLinearGroup.map (pFin F) x = g
    generalize Units.map (TR.pInf F).toMonoidHom z = t
    generalize Units.map (pFin F).toMonoidHom z = s
    have e : toInf (τ h) * (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) =
        Matrix.GeneralLinearGroup.scalar (Fin 2) t * (toInf (τ h) * h) := by
      rw [← mul_assoc, scalar_comm, mul_assoc]
    have e' : toFin (τ h) * (Matrix.GeneralLinearGroup.scalar (Fin 2) s * g) =
        Matrix.GeneralLinearGroup.scalar (Fin 2) s * (toFin (τ h) * g) := by
      rw [← mul_assoc, scalar_comm, mul_assoc]
    have H := (GlobalTheory.T.hilbert_slash_rational_matrix_properties F k (Ψ (toFin (τ h) * g))).2.2.1 hk t _ (hτ h)
    rw [hG _ _ (τ h) (by rw [e]; exact H.1), e, e', hΨ.cent, H.2]

end GlobalTheory.HilbertThetaSeries.AdelicLift

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_lift_of_hilbert_system : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ), Even k → ∀ (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ), Sys k Ψ → ∃ φ : GA F 2 → ℂ, IsLift k Ψ φ ∧ (∀ u ∈ KLev F 2 1, ∀ g, φ (g * finGL F 2 u) = φ g) ∧ ∀ (z : Ideles F) (g : GA F 2), φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = φ g := by
  first | exact @GlobalTheory.HilbertThetaSeries.AdelicLift.exists_lift | exact GlobalTheory.HilbertThetaSeries.AdelicLift.exists_lift | (intros; apply GlobalTheory.HilbertThetaSeries.AdelicLift.exists_lift <;> assumption)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsInGScalarMulAndAbsNormDetMulAbsFEq
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.CmpP

variable {F : Type} [Field F] [NumberField F]

theorem pint_mul {p : ℕ} {x y : F} (hx : PInt p x) (hy : PInt p y) : PInt p (x * y) := fun w hw => by
  rw [map_mul]; exact mul_le_one' (hx w hw) (hy w hw)

theorem pint_add {p : ℕ} {x y : F} (hx : PInt p x) (hy : PInt p y) : PInt p (x + y) := fun w hw =>
  Valuation.map_add_le _ (hx w hw) (hy w hw)

theorem punit_mul {p : ℕ} {x y : F} (hx : PUnit p x) (hy : PUnit p y) : PUnit p (x * y) := fun w hw => by
  rw [map_mul, hx w hw, hy w hw, mul_one]

theorem reAt_eq [IsTotallyReal F] (v : InfinitePlace F) (x : F) :
    reAt v x = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x := by
  rw [reAt, ← InfinitePlace.embedding_of_isReal_apply, Complex.ofReal_re]

theorem tp_mul [IsTotallyReal F] {x y : F} (hx : TP x) (hy : TP y) : TP (x * y) := fun v => by
  have := mul_pos (hx v) (hy v); rw [reAt_eq] at this ⊢; rw [reAt_eq] at this; simpa [map_mul] using this

theorem tp_one [IsTotallyReal F] : TP (1 : F) := fun v => by rw [reAt_eq, map_one]; exact one_pos

theorem abs_norm_eq [IsTotallyReal F] (x : F) : |((Algebra.norm ℚ x : ℚ) : ℝ)| = ∏ v, |reAt v x| := by
  rw [← Rat.cast_abs, ← InfinitePlace.prod_eq_abs_norm]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hv : v.IsReal := IsTotallyReal.isReal v
  have hm : v.mult = 1 := by simp [InfinitePlace.mult, hv]
  rw [hm, pow_one, reAt, ← InfinitePlace.norm_embedding_eq, ← InfinitePlace.embedding_of_isReal_apply hv,
    Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs]

end GlobalTheory.HilbertThetaSeries.CmpP

namespace GlobalTheory.HilbertThetaSeries.CmpP

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem inG_mul {p : ℕ} {δ : F} (hδ0 : δ ≠ 0) {γ γ' : GL (Fin 2) F} (h : InG p δ γ) (h' : InG p δ γ') :
    InG p δ (γ * γ') := by
  obtain ⟨a, b, c, d, de, dt⟩ := h
  obtain ⟨a', b', c', d', de', dt'⟩ := h'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : (γ * γ').val 0 0 = γ.val 0 0 * γ'.val 0 0 + (δ * γ.val 0 1) * (γ'.val 1 0 / δ) := by
      simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]; field_simp
    rw [this]; exact pint_add (pint_mul a a') (pint_mul b c')
  · have : δ * (γ * γ').val 0 1 = γ.val 0 0 * (δ * γ'.val 0 1) + (δ * γ.val 0 1) * γ'.val 1 1 := by
      simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]; ring
    rw [this]; exact pint_add (pint_mul a b') (pint_mul b d')
  · have : (γ * γ').val 1 0 / δ = (γ.val 1 0 / δ) * γ'.val 0 0 + γ.val 1 1 * (γ'.val 1 0 / δ) := by
      simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]; ring
    rw [this]; exact pint_add (pint_mul c a') (pint_mul d c')
  · have : (γ * γ').val 1 1 = (γ.val 1 0 / δ) * (δ * γ'.val 0 1) + γ.val 1 1 * γ'.val 1 1 := by
      simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]; field_simp
    rw [this]; exact pint_add (pint_mul c b') (pint_mul d d')
  · rw [Units.val_mul, Matrix.det_mul]; exact punit_mul de de'
  · rw [Units.val_mul, Matrix.det_mul]; exact tp_mul dt dt'

theorem inG_one (p : ℕ) (δ : F) : InG p δ 1 := by
  have h1 : PInt p (1 : F) := fun w _ => by rw [map_one]
  have h0 : PInt p (0 : F) := fun w _ => by rw [map_zero]; exact zero_le'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [h1, h0]
  · intro w _; simp
  · exact tp_one

end GlobalTheory.HilbertThetaSeries.CmpP

namespace GlobalTheory.HilbertThetaSeries.CmpP

section Alg
variable {M : Type} [CommGroupWithZero M] {a z t d c s : M}

theorem alg1 (ha : a * z = 1) (ht : t ≠ 0) (h : c * t = z * t * s) : a * c = s :=
  mul_right_cancel₀ ht (by rw [mul_assoc, h, ← mul_assoc, ← mul_assoc, ha, one_mul, mul_comm])

theorem alg2 (ha : a * z = 1) (hd : t * d = 1) (h : c = z * t * s) : d * (a * c) = s := by
  rw [h]; calc d * (a * (z * t * s)) = (a * z) * (t * d) * s := by ac_rfl
    _ = s := by rw [ha, hd, one_mul, one_mul]

theorem alg3 (ha : a * z = 1) (hd : t * d = 1) (h : c * t = z * s) : a * c / d = s := by
  have hd0 : d ≠ 0 := right_ne_zero_of_mul_eq_one hd
  have : d⁻¹ = t := (eq_inv_of_mul_eq_one_left hd).symm
  rw [div_eq_mul_inv, this, mul_assoc, h, ← mul_assoc, ha, one_mul]

theorem alg4 (ha : a * z = 1) (h : c = z * s) : a * c = s := by rw [h, ← mul_assoc, ha, one_mul]

theorem alg5 (ha : a * z = 1) (ht : t ≠ 0) (h : c * t = z ^ 2 * t * s) : a ^ 2 * c = s :=
  mul_right_cancel₀ ht (by
    calc a ^ 2 * c * t = a ^ 2 * (c * t) := by rw [mul_assoc]
      _ = (a * z) ^ 2 * s * t := by rw [h, mul_pow]; ac_rfl
      _ = s * t := by rw [ha, one_pow, one_mul])
end Alg

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem rep_cmp {p : ℕ} [hp : Fact p.Prime] {δ : F} (hδ : IsDel p δ) (y y' z : (Af F)ˣ) (γ : GL (Fin 2) F)
    (u : GL (Fin 2) (Af F)) (hy : AtP p δ y) (hy' : AtP p δ y') (hT : TP γ.val.det) (hu : u ∈ KLev F 2 1)
    (heq : toFin γ * aff y 0 = Matrix.GeneralLinearGroup.scalar (Fin 2) z * aff y' 0 * u) :
    ∃ (η : Fˣ) (r : ℚ), InG p δ (Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ) ∧ 0 < r ∧ ‖(r : ℚ_[p])‖ = 1 ∧
      |((Algebra.norm ℚ (Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ).val.det : ℚ) : ℝ)| * absF y' =
        (r : ℝ) ^ 2 * absF y := by
  obtain ⟨ξ, hξT, hξ⟩ := (GlobalTheory.HilbertThetaSeries.del_exists_and_move F p hp.out).2 δ hδ (z * y)
  have hK := ((GlobalTheory.HilbertThetaSeries.kMem F).1 u).1 hu
  have hV := (GlobalTheory.HilbertThetaSeries.kMem F).2.2.2.1
  have e := congrArg (fun g : GL (Fin 2) (Af F) => g.val) heq
  have e00 := congrFun (congrFun e 0) 0
  have e01 := congrFun (congrFun e 0) 1
  have e10 := congrFun (congrFun e 1) 0
  have e11 := congrFun (congrFun e 1) 1
  simp [toFin, aff, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have edet : algebraMap F (Af F) γ.val.det * y = z ^ 2 * y' * u.val.det := by
    rw [Matrix.det_fin_two, Matrix.det_fin_two, map_sub, map_mul, map_mul]
    linear_combination (algebraMap F (Af F) (γ.val 1 1)) * e00 + ((z : Af F) * y' * u.val 0 0) * e11 -
      (algebraMap F (Af F) (γ.val 0 1)) * e10 - ((z : Af F) * u.val 1 0) * e01
  have hs : ∀ i j, (Matrix.GeneralLinearGroup.scalar (Fin 2) ξ * γ).val i j = (ξ : F) * γ.val i j := by
    intro i j; fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]
  have hsd : (Matrix.GeneralLinearGroup.scalar (Fin 2) ξ * γ).val.det = (ξ : F) ^ 2 * γ.val.det := by
    rw [Matrix.det_fin_two, Matrix.det_fin_two, hs, hs, hs, hs]; ring
  have key : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal →
      Valued.v (pLoc F w (algebraMap F (Af F) ξ)) * Valued.v (pLoc F w (z : Af F)) = 1 ∧
      Valued.v (pLoc F w (y' : Af F)) = Valued.v (pLoc F w (y : Af F)) ∧
      Valued.v (pLoc F w (y : Af F)) * w.valuation F δ = 1 := by
    intro w hw
    have h1 := hy w hw
    have h2 := hy' w hw
    have h3 := hξ w hw
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, map_mul] at h3
    have hd0 : w.valuation F δ ≠ 0 := right_ne_zero_of_mul_eq_one h1
    refine ⟨?_, mul_right_cancel₀ hd0 (h2.trans h1.symm), h1⟩
    calc _ = Valued.v (pLoc F w (algebraMap F (Af F) ξ)) * Valued.v (pLoc F w (z : Af F)) *
          (Valued.v (pLoc F w (y : Af F)) * w.valuation F δ) := by rw [h1, mul_one]
      _ = 1 := by rw [← h3]; ac_rfl
  have push : ∀ (w : HeightOneSpectrum (𝓞 F)) {a b : Af F}, a = b → Valued.v (pLoc F w a) = Valued.v (pLoc F w b) :=
    fun w _ _ h => by rw [h]
  have hG : InG p δ (Matrix.GeneralLinearGroup.scalar (Fin 2) ξ * γ) := by
    refine ⟨fun w hw => ?_, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_, ?_⟩
    · obtain ⟨k1, k2, k3⟩ := key w hw
      have h := push w e00
      simp only [map_mul, k2] at h
      rw [hs, map_mul, ← hV, ← hV, alg1 k1 (left_ne_zero_of_mul_eq_one k3) h]
      exact hK.1 w 0 0
    · obtain ⟨k1, k2, k3⟩ := key w hw
      have h := push w e01
      simp only [map_mul, k2] at h
      rw [hs, map_mul, map_mul, ← hV ξ, ← hV (γ.val 0 1), alg2 k1 k3 h]
      exact hK.1 w 0 1
    · obtain ⟨k1, k2, k3⟩ := key w hw
      have h := push w e10
      simp only [map_mul] at h
      rw [hs, map_div₀, map_mul, ← hV ξ, ← hV (γ.val 1 0), alg3 k1 k3 h]
      exact hK.1 w 1 0
    · obtain ⟨k1, k2, k3⟩ := key w hw
      have h := push w e11
      simp only [map_mul] at h
      rw [hs, map_mul, ← hV, ← hV, alg4 k1 h]
      exact hK.1 w 1 1
    · obtain ⟨k1, k2, k3⟩ := key w hw
      have h := push w edet
      simp only [map_mul, map_pow, k2] at h
      rw [hsd, map_mul, map_pow, ← hV, ← hV, alg5 k1 (left_ne_zero_of_mul_eq_one k3) h]
      exact hK.2 w
    · rw [hsd, sq]; exact tp_mul (tp_mul hξT hξT) hT
  obtain ⟨-, hmul, hone, hprod⟩ := UpperTheory.V.Sd.Hm.absf F
  obtain ⟨r, hr, hr1, hrz⟩ := GlobalTheory.HilbertThetaSeries.IdeleAbs.absF_eq_rat F p (Units.map (algebraMap F (Af F)).toMonoidHom ξ * z) fun w hw => by
    simpa only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, map_mul] using (key w hw).1
  have hid : Units.map (algebraMap F (Af F)).toMonoidHom
        (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) ξ * γ)) * y =
      (Units.map (algebraMap F (Af F)).toMonoidHom ξ * z) * (Units.map (algebraMap F (Af F)).toMonoidHom ξ * z) * y' *
        Matrix.GeneralLinearGroup.det u := by
    apply Units.ext
    simp only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      Matrix.GeneralLinearGroup.val_det_apply]
    rw [← Units.val_mul, hsd, map_mul, map_pow]
    linear_combination (algebraMap F (Af F) ξ) ^ 2 * edet
  have h1 := hprod (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) ξ * γ))
  have h2 := congrArg absF hid
  rw [hmul, hmul, hmul, hmul, hrz, hone (Matrix.GeneralLinearGroup.det u) hK.2, mul_one] at h2
  rw [Matrix.GeneralLinearGroup.val_det_apply, ← abs_norm_eq] at h1
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  refine ⟨ξ, r⁻¹, hG, inv_pos.2 hr, by rw [Rat.cast_inv, norm_inv, hr1, inv_one], ?_⟩
  rw [Rat.cast_inv, inv_pow, eq_inv_mul_iff_mul_eq₀ (pow_pos hr' 2).ne']
  linear_combination absF y * h1 -
    |((Algebra.norm ℚ (Matrix.GeneralLinearGroup.scalar (Fin 2) ξ * γ).val.det : ℚ) : ℝ)| * h2

end GlobalTheory.HilbertThetaSeries.CmpP

theorem GlobalTheory.HilbertThetaSeries.CmpP.compare_at_p : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (δ : F), IsDel p δ → (∀ γ γ' : GL (Fin 2) F, InG p δ γ → InG p δ γ' → InG p δ (γ * γ')) ∧ InG p δ 1 ∧ ∀ (y y' z : (Af F)ˣ) (γ : GL (Fin 2) F) (u : GL (Fin 2) (Af F)), AtP p δ y → AtP p δ y' → TP γ.val.det → u ∈ KLev F 2 1 → toFin γ * aff y 0 = Matrix.GeneralLinearGroup.scalar (Fin 2) z * aff y' 0 * u → ∃ (η : Fˣ) (r : ℚ), InG p δ (Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ) ∧ 0 < r ∧ ‖(r : ℚ_[p])‖ = 1 ∧ |((Algebra.norm ℚ (Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ).val.det : ℚ) : ℝ)| * absF y' = (r : ℝ) ^ 2 * absF y :=
  fun F _ _ _ p hp δ hδ =>
    ⟨fun _ _ h h' => GlobalTheory.HilbertThetaSeries.CmpP.inG_mul (GlobalTheory.HilbertThetaSeries.denominators_prime_to F p hp.out δ hδ).1 h h', GlobalTheory.HilbertThetaSeries.CmpP.inG_one p δ,
      fun y y' z γ u hy hy' hT hu heq => GlobalTheory.HilbertThetaSeries.CmpP.rep_cmp hδ y y' z γ u hy hy' hT hu heq⟩

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inG_scalar_mul_and_abs_norm_det_mul_absF_eq : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (δ : F), IsDel p δ → (∀ γ γ' : GL (Fin 2) F, InG p δ γ → InG p δ γ' → InG p δ (γ * γ')) ∧ InG p δ 1 ∧ ∀ (y y' z : (Af F)ˣ) (γ : GL (Fin 2) F) (u : GL (Fin 2) (Af F)), AtP p δ y → AtP p δ y' → TP γ.val.det → u ∈ KLev F 2 1 → toFin γ * aff y 0 = Matrix.GeneralLinearGroup.scalar (Fin 2) z * aff y' 0 * u → ∃ (η : Fˣ) (r : ℚ), InG p δ (Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ) ∧ 0 < r ∧ ‖(r : ℚ_[p])‖ = 1 ∧ |((Algebra.norm ℚ (Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ).val.det : ℚ) : ℝ)| * absF y' = (r : ℝ) ^ 2 * absF y := by
  first | exact @GlobalTheory.HilbertThetaSeries.CmpP.compare_at_p | exact GlobalTheory.HilbertThetaSeries.CmpP.compare_at_p | (intros; apply GlobalTheory.HilbertThetaSeries.CmpP.compare_at_p <;> assumption)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.FormSystemOfFinitelyManyStabilizerForms
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.SysOfStab

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

lemma pos_iff (γ : GL (Fin 2) F) : Pos (toInf γ) ↔ TP γ.val.det := by
  have h : ((toInf γ : GL (Fin 2) (InfinitePlace F → ℝ)) : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det
      = rhom γ.val.det := by
    rw [RingHom.map_det]; rfl
  unfold Pos TP
  rw [h]
  rfl

lemma scal_comm {R : Type} [CommRing R] (z : Rˣ) (g : GL (Fin 2) R) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 2) z = Matrix.GeneralLinearGroup.scalar (Fin 2) z * g := by
  ext1
  exact ((Matrix.scalar_commute (z : R) (fun _ => Commute.all _ _) g.val).eq).symm

def Rel (g g' : GL (Fin 2) (Af F)) (γ : GL (Fin 2) F) : Prop :=
  TP γ.val.det ∧ ∃ (z : (Af F)ˣ) (u : GL (Fin 2) (Af F)), u ∈ KLev F 2 1 ∧
    toFin γ * g = Matrix.GeneralLinearGroup.scalar (Fin 2) z * g' * u

lemma tp_mul {γ γ' : GL (Fin 2) F} (h : TP γ.val.det) (h' : TP γ'.val.det) : TP (γ * γ').val.det := by
  rw [← pos_iff] at h h' ⊢
  rw [map_mul]
  exact (SlashCocycle.slash_cocycle F 0 _ _ 0 h h').1

lemma tp_inv {γ : GL (Fin 2) F} (h : TP γ.val.det) : TP (γ⁻¹).val.det := by
  rw [← pos_iff] at h ⊢
  rw [map_inv]
  exact (SlashCocycle.slash_cocycle F 0 _ _ 0 h h).2.1

lemma tp_one : TP (1 : GL (Fin 2) F).val.det := by
  rw [← pos_iff, map_one]
  intro v
  simp

lemma sl_mul (k : ℕ) {γ γ' : GL (Fin 2) F} (h : TP γ.val.det) (h' : TP γ'.val.det) (f : Hn F → ℂ) :
    sl k (toInf (γ * γ')) f = sl k (toInf γ') (sl k (toInf γ) f) := by
  rw [← pos_iff] at h h'
  rw [map_mul]
  exact (SlashCocycle.slash_cocycle F k _ _ f h h').2.2.2.1

lemma sl_one (k : ℕ) (f : Hn F → ℂ) : sl k (toInf (1 : GL (Fin 2) F)) f = f := by
  have h := (pos_iff (1 : GL (Fin 2) F)).2 tp_one
  rw [map_one]
  exact (SlashCocycle.slash_cocycle F k _ _ f h h).2.2.2.2.2

lemma Rel.symm {g g' : GL (Fin 2) (Af F)} {γ : GL (Fin 2) F} (h : Rel g g' γ) : Rel g' g γ⁻¹ := by
  obtain ⟨hγ, z, u, hu, e⟩ := h
  refine ⟨tp_inv hγ, z⁻¹, u⁻¹, inv_mem hu, ?_⟩
  have e' : g' = (Matrix.GeneralLinearGroup.scalar (Fin 2) z)⁻¹ * (toFin γ * g) * u⁻¹ := by
    rw [e]; group
  rw [e', map_inv, map_inv, ← map_inv (Matrix.GeneralLinearGroup.scalar (Fin 2)), ← mul_assoc, ← mul_assoc,
    scal_comm]
  group

lemma Rel.trans {g g' g'' : GL (Fin 2) (Af F)} {γ γ' : GL (Fin 2) F} (h : Rel g g' γ) (h' : Rel g' g'' γ') :
    Rel g g'' (γ' * γ) := by
  obtain ⟨hγ, z, u, hu, e⟩ := h
  obtain ⟨hγ', z', u', hu', e'⟩ := h'
  refine ⟨tp_mul hγ' hγ, z * z', u' * u, mul_mem hu' hu, ?_⟩
  rw [map_mul, mul_assoc, e, ← mul_assoc, ← mul_assoc, scal_comm, mul_assoc _ (toFin γ'), e', map_mul]
  group

theorem main : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (Y : Finset (Af F)ˣ) (f : (Af F)ˣ → Hn F → ℂ), (∀ g : GL (Fin 2) (Af F), ∃ γ : GL (Fin 2) F, TP γ.val.det ∧ ∃ y ∈ Y, ∃ u ∈ KLev F 2 1, toFin γ * g = aff y 0 * u) → (∀ y ∈ Y, Hol (f y) ∧ Gr (f y) ∧ ∀ γ, Stab (aff y 0) γ → sl k (toInf γ) (f y) = f y) → ∃ Ψ : GL (Fin 2) (Af F) → Hn F → ℂ, Sys k Ψ ∧ ∀ g, ∃ (γ : GL (Fin 2) F) (z : (Af F)ˣ), TP γ.val.det ∧ ∃ y ∈ Y, ∃ u ∈ KLev F 2 1, toFin γ * g = Matrix.GeneralLinearGroup.scalar (Fin 2) z * aff y 0 * u ∧ Ψ g = sl k (toInf γ) (f y) := by
  intro F _ _ _ k Y f hcov hf
  let P : GL (Fin 2) (Af F) → (Af F)ˣ → Prop := fun g y => y ∈ Y ∧ ∃ γ, Rel g (aff y 0) γ
  let y : GL (Fin 2) (Af F) → (Af F)ˣ := fun g => Classical.epsilon (P g)
  have hy : ∀ g, P g (y g) := by
    intro g
    apply Classical.epsilon_spec (p := P g)
    obtain ⟨γ, hγ, y, hyY, u, hu, e⟩ := hcov g
    exact ⟨y, hyY, γ, hγ, 1, u, hu, by rw [map_one, one_mul, e]⟩
  have hyeq : ∀ g g' γ, Rel g g' γ → y g = y g' := by
    intro g g' γ h
    have : P g = P g' := by
      funext x
      exact propext ⟨fun ⟨a, δ, b⟩ => ⟨a, _, h.symm.trans b⟩, fun ⟨a, δ, b⟩ => ⟨a, _, h.trans b⟩⟩
    simp only [y, this]
  choose c hc using fun g => (hy g).2
  let Ψ : GL (Fin 2) (Af F) → Hn F → ℂ := fun g => sl k (toInf (c g)) (f (y g))
  have key : ∀ g g' γ, Rel g g' γ → sl k (toInf γ) (Ψ g') = Ψ g := by
    intro g g' γ h
    have h1 : Rel g (aff (y g) 0) (c g' * γ) := by
      rw [hyeq g g' γ h]; exact h.trans (hc g')
    have h2 : Stab (aff (y g) 0) (c g' * γ * (c g)⁻¹) := (hc g).symm.trans h1
    have h3 := (hf _ (hy g).1).2.2 _ h2
    simp only [Ψ]
    rw [← sl_mul k (hc g').1 h.1, ← hyeq g g' γ h]
    conv_rhs => rw [← h3, ← sl_mul k h2.1 (hc g).1, inv_mul_cancel_right]
  refine ⟨Ψ, ⟨fun g => ?_, fun g => ?_, fun γ hγ g => ?_, fun g u hu => ?_, fun z g => ?_⟩, fun g => ?_⟩
  · have h := (hf _ (hy g).1).1
    exact ((HolKeep.main F k _ _ 0 h h).2.2.2.2.2 _ ((pos_iff _).2 (hc g).1)).2
  · have h := (hf _ (hy g).1).2.1
    exact ((Growth.gr_closed F k _ _ 0 h h).2.2.2.2.2 _ ((pos_iff _).2 (hc g).1)).2
  · exact key _ _ _ ⟨hγ, 1, 1, one_mem _, by rw [map_one, one_mul, mul_one]⟩
  · have := key (g * u) g 1 ⟨tp_one, 1, u, hu, by rw [map_one, map_one, one_mul, one_mul]⟩
    rw [← this, sl_one]
  · have := key (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) g 1
      ⟨tp_one, z, 1, one_mem _, by rw [map_one, one_mul, mul_one]⟩
    rw [← this, sl_one]
  · obtain ⟨hγ, z, u, hu, e⟩ := hc g
    exact ⟨c g, z, hγ, y g, (hy g).1, u, hu, e, rfl⟩

end GlobalTheory.HilbertThetaSeries.SysOfStab

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.form_system_of_finitely_many_stabilizer_forms : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (Y : Finset (Af F)ˣ) (f : (Af F)ˣ → Hn F → ℂ), (∀ g : GL (Fin 2) (Af F), ∃ γ : GL (Fin 2) F, TP γ.val.det ∧ ∃ y ∈ Y, ∃ u ∈ KLev F 2 1, toFin γ * g = aff y 0 * u) → (∀ y ∈ Y, Hol (f y) ∧ Gr (f y) ∧ ∀ γ, Stab (aff y 0) γ → sl k (toInf γ) (f y) = f y) → ∃ Ψ : GL (Fin 2) (Af F) → Hn F → ℂ, Sys k Ψ ∧ ∀ g, ∃ (γ : GL (Fin 2) F) (z : (Af F)ˣ), TP γ.val.det ∧ ∃ y ∈ Y, ∃ u ∈ KLev F 2 1, toFin γ * g = Matrix.GeneralLinearGroup.scalar (Fin 2) z * aff y 0 * u ∧ Ψ g = sl k (toInf γ) (f y) := by
  first | exact @GlobalTheory.HilbertThetaSeries.SysOfStab.main | exact GlobalTheory.HilbertThetaSeries.SysOfStab.main | (intros; apply GlobalTheory.HilbertThetaSeries.SysOfStab.main <;> assumption)
end
end

