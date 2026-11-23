module

public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SLevel
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.LevelEisenstein

variable {F : Type} [Field F] [NumberField F]

theorem v_le_of_mem_pow (w : HeightOneSpectrum (𝓞 F)) : ∀ (n : ℕ) (a : w.adicCompletionIntegers F),
    a ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ n →
    Valued.v (a : w.adicCompletion F) ≤ WithZero.exp (-(n : ℤ))
  | 0, a, _ => by rw [Nat.cast_zero, neg_zero, WithZero.exp_zero]; exact a.2
  | n + 1, a, ha => by
    rw [pow_succ] at ha
    refine Submodule.mul_induction_on (C := fun a : w.adicCompletionIntegers F =>
      Valued.v (a : w.adicCompletion F) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ))) ha ?_ ?_
    · intro x hx y hy
      have h1 := v_le_of_mem_pow w n x hx
      have hy1 : Valued.v (y : w.adicCompletion F) < 1 := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
          HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one] at hy
        exact lt_of_le_of_ne y.2 hy
      have h2 : Valued.v (y : w.adicCompletion F) ≤ WithZero.exp (-1 : ℤ) := by
        by_cases h0 : Valued.v (y : w.adicCompletion F) = 0
        · rw [h0]; exact zero_le
        · rw [← WithZero.exp_log h0] at hy1 ⊢
          rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hy1
          rw [WithZero.exp_le_exp]; omega
      show Valued.v ((x : w.adicCompletion F) * (y : w.adicCompletion F)) ≤ _
      rw [map_mul]
      refine (mul_le_mul' h1 h2).trans_eq ?_
      rw [← WithZero.exp_add]
      congr 1
      push_cast
      ring
    · intro x y hx hy
      show Valued.v ((x : w.adicCompletion F) + (y : w.adicCompletion F)) ≤ _
      exact (Valued.v.map_add _ _).trans (max_le hx hy)

theorem congruence_subgroup_entries_bound {w : HeightOneSpectrum (𝓞 F)} {n : ℕ} {k : GL (Fin 2) (w.adicCompletion F)} (hk : k ∈ K1 w n) :
    (∀ i j, Valued.v ((k : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) i j) ≤ 1) ∧
      Valued.v ((k : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) 1 0) ≤ WithZero.exp (-(n : ℤ)) ∧
      Valued.v ((k : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) 1 1 - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  obtain ⟨k', hk', rfl⟩ := hk
  have hk'' := hk'
  change ![0, 1] ᵥ* _ = ![0, 1] at hk''
  have h0 := congrFun hk'' 0
  have h1 := congrFun hk'' 1
  have m0 : k' 1 0 ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ n := by
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Ideal.Quotient.eq_zero_iff_mem] using h0
  have m1 : k' 1 1 - 1 ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ n := by
    refine Ideal.Quotient.eq.1 ?_
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_succ] using h1
  refine ⟨fun i j => (k' i j).2, v_le_of_mem_pow w n _ m0, ?_⟩
  have := v_le_of_mem_pow w n _ m1
  simpa using this

theorem loc_vecMul {w : HeightOneSpectrum (𝓞 F)} {n : ℕ} {k : GL (Fin 2) (w.adicCompletion F)} (hk : k ∈ K1 w n)
    {y : Fin 2 → w.adicCompletion F}
    (hy : Valued.v (y 0) ≤ WithZero.exp (-(n : ℤ)) ∧ Valued.v (y 1 - 1) ≤ WithZero.exp (-(n : ℤ))) :
    Valued.v ((y ᵥ* (k : Matrix (Fin 2) (Fin 2) (w.adicCompletion F))) 0) ≤ WithZero.exp (-(n : ℤ)) ∧
      Valued.v ((y ᵥ* (k : Matrix (Fin 2) (Fin 2) (w.adicCompletion F))) 1 - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  obtain ⟨he, h10, h11⟩ := congruence_subgroup_entries_bound hk
  have hε : WithZero.exp (-(n : ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  have hmul : ∀ {a b : w.adicCompletion F} {A B : WithZero (Multiplicative ℤ)}, Valued.v a ≤ A → Valued.v b ≤ B →
      Valued.v (a * b) ≤ A * B := fun ha hb => by rw [map_mul]; exact mul_le_mul' ha hb
  have hadd : ∀ {a b : w.adicCompletion F} {C : WithZero (Multiplicative ℤ)}, Valued.v a ≤ C → Valued.v b ≤ C →
      Valued.v (a + b) ≤ C := fun ha hb => (Valued.v.map_add _ _).trans (max_le ha hb)
  have hy1 : Valued.v (y 1) ≤ 1 := by
    have : y 1 = (y 1 - 1) + 1 := by ring
    rw [this]
    exact hadd (hy.2.trans hε) (by rw [map_one])
  constructor
  · have e : (y ᵥ* (k : Matrix (Fin 2) (Fin 2) (w.adicCompletion F))) 0 =
        y 0 * (k : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) 0 0 +
          y 1 * (k : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) 1 0 := by
      simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    rw [e]
    exact hadd ((hmul hy.1 (he 0 0)).trans_eq (mul_one _)) ((hmul hy1 h10).trans_eq (one_mul _))
  · have e : (y ᵥ* (k : Matrix (Fin 2) (Fin 2) (w.adicCompletion F))) 1 - 1 =
        y 0 * (k : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) 0 1 +
          (y 1 - 1) * (k : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) 1 1 +
          ((k : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) 1 1 - 1) := by
      simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
      ring
    rw [e]
    exact hadd (hadd ((hmul hy.1 (he 0 1)).trans_eq (mul_one _)) ((hmul hy.2 (he 1 1)).trans_eq (mul_one _))) h11

theorem norm_det_congruence_subgroup {w : HeightOneSpectrum (𝓞 F)} {n : ℕ} {k : GL (Fin 2) (w.adicCompletion F)} (hk : k ∈ K1 w n) :
    ‖((Matrix.GeneralLinearGroup.det k : (w.adicCompletion F)ˣ) : w.adicCompletion F)‖ = 1 := by
  obtain ⟨k', -, rfl⟩ := hk
  rw [det_map]
  refine GroundTheory.Global.IdeleGroup.norm_eq_one_of_mul_eq_one
    (b := (w.adicCompletionIntegers F).subtype ((Matrix.GeneralLinearGroup.det k')⁻¹ : (w.adicCompletionIntegers F)ˣ))
    ?_ (SetLike.coe_mem _) (SetLike.coe_mem _)
  rw [← map_mul, Units.mul_inv, map_one]

variable [IsTotallyReal F]

theorem pInf_vecMul (w : HeightOneSpectrum (𝓞 F)) (k : GL (Fin 2) (w.adicCompletion F)) (x : Fin 2 → Ad F) (i : Fin 2) :
    UpperTheory.V.TR.pInf F ((x ᵥ* ((finGL F 2 (locGL F 2 w k) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) i) =
      UpperTheory.V.TR.pInf F (x i) := by
  have hK := UpperTheory.V.TR.pInf_finGL (E := F) (a := 2) (locGL F 2 w k)
  have hKij : ∀ a b, UpperTheory.V.TR.pInf F (((finGL F 2 (locGL F 2 w k) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) a b) =
      (1 : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) a b := fun a b =>
    congrArg (fun M : GL (Fin 2) (UpperTheory.V.TR.Rinf F) => (M : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) a b) hK
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.vecMul, dotProduct, map_sum, map_mul, hKij]
  fin_cases i <;> simp [Fin.sum_univ_two, Matrix.one_apply]

theorem pLoc_vecMul (w v : HeightOneSpectrum (𝓞 F)) (k : GL (Fin 2) (w.adicCompletion F)) (x : Fin 2 → Ad F)
    (i : Fin 2) :
    pLoc F v (pFin F ((x ᵥ* ((finGL F 2 (locGL F 2 w k) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) i)) =
      ((fun j => pLoc F v (pFin F (x j))) ᵥ*
        ((Matrix.GeneralLinearGroup.map (pLoc F v) (locGL F 2 w k) : GL (Fin 2) (v.adicCompletion F)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion F))) i := by
  have hK := pFin_finGL (E := F) (a := 2) (locGL F 2 w k)
  have hKij : ∀ a b, pFin F (((finGL F 2 (locGL F 2 w k) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) a b) =
      ((locGL F 2 w k : GL (Fin 2) (Af F)) : Matrix (Fin 2) (Fin 2) (Af F)) a b := fun a b =>
    congrArg (fun M : GL (Fin 2) (Af F) => (M : Matrix (Fin 2) (Fin 2) (Af F)) a b) hK
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.vecMul, dotProduct, map_sum, map_mul, hKij]
  rfl

def cond (c : HeightOneSpectrum (𝓞 F) → ℕ) (x : Fin 2 → Ad F) : Prop :=
  ∀ v, Valued.v (pLoc F v (pFin F (x 0))) ≤ WithZero.exp (-(c v : ℤ)) ∧
    Valued.v (pLoc F v (pFin F (x 1)) - 1) ≤ WithZero.exp (-(c v : ℤ))

theorem cond_mul (c : HeightOneSpectrum (𝓞 F) → ℕ) {w : HeightOneSpectrum (𝓞 F)} {k : GL (Fin 2) (w.adicCompletion F)}
    (hk : k ∈ K1 w (c w)) {x : Fin 2 → Ad F} (hx : cond c x) :
    cond c (x ᵥ* ((finGL F 2 (locGL F 2 w k) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) := by
  intro v
  rw [pLoc_vecMul, pLoc_vecMul]
  by_cases hv : v = w
  · subst hv
    rw [pLoc_locGL]
    exact loc_vecMul hk (hx v)
  · rw [pLoc_locGL_of_ne hv, Units.val_one, Matrix.vecMul_one]
    exact hx v

theorem cond_iff (c : HeightOneSpectrum (𝓞 F) → ℕ) {w : HeightOneSpectrum (𝓞 F)} {k : GL (Fin 2) (w.adicCompletion F)}
    (hk : k ∈ K1 w (c w)) (x : Fin 2 → Ad F) :
    cond c (x ᵥ* ((finGL F 2 (locGL F 2 w k) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) ↔ cond c x := by
  refine ⟨fun h => ?_, cond_mul c hk⟩
  have := cond_mul c (inv_mem hk) h
  rwa [Matrix.vecMul_vecMul, ← Units.val_mul, map_inv, map_inv, mul_inv_cancel, Units.val_one,
    Matrix.vecMul_one] at this

theorem Phi_vecMul (c : HeightOneSpectrum (𝓞 F) → ℕ) {w : HeightOneSpectrum (𝓞 F)} {k : GL (Fin 2) (w.adicCompletion F)}
    (hk : k ∈ K1 w (c w)) (x : Fin 2 → Ad F) :
    Phi c (x ᵥ* ((finGL F 2 (locGL F 2 w k) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) = Phi c x := by
  unfold Phi
  rw [pInf_vecMul, pInf_vecMul]
  congr 2
  exact propext (cond_iff c hk x)

theorem thetaS_mul (c : HeightOneSpectrum (𝓞 F) → ℕ) {w : HeightOneSpectrum (𝓞 F)} {k : GL (Fin 2) (w.adicCompletion F)}
    (hk : k ∈ K1 w (c w)) (h : GA F 2) :
    thetaS (Phi c) (h * finGL F 2 (locGL F 2 w k)) = thetaS (Phi c) h := by
  unfold thetaS
  refine tsum_congr fun ξ => ?_
  rw [Units.val_mul, ← Matrix.vecMul_vecMul, Phi_vecMul c hk]

theorem absD_mul (g h : GA F 2) : absD (g * h) = absD g * absD h := by
  unfold absD
  rw [map_mul, map_mul, Positive.val_mul]

theorem absD_K {w : HeightOneSpectrum (𝓞 F)} {n : ℕ} {k : GL (Fin 2) (w.adicCompletion F)} (hk : k ∈ K1 w n) :
    absD (finGL F 2 (locGL F 2 w k)) = 1 := by
  unfold absD
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq]
  have hp : UpperTheory.V.TR.pInf F
      ((Matrix.GeneralLinearGroup.det (finGL F 2 (locGL F 2 w k)) : (Ad F)ˣ) : Ad F) = 1 := by
    rw [← det_map, UpperTheory.V.TR.pInf_finGL]
    simp
  have hinf' : ((Matrix.GeneralLinearGroup.det (finGL F 2 (locGL F 2 w k)) : (Ad F)ˣ) : Ad F).1 = 1 :=
    (UpperTheory.V.TR.infEq F).symm.injective (hp.trans (map_one _).symm)
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F),
      ‖((Matrix.GeneralLinearGroup.det (finGL F 2 (locGL F 2 w k)) : (Ad F)ˣ) : Ad F).2 v‖ = 1 := by
    intro v
    have e : ((Matrix.GeneralLinearGroup.det (finGL F 2 (locGL F 2 w k)) : (Ad F)ˣ) : Ad F).2 v =
        ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (pLoc F v) (locGL F 2 w k)) :
          (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
      change pLoc F v (pFin F ((Matrix.GeneralLinearGroup.det (finGL F 2 (locGL F 2 w k)) : (Ad F)ˣ) : Ad F)) = _
      rw [← det_map (pFin F), pFin_finGL, ← det_map]
    rw [e]
    by_cases hv : v = w
    · subst hv
      rw [pLoc_locGL]
      exact norm_det_congruence_subgroup hk
    · rw [pLoc_locGL_of_ne hv]
      simp
  rw [hinf', finprod_eq_one_of_forall_eq_one hfin, mul_one]
  refine Finset.prod_eq_one fun v _ => ?_
  rw [show (1 : InfiniteAdeleRing F) v = 1 from rfl, norm_one, one_pow]

end UpperTheory.HilbertEisensteinWeightOne.LevelEisenstein

namespace UpperTheory.HilbertEisensteinWeightOne

open LevelEisenstein in
theorem level_holds : SPois → SInt → SSmooth → SLevel := by
  intro _ _ _ F _ _ _ ω c _ w k hk g
  have e : eisInt ω (Phi c) (g * finGL F 2 (locGL F 2 w k)) = eisInt ω (Phi c) g := by
    funext t u
    unfold eisInt
    rw [← mul_assoc, thetaS_mul c hk, absD_mul, absD_K hk, mul_one]
  unfold Eis
  rw [e]

end UpperTheory.HilbertEisensteinWeightOne
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.WeightHolds
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.ArchimedeanWeightRotation

open Classical

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def ca (v : InfinitePlace F) (θ : ℝ) : UpperTheory.V.TR.Rinf F := fun u => if u = v then Real.cos θ else 1

def sa (v : InfinitePlace F) (θ : ℝ) : UpperTheory.V.TR.Rinf F := fun u => if u = v then Real.sin θ else 0

omit [NumberField F] [IsTotallyReal F] in
theorem ca_sq (v : InfinitePlace F) (θ : ℝ) (u : InfinitePlace F) : ca v θ u ^ 2 + sa v θ u ^ 2 = 1 := by
  unfold ca sa
  split_ifs <;> simp [Real.cos_sq_add_sin_sq]

def rotv (v : InfinitePlace F) (θ : ℝ) : UpperTheory.V.TR.Kinf F 2 :=
  ⟨!![ca v θ, sa v θ; -sa v θ, ca v θ], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j u
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply] <;>
      nlinarith [ca_sq v θ u]⟩

theorem rotv_zero (v : InfinitePlace F) : rotv v 0 = (1 : UpperTheory.V.TR.Kinf F 2) := by
  ext i j u
  fin_cases i <;> fin_cases j <;> simp [rotv, ca, sa]

def Xv (v : InfinitePlace F) : UpperTheory.V.TR.Lie F 2 :=
  UpperTheory.V.TR.toL (Matrix.single 0 1 (Pi.single v 1)) - UpperTheory.V.TR.toL (Matrix.single 1 0 (Pi.single v 1))

theorem rot_deriv (v : InfinitePlace F) :
    HasDerivAt (fun t : ℝ => UpperTheory.V.TR.toL (Unitary.toUnits (rotv v t)).val) (Xv v) 0 := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun u => ?_
  by_cases hu : u = v
  · subst hu
    fin_cases i <;> fin_cases j
    · simpa [Xv, rotv, ca, sa] using Real.hasDerivAt_cos 0
    · simpa [Xv, rotv, ca, sa] using Real.hasDerivAt_sin 0
    · simpa [Xv, rotv, ca, sa] using (Real.hasDerivAt_sin 0).fun_neg
    · simpa [Xv, rotv, ca, sa] using Real.hasDerivAt_cos 0
  · fin_cases i <;> fin_cases j <;> simp [Xv, rotv, ca, sa, hu, hasDerivAt_const]

theorem det_rotv (v : InfinitePlace F) (θ : ℝ) :
    Matrix.GeneralLinearGroup.det (Unitary.toUnits (rotv v θ)) = 1 := by
  refine Units.ext ?_
  ext u
  simp [rotv, Matrix.det_fin_two]
  nlinarith [ca_sq v θ u]

theorem factor (x y a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    (((x * a + y * -b : ℝ) : ℂ) + Complex.I * ((x * b + y * a : ℝ) : ℂ)) *
        Complex.exp (-(Real.pi : ℂ) * (((x * a + y * -b : ℝ) : ℂ) ^ 2 + ((x * b + y * a : ℝ) : ℂ) ^ 2)) =
      ((a : ℂ) + Complex.I * (b : ℂ)) *
        (((x : ℂ) + Complex.I * (y : ℂ)) * Complex.exp (-(Real.pi : ℂ) * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2))) := by
  have hr : (x * a + y * -b) ^ 2 + (x * b + y * a) ^ 2 = x ^ 2 + y ^ 2 := by
    linear_combination (x ^ 2 + y ^ 2) * h
  have hc : (((x * a + y * -b : ℝ) : ℂ) ^ 2 + ((x * b + y * a : ℝ) : ℂ) ^ 2) = (x : ℂ) ^ 2 + (y : ℂ) ^ 2 := by
    exact_mod_cast hr
  rw [hc]
  push_cast
  linear_combination (-(b : ℂ) * y * Complex.exp (-(Real.pi : ℂ) * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2))) * Complex.I_sq

omit [IsTotallyReal F] in
theorem prod_rot (v : InfinitePlace F) (θ : ℝ) :
    ∏ u, (((ca v θ u : ℝ) : ℂ) + Complex.I * ((sa v θ u : ℝ) : ℂ)) = Complex.exp (θ * Complex.I) := by
  rw [Fintype.prod_eq_single v (fun u hu => by simp [ca, sa, hu])]
  simp [ca, sa, Complex.exp_mul_I]
  ring

theorem phi_rot (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : InfinitePlace F) (θ : ℝ) (η : Fin 2 → Ad F) :
    Phi c (η ᵥ* ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits (rotv v θ)) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) =
      Complex.exp (θ * Complex.I) * Phi c η := by
  set M := ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits (rotv v θ)) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))
  have hI : M.map (UpperTheory.V.TR.pInf F) = ((Unitary.toUnits (rotv v θ) : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
      Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) :=
    congrArg Units.val (UpperTheory.V.TR.pInf_infGL (Unitary.toUnits (rotv v θ)))
  have hF : M.map (pFin F) = 1 := congrArg Units.val (UpperTheory.V.TR.pFin_infGL (Unitary.toUnits (rotv v θ)))
  have eI : ∀ i, UpperTheory.V.TR.pInf F ((η ᵥ* M) i) = ((fun j => UpperTheory.V.TR.pInf F (η j)) ᵥ*
      ((Unitary.toUnits (rotv v θ) : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F))) i :=
    fun i => by rw [RingHom.map_vecMul, hI]; rfl
  have eF : ∀ i, pFin F ((η ᵥ* M) i) = pFin F (η i) := fun i => by
    rw [RingHom.map_vecMul, hF, Matrix.vecMul_one]; rfl
  unfold Phi
  rw [eF 0, eF 1, eI 0, eI 1, ← mul_assoc]
  congr 1
  unfold arch
  rw [← prod_rot v θ, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun u _ => ?_
  have h := factor (UpperTheory.V.TR.pInf F (η 0) u) (UpperTheory.V.TR.pInf F (η 1) u) (ca v θ u) (sa v θ u) (ca_sq v θ u)
  simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two, rotv] using h

theorem thetaS_rot (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : InfinitePlace F) (θ : ℝ) (h : GA F 2) :
    thetaS (Phi c) (h * UpperTheory.V.TR.infGL F 2 (Unitary.toUnits (rotv v θ))) =
      Complex.exp (θ * Complex.I) * thetaS (Phi c) h := by
  unfold thetaS
  rw [← tsum_mul_left]
  congr 1
  funext ξ
  rw [Units.val_mul, ← Matrix.vecMul_vecMul, phi_rot]

theorem eis_rot (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : InfinitePlace F) (θ : ℝ) (g : GA F 2) :
    Eis ω (Phi c) (g * UpperTheory.V.TR.infGL F 2 (Unitary.toUnits (rotv v θ))) =
      Complex.exp (θ * Complex.I) * Eis ω (Phi c) g := by
  have hd : absD (g * UpperTheory.V.TR.infGL F 2 (Unitary.toUnits (rotv v θ))) = absD g := by
    unfold absD
    rw [map_mul, UpperTheory.V.TR.det_infGL, det_rotv, map_one, mul_one]
  have he : ∀ t u, eisInt ω (Phi c) (g * UpperTheory.V.TR.infGL F 2 (Unitary.toUnits (rotv v θ))) t u =
      Complex.exp (θ * Complex.I) * eisInt ω (Phi c) g t u := by
    intro t u
    unfold eisInt
    rw [← mul_assoc, thetaS_rot, hd]
    ring
  simp only [Eis, he, integral_const_mul]

end UpperTheory.HilbertEisensteinWeightOne.ArchimedeanWeightRotation

open UpperTheory.HilbertEisensteinWeightOne.ArchimedeanWeightRotation in
theorem UpperTheory.HilbertEisensteinWeightOne.weight_holds : SPois → SInt → SSmooth → SWt := by
  intro _ _ _ F _ _ _ ω c _ hs v
  set φ : UpperTheory.V.TR.Sm F 2 := ⟨Eis ω (Phi c), hs⟩
  have hX : UpperTheory.V.TR.Eop v 0 1 φ - UpperTheory.V.TR.Eop v 1 0 φ = UpperTheory.V.TR.lie F 2 (Xv v) φ := by
    unfold UpperTheory.V.TR.Eop
    rw [← LinearMap.sub_apply, ← map_sub]
    rfl
  rw [hX]
  apply Subtype.ext
  funext g
  have h1 := UpperTheory.V.TR.hasDerivAt_curve φ g (fun t => Unitary.toUnits (rotv v t)) (Xv v)
    (by rw [rotv_zero, map_one]) (rot_deriv v)
  have h2 : HasDerivAt (fun t : ℝ => φ.1 (g * UpperTheory.V.TR.infGL F 2 (Unitary.toUnits (rotv v t))))
      (Complex.I * φ.1 g) 0 := by
    have e : (fun t : ℝ => φ.1 (g * UpperTheory.V.TR.infGL F 2 (Unitary.toUnits (rotv v t)))) =
        fun t : ℝ => Complex.exp (t * Complex.I) * φ.1 g := funext fun t => eis_rot ω c v t g
    rw [e]
    have h3 := (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const Complex.I).cexp.mul_const (φ.1 g)
    simpa using h3
  rw [UpperTheory.V.TR.lie_apply, h1.unique h2]
  simp [φ]
end
end

