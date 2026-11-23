module

public import Mathlib
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Formalism.LocalToGlobal.Columns.PolyFn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0186
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0210

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOneOfInfOfVal
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff
open Formalism.L2.Host (HChar)

namespace GlobalTheory.HeckeUnrTrivial

theorem eq_one_of_val_eq_one {K : Type} [Field K] [NumberField K] (χ : HChar K)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), χ.UnrAt v → χ.val v = 1) : χ = 1 := by
  refine Subtype.ext (GlobalTheory.FrobDense.eq_one_of_away χ.1 χ.2.1 χ.2.2
    (GlobalTheory.Mem.UnrAe.finite_ramified χ).toFinset fun v hv => ?_)
  have hu : χ.UnrAt v := by simpa using hv
  exact GlobalTheory.FrobDense.eq_one_of_unif (χ.loc v) fun x hx => (χ.val_eq hu x hx).trans (h v hu)

theorem eq_one_of_inf_of_val : ∀ (K : Type) [Field K] [NumberField K] (χ : HChar K), (∀ k : Kˣ, χ.inf k = 1) → (∀ v : HeightOneSpectrum (𝓞 K), χ.UnrAt v → χ.val v = 1) → χ = 1 :=
  fun _ _ _ χ _ h => eq_one_of_val_eq_one χ h

end GlobalTheory.HeckeUnrTrivial
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivariantGLOfEquivariantUnitaryCoefficientSpac
section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV

namespace GlobalTheory.Branching.Family

variable {ι : Type} [Fintype ι]


omit [Fintype ι] in
theorem exists_poly_blockAct_coef {k : ℕ} (f : MvPolynomial (ι × Fin k × Fin k) ℂ)
    (l : Module.Dual ℂ (MvPolynomial (ι × Fin k × Fin k) ℂ)) :
    ∃ P : MvPolynomial (ι × Fin k × Fin k) ℂ, ∀ g : ι → Matrix (Fin k) (Fin k) ℂ,
      l (Formalism.GradedWeylDivisibility.blockAct ℂ g f) = eval (fun x => g x.1 x.2.1 x.2.2) P := by
  classical

  let Φ : ι × Fin k × Fin k → MvPolynomial (ι × Fin k × Fin k) (MvPolynomial (ι × Fin k × Fin k) ℂ) :=
    fun v => ∑ b : Fin k, C (X (v.1, v.2.1, b) : MvPolynomial (ι × Fin k × Fin k) ℂ) * X (v.1, (b, v.2.2))
  let T : MvPolynomial (ι × Fin k × Fin k) ℂ → MvPolynomial (ι × Fin k × Fin k) (MvPolynomial (ι × Fin k × Fin k) ℂ) :=
    fun p => aeval Φ (map (C : ℂ →+* MvPolynomial (ι × Fin k × Fin k) ℂ) p)
  have hT : ∀ (g : ι → Matrix (Fin k) (Fin k) ℂ) (p : MvPolynomial (ι × Fin k × Fin k) ℂ),
      Formalism.GradedWeylDivisibility.blockAct ℂ g p = map (eval fun x => g x.1 x.2.1 x.2.2) (T p) := by
    intro g p
    induction p using MvPolynomial.induction_on with
    | C a => simp [T, aeval_C, MvPolynomial.algebraMap_eq, map_C, eval_C]
    | add p q hp hq => simp only [map_add (f := _), hp, hq, T]
    | mul_X p v hp =>
      simp only [T] at hp ⊢
      simp only [map_mul, hp]
      congr 1
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Formalism.GradedWeylDivisibility.blockAct, aeval_X, map_X, Φ, map_sum, map_mul, map_C, eval_X]
  refine ⟨∑ m ∈ (T f).support, C (l (monomial m 1)) * (T f).coeff m, fun g => ?_⟩
  rw [hT g f]
  conv_lhs => rw [(T f).as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_monomial, map_mul, eval_C]
  rw [show (monomial m (eval (fun x => g x.1 x.2.1 x.2.2) ((T f).coeff m)) : MvPolynomial (ι × Fin k × Fin k) ℂ) =
      eval (fun x => g x.1 x.2.1 x.2.2) ((T f).coeff m) • monomial m 1 by
    rw [smul_monomial, smul_eq_mul, mul_one]]
  rw [map_smul, smul_eq_mul, mul_comm]

theorem exists_coef_rhoK {k : ℕ} (lam : ι → DomWeight k) (f : VV ℂ lam) (l : Module.Dual ℂ (VV ℂ lam)) :
    ∃ P : MvPolynomial (ι × Fin k × Fin k) ℂ, ∀ g : ι → GL (Fin k) ℂ,
      l (rhoK lam g f) = (∏ τ, (g τ : Matrix (Fin k) (Fin k) ℂ).det ^ (lam τ).detShift) *
        eval (fun x => (g x.1 : Matrix (Fin k) (Fin k) ℂ) x.2.1 x.2.2) P := by
  classical
  obtain ⟨L, hL⟩ := LinearMap.exists_extend (K := ℂ) (p := VV ℂ lam) l
  obtain ⟨P, hP⟩ := exists_poly_blockAct_coef (ι := ι) (k := k) (f : MvPolynomial (ι × Fin k × Fin k) ℂ) L
  refine ⟨rename (fun x : ι × Fin k × Fin k => (x.1, x.2.2, x.2.1)) P, fun g => ?_⟩
  have hl : l (rhoK lam g f) = L ((rhoK lam g f : VV ℂ lam) : MvPolynomial (ι × Fin k × Fin k) ℂ) := by
    rw [← hL]; rfl
  have hv : ((rhoK lam g f : VV ℂ lam) : MvPolynomial (ι × Fin k × Fin k) ℂ) =
      detTwK lam g • Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => Matrix.transpose ((g τ : GL (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ))
        (f : MvPolynomial (ι × Fin k × Fin k) ℂ) := rfl
  have hd : detTwK lam g = ∏ τ, ((g τ : GL (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ).det ^ (lam τ).detShift := by
    simp only [detTwK, detPow, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]
  rw [hl, hv, map_smul, hP, eval_rename, smul_eq_mul, hd]
  rfl

theorem det_diag_one {n N : ℕ} (h : n + 1 = N) (g : GL (Fin n) ℂ) :
    (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N h g : Matrix (Fin N) (Fin N) ℂ).det = (g : Matrix (Fin n) (Fin n) ℂ).det := by
  subst h
  have h1 : ∀ a b : Fin n, ((Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n (n + 1) rfl g : GL (Fin (n + 1)) ℂ) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) a.castSucc b.castSucc = (g : Matrix (Fin n) (Fin n) ℂ) a b := by
    intro a b
    simp [GlobalTheory.Branching.embGL_apply]
  have h2 : ((Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n (n + 1) rfl g : GL (Fin (n + 1)) ℂ) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (Fin.last n) (Fin.last n) = 1 := by
    simp [GlobalTheory.Branching.embGL_apply]
  have hev : (-1 : ℂ) ^ (n + n) = 1 := Even.neg_one_pow ⟨n, rfl⟩
  rw [Matrix.det_succ_row _ (Fin.last n), Finset.sum_eq_single (Fin.last n)]
  · simp only [h2, Fin.succAbove_last, Fin.val_last, hev, one_mul, mul_one]
    congr 1
    ext a b
    exact h1 a b
  · intro j _ hj
    have h3 : ((Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n (n + 1) rfl g : GL (Fin (n + 1)) ℂ) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (Fin.last n) j = 0 := by
      simp [GlobalTheory.Branching.embGL_apply, Ne.symm hj]
    rw [h3, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem exists_coef_rhoK_emb {n N : ℕ} (h : n + 1 = N) (lam : ι → DomWeight N) (f : VV ℂ lam)
    (l : Module.Dual ℂ (VV ℂ lam)) :
    ∃ P : MvPolynomial (ι × Fin n × Fin n) ℂ, ∀ g : ι → GL (Fin n) ℂ,
      l (rhoK lam (fun τ => Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N h (g τ)) f) =
        (∏ τ, (g τ : Matrix (Fin n) (Fin n) ℂ).det ^ (lam τ).detShift) *
          eval (fun x => (g x.1 : Matrix (Fin n) (Fin n) ℂ) x.2.1 x.2.2) P := by
  classical
  obtain ⟨P, hP⟩ := exists_coef_rhoK lam f l

  let S : ι × Fin N × Fin N → MvPolynomial (ι × Fin n × Fin n) ℂ := fun x =>
    if hab : x.2.1.val < n ∧ x.2.2.val < n then X (x.1, ⟨x.2.1.val, hab.1⟩, ⟨x.2.2.val, hab.2⟩)
    else if x.2.1 = x.2.2 then 1 else 0
  refine ⟨aeval S P, fun g => ?_⟩
  rw [hP, Formalism.L2.Col.eval_aeval_poly]
  simp only [det_diag_one]
  congr 1
  apply congrArg (fun F => eval F P)
  funext x
  simp only [S, GlobalTheory.Branching.embGL_apply]
  split_ifs <;> simp

theorem prod_zpow_mul_eq_iff (d : ι → ℂ) (x y : ℂ) (hd : ∀ τ, d τ ≠ 0) (a b : ι → ℤ) :
    (∏ τ, d τ ^ a τ) * x = (∏ τ, d τ ^ b τ) * y ↔
      (∏ τ, d τ ^ (a τ - b τ).toNat) * x = (∏ τ, d τ ^ (b τ - a τ).toNat) * y := by

  have split : ∀ (c e : ι → ℤ) τ, d τ ^ c τ = d τ ^ min (c τ) (e τ) * d τ ^ (c τ - e τ).toNat := by
    intro c e τ
    rw [← zpow_natCast, ← zpow_add₀ (hd τ)]
    congr 1
    rcases le_total (c τ) (e τ) with h | h
    · have h' : c τ - e τ ≤ 0 := by linarith
      rw [min_eq_left h, Int.toNat_of_nonpos h', Nat.cast_zero, add_zero]
    · have h' : 0 ≤ c τ - e τ := by linarith
      rw [min_eq_right h, Int.toNat_of_nonneg h']
      ring
  have hne : (∏ τ, d τ ^ min (a τ) (b τ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (hd τ)
  have hmin : ∀ τ, min (b τ) (a τ) = min (a τ) (b τ) := fun τ => min_comm _ _
  rw [Finset.prod_congr rfl fun τ _ => split a b τ, Finset.prod_congr rfl fun τ _ => split b a τ,
    Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [hmin]
  rw [mul_assoc, mul_assoc, mul_right_inj' hne]

theorem equivariant_gl_of_unitary {N n : ℕ} (hN : N = n + 1) (Λ : ι → DomWeight N) (σ : ι → DomWeight n)
    (φ : VV ℂ Λ →ₗ[ℂ] VV ℂ σ)
    (hφ : ∀ (u : ι → Matrix.unitaryGroup (Fin n) ℂ) (v : VV ℂ Λ),
      φ (rhoK Λ (fun τ => Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm (GlobalTheory.Branching.unitaryIncl n (u τ))) v) =
        rhoK σ (fun τ => GlobalTheory.Branching.unitaryIncl n (u τ)) (φ v))
    (g : ι → GL (Fin n) ℂ) (v : VV ℂ Λ) :
    φ (rhoK Λ (fun τ => Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm (g τ)) v) = rhoK σ g (φ v) := by
  classical
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
  intro l
  rw [map_sub, sub_eq_zero]
  obtain ⟨P₁, hP₁⟩ := exists_coef_rhoK_emb hN.symm Λ v (l ∘ₗ φ)
  obtain ⟨P₂, hP₂⟩ := exists_coef_rhoK σ (φ v) l

  let D : ι → MvPolynomial (ι × Fin n × Fin n) ℂ := fun τ =>
    (Matrix.of fun a b => (X (τ, a, b) : MvPolynomial (ι × Fin n × Fin n) ℂ)).det
  have hD : ∀ (y : ι → Matrix (Fin n) (Fin n) ℂ) τ, eval (fun x => y x.1 x.2.1 x.2.2) (D τ) = (y τ).det := by
    intro y τ
    simp only [D]
    rw [RingHom.map_det]
    congr 1
    ext a b
    simp [RingHom.mapMatrix_apply]
  let a : ι → ℤ := fun τ => (Λ τ).detShift
  let b : ι → ℤ := fun τ => (σ τ).detShift

  let Q := (∏ τ, D τ ^ (a τ - b τ).toNat) * P₁ - (∏ τ, D τ ^ (b τ - a τ).toNat) * P₂
  have hQ : ∀ y : ι → Matrix (Fin n) (Fin n) ℂ, eval (fun x => y x.1 x.2.1 x.2.2) Q =
      (∏ τ, (y τ).det ^ (a τ - b τ).toNat) * eval (fun x => y x.1 x.2.1 x.2.2) P₁ -
        (∏ τ, (y τ).det ^ (b τ - a τ).toNat) * eval (fun x => y x.1 x.2.1 x.2.2) P₂ := by
    intro y
    simp only [Q, map_sub, map_mul, map_prod, map_pow, hD]

  have hQ0 : Q = 0 := by
    refine Formalism.L2.Col.eq_zero_of_forall_unitary (fun _ => 1) (fun _ => by simp) Q fun u hu => ?_
    simp only [one_mul]
    let w : ι → Matrix.unitaryGroup (Fin n) ℂ := fun τ =>
      ⟨u τ, Matrix.mem_unitaryGroup_iff'.mpr (by simpa [Matrix.star_eq_conjTranspose] using hu τ)⟩
    have hdet : ∀ τ, (u τ).det ≠ 0 := by
      intro τ h0
      have := congrArg Matrix.det (hu τ)
      rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
      exact zero_ne_one this
    have e := congrArg l (hφ w v)
    have e₁ := hP₁ (fun τ => GlobalTheory.Branching.unitaryIncl n (w τ))
    have e₂ := hP₂ (fun τ => GlobalTheory.Branching.unitaryIncl n (w τ))
    simp only [LinearMap.comp_apply] at e₁
    rw [e₁, e₂] at e
    simp only [GlobalTheory.Branching.unitaryIncl_coe] at e
    rw [hQ u, sub_eq_zero]
    exact (prod_zpow_mul_eq_iff (fun τ => (u τ).det) _ _ hdet a b).mp e
  have hg : ∀ τ, ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det ≠ 0 := fun τ =>
    by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have e₃ := hQ (fun τ => (g τ : Matrix (Fin n) (Fin n) ℂ))
  rw [hQ0, map_zero, eq_comm, sub_eq_zero] at e₃
  have e₁ := hP₁ g
  simp only [LinearMap.comp_apply] at e₁
  rw [e₁, hP₂ g]
  exact (prod_zpow_mul_eq_iff (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det) _ _ hg a b).mpr e₃

end GlobalTheory.Branching.Family
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeFunctionEquivalence
section
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SphJet.PsEquivar

open GlobalTheory.Dec.Local

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W}

theorem eventually_fderiv_ps (hl : IsHCParam lam) (hτ : IsTau ε (lowK ε lam) τ w)
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y * Jm ε = Jm ε * Y) :
    ∀ᶠ z in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ),
      fderiv ℂ (ps ε lam τ w) z (z * Y) = ps ε lam τ w z * fderiv ℂ (fun y => τ (prJ ε y)) 1 Y ∧
      fderiv ℂ (ps ε lam τ w) z (Y * z) = fderiv ℂ (fun y => τ (prJ ε y)) 1 Y * ps ε lam τ w z := by
  have hf1 : HasFDerivAt (fun y => τ (prJ ε y)) (fderiv ℂ (fun y => τ (prJ ε y)) 1) 1 :=
    (eventually_differentiableAt_tau hτ).self_of_nhds.hasFDerivAt
  have hτ1 : τ 1 = 1 := hτ.2.1.1
  have hc : HasDerivAt (fun t : ℂ => (1 : Matrix (Fin n) (Fin n) ℂ) + t • Y) Y 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const Y).const_add (1 : Matrix (Fin n) (Fin n) ℂ)
  have hcJ : ∀ t : ℂ, prJ ε (1 + t • Y) = 1 + t • Y := fun t =>
    prJ_of_comm (by rw [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hY])
  have hτc : HasDerivAt (fun t : ℂ => τ (prJ ε (1 + t • Y))) (fderiv ℂ (fun y => τ (prJ ε y)) 1 Y) 0 :=
    hf1.comp_hasDerivAt_of_eq 0 hc (by simp)
  obtain ⟨hUo, hU1, hUd, -⟩ := psBasic n ε lam W τ w hl hτ
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] (Fin n → Fin n → ℂ) :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℂ).symm.toLinearMap
  have hdiff : ∀ᶠ z in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), DifferentiableAt ℂ (ps ε lam τ w) z := by
    have hm : L 1 ∈ {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε} := hU1 1 Matrix.PosDef.one
    filter_upwards [L.continuous.continuousAt.preimage_mem_nhds (hUo.mem_nhds hm)] with z hz
    exact ((hUd (L z) hz).differentiableAt (hUo.mem_nhds hz)).comp z L.differentiableAt
  have hmul := eventually_ps_mul psBasic GlobalTheory.Dec.Equivar.psEquiv hl hτ
  have hR : ∀ᶠ p : Matrix (Fin n) (Fin n) ℂ × ℂ in 𝓝 ((1 : Matrix (Fin n) (Fin n) ℂ), (0 : ℂ)),
      ps ε lam τ w (p.1 * (1 + p.2 • Y)) = ps ε lam τ w p.1 * τ (prJ ε (1 + p.2 • Y)) := by
    have hcont : Continuous (fun p : Matrix (Fin n) (Fin n) ℂ × ℂ =>
        (((1 : Matrix (Fin n) (Fin n) ℂ), p.1), ((1 : Matrix (Fin n) (Fin n) ℂ) + p.2 • Y,
          (1 : Matrix (Fin n) (Fin n) ℂ)))) := by fun_prop
    have ht := hcont.tendsto ((1 : Matrix (Fin n) (Fin n) ℂ), (0 : ℂ))
    simp only [zero_smul, add_zero] at ht
    filter_upwards [ht.eventually hmul] with p hp
    have key := sub_eq_zero.mp hp
    simp only [prJ_one, hτ1, one_mul, mul_one] at key
    calc ps ε lam τ w (p.1 * (1 + p.2 • Y)) = ps ε lam τ w (p.1 * prJ ε (1 + p.2 • Y)) := by rw [hcJ]
      _ = _ := key
  have hL : ∀ᶠ p : Matrix (Fin n) (Fin n) ℂ × ℂ in 𝓝 ((1 : Matrix (Fin n) (Fin n) ℂ), (0 : ℂ)),
      ps ε lam τ w ((1 + p.2 • Y) * p.1) = τ (prJ ε (1 + p.2 • Y)) * ps ε lam τ w p.1 := by
    have hcont : Continuous (fun p : Matrix (Fin n) (Fin n) ℂ × ℂ =>
        (((1 : Matrix (Fin n) (Fin n) ℂ) + p.2 • Y, (1 : Matrix (Fin n) (Fin n) ℂ)),
          ((1 : Matrix (Fin n) (Fin n) ℂ), p.1))) := by fun_prop
    have ht := hcont.tendsto ((1 : Matrix (Fin n) (Fin n) ℂ), (0 : ℂ))
    simp only [zero_smul, add_zero] at ht
    filter_upwards [ht.eventually hmul] with p hp
    have key := sub_eq_zero.mp hp
    simp only [prJ_one, hτ1, one_mul, mul_one] at key
    calc ps ε lam τ w ((1 + p.2 • Y) * p.1) = ps ε lam τ w (prJ ε (1 + p.2 • Y) * p.1) := by rw [hcJ]
      _ = _ := key
  rw [nhds_prod_eq] at hR hL
  filter_upwards [hdiff, hR.curry, hL.curry] with z hz hRz hLz
  have hps := hz.hasFDerivAt
  constructor
  · have h1 : HasDerivAt (fun t : ℂ => ps ε lam τ w (z * (1 + t • Y)))
        (fderiv ℂ (ps ε lam τ w) z (z * Y)) 0 :=
      hps.comp_hasDerivAt_of_eq 0 (hc.const_mul z) (by simp)
    have h2 : HasDerivAt (fun t : ℂ => ps ε lam τ w z * τ (prJ ε (1 + t • Y)))
        (ps ε lam τ w z * fderiv ℂ (fun y => τ (prJ ε y)) 1 Y) 0 := hτc.const_mul _
    exact h1.unique (h2.congr_of_eventuallyEq hRz)
  · have h1 : HasDerivAt (fun t : ℂ => ps ε lam τ w ((1 + t • Y) * z))
        (fderiv ℂ (ps ε lam τ w) z (Y * z)) 0 :=
      hps.comp_hasDerivAt_of_eq 0 (hc.mul_const z) (by simp)
    have h2 : HasDerivAt (fun t : ℂ => τ (prJ ε (1 + t • Y)) * ps ε lam τ w z)
        (fderiv ℂ (fun y => τ (prJ ε y)) 1 Y * ps ε lam τ w z) 0 := hτc.mul_const _
    exact h1.unique (h2.congr_of_eventuallyEq hLz)

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {E : Fin n → Fin n → Module.End ℂ V}
  {j : W →ₗᵢ[ℂ] V}

theorem fderiv_tau_of_inK {abelian₂ : Fin n → ℝ} (hτ : IsTau ε abelian₂ τ w) (hT : TauTie ε E j τ)
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) {v v' : W} (hv : j v' = actM E (Y.map star) (j v)) :
    fderiv ℂ (fun y => τ (prJ ε y)) 1 Y v = v' := by
  have hf1 : HasFDerivAt (fun y => τ (prJ ε y)) (fderiv ℂ (fun y => τ (prJ ε y)) 1) 1 :=
    (eventually_differentiableAt_tau hτ).self_of_nhds.hasFDerivAt
  have hγ : HasDerivAt (fun u : ℂ => NormedSpace.exp (u • Y)) Y 0 := by
    simpa using hasDerivAt_exp_smul_const (𝕂 := ℂ) Y (0 : ℂ)
  have hcommc : ∀ u : ℂ, prJ ε (NormedSpace.exp (u • Y)) = NormedSpace.exp (u • Y) := fun u =>
    prJ_of_comm ((Commute.smul_left (show Commute Y (Jm ε) from hY.2) u).exp_left).eq
  have hg : HasDerivAt (fun u : ℂ => τ (NormedSpace.exp (u • Y)) v)
      (fderiv ℂ (fun y => τ (prJ ε y)) 1 Y v) ((0 : ℝ) : ℂ) := by
    have h1 := hf1.comp_hasDerivAt_of_eq 0 hγ (by simp)
    have h2 := (ContinuousLinearMap.apply ℂ W v).hasFDerivAt.comp_hasDerivAt 0 h1
    rw [Complex.ofReal_zero]
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    simp [hcommc u]
  have hh : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have h4 : HasDerivAt (fun t : ℝ => τ (NormedSpace.exp ((t : ℂ) • Y)) v)
      (fderiv ℂ (fun y => τ (prJ ε y)) 1 Y v) 0 := by
    have h3 := HasDerivAt.scomp (x := (0 : ℝ)) hg hh
    rw [one_smul] at h3
    exact h3
  exact ((hT Y hY v v' hv).unique h4).symm

theorem actM_single (a b : Fin n) : actM E (Matrix.single a b (1 : ℂ)) = E a b := by
  simp [actM, Matrix.single_apply, ite_and]

theorem actM_add (X Y : Matrix (Fin n) (Fin n) ℂ) : actM E (X + Y) = actM E X + actM E Y := by
  simp [actM, add_smul, Finset.sum_add_distrib]

theorem actM_smul (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) : actM E (c • X) = c • actM E X := by
  simp [actM, Finset.smul_sum, mul_smul]

theorem single_comm_Jm {a b : Fin n} (h : ε a = ε b) :
    Matrix.single a b (1 : ℂ) * Jm ε = Jm ε * Matrix.single a b (1 : ℂ) := by
  ext i k
  rw [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
  by_cases h1 : a = i ∧ b = k
  · rcases h1 with ⟨rfl, rfl⟩
    rw [if_pos ⟨rfl, rfl⟩, h, one_mul, mul_one]
  · rw [if_neg h1, zero_mul, mul_zero]

theorem inK_of_skew {Y : Matrix (Fin n) (Fin n) ℂ} (h : Yᴴ = -Y) (h' : Y * Jm ε = Jm ε * Y) : inK ε Y := by
  refine ⟨?_, h'⟩
  show Yᴴ * Jm ε + Jm ε * Y = 0
  rw [h, neg_mul, h', neg_add_cancel]

private lemma actM_mem_kSpan_of_block_diagonal {u : V} (Z : Matrix (Fin n) (Fin n) ℂ) (hZ : ∀ c d, ε c ≠ ε d → Z c d = 0)
    {x : V} (hx : x ∈ kSpan ε E u) : actM E Z x ∈ kSpan ε E u := by
  unfold actM
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun c _ => ?_
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun d _ => ?_
  by_cases hcd : ε c = ε d
  · rw [LinearMap.smul_apply]
    refine Submodule.smul_mem _ _ ?_
    simp only [kSpan, Submodule.mem_sInf] at hx ⊢
    exact fun S hS => hS.2 c d hcd x (hx S hS)
  · rw [hZ c d hcd, zero_smul, LinearMap.zero_apply]
    exact Submodule.zero_mem _

theorem fderiv_tau_thE {abelian₂ Λ : Fin n → ℝ} {u : V} (hτ : IsTau ε abelian₂ τ w) (hL : LowData ε E Λ u j)
    (hT : TauTie ε E j τ) {a b : Fin n} (hab : ε a = ε b) (v : W) :
    j (fderiv ℂ (fun y => τ (prJ ε y)) 1 (thE ε (a, b)) v) = E a b (j v) := by
  set D := fderiv ℂ (fun y => τ (prJ ε y)) 1 with hD
  set S : Matrix (Fin n) (Fin n) ℂ := Matrix.single b a 1 with hS
  set T : Matrix (Fin n) (Fin n) ℂ := Matrix.single a b 1 with hT'
  have hSh : Sᴴ = T := by simp [S, T]
  have hTh : Tᴴ = S := by simp [S, T]
  have hSJ : S * Jm ε = Jm ε * S := single_comm_Jm hab.symm
  have hTJ : T * Jm ε = Jm ε * T := single_comm_Jm hab
  have hA : inK ε (S - T) := inK_of_skew (by rw [Matrix.conjTranspose_sub, hSh, hTh, neg_sub])
    (by rw [sub_mul, mul_sub, hSJ, hTJ])
  have hB : inK ε (Complex.I • (S + T)) := inK_of_skew
    (by simp [Matrix.conjTranspose_smul, hSh, hTh, add_comm])
    (by rw [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, hSJ, hTJ])
  have hS0 : ∀ c d, ε c ≠ ε d → S c d = 0 := by
    intro c d hcd
    simp only [S, Matrix.single_apply]
    split_ifs with h1
    · rcases h1 with ⟨rfl, rfl⟩
      exact absurd hab.symm hcd
    · rfl
  have hT0 : ∀ c d, ε c ≠ ε d → T c d = 0 := by
    intro c d hcd
    simp only [T, Matrix.single_apply]
    split_ifs with h1
    · rcases h1 with ⟨rfl, rfl⟩
      exact absurd hab hcd
    · rfl
  have hjv : j v ∈ kSpan ε E u := by
    rw [← hL.2.2.2.2]
    exact LinearMap.mem_range_self _ v
  have hmA : actM E ((S - T).map star) (j v) ∈ LinearMap.range j.toLinearMap := by
    rw [hL.2.2.2.2]
    exact actM_mem_kSpan_of_block_diagonal _ (fun c d hcd => by simp [hS0 c d hcd, hT0 c d hcd]) hjv
  have hmB : actM E ((Complex.I • (S + T)).map star) (j v) ∈ LinearMap.range j.toLinearMap := by
    rw [hL.2.2.2.2]
    exact actM_mem_kSpan_of_block_diagonal _ (fun c d hcd => by simp [hS0 c d hcd, hT0 c d hcd]) hjv
  obtain ⟨xA, hxA⟩ := LinearMap.mem_range.mp hmA
  obtain ⟨xB, hxB⟩ := LinearMap.mem_range.mp hmB
  have hDA : D (S - T) v = xA := fderiv_tau_of_inK hτ hT hA hxA
  have hDB : D (Complex.I • (S + T)) v = xB := fderiv_tau_of_inK hτ hT hB hxB
  have hAm : (S - T).map star = S + (-1 : ℂ) • T := by
    ext c d
    simp only [S, T, Matrix.map_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.single_apply]
    split_ifs <;> simp <;> ring
  have hBm : (Complex.I • (S + T)).map star = (-Complex.I) • S + (-Complex.I) • T := by
    ext c d
    simp only [S, T, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply]
    split_ifs <;> simp <;> ring
  have hthE : thE ε (a, b) = -((1 / 2 : ℂ) • ((S - T) - Complex.I • (Complex.I • (S + T)))) := by
    rw [smul_smul, Complex.I_mul_I]
    simp only [thE, Formalism.REAL.sgn, hab, if_true, Complex.ofReal_one]
    module
  rw [hthE, map_neg, map_smul, map_sub, map_smul]
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply]
  rw [hDA, hDB]
  simp only [map_neg, map_smul, map_sub]
  have hxA' : j xA = actM E ((S - T).map star) (j v) := hxA
  have hxB' : j xB = actM E ((Complex.I • (S + T)).map star) (j v) := hxB
  rw [hxA', hxB', hAm, hBm, actM_add, actM_add, actM_smul, actM_smul, actM_smul, actM_single,
    actM_single]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_add, smul_smul, mul_neg,
    Complex.I_mul_I]
  module

theorem psFunEquiv : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (W : Type) [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), IsHCParam lam →
    IsTau ε (lowK ε lam) τ w → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (u : V) (j : W →ₗᵢ[ℂ] V), LowData ε E (lowK ε lam) u j →
    TauTie ε E j τ → FunEquiv ε E j (ps ε lam τ w) := by
  intro n ε lam W _ _ τ w hl hτ V _ _ E u j hL hT a b hab
  have hY : thE ε (a, b) * Jm ε = Jm ε * thE ε (a, b) := by
    simp only [thE, smul_mul_assoc, mul_smul_comm, single_comm_Jm hab.symm]
  filter_upwards [eventually_fderiv_ps hl hτ hY] with z hz
  refine ⟨fun x x' hx => ?_, fun y y' x hy => ?_⟩
  · rw [hz.1, ContinuousLinearMap.mul_apply]
    congr 1
    apply j.injective
    rw [fderiv_tau_thE hτ hL hT hab x, hx]
  · rw [hz.2, ContinuousLinearMap.mul_apply, ← j.inner_map_map y, fderiv_tau_thE hτ hL hT hab,
      ← j.inner_map_map y', hy, hL.2.1 b a]
    simp [Formalism.REAL.sgn, hab]

end GlobalTheory.SphJet.PsEquivar
end
end

