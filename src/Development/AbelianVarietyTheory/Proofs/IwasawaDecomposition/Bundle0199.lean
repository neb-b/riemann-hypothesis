module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0003
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralCompContinuousLinearEquiv
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.DualLattices.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSelfDualHaarMeasureInfiniteAdeles
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.SdInf

theorem existsUnique_of_equiv {V W : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (e : V ≃+ W) (he : Continuous e) (he' : Continuous e.symm) (l : V → V → ℝ)
    (ha : ∀ x x' y, l (x + x') y = l x y + l x' y) (hs : ∀ x y, l x y = l y x)
    (hc : ∀ y, Continuous fun x => l x y) (hn : ∀ x, (∀ y, l x y = 0) → x = 0) :
    ∃! μ : Measure V,
      SelfDual μ (fun x y => Complex.exp (2 * Real.pi * Complex.I * ((l x y : ℝ) : ℂ))) :=
  _root_.UpperTheory.Reformulated.B.Yzb9.existsUnique_of_equiv e he he' l ha hs hc hn

theorem exists_log_char {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (f : W → ℂ)
    (hf : Continuous f) (h1 : ∀ x, ‖f x‖ = 1) (hadd : ∀ x y, f (x + y) = f x * f y) :
    ∃ L : W → ℝ, Continuous L ∧ (∀ x y, L (x + y) = L x + L y) ∧
      ∀ x, f x = Complex.exp (2 * Real.pi * Complex.I * ((L x : ℝ) : ℂ)) := by
  let g : W → Circle := fun x => ⟨f x, by simp [Submonoid.unitSphere, h1]⟩
  have hg : Continuous g := hf.subtype_mk _
  have hgadd : ∀ x y, g (x + y) = g x * g y := fun x y => Subtype.ext (hadd x y)
  have h0 : g 0 = 1 := by
    have := hgadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  obtain ⟨G, ⟨hG0, hG⟩, -⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts ⟨g, hg⟩ 0 0
    (by simp [h0])
  have hG' : ∀ x, Circle.exp (G x) = g x := fun x => congrFun hG x
  have hGadd : ∀ x y, G (x + y) = G x + G y := by
    intro x y
    have hc : Continuous fun y : W => G (x + y) - G x - G y := by fun_prop
    have := Circle.isCoveringMap_exp.const_of_comp hc (fun y y' => by
      simp only [Circle.exp_sub, hG', hgadd]
      simp) y 0
    simp only [add_zero, hG0, sub_self] at this
    linarith
  refine ⟨fun x => G x / (2 * Real.pi), by fun_prop, fun x y => by simp only [hGadd, add_div], fun x => ?_⟩
  have : f x = ((Circle.exp (G x) : Circle) : ℂ) := by rw [hG']
  rw [this, Circle.coe_exp]
  congr 1
  have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R]

theorem trace_tmul (c : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (c ⊗ₜ[F] e) = c * algebraMap F R (Algebra.trace F E e) := by
  have h1 : (c ⊗ₜ[F] e : R ⊗[F] E) = c • ((1 : R) ⊗ₜ[F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, smul_eq_mul]
  congr 1
  rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange]
  congr 1
  ext x
  simp

theorem trace_nondeg [Algebra.IsSeparable F E] (z : R ⊗[F] E)
    (h : ∀ w, Algebra.trace R (R ⊗[F] E) (z * w) = 0) : z = 0 := by
  classical
  let b := Module.finBasis F E
  let b' := (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) b
  have key : ∀ (k) (z : R ⊗[F] E), (Algebra.TensorProduct.basis R b').repr z k =
      Algebra.trace R (R ⊗[F] E) (z * (1 : R) ⊗ₜ[F] b k) := by
    intro k z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy, add_mul]
    | tmul a e =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, trace_tmul, Algebra.TensorProduct.basis_repr_tmul]
      simp [b', LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
  refine (Algebra.TensorProduct.basis R b').ext_elem fun k => ?_
  rw [key, h]; simp

variable (σ : E →ₐ[F] E)

omit [FiniteDimensional F E] in
theorem sigR_sigR (hσ : ∀ x, σ (σ x) = x) (z : R ⊗[F] E) : sigR R σ (sigR R σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a e =>
    show a ⊗ₜ[F] σ (σ e) = _
    rw [hσ]

theorem trace_sigR (z : R ⊗[F] E) :
    Algebra.trace R (R ⊗[F] E) (sigR R σ z) = Algebra.trace R (R ⊗[F] E) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a e =>
    show Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] σ e) = _
    rw [trace_tmul, trace_tmul]
    congr 2
    exact Algebra.trace_eq_of_algEquiv
      (AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)) e

variable {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

omit [FiniteDimensional F E] in
theorem BR_add (X X' Y : Fin 1 → Fin M → R ⊗[F] E) :
    BR R σ J (X + X') Y = BR R σ J X Y + BR R σ J X' Y := by
  simp only [BR, hR, Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

omit [FiniteDimensional F E] in
theorem BR_smul (t : R) (X Y : Fin 1 → Fin M → R ⊗[F] E) :
    BR R σ J X (t • Y) = BR R σ J X Y * t := by
  simp only [BR, hR, Formalism.UG.hform, Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul,
    smul_eq_mul, mul_comm t, Finset.sum_mul]

theorem BR_symm (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (X Y : Fin 1 → Fin M → R ⊗[F] E) :
    BR R σ J X Y = BR R σ J Y X := by
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← trace_sigR R σ]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, Formalism.UG.hform, map_sum, map_mul, sigR_sigR R σ hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : sigR R σ (JR R J j i) = JR R J i j := by
    show (1 : R) ⊗ₜ[F] σ (J j i) = (1 : R) ⊗ₜ[F] J i j
    rw [hJ.1]
  rw [this]; ring

theorem BR_nondeg [Algebra.IsSeparable F E] (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J)
    (X : Fin 1 → Fin M → R ⊗[F] E) (h : ∀ Y, BR R σ J X Y = 0) : X = 0 := by
  have h1 : Matrix.vecMul (fun i => sigR R σ (X 0 i)) (JR R J) = 0 := by
    funext j
    refine trace_nondeg R _ fun w => ?_
    have := h fun _ => Pi.single j w
    simpa [BR, hR, Formalism.UG.hform, Pi.single_apply, Matrix.vecMul, dotProduct, Finset.sum_mul] using this
  have hu : IsUnit (JR R J : Matrix (Fin M) (Fin M) (R ⊗[F] E)).det := by
    have : (JR R J : Matrix (Fin M) (Fin M) (R ⊗[F] E)).det = inclR R J.det :=
      ((inclR R).map_det J).symm
    rw [this]
    exact (Ne.isUnit hJ.2).map _
  have h2 := congrArg (fun v => Matrix.vecMul v (JR R J)⁻¹) h1
  simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one,
    Matrix.zero_vecMul] at h2
  funext a i
  rw [Subsingleton.elim a 0, ← sigR_sigR R σ hσ (X 0 i), congrFun h2 i]
  simp

theorem BR_continuous [TopologicalSpace R] [IsTopologicalRing R] (Y : Fin 1 → Fin M → R ⊗[F] E) :
    Continuous fun X => BR R σ J X Y := by
  have h1 : Continuous (Algebra.trace R (R ⊗[F] E)) := IsModuleTopology.continuous_of_linearMap _
  have h2 := GlobalTheory.AdelicUnitaryTop.continuous_sigR R σ
  unfold BR hR Formalism.UG.hform
  fun_prop

end Alg

theorem exists_equiv_Ainf (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    ∃ a : Ainf F ≃+ (InfinitePlace F → ℝ), Continuous a ∧ Continuous a.symm := by
  refine ⟨AddEquiv.piCongrRight fun v =>
    (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).toAddEquiv, ?_, ?_⟩
  · exact continuous_pi fun v =>
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).continuous.comp
        (continuous_apply v)
  · exact continuous_pi fun v =>
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.continuous.comp
        (continuous_apply v)

theorem existsUnique_selfDual_inf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → (∃! ν, SdR (Ainf F) (psiInf F ψ) ν) ∧ ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∃! μ, SdW F E σ M J (Ainf F) (psiInf F ψ) 1 μ := by
  intro F E _ _ _ _ _ σ hCM ψ hψ
  obtain ⟨hF, -, -, hσ'⟩ := hCM
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply φ.injective
    rw [hσ', hσ', star_star]
  have hnd := (_root_.GlobalTheory.GaugeEx.CharLoc.char_local F ψ hψ).2.2
  obtain ⟨a, ha, ha'⟩ := exists_equiv_Ainf F
  have hpc : Continuous (psiInf F ψ) := hψ.1.comp (continuous_id.prodMk continuous_const)
  obtain ⟨L₀, hL₀c, hL₀a, hL₀⟩ := exists_log_char (fun u => psiInf F ψ (a.symm u)) (hpc.comp ha')
    (fun u => hψ.2.1 _) (fun u v => by
      simp only [psiInf, map_add (f := _), ← AddChar.map_add_eq_mul]
      congr 1
      exact Prod.ext rfl (add_zero _).symm)
  let L : Ainf F → ℝ := fun x => L₀ (a x)
  have hLc : Continuous L := hL₀c.comp ha
  have hLa : ∀ x y, L (x + y) = L x + L y := fun x y => by simp only [L, map_add (f := _), hL₀a]
  have hL : ∀ x, psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I * ((L x : ℝ) : ℂ)) :=
    fun x => by simpa using hL₀ (a x)
  have hLn : ∀ x, (∀ y, L (x * y) = 0) → x = 0 := fun x h => hnd x fun y => by simp [hL, h]
  refine ⟨?_, fun M J hJ => ?_⟩
  · have := existsUnique_of_equiv a ha ha' (fun s t => L (s * t)) (fun x x' y => by rw [add_mul, hLa])
      (fun x y => by rw [mul_comm]) (fun y => hLc.comp (continuous_id.mul continuous_const)) hLn
    simpa only [SdR, hL] using this
  · simp only [SdW, hL]
    let c := (Algebra.TensorProduct.basis (Ainf F) (Module.finBasis F E)).equivFun
    have hc : Continuous c := IsModuleTopology.continuous_of_linearMap c.toLinearMap
    have hc' : Continuous c.symm := IsModuleTopology.continuous_of_linearMap c.symm.toLinearMap
    let e : (Fin 1 → Fin M → Ainf F ⊗[F] E) ≃+
        (Fin 1 → Fin M → Fin (Module.finrank F E) → InfinitePlace F → ℝ) :=
      AddEquiv.piCongrRight fun _ => AddEquiv.piCongrRight fun _ =>
        c.toAddEquiv.trans (AddEquiv.piCongrRight fun _ => a)
    refine existsUnique_of_equiv e ?_ ?_ (fun X Y => L (BR (Ainf F) σ J X Y))
      (fun X X' Y => by rw [BR_add, hLa]) (fun X Y => by rw [BR_symm _ σ J hσ hJ])
      (fun Y => hLc.comp (BR_continuous _ σ J Y))
      (fun X h => BR_nondeg _ σ J hσ hJ X fun Y => hLn _ fun t => by rw [← BR_smul]; exact h _)
    · show Continuous fun (X : Fin 1 → Fin M → Ainf F ⊗[F] E) i j k => a (c (X i j) k)
      fun_prop
    · show Continuous fun (X : Fin 1 → Fin M → Fin (Module.finrank F E) → InfinitePlace F → ℝ) i j =>
        c.symm fun k => a.symm (X i j k)
      fun_prop

end GlobalTheory.GaugeEx.SdInf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryGroupIntertwinerOfHighestWeightPoly
section
open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HighestPolynomial

open MvPolynomial ReciprocityTheory.PGsh

theorem differentiable_rowSubst {k : ℕ} {κ : Type} {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (P : MvPolynomial (Fin k × κ) ℂ) (ψ : MvPolynomial (Fin k × κ) ℂ →ₗ[ℂ] F) :
    Differentiable ℂ fun g : Fin k → Fin k → ℂ => ψ (rowSubst (Matrix.of g) P) := by
  induction P using MvPolynomial.induction_on generalizing ψ with
  | C c => simp only [rowSubst_C]; exact differentiable_const _
  | add p q hp hq => simp only [map_add (f := _)]; exact (hp ψ).add (hq ψ)
  | mul_X p s hp =>
    have h : (fun g : Fin k → Fin k → ℂ => ψ (rowSubst (Matrix.of g) (p * X s))) =
        fun g : Fin k → Fin k → ℂ => ∑ l, g l s.1 •
          (ψ ∘ₗ LinearMap.mulRight ℂ (X (l, s.2))) (rowSubst (Matrix.of g) p) := by
      funext g
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_mul, rowSubst_X, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [LinearMap.comp_apply, LinearMap.mulRight_apply, ← map_smul, MvPolynomial.smul_eq_C_mul, Matrix.of_apply]
      congr 1
      ring
    rw [h]
    refine Differentiable.fun_sum fun l _ => Differentiable.smul ?_ (hp _)
    fun_prop

theorem totalDegree_rowSubst_le {k : ℕ} {κ : Type} (g : Matrix (Fin k) (Fin k) ℂ)
    (P : MvPolynomial (Fin k × κ) ℂ) : (rowSubst g P).totalDegree ≤ P.totalDegree :=
  totalDegree_aeval_le _ (fun _ => totalDegree_finsetSum_le fun _ _ =>
    (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])) P

theorem fischer_conj {k : ℕ} {κ : Type} (P Q : MvPolynomial (Fin k × κ) ℂ) :
    starRingEnd ℂ (fischer P Q) = fischer Q P := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [fischer_eq_sum P Q (P.support ∪ Q.support) Finset.subset_union_left,
    fischer_eq_sum Q P (P.support ∪ Q.support) Finset.subset_union_right, map_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  simp only [fw, map_mul, Complex.conj_conj, map_natCast]
  ring

theorem fischer_self_re_nonneg {k : ℕ} {κ : Type} (P : MvPolynomial (Fin k × κ) ℂ) : 0 ≤ (fischer P P).re := by
  rw [fischer_eq_sum P P P.support subset_rfl, Complex.re_sum]
  refine Finset.sum_nonneg fun A _ => ?_
  rw [Complex.mul_conj, fw, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

@[reducible] def fischerCore {k : ℕ} {κ : Type} (S : Submodule ℂ (MvPolynomial (Fin k × κ) ℂ)) :
    InnerProductSpace.Core ℂ S where
  inner x y := fischer y.1 x.1
  conj_inner_symm x y := fischer_conj _ _
  re_inner_nonneg x := fischer_self_re_nonneg _
  add_left x y z := fischer_add_right _ _ _
  smul_left x y r := fischer_smul_right _ _ _
  definite x hx := by
    by_contra h
    exact fischer_self_ne_zero x.1 (fun h' => h (Subtype.ext h')) hx

theorem mem_UJset_allPos {k : ℕ} {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ UJset (allPos k)) : gᴴ * g = 1 := by
  have hJ : Formalism.REAL.Jm (allPos k) = 1 := by simp [Formalism.REAL.Jm, allPos]
  have h : gᴴ * Formalism.REAL.Jm (allPos k) * g = Formalism.REAL.Jm (allPos k) := hg
  rwa [hJ, Matrix.mul_one] at h

theorem exists_intertwiner_of_embedding (k : ℕ) (κ : Type) (ν : Fin k → ℕ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (τ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H))
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (j : E →ₗ[ℂ] MvPolynomial (Fin k × κ) ℂ) (hj : Function.Injective j)
    (hin : ∀ x y : E, inner ℂ x y = fischer (j y) (j x))
    (hst : ∀ g x, ∃ y, j y = rowSubst g (j x)) (D : E)
    (hτ : IsURepOn (UJset (allPos k)) τ) (hK : IsKTypeOf (allPos k) τ (fun a => (ν a : ℝ)) ⊤) (hD : j D ≠ 0)
    (hu : ∀ g, IsUpperUnitri g → rowSubst g (j D) = j D)
    (hd : ∀ d : Fin k → ℂ, rowSubst (Matrix.diagonal d) (j D) = (∏ a, d a ^ ν a) • j D) :
    ∃ L : H →ₗ[ℂ] MvPolynomial (Fin k × κ) ℂ,
      (∀ g ∈ UJset (allPos k), ∀ u, L (τ g u) = rowSubst g (L u)) ∧ ∃ v, L v = j D := by
  obtain ⟨r, hr⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hj)
  have hrj : ∀ x, r (j x) = x := fun x => LinearMap.congr_fun hr x
  let π : Matrix (Fin k) (Fin k) ℂ → (E →L[ℂ] E) := fun g =>
    LinearMap.toContinuousLinearMap (r ∘ₗ (rowSubst g).toLinearMap ∘ₗ j)
  have hπ : ∀ g x, π g x = r (rowSubst g (j x)) := fun g x => rfl
  have hjπ : ∀ g x, j (π g x) = rowSubst g (j x) := by
    intro g x
    obtain ⟨y, hy⟩ := hst g x
    rw [hπ, ← hy, hrj]
  have hdiff : ∀ w : E, Differentiable ℂ fun g : Fin k → Fin k → ℂ => π (Matrix.of g) w := fun w =>
    differentiable_rowSubst (j w) r
  have hrep : IsURepOn (UJset (allPos k)) π := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · ext x
      apply hj
      rw [hjπ, rowSubst_one]
      rfl
    · intro a _ b _
      ext x
      apply hj
      change _ = j (π a (π b x))
      rw [hjπ, hjπ, hjπ, rowSubst_mul]
    · intro g hg v
      rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ _ _ _ _ v, hin, hin, hjπ, fischer_rowSubst,
        rowSubst_mul, mem_UJset_allPos hg, rowSubst_one]
    · intro v
      exact (hdiff v).continuous.continuousOn
  obtain ⟨L, hL, v, hv⟩ := _root_.GlobalTheory.HighestWeightMap.exists_intertwiner k (fun a => (ν a : ℝ)) H τ E π D hτ hK hrep (fun w => hdiff w _)
    (fun h => hD (by rw [h, map_zero]))
    (by
      intro a b hab s
      apply hj
      rw [hjπ]
      refine hu _ ⟨fun i => ?_, fun i l hl => ?_⟩
      · rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply_of_ne, add_zero]
        rintro ⟨h1, h2⟩
        exact hab.ne (h1.trans h2.symm)
      · rw [Matrix.add_apply, Matrix.one_apply_ne hl.ne', Matrix.single_apply_of_ne, add_zero]
        rintro ⟨h1, h2⟩
        subst h1 h2
        exact lt_asymm hab hl)
    (by
      intro θ _
      apply hj
      rw [hjπ, hd, map_smul]
      congr 1
      push_cast
      rw [Finset.sum_mul, Complex.exp_sum]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [← Complex.exp_nat_mul, mul_assoc])
  exact ⟨j ∘ₗ L, fun g hg u => by rw [LinearMap.comp_apply, hL g hg, hjπ]; rfl, v, by rw [LinearMap.comp_apply, hv]⟩

theorem exists_intertwiner : ∀ (k : ℕ) (κ : Type) [Fintype κ] (ν : Fin k → ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (τ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (Δ : MvPolynomial (Fin k × κ) ℂ), IsURepOn (UJset (allPos k)) τ → IsKTypeOf (allPos k) τ (fun a => (ν a : ℝ)) ⊤ → Δ ≠ 0 → (∀ g, ReciprocityTheory.PGsh.IsUpperUnitri g → ReciprocityTheory.PGsh.rowSubst g Δ = Δ) → (∀ d : Fin k → ℂ, ReciprocityTheory.PGsh.rowSubst (Matrix.diagonal d) Δ = (∏ a, d a ^ ν a) • Δ) → ∃ L : H →ₗ[ℂ] MvPolynomial (Fin k × κ) ℂ, (∀ g ∈ UJset (allPos k), ∀ u, L (τ g u) = ReciprocityTheory.PGsh.rowSubst g (L u)) ∧ ∃ v, L v = Δ := by
  intro k κ _ ν H _ _ _ τ Δ hτ hK hΔ hu hd
  let S : Submodule ℂ (MvPolynomial (Fin k × κ) ℂ) := restrictTotalDegree (Fin k × κ) ℂ Δ.totalDegree
  have hfin : FiniteDimensional ℂ S := inferInstanceAs (Module.Finite ℂ (restrictTotalDegree (Fin k × κ) ℂ Δ.totalDegree))
  letI : InnerProductSpace.Core ℂ S := fischerCore S
  letI : NormedAddCommGroup S := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ S := InnerProductSpace.ofCore _
  exact exists_intertwiner_of_embedding k κ ν H τ S S.subtype S.injective_subtype (fun _ _ => rfl)
    (fun g x => ⟨⟨rowSubst g x.1, (mem_restrictTotalDegree _ _ _).mpr
      ((totalDegree_rowSubst_le g x.1).trans ((mem_restrictTotalDegree _ _ _).mp x.2))⟩, rfl⟩)
    ⟨Δ, (mem_restrictTotalDegree _ _ _).mpr le_rfl⟩ hτ hK hΔ hu hd

end GlobalTheory.HighestPolynomial

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvMulIntAway
section
open NumberField IsDedekindDomain Matrix Formalism.L2.Col GlobalTheory.InertNbr
open Formalism.L2.DIV (Pl kP St resS oToS idS cmpS)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.InertNbr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem idS_smul_latS (I : Ideal (𝓞 E)) (N : Submodule (𝓞 E) (Fin n → E)) {t : Formalism.L2.Herm.intAf F E}
    (ht : t ∈ idS F I) {u : Fin n → E ⊗[F] Formalism.L2.Herm.Af F}
    (hu : u ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) N) :
    t • u ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (I • N) := by
  have hA : ∀ p ∈ I, ∀ u ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) N,
      oToS F E p • u ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (I • N) := by
    intro p hp u hu
    refine Submodule.span_induction (p := fun u _ => oToS F E p • u ∈
      Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (I • N)) ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨m, hm, rfl⟩
      refine Submodule.subset_span ⟨p • m, Submodule.smul_mem_smul hp hm, ?_⟩
      funext i
      show iA F E ((p • m) i) = (oToS F E p : E ⊗[F] Formalism.L2.Herm.Af F) * iA F E (m i)
      rw [Pi.smul_apply, Algebra.smul_def, map_mul]
      rfl
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb
      rw [smul_add]; exact Submodule.add_mem _ ha hb
    · intro c a _ ha
      rw [smul_comm]; exact Submodule.smul_mem _ c ha
  have hmap : idS F I = Ideal.span (oToS F E '' I) := rfl
  rw [hmap] at ht
  refine Submodule.span_induction (p := fun t _ => t • u ∈
      Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (I • N)) ?_ ?_ ?_ ?_ ht
  · rintro _ ⟨p, hp, rfl⟩
    exact hA p hp u hu
  · rw [zero_smul]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    rw [add_smul]; exact Submodule.add_mem _ ha hb
  · intro c a _ ha
    rw [smul_eq_mul, mul_smul]; exact Submodule.smul_mem _ c ha

theorem inv_mul_int_away {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
    (Q : Pl E) (ε : E ⊗[F] Formalism.L2.Herm.Af F) (h : IdemOf F Q ε) (m : ℕ)
    (y y' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hle : (Q.asIdeal ^ m) • Formalism.UG.CS.globLat y (stdLat E n) ≤ Formalism.UG.CS.globLat y' (stdLat E n)) :
    ∀ i j, (1 - ε) * (y'⁻¹ * y).1 i j ∈ Formalism.L2.Herm.intAf F E := by
  classical
  intro i j
  have hfin := Module.Finite.iff_fg.2 (stdLat_lattice (E := E) (n := n)).fg
  have hspan : Submodule.span E (stdLat E n : Set (Fin n → E)) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨k, rfl⟩
    simpa using single_mem_stdLat (E := E) k 1
  have hSR := Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds F E (Fin n) (stdLat E n) hfin hspan
  have hcol : (y : Matrix (Fin n) (Fin n) _) *ᵥ (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) ∈
      Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (Formalism.UG.CS.globLat y (stdLat E n)) := by
    refine (hSR _ _).2 ?_
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec, mem_latS_std]
    intro k
    by_cases hkj : k = j
    · subst hkj; simp only [Pi.single_eq_same]; exact Subring.one_mem _
    · rw [Pi.single_eq_of_ne hkj]; exact Subring.zero_mem _
  have h1 := idS_smul_latS (Q.asIdeal ^ m) _ (h.one_sub_mem_idS m) hcol
  have h2 := Submodule.span_mono (Set.image_mono hle) h1
  have h3 := ((mem_latS_std _).1 ((hSR y' _).1 h2)) i
  convert h3 using 1
  have e : ((⟨1 - ε, h.one_sub_mem⟩ : Formalism.L2.Herm.intAf F E) •
      ((y : Matrix (Fin n) (Fin n) _) *ᵥ (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F))) =
      (1 - ε) • ((y : Matrix (Fin n) (Fin n) _) *ᵥ (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)) := rfl
  rw [e, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Units.val_mul, Matrix.mulVec_single_one, Pi.smul_apply,
    smul_eq_mul]
  rfl

end GlobalTheory.InertNbr
end
end

