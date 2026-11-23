module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivSplitCentre
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

noncomputable section

namespace GlobalTheory.CuspRep.SplitDeriv

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem hasDerivAt_scalar_exp :
    HasDerivAt (fun t : ℝ =>
      toL (Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => (t : ℂ))).val)
      (fun i j => if i = j then (1 : Cinf E) else 0) 0 := by
  rw [hasDerivAt_pi]; intro i
  rw [hasDerivAt_pi]; intro j
  rw [hasDerivAt_pi]; intro w
  by_cases h : i = j
  · subst h
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
    have h2 := h1.cexp
    simpa [toL, Matrix.scalar_apply, Matrix.diagonal_apply, expU] using h2
  · simpa [toL, Matrix.scalar_apply, Matrix.diagonal_apply, h] using hasDerivAt_const (0 : ℝ) (0 : ℂ)


open GlobalTheory.UnitaryBC in
theorem hasDerivAt_splitCentre (ψ : Sm E a) (g : GA E a) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ψ.1 (g * splitCentre E a t))
      ((lie E a (fun i j => if i = j then (1 : Cinf E) else 0) ψ).1 (g * splitCentre E a s)) s := by
  have h0 : Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => ((0 : ℝ) : ℂ)) = 1 := by
    ext i j w
    by_cases h : i = j <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply, expU, Matrix.one_apply, h]
  have h := hasDerivAt_curve ψ (g * splitCentre E a s)
    (fun t => Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => (t : ℂ)))
    _ h0 hasDerivAt_scalar_exp
  have h' := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact h)
  rw [lie_apply]
  refine h'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  change ψ.1 (g * splitCentre E a t) = ψ.1 (g * splitCentre E a s * splitCentre E a (t - s))
  rw [mul_assoc, ← splitCentre_add, add_sub_cancel]

end GlobalTheory.CuspRep.SplitDeriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaplacianPolynomialKernelOfPolynomialLaplacian
section
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic GlobalTheory.HCAlpha
open scoped ContDiff
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
noncomputable section

namespace GlobalTheory.HCA

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


variable (E a) in
def glRho : glL E a →ₗ[ℝ] Module.End ℂ ((glH E a).smoothFuns (F := ℂ)) where
  toFun X := (glH E a).rightDerivEnd X
  map_add' X Y := by ext1 f; ext1; exact (glH E a).rightDeriv_add_left _ _ _
  map_smul' r X := by ext1 f; ext1; exact (glH E a).rightDeriv_smul_left r _ _


variable (E a) in
def glLap : Module.End ℂ ((glH E a).smoothFuns (F := ℂ)) :=
  ∑ τ : E →+* ℂ, ∑ i : Fin a, ∑ j : Fin a,
    ((glH E a).rightDerivEnd ⟨Matrix.single i j (atEmb τ 1), Submodule.mem_top⟩ ^ 2 +
      (glH E a).rightDerivEnd ⟨Matrix.single i j (atEmb τ Complex.I), Submodule.mem_top⟩ ^ 2)

theorem aeval_intertwine {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (Φ : M →ₗ[ℂ] N) (A : Module.End ℂ M) (B : Module.End ℂ N) (h : ∀ x, Φ (A x) = B (Φ x))
    (p : Polynomial ℂ) (x : M) : Φ (Polynomial.aeval A p x) = Polynomial.aeval B p (Φ x) := by
  have hp : ∀ n : ℕ, ∀ x, Φ ((A ^ n) x) = (B ^ n) (Φ x) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih => intro x; rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, h, ih]
  induction p using Polynomial.induction_on' with
  | add p q hp' hq' => simp only [map_add (f := _), LinearMap.add_apply, hp', hq']
  | monomial n c =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul, hp]

theorem contDiffOn_finsum {ι : Type*} (s : Finset ι) (g : ι → Lie E a → ℂ)
    (hg : ∀ i ∈ s, ContDiffOn ℝ ∞ (g i) (invSet E a)) : ContDiffOn ℝ ∞ (∑ i ∈ s, g i) (invSet E a) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact contDiffOn_const (c := (0 : ℂ))
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hg i (Finset.mem_insert_self _ _)).add (ih fun j hj => hg j (Finset.mem_insert_of_mem hj))

theorem rightDeriv_glF {f : Lie E a → ℂ} (hf : ContDiffOn ℝ ∞ f (invSet E a)) (X : glL E a)
    (g : (glH E a).smoothFuns (F := ℂ)) (hg : g.1 = fun y : glG E a => f (toL y.1.val)) :
    ((glH E a).rightDerivEnd X g).1 = fun y : glG E a => vecF E a (toL X.1) f (toL y.1.val) := by
  rw [IsExpLieAlgebra.coe_rightDerivEnd, hg]
  exact ((_root_.GlobalTheory.GlVec.isSmoothFun_and_rightDeriv_eq_vecF E a f hf).2 X).2

theorem glLap_glF {f : Lie E a → ℂ} (hf : ContDiffOn ℝ ∞ f (invSet E a))
    (g : (glH E a).smoothFuns (F := ℂ)) (hg : g.1 = fun y : glG E a => f (toL y.1.val)) :
    (glLap E a g).1 = (fun y : glG E a => lapF E a f (toL y.1.val)) ∧ ContDiffOn ℝ ∞ (lapF E a f) (invSet E a) := by
  have key : ∀ X : glL E a, ((glH E a).rightDerivEnd X ((glH E a).rightDerivEnd X g)).1 =
      fun y : glG E a => vecF E a (toL X.1) (vecF E a (toL X.1) f) (toL y.1.val) := fun X =>
    rightDeriv_glF ((_root_.GlobalTheory.GlVec.isSmoothFun_and_rightDeriv_eq_vecF E a f hf).2 X).1 X _ (rightDeriv_glF hf X g hg)
  have hv : ∀ X : Lie E a, ContDiffOn ℝ ∞ (vecF E a X f) (invSet E a) := fun X =>
    ((_root_.GlobalTheory.GlVec.isSmoothFun_and_rightDeriv_eq_vecF E a f hf).2 ⟨Matrix.of X, Submodule.mem_top⟩).1
  have hvv : ∀ X : Lie E a, ContDiffOn ℝ ∞ (vecF E a X (vecF E a X f)) (invSet E a) := fun X =>
    ((_root_.GlobalTheory.GlVec.isSmoothFun_and_rightDeriv_eq_vecF E a _ (hv X)).2 ⟨Matrix.of X, Submodule.mem_top⟩).1
  refine ⟨?_, ?_⟩
  · simp only [glLap, LinearMap.sum_apply, LinearMap.add_apply, sq, Module.End.mul_apply,
      Submodule.coe_sum, Submodule.coe_add, key]
    funext y
    simp only [lapF, Finset.sum_apply, Pi.add_apply]
  · unfold lapF
    exact contDiffOn_finsum _ _ fun τ _ => contDiffOn_finsum _ _ fun i _ => contDiffOn_finsum _ _ fun j _ =>
      (hvv _).add (hvv _)

theorem glLap_pow_glF (k : ℕ) : ∀ {f : Lie E a → ℂ}, ContDiffOn ℝ ∞ f (invSet E a) →
    ∀ (g : (glH E a).smoothFuns (F := ℂ)), g.1 = (fun y : glG E a => f (toL y.1.val)) →
    ((glLap E a ^ k) g).1 = (fun y : glG E a => (lapF E a)^[k] f (toL y.1.val)) ∧
      ContDiffOn ℝ ∞ ((lapF E a)^[k] f) (invSet E a) := by
  induction k with
  | zero => intro f hf g hg; exact ⟨hg, hf⟩
  | succ k ih =>
    intro f hf g hg
    obtain ⟨h1, h2⟩ := glLap_glF hf g hg
    rw [pow_succ, Module.End.mul_apply, Function.iterate_succ_apply]
    exact ih h2 _ h1

theorem glLap_glRes (φ : Sm E a) (x : GA E a) :
    glLap E a ⟨glRes φ.1 x, (_root_.GlobalTheory.HCA.glRes_smooth_rightDeriv E a φ x).1⟩ = ⟨glRes (lapOp E a φ).1 x, (_root_.GlobalTheory.HCA.glRes_smooth_rightDeriv E a _ x).1⟩ := by
  have key : ∀ (i j : Fin a) (z : Cinf E) (ψ : Sm E a),
      (glH E a).rightDerivEnd ⟨Matrix.single i j z, Submodule.mem_top⟩ ⟨glRes ψ.1 x, (_root_.GlobalTheory.HCA.glRes_smooth_rightDeriv E a ψ x).1⟩ =
        ⟨glRes (lieS E a i j z ψ).1 x, (_root_.GlobalTheory.HCA.glRes_smooth_rightDeriv E a _ x).1⟩ := by
    intro i j z ψ
    apply Subtype.ext
    rw [IsExpLieAlgebra.coe_rightDerivEnd, (_root_.GlobalTheory.HCA.glRes_smooth_rightDeriv E a ψ x).2, lieS_apply]
  apply Subtype.ext
  simp only [glLap, lapOp, LinearMap.sum_apply, LinearMap.add_apply, sq, Module.End.mul_apply,
    key, Submodule.coe_sum, Submodule.coe_add]
  funext y
  simp only [glRes, Finset.sum_apply, Pi.add_apply, Submodule.coe_sum, Submodule.coe_add]

theorem solG_of_polyLap : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∀ p : Polynomial ℂ, p ≠ 0 → ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ (glL E a)) (P : Polynomial ℂ), P.Monic ∧ (∀ f : Lie E a → ℂ, ContDiffOn ℝ ∞ f (invSet E a) → (∀ y ∈ invSet E a, polyF E a p f y = 0) → (fun y : glG E a => f (toL y.1.val)) ∈ solG (glH E a) b P) ∧ ∀ φ : Sm E a, Polynomial.aeval (lapOp E a) p φ = 0 → ∀ x, glRes φ.1 x ∈ solG (glH E a) b P := by
  intro E _ _ _ a p hp
  obtain ⟨d, b, hb⟩ := _root_.GlobalTheory.glBasis_sum_sq E a
  have hΔ : (∑ i, (glH E a).rightDerivEnd (F := ℂ) (b i) * (glH E a).rightDerivEnd (F := ℂ) (b i)) = glLap E a := by
    rw [glLap]
    simp only [sq]
    exact hb _ (glRho E a)
  refine ⟨d, b, p * Polynomial.C p.leadingCoeff⁻¹, Polynomial.monic_mul_leadingCoeff_inv hp, ?_, ?_⟩
  · have hP : ∀ g, Polynomial.aeval (glLap E a) (p * Polynomial.C p.leadingCoeff⁻¹) g =
        p.leadingCoeff⁻¹ • Polynomial.aeval (glLap E a) p g := by
      intro g
      rw [Polynomial.aeval_mul, Polynomial.aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]
    intro f hf h0
    rw [mem_solG]
    refine ⟨(_root_.GlobalTheory.GlVec.isSmoothFun_and_rightDeriv_eq_vecF E a f hf).1, ?_⟩
    rw [hΔ, hP]
    have hk : ∀ k : ℕ, ((glLap E a ^ k) ⟨_, (_root_.GlobalTheory.GlVec.isSmoothFun_and_rightDeriv_eq_vecF E a f hf).1⟩).1 =
        (fun y : glG E a => (lapF E a)^[k] f (toL y.1.val)) := fun k => (glLap_pow_glF k hf _ rfl).1
    suffices h : Polynomial.aeval (glLap E a) p ⟨_, (_root_.GlobalTheory.GlVec.isSmoothFun_and_rightDeriv_eq_vecF E a f hf).1⟩ = 0 by rw [h, smul_zero]
    apply Subtype.ext
    rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, Submodule.coe_sum]
    funext y
    simp only [Finset.sum_apply, LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, hk, Submodule.coe_zero,
      Pi.zero_apply]
    have := h0 _ (val_mem_invSet y.1)
    simpa only [polyF, Finset.sum_apply, Pi.smul_apply] using this
  · intro φ hφ x
    rw [mem_solG]
    refine ⟨(_root_.GlobalTheory.HCA.glRes_smooth_rightDeriv E a φ x).1, ?_⟩
    rw [hΔ, Polynomial.aeval_mul, Polynomial.aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]
    let Φ : Sm E a →ₗ[ℂ] (glH E a).smoothFuns (F := ℂ) :=
      { toFun := fun ψ => ⟨glRes ψ.1 x, (_root_.GlobalTheory.HCA.glRes_smooth_rightDeriv E a ψ x).1⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have e := aeval_intertwine Φ (lapOp E a) (glLap E a) (fun ψ => (glLap_glRes ψ x).symm) p φ
    change p.leadingCoeff⁻¹ • Polynomial.aeval (glLap E a) p (Φ φ) = 0
    rw [← e, hφ, map_zero, smul_zero]

end GlobalTheory.HCA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStableAlmostAllPlacesLeft
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

open scoped TensorProduct
open Matrix
namespace GlobalTheory.AdelMatLat

theorem exists_int_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    (hL : L.IsFullLattice E) (v : Fin n → E) : ∃ d : ℤ, d ≠ 0 ∧ d • v ∈ L := by
  have hv : v ∈ Submodule.span E (L : Set (Fin n → E)) := by
    let _ := hL
    rw [Submodule.IsFullLattice.span_eq_top (A := E) (M := L)]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, h₁, hx⟩ := hx
    obtain ⟨d₂, h₂, hy⟩ := hy
    refine ⟨d₁ * d₂, mul_ne_zero h₁ h₂, ?_⟩
    have : (d₁ * d₂) • (x + y) = d₂ • (d₁ • x) + d₁ • (d₂ • y) := by
      rw [smul_add, mul_comm, mul_smul, mul_comm, mul_smul]
    rw [this]
    exact add_mem (zsmul_mem hx _) (zsmul_mem hy _)
  | smul e x _ hx =>
    obtain ⟨d, hd, hx⟩ := hx
    obtain ⟨m, hm, hint⟩ := exists_integral_multiples ℤ ℚ (L := E) {e}
    let o : 𝓞 E := ⟨m • e, (hint e (Finset.mem_singleton_self e) :)⟩
    refine ⟨m * d, mul_ne_zero hm hd, ?_⟩
    have : (m * d) • (e • x) = o • (d • x) := by
      have ho : algebraMap (𝓞 E) E o = m • e := rfl
      rw [← algebraMap_smul E o (d • x), ho, smul_assoc, smul_comm e d x, mul_smul]
    rw [this]
    exact L.smul_mem o hx

theorem exists_int_mulVec_mem {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    (hL : L.IsFullLattice E) (N : Matrix (Fin n) (Fin n) E) : ∃ D : ℤ, D ≠ 0 ∧ ∀ x ∈ L, D • (N *ᵥ x) ∈ L := by
  obtain ⟨s, hs⟩ := hL.toIsLattice.fg
  choose d hd hdm using fun g : Fin n → E => exists_int_smul_mem L hL (N *ᵥ g)
  refine ⟨∏ g ∈ s, d g, Finset.prod_ne_zero_iff.2 fun g _ => hd g, ?_⟩
  let f : (Fin n → E) →ₗ[𝓞 E] (Fin n → E) := ((∏ g ∈ s, d g) • N.mulVecLin).restrictScalars (𝓞 E)
  have hf : ∀ x, f x = (∏ g ∈ s, d g) • (N *ᵥ x) := fun x => rfl
  have hle : Submodule.span (𝓞 E) (s : Set (Fin n → E)) ≤ L.comap f := by
    rw [Submodule.span_le]
    intro g hg
    simp only [SetLike.mem_coe, Submodule.mem_comap, hf]
    classical
    rw [← Finset.mul_prod_erase s d hg, mul_comm, mul_smul]
    exact zsmul_mem (hdm g) _
  intro x hx
  rw [← hs] at hx
  have := hle hx
  rwa [Submodule.mem_comap, hf] at this

theorem incM_zsmul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m k : Type}
    (D : ℤ) (V : Matrix m k E) : incM F (D • V) = (algebraMap F (AF F) (D : F)) • incM F V := by
  ext i j
  simp only [incM, Matrix.map_apply, Matrix.smul_apply, map_zsmul, algebraMap_smul, Int.cast_smul_eq_zsmul]

theorem smul_incM_mul_stable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) (c : AF F) (N : Matrix (Fin n) (Fin n) E) (D : ℤ) (hD0 : D ≠ 0)
    (hD : ∀ x ∈ X.L, D • (N *ᵥ x) ∈ X.L) (w : Pl (F := F))
    (hw : evFin F w (c * algebraMap F (AF F) (D : F)⁻¹) ∈ w.adicCompletionIntegers F) :
    ∀ γ ∈ latAtV X Y w, (c • incM F N) * γ ∈ latAtV X Y w := by
  intro γ hγ
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hint, x, hx, y, hy, rfl⟩ := hz
    have hDF : (D : F) ≠ 0 := Int.cast_ne_zero.2 hD0
    have heq : (c • incM F N) * (a • incM F (Matrix.vecMulVec x y)) =
        ((c * algebraMap F (AF F) (D : F)⁻¹) * a) • incM F (Matrix.vecMulVec (D • (N *ᵥ x)) y) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.smul_vecMulVec, incM_zsmul, smul_smul,
        ← Matrix.mul_vecMulVec]
      have hm : incM F (N * Matrix.vecMulVec x y) = incM F N * incM F (Matrix.vecMulVec x y) := by
        simp only [incM, Matrix.map_mul]
      rw [hm]
      congr 1
      rw [mul_right_comm, mul_assoc c, ← map_mul, inv_mul_cancel₀ hDF, map_one, mul_one]
    rw [heq]
    refine AddSubgroup.subset_closure ⟨_, ?_, ?_, _, hD x hx, y, hy, rfl⟩
    · intro u hu
      rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]
    · rw [map_mul]
      exact mul_mem hw hint
  | zero => rw [Matrix.mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg]; exact neg_mem hx

theorem finite_not_integral {F : Type} [Field F] [NumberField F] (c : AF F) :
    {w : Pl (F := F) | evFin F w c ∉ w.adicCompletionIntegers F}.Finite :=
  Filter.eventually_cofinite.1 c.2.2

theorem finite_bad_smul_incM {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) (hX : X.L.IsFullLattice E) (c : AF F) (N : Matrix (Fin n) (Fin n) E) :
    {w : Pl (F := F) | ¬ ∀ γ ∈ latAtV X Y w, (c • incM F N) * γ ∈ latAtV X Y w}.Finite := by
  obtain ⟨D, hD0, hD⟩ := exists_int_mulVec_mem X.L hX N
  refine (finite_not_integral (c * algebraMap F (AF F) (D : F)⁻¹)).subset ?_
  intro w hw hint
  exact hw (smul_incM_mul_stable X Y c N D hD0 hD w hint)

theorem almost_all_stable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ)
    (X : Spc F E n) (Y : Spc F E d), X.L.IsFullLattice E → ∀ M : Matrix (Fin n) (Fin n) (AE F E),
    Set.Finite {w : Pl (F := F) | ¬ ∀ γ ∈ latAtV X Y w, M * γ ∈ latAtV X Y w} := by
  intro F E _ _ _ _ _ n d X Y hX M
  let bad : Matrix (Fin n) (Fin n) (AE F E) → Set (Pl (F := F)) :=
    fun M => {w | ¬ ∀ γ ∈ latAtV X Y w, M * γ ∈ latAtV X Y w}
  have hadd : ∀ M M', (bad M).Finite → (bad M').Finite → (bad (M + M')).Finite := by
    intro M M' h h'
    refine (h.union h').subset fun w hw => ?_
    by_contra hc
    simp only [Set.mem_union, not_or, bad, Set.mem_setOf_eq, not_not] at hc hw
    exact hw fun γ hγ => by rw [Matrix.add_mul]; exact add_mem (hc.1 γ hγ) (hc.2 γ hγ)
  have hzero : (bad 0).Finite := by
    refine Set.finite_empty.subset fun w hw => hw fun γ _ => ?_
    rw [Matrix.zero_mul]; exact zero_mem _
  have hsingle : ∀ i j (t : AE F E), (bad (Matrix.single i j t)).Finite := by
    intro i j t
    induction t using TensorProduct.induction_on with
    | zero => rw [Matrix.single_zero]; exact hzero
    | tmul a e =>
      have h : Matrix.single i j (a ⊗ₜ[F] e) = a • incM F (Matrix.single i j e) := by
        ext k l
        simp only [incM, Matrix.map_apply, Matrix.smul_apply, Matrix.single_apply]
        split_ifs <;> simp [inclR, TensorProduct.smul_tmul']
      rw [h]
      exact finite_bad_smul_incM X Y hX a _
    | add t t' ht ht' => rw [Matrix.single_add]; exact hadd _ _ ht ht'
  show (bad M).Finite
  rw [Matrix.matrix_eq_sum_single M]
  exact Finset.sum_induction _ (fun M => (bad M).Finite) hadd hzero fun i _ =>
    Finset.sum_induction _ (fun M => (bad M).Finite) hadd hzero fun j _ => hsingle i j _

end GlobalTheory.AdelMatLat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieFirstOfLieSecond
section
open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

open NumberField MvPolynomial Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.RealLift.LieFirstPf

variable {P Q R S : ℕ}

def swapE (P Q R S : ℕ) : Formalism.BasicNotions.TH.Pol R S P Q ≃ₗ[ℂ] Formalism.BasicNotions.TH.Pol P Q R S :=
  (renameEquiv ℂ (Equiv.prodComm (Ix R S) (Ix P Q))).toLinearEquiv

theorem swapE_apply (f : Formalism.BasicNotions.TH.Pol R S P Q) : swapE P Q R S f = rename Prod.swap f := rfl

theorem lineSign_swap (a : Ix P Q) (b : Ix R S) :
    lineSign (p := R) (q := S) (r := P) (s := Q) b a = lineSign (p := P) (q := Q) (r := R) (s := S) a b := by
  rcases a with a | a <;> rcases b with b | b <;> rfl

theorem swapE_heisOp (c : Matrix (Ix R S) (Ix P Q) ℂ) (f : Formalism.BasicNotions.TH.Pol R S P Q) :
    swapE P Q R S (heisOp c f) = heisOp cᵀ (swapE P Q R S f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [heisOp, swapE_apply, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.sub_apply,
    map_smul, map_sum, map_sub, GlobalTheory.FockSwap.rename_raiB, GlobalTheory.FockSwap.rename_lowB]
  congr 1
  refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun l => ?_
  simp [lineSign_swap]

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def swapT (ι : Type) (P Q R S : ℕ) :
    (⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol R S P Q) ≃ₗ[ℂ] ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S :=
  PiTensorProduct.congr fun _ => swapE P Q R S

theorem swapT_atPl (w : ι) (L' : Module.End ℂ (Formalism.BasicNotions.TH.Pol R S P Q)) (L : Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S))
    (h : ∀ f, swapE P Q R S (L' f) = L (swapE P Q R S f)) (T : ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol R S P Q) :
    swapT ι P Q R S (atPl w L' T) = atPl w L (swapT ι P Q R S T) := by
  have e : (swapT ι P Q R S).toLinearMap ∘ₗ atPl w L' = atPl w L ∘ₗ (swapT ι P Q R S).toLinearMap := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, atPl, swapT,
      PiTensorProduct.map_tprod, PiTensorProduct.congr_tprod]
    congr 1
    funext i
    by_cases hi : i = w
    · subst hi; simp [h]
    · simp [Function.update_of_ne hi]
  exact LinearMap.congr_fun e T

theorem swapT_sumPl (L' : ι → Module.End ℂ (Formalism.BasicNotions.TH.Pol R S P Q)) (L : ι → Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S))
    (h : ∀ w f, swapE P Q R S (L' w f) = L w (swapE P Q R S f)) (T : ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol R S P Q) :
    swapT ι P Q R S (sumPl L' T) = sumPl L (swapT ι P Q R S T) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [sumPl, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun w _ => swapT_atPl w (L' w) (L w) (h w) T

end Tensor


open scoped Classical in
theorem lieFirst_of_lieSecond : LieSecond → LieFirst := by
  intro h2 F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d d' a b A C Φ om χ m hCM hψ hfr hΦ hdd hW hm
  have hfr' : Framed τ JB JA b a C A := ⟨by rw [mul_comm]; exact hfr.1, hfr.2.2, hfr.2.1⟩
  have hΦ' : IsFockMap ψ τ d' C A (Φ ∘ₗ (swapT (InfinitePlace F) P Q R S).toLinearMap) := by
    refine ⟨hΦ.1.comp (swapT (InfinitePlace F) P Q R S).injective, fun u hu c hc T => ?_⟩
    have hu' : At (evI F) uᵀ := fun x hx => by rw [← Matrix.transpose_smul, hu x hx, Matrix.transpose_zero]
    have hc' : ∀ w, uᵀ.map (piInf (τ w)) = A w * (c w)ᵀ * (C w)ᵀ := fun w => by
      rw [Matrix.transpose_map, hc w]; simp [Matrix.transpose_mul, Matrix.mul_assoc]
    have key := hΦ.2 uᵀ hu' (fun w => (c w)ᵀ) hc' (swapT (InfinitePlace F) P Q R S T)
    have hr : ∀ t : ℝ, d'.rho ψ (realAd F t • u) = d.rho ψ (realAd F t • uᵀ) := fun t => by
      show schr ψ (d'.e _) = schr ψ (d.e _)
      rw [← hdd, Matrix.transpose_smul, Matrix.transpose_transpose]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hr]
    rwa [swapT_sumPl (fun w => heisOp (c w)) (fun w => heisOp (c w)ᵀ) (fun w f => swapE_heisOp (c w) f)]
  have hA := h2 F E σ β α κ R S P Q ψ τ JB JA d' b a C A _ om χ m hCM hψ hfr' hΦ' hW hm
  intro γ hγ Y hY T
  have key := hA γ hγ Y hY ((swapT (InfinitePlace F) P Q R S).symm T)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at key
  rwa [swapT_sumPl (fun w => fockAct2 R S P Q (Y w) + (((m w : ℂ) / 2) * (Y w).trace) • 1)
    (fun w => fockAct1 P Q R S (Y w) + (((m w : ℂ) / 2) * (Y w).trace) • 1) (fun w f => by
      simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add (f := _), map_smul, swapE_apply,
        (GlobalTheory.FockSwap.swap_symmetry R S P Q).2.1]), LinearEquiv.apply_symm_apply] at key

end GlobalTheory.RealLift.LieFirstPf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqSchwartzPosFinite
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem schwartzBruhat_matrix_lintegral_sq_ne_zero_ne_top : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a d : ℕ}
    (Φ : Matrix (Fin a) (Fin d) k → ℂ), Φ ∈ SB (Matrix (Fin a) (Fin d) k) → Φ ≠ 0 →
    ∀ ν : @Measure (Matrix (Fin a) (Fin d) k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
      ∫⁻ Y, ‖Φ Y‖ₑ ^ 2 ∂ν ≠ 0 ∧ ∫⁻ Y, ‖Φ Y‖ₑ ^ 2 ∂ν ≠ ⊤ := by
  intro k _ _ _ _ a d Φ hΦ h0 ν hν
  letI : MeasurableSpace (Matrix (Fin a) (Fin d) k) := borel _
  haveI : BorelSpace (Matrix (Fin a) (Fin d) k) := ⟨rfl⟩
  obtain ⟨hlc, hcs⟩ : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
  have hc : Continuous Φ := hlc.continuous
  have hcont : Continuous fun Y => ‖Φ Y‖ₑ ^ 2 :=
    (ENNReal.continuous_pow 2).comp hc.enorm
  constructor
  · intro h
    rw [lintegral_eq_zero_iff hcont.measurable] at h
    have h' := (Continuous.ae_eq_iff_eq ν hcont continuous_zero).1 h
    apply h0
    funext Y
    have := congrFun h' Y
    simpa using this
  · obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs
    have hle : ∫⁻ Y, ‖Φ Y‖ₑ ^ 2 ∂ν ≤
        ∫⁻ Y, (tsupport Φ).indicator (fun _ => ENNReal.ofReal C ^ 2) Y ∂ν := by
      refine lintegral_mono fun Y => ?_
      by_cases hY : Y ∈ tsupport Φ
      · rw [Set.indicator_of_mem hY]
        gcongr
        rw [← ofReal_norm_eq_enorm]
        exact ENNReal.ofReal_le_ofReal (hC Y)
      · simp [image_eq_zero_of_notMem_tsupport hY]
    refine ne_top_of_le_ne_top ?_ hle
    rw [lintegral_indicator_const (isClosed_tsupport Φ).measurableSet]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      (IsCompact.measure_lt_top hcs).ne

end GlobalTheory
end

