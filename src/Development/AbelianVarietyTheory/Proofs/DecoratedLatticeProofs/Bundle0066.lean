module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0215
public import Formalism.LocalToGlobal.Columns.PolyFnLemmas

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylDeterminantTwistTensorFiniteDimensionalStabl
section
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.KJInf.VnStable

variable {ι : Type} [Fintype ι] {a : ℕ}

theorem lft_rename (g : ι → Matrix (Fin a) (Fin a) ℂ) (τ : ι) (p : MvPolynomial (Fin a × Fin a) ℂ) :
    lft g (rename (Prod.mk τ) p) = rename (Prod.mk τ) (Formalism.GradedWeylDivisibility.rowAct ℂ (g τ) p) := by
  have : (lft g).comp (rename (Prod.mk τ)) = (rename (Prod.mk τ)).comp (Formalism.GradedWeylDivisibility.rowAct ℂ (n := a) (g τ)) := by
    apply MvPolynomial.algHom_ext
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      simp [lft, Formalism.GradedWeylDivisibility.rowAct, rename_X, aeval_X, map_sum]
  exact congrArg (fun φ : MvPolynomial (Fin a × Fin a) ℂ →ₐ[ℂ] PY ι a => φ p) this

theorem lft_ten (g : ι → Matrix (Fin a) (Fin a) ℂ) (f : ι → MvPolynomial (Fin a × Fin a) ℂ) :
    lft g (ten f) = ten (fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (g τ) (f τ)) := by
  simp only [ten, map_prod, lft_rename]

theorem lft_frDet (g : ι → Matrix (Fin a) (Fin a) ℂ) (τ : ι) :
    lft g (frDet ℂ a τ : PY ι a) = (g τ).det • (frDet ℂ a τ : PY ι a) := by
  unfold frDet
  rw [AlgHom.map_det]
  have hM : (lft g).mapMatrix (Matrix.of fun α s : Fin a => (X (τ, α, s) : PY ι a)) =
      (g τ).map C * Matrix.of fun α s : Fin a => (X (τ, α, s) : PY ι a) := by
    ext α s
    simp [lft, Matrix.mul_apply]
  rw [hM, Matrix.det_mul, smul_eq_C_mul]
  congr 1
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]

theorem prod_mem_prodS {A : Type} [CommRing A] [Algebra ℂ A] (s : Finset ι) (M : ι → Submodule ℂ A) (x : ι → A)
    (h : ∀ τ ∈ s, x τ ∈ M τ) : ∏ τ ∈ s, x τ ∈ ∏ τ ∈ s, M τ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact Submodule.one_le.mp le_rfl
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact Submodule.mul_mem_mul (h i (Finset.mem_insert_self _ _))
      (ih fun τ hτ => h τ (Finset.mem_insert_of_mem hτ))

theorem fg_prodS {A : Type} [CommRing A] [Algebra ℂ A] (s : Finset ι) (M : ι → Submodule ℂ A)
    (h : ∀ τ, (M τ).FG) : (∏ τ ∈ s, M τ).FG := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  | insert i s hi ih => rw [Finset.prod_insert hi]; exact (h i).mul ih

theorem ten_mem_prod (lam : ι → DomWeight a) (f : ι → MvPolynomial (Fin a × Fin a) ℂ)
    (hf : ∀ τ, f τ ∈ delSq ℂ a (lam τ)) :
    ten f ∈ ∏ τ, (delSq ℂ a (lam τ)).map (rename (Prod.mk τ)).toLinearMap := by
  unfold ten
  exact prod_mem_prodS _ _ _ (fun τ _ => Submodule.mem_map_of_mem (hf τ))

theorem cspan_fd (lam : ι → DomWeight a) : FiniteDimensional ℂ (CSpan lam) := by
  have hP : (∏ τ, (delSq ℂ a (lam τ)).map (rename (Prod.mk τ)).toLinearMap).FG := by
    apply fg_prodS
    intro τ
    apply Submodule.FG.map
    haveI := (GlobalTheory.WeylUnitary.delSq_irreducible_unitary a (lam τ)).1
    exact (Submodule.fg_iff_finiteDimensional _).mpr inferInstance
  have hle : CSpan lam ≤ ∏ τ, (delSq ℂ a (lam τ)).map (rename (Prod.mk τ)).toLinearMap := by
    unfold CSpan
    rw [Submodule.span_le]
    rintro p ⟨f, hf, rfl⟩
    exact ten_mem_prod lam f hf
  haveI : FiniteDimensional ℂ ↥(∏ τ, ((delSq ℂ a (lam τ)).map (rename (Prod.mk τ)).toLinearMap : Submodule ℂ (PY ι a))) :=
    (Submodule.fg_iff_finiteDimensional _).mp hP
  exact Submodule.finiteDimensional_of_le hle

theorem lft_cspan (lam : ι → DomWeight a) (g : ι → Matrix (Fin a) (Fin a) ℂ) :
    ∀ p ∈ CSpan lam, lft g p ∈ CSpan lam := by
  intro p hp
  unfold CSpan at hp ⊢
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    rw [lft_ten]
    exact Submodule.subset_span ⟨_, fun τ => (GlobalTheory.WeylUnitary.delSq_irreducible_unitary a (lam τ)).2.2.1 (g τ) (f τ) (hf τ), rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

end GlobalTheory.KJInf.VnStable


open GlobalTheory.KJInf.VnStable in
theorem GlobalTheory.KJInf.vn_finiteDimensional_and_lft_mem : ∀ (ι : Type) [Fintype ι] (a : ℕ) (lam : ι → DomWeight a) (n : ι → ℕ),
    FiniteDimensional ℂ (Vn lam n) ∧ ∀ (g : ι → Matrix (Fin a) (Fin a) ℂ), ∀ F ∈ Vn lam n, lft g F ∈ Vn lam n := by
  intro ι _ a lam n
  haveI := cspan_fd lam
  refine ⟨?_, ?_⟩
  · unfold Vn; infer_instance
  · intro g F hF
    unfold Vn at hF ⊢
    obtain ⟨p, hp, rfl⟩ := hF
    have hD : lft g (∏ τ, (frDet ℂ a τ : PY ι a) ^ n τ) = C (∏ τ, (g τ).det ^ n τ) * ∏ τ, (frDet ℂ a τ : PY ι a) ^ n τ := by
      rw [map_prod, map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [map_pow, lft_frDet, smul_eq_C_mul, mul_pow, map_pow]
    refine ⟨(∏ τ, (g τ).det ^ n τ) • lft g p, Submodule.smul_mem _ _ (lft_cspan lam g p hp), ?_⟩
    simp only [LinearMap.mulRight_apply, map_mul, hD, smul_eq_C_mul]; ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylDeterminantTwistTensorUnitIndexIrreducibleUn
section
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.KJInf

theorem lft_rename_unit {a : ℕ} (u : Matrix (Fin a) (Fin a) ℂ) (f : MvPolynomial (Fin a × Fin a) ℂ) :
    lft (fun _ : Unit => u) (rename (Prod.mk ()) f) = rename (Prod.mk ()) (Formalism.GradedWeylDivisibility.rowAct ℂ u f) := by
  have : (lft (fun _ : Unit => u)).comp (rename (Prod.mk ())) = (rename (Prod.mk ())).comp (Formalism.GradedWeylDivisibility.rowAct ℂ (n := a) u) := by
    apply MvPolynomial.algHom_ext
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      simp [lft, Formalism.GradedWeylDivisibility.rowAct, rename_X, aeval_X, map_sum]
  exact congrArg (fun φ => φ f) this

theorem lft_frDet_unit {a : ℕ} (u : Matrix (Fin a) (Fin a) ℂ) :
    lft (fun _ : Unit => u) (frDet ℂ a ()) = C u.det * frDet ℂ a () := by
  unfold frDet
  rw [AlgHom.map_det]
  have : (lft (fun _ : Unit => u)).mapMatrix (Matrix.of fun α s : Fin a => (X ((), α, s) : PY Unit a)) =
      u.map C * Matrix.of fun α s : Fin a => (X ((), α, s) : PY Unit a) := by
    ext i j
    simp [lft, aeval_X, Matrix.mul_apply]
  rw [this, Matrix.det_mul, RingHom.map_det]
  rfl

theorem frDet_unit_ne_zero (a : ℕ) : frDet ℂ a () ≠ 0 := by
  have h : frDet ℂ a () = rename (Prod.mk ()) (Matrix.mvPolynomialX (Fin a) (Fin a) ℂ).det := by
    unfold frDet
    rw [AlgHom.map_det]
    congr 1
    ext i j
    simp [Matrix.mvPolynomialX]
  rw [h]
  intro e
  apply Matrix.det_mvPolynomialX_ne_zero (Fin a) ℂ
  exact rename_injective _ (Prod.mk_right_injective ()) (e.trans (map_zero _).symm)

theorem CSpan_unit {a : ℕ} (lam : Unit → DomWeight a) :
    CSpan lam = (delSq ℂ a (lam ())).map (rename (R := ℂ) (Prod.mk ())).toLinearMap := by
  apply le_antisymm
  · unfold CSpan
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    refine ⟨f (), hf (), ?_⟩
    simp [ten]
  · rintro _ ⟨f, hf, rfl⟩
    apply Submodule.subset_span
    refine ⟨fun _ => f, fun _ => hf, ?_⟩
    simp [ten]

theorem Vn_unit_irreducible : ∀ (a : ℕ), 0 < a → ∀ (lam : Unit → DomWeight a) (n : Unit → ℕ), Vn lam n ≠ ⊥ ∧
    ∀ U : Submodule ℂ (PY Unit a), U ≤ Vn lam n → (∀ k, IsUni k → ∀ F ∈ U, lft k F ∈ U) → U = ⊥ ∨ U = Vn lam n := by
  intro a _ lam n
  set D : PY Unit a := ∏ τ, frDet ℂ a τ ^ n τ with hDdef
  have hD : D = frDet ℂ a () ^ n () := by simp [D]
  have hD0 : D ≠ 0 := hD ▸ pow_ne_zero _ (frDet_unit_ne_zero a)
  let φ : MvPolynomial (Fin a × Fin a) ℂ →ₗ[ℂ] PY Unit a :=
    LinearMap.mulRight ℂ D ∘ₗ (rename (R := ℂ) (Prod.mk ())).toLinearMap
  have hφ : ∀ f, φ f = rename (Prod.mk ()) f * D := fun f => rfl
  have hVn : Vn lam n = (delSq ℂ a (lam ())).map φ := by
    rw [Vn, CSpan_unit, ← Submodule.map_comp]
  have hinj : Function.Injective φ := by
    intro f g e
    rw [hφ, hφ] at e
    exact rename_injective _ (Prod.mk_right_injective ()) (mul_right_cancel₀ hD0 e)
  have hdel : delSq ℂ a (lam ()) = Formalism.GradedWeylDivisibility.dualWeyl ℂ a a (lam ()).natW := by
    rw [← Formalism.L2.Col.nablaSq_eq_delSq]; rfl
  have hanti : Antitone (lam ()).natW := fun i j hij => by
    have := (lam ()).anti hij
    simp only [DomWeight.natW]
    omega
  constructor
  · intro h
    rw [hVn] at h
    have h2 : delSq ℂ a (lam ()) = ⊥ :=
      Submodule.map_injective_of_injective hinj (h.trans (Submodule.map_bot _).symm)
    have hne : nablaSq ℂ a (lam ()) ≠ ⊥ := Submodule.nontrivial_iff_ne_bot.mp inferInstance
    exact hne (by rw [Formalism.L2.Col.nablaSq_eq_delSq]; exact h2)
  · intro U hU hst
    let M : Submodule ℂ (MvPolynomial (Fin a × Fin a) ℂ) := U.comap φ
    have hMU : M.map φ = U := by
      apply Submodule.map_comap_eq_self
      refine hU.trans ?_
      rw [hVn]
      exact LinearMap.map_le_range
    have hMd : M ≤ delSq ℂ a (lam ()) := by
      intro f hf
      have h1 : φ f ∈ (delSq ℂ a (lam ())).map φ := hVn ▸ hU hf
      obtain ⟨g, hg, e⟩ := h1
      exact hinj e ▸ hg
    have hrow : ∀ u ∈ Matrix.unitaryGroup (Fin a) ℂ, ∀ f ∈ M, Formalism.GradedWeylDivisibility.rowAct ℂ u f ∈ M := by
      intro u hu f hf
      have h1 := hst (fun _ => u) (fun _ => hu) (φ f) hf
      have hdet : u.det ≠ 0 := by
        have h := (Matrix.mem_unitaryGroup_iff.mp hu)
        have h' := congrArg Matrix.det h
        rw [Matrix.det_mul, Matrix.det_one] at h'
        exact left_ne_zero_of_mul_eq_one h'
      have e : lft (fun _ : Unit => u) (φ f) = (u.det ^ n ()) • φ (Formalism.GradedWeylDivisibility.rowAct ℂ u f) := by
        rw [hφ, hφ, map_mul, lft_rename_unit, hD, map_pow, lft_frDet_unit, smul_eq_C_mul, map_pow, mul_pow]
        ring
      rw [e] at h1
      exact (U.smul_mem_iff (pow_ne_zero _ hdet)).1 h1
    by_cases hM : M = ⊥
    · left
      rw [← hMU, hM, Submodule.map_bot]
    · right
      apply le_antisymm hU
      rw [hVn, ← hMU]
      apply Submodule.map_mono
      rw [hdel]
      exact GlobalTheory.Branching.dualWeyl_le_of_rowDivClosed le_rfl _ hanti M (hdel ▸ hMd)
        (GlobalTheory.Branching.rowDivClosed_of_rowAct_stable M (GlobalTheory.Branching.rowAct_mem_of_unitary_stable M hrow)) hM
end GlobalTheory.KJInf
end
end

