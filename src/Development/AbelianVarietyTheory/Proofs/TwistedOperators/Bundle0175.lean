module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockKsetPreservesHomogeneousDegree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0517
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
public import ReciprocityTheory.DualLattices.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0071
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContractionIsometricDiscreteSeriesFock
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.CoverContr

theorem inner_map_of_norm {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (A : H →L[ℂ] H)
    (hA : ∀ x, ‖A x‖ = ‖x‖) (x y : H) : inner ℂ (A x) (A y) = inner ℂ x y := by
  let L : H →ₗᵢ[ℂ] H := ⟨A.toLinearMap, hA⟩
  exact L.inner_map_map x y

private theorem inner_unitary_apply_eq_inner_inv {G E : Type} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : G →* E →L[ℂ] E) (hU : ∀ g x, ‖U g x‖ = ‖x‖) (g : G) (v w : E) :
    inner ℂ (U g v) w = inner ℂ v (U g⁻¹ w) := by
  have h1 : U g (U g⁻¹ w) = w := by
    have h := congrArg (fun f : E →L[ℂ] E => f w) (map_mul U g g⁻¹)
    simpa using h.symm
  conv_lhs => rw [← h1]
  exact inner_map_of_norm (U g) (hU g) v (U g⁻¹ w)

theorem exists_isCoverIt : ∀ (p q r s : ℕ) (T₀ : GrpData (p * r + q * s) (p * s + q * r)) (T₁ : GrpData p q) (T₂ : GrpData r s) (F : FockData T₀ T₁ T₂) (R₁ : DSRep T₁) (R₂ : DSRep T₂) (Tm : R₁.U.H →L[ℂ] R₂.U.H →L[ℂ] F.H), (∀ x x' y y', inner ℂ (Tm x y) (Tm x' y') = inner ℂ x x' * inner ℂ y y') → (∀ g h x y, F.π (g, h) (Tm x y) = Tm (R₁.U.π g x) (R₂.U.π h y)) → ∃ B : Pol p q r s →ₗ[ℂ] R₂.U.H →ₛₗ[starRingEnd ℂ] R₁.U.H, IsCoverIt R₁ R₂ B := by
  intro p q r s T₀ T₁ T₂ F R₁ R₂ Tm hTm hEq

  have hnorm : ∀ x y, ‖Tm x y‖ = ‖x‖ * ‖y‖ := by
    intro x y
    have h := hTm x x y y
    simp only [inner_self_eq_norm_sq_to_K] at h
    have h2 : ‖Tm x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by
      rw [mul_pow]; exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) two_ne_zero).1 h2
  have hflip : ∀ y, ‖Tm.flip y‖ ≤ ‖y‖ := fun y =>
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg y) fun x => by
      rw [ContinuousLinearMap.flip_apply, hnorm, mul_comm]

  have hsrc : ∀ (g : T₁.G) (y : R₂.U.H) (v : F.H),
      R₁.U.π g (ContinuousLinearMap.adjoint (Tm.flip y) v) =
        ContinuousLinearMap.adjoint (Tm.flip y) (F.π (g, 1) v) := by
    intro g y v
    apply ext_inner_right ℂ
    intro x
    rw [inner_unitary_apply_eq_inner_inv R₁.U.π R₁.U.isom, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.flip_apply]
    have e1 : Tm (R₁.U.π g⁻¹ x) y = F.π (g⁻¹, 1) (Tm x y) := by
      rw [hEq]; simp
    have e2 : F.π (g, 1) v = F.Om (F.emb (g, 1)) v := rfl
    have e3 : F.π (g⁻¹, 1) (Tm x y) = F.Om (F.emb (g, 1))⁻¹ (Tm x y) := by
      have : ((g⁻¹, 1) : T₁.G × T₂.G) = (g, 1)⁻¹ := by simp
      show F.Om (F.emb (g⁻¹, 1)) (Tm x y) = _
      rw [this, map_inv]
    rw [e1, e2, e3, inner_unitary_apply_eq_inner_inv F.Om F.isom]

  have htgt : ∀ (h : T₂.G) (y : R₂.U.H) (v : F.H),
      ContinuousLinearMap.adjoint (Tm.flip (R₂.U.π h y)) v =
        ContinuousLinearMap.adjoint (Tm.flip y) (F.π (1, h⁻¹) v) := by
    intro h y v
    apply ext_inner_right ℂ
    intro x
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply]
    have e1 : Tm x (R₂.U.π h y) = F.π (1, h) (Tm x y) := by
      rw [hEq]; simp
    have e2 : F.π (1, h⁻¹) v = F.Om (F.emb (1, h⁻¹)) v := rfl
    have e3 : F.π (1, h) (Tm x y) = F.Om (F.emb (1, h⁻¹))⁻¹ (Tm x y) := by
      have : ((1, h) : T₁.G × T₂.G) = (1, h⁻¹)⁻¹ := by simp
      show F.Om (F.emb (1, h)) (Tm x y) = _
      rw [this, map_inv]
    rw [e1, e2, e3, inner_unitary_apply_eq_inner_inv F.Om F.isom]
  let B : Pol p q r s →ₗ[ℂ] R₂.U.H →ₛₗ[starRingEnd ℂ] R₁.U.H :=
    { toFun := fun P =>
        { toFun := fun y => ContinuousLinearMap.adjoint (Tm.flip y) (F.ι P)
          map_add' := fun y y' => by simp
          map_smul' := fun c y => by
            rw [map_smul, LinearIsometryEquiv.map_smulₛₗ, ContinuousLinearMap.smul_apply] }
      map_add' := fun P P' => by ext y; simp
      map_smul' := fun c P => by ext y; simp }
  have hB : ∀ P y, B P y = ContinuousLinearMap.adjoint (Tm.flip y) (F.ι P) := fun _ _ => rfl
  refine ⟨B, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro P
    refine ⟨‖F.ι P‖, fun y => ?_⟩
    rw [hB]
    calc ‖ContinuousLinearMap.adjoint (Tm.flip y) (F.ι P)‖
        ≤ ‖ContinuousLinearMap.adjoint (Tm.flip y)‖ * ‖F.ι P‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖Tm.flip y‖ * ‖F.ι P‖ := by rw [LinearIsometryEquiv.norm_map]
      _ ≤ ‖y‖ * ‖F.ι P‖ := by gcongr; exact hflip y
      _ = ‖F.ι P‖ * ‖y‖ := mul_comm _ _
  · intro P y
    rw [R₁.ι_range, hB]
    unfold KFin
    have hk := (GlobalTheory.FockKFin.kfin_fock p q r s T₀ T₁ T₂ F
      (GlobalTheory.FockDegree.Om_Kset_homog p q r s T₀ T₁ T₂ F) P).1
    unfold KFin at hk
    haveI := hk
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.map
      (ContinuousLinearMap.adjoint (Tm.flip y)).toLinearMap
      (Submodule.span ℂ (Set.range fun k : ↥T₁.Kset => F.π ((k : T₁.G), 1) (F.ι P)))) ?_
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, (hsrc _ y _).symm⟩
  · intro y hy
    by_contra hcon
    push_neg at hcon
    haveI := R₁.nontriv
    obtain ⟨x, hx⟩ := exists_ne (0 : R₁.U.H)
    have hz : (fun v : F.H => inner ℂ v (Tm x y)) = fun _ => 0 := by
      refine Continuous.ext_on F.dense (continuous_id.inner continuous_const) continuous_const ?_
      rintro _ ⟨P, rfl⟩
      have h0 : ContinuousLinearMap.adjoint (Tm.flip y) (F.ι P) = 0 := by rw [← hB]; exact hcon P
      have := ContinuousLinearMap.adjoint_inner_left (Tm.flip y) x (F.ι P)
      rw [h0, inner_zero_left, ContinuousLinearMap.flip_apply] at this
      exact this.symm
    have h1 : Tm x y = 0 := inner_self_eq_zero.1 (congrFun hz (Tm x y))
    have h2 := hnorm x y
    rw [h1, norm_zero] at h2
    exact mul_ne_zero (norm_ne_zero_iff.2 hx) (norm_ne_zero_iff.2 hy) h2.symm
  · intro Z hZ P y
    have hd := (_root_.GlobalTheory.FockEmbExp.fock_derived p q r s T₀ T₁ T₂ F).2.1 Z hZ P
    have hc := ((ContinuousLinearMap.adjoint (Tm.flip y)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    have e : (fun t : ℝ => R₁.U.π (T₁.expt (t • Z)) (B P y)) =
        (ContinuousLinearMap.adjoint (Tm.flip y)) ∘
          (fun t : ℝ => F.π (T₁.expt (t • Z), 1) (F.ι P)) := by
      funext t
      rw [hB, Function.comp_apply, hsrc]
    rw [e, hB]
    exact hc
  · intro Z hZ P y
    have hone : T₂.expt ((0 : ℝ) • Z) = 1 := by
      have h := T₂.expt_add Z hZ 0 0
      rw [add_zero] at h
      have h' := congrArg (· * (T₂.expt ((0 : ℝ) • Z))⁻¹) h
      simpa [mul_assoc] using h'.symm
    have hinv : ∀ t : ℝ, (T₂.expt (t • Z))⁻¹ = T₂.expt ((-t) • Z) := by
      intro t
      have h := T₂.expt_add Z hZ (-t) t
      rw [neg_add_cancel, hone] at h
      exact (eq_inv_of_mul_eq_one_left h.symm).symm
    have hd := (_root_.GlobalTheory.FockEmbExp.fock_derived p q r s T₀ T₁ T₂ F).2.2 Z hZ P
    have hd' : HasDerivAt (fun u : ℝ => F.π (1, T₂.expt (u • Z)) (F.ι P))
        (F.ι (fockAct2 p q r s Z P)) (-(0 : ℝ)) := by rw [neg_zero]; exact hd
    have hn := hd'.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
    have hc := ((ContinuousLinearMap.adjoint (Tm.flip y)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hn
    have e : (fun t : ℝ => B P (R₂.U.π (T₂.expt (t • Z)) y)) =
        (ContinuousLinearMap.adjoint (Tm.flip y)) ∘
          ((fun u : ℝ => F.π (1, T₂.expt (u • Z)) (F.ι P)) ∘ fun t : ℝ => -t) := by
      funext t
      rw [hB, htgt, hinv]
      rfl
    have hval : ((ContinuousLinearMap.adjoint (Tm.flip y)).restrictScalars ℝ)
        ((-1 : ℝ) • F.ι (fockAct2 p q r s Z P)) =
        -(ContinuousLinearMap.adjoint (Tm.flip y)) (F.ι (fockAct2 p q r s Z P)) := by
      rw [neg_one_smul, map_neg]
      rfl
    rw [e, hB, ← hval]
    exact hc

end GlobalTheory.Chain.CoverContr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGlobalFockIntertwinerTensorRealPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.RealIt.TensorGlob

theorem der_span {E : Type*} [AddCommGroup E] [Module ℂ E] {s : Set E} (hs : Submodule.span ℂ s = ⊤)
    (f : ℝ → E →ₗ[ℂ] ℂ) (g : E →ₗ[ℂ] ℂ) (h : ∀ e ∈ s, HasDerivAt (fun t => f t e) (g e) 0) (e : E) :
    HasDerivAt (fun t => f t e) (g e) 0 := by
  have he : e ∈ Submodule.span ℂ s := hs ▸ Submodule.mem_top
  induction he using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    have h0 : (fun t => f t 0) = fun _ => (0 : ℂ) := funext fun t => map_zero (f t)
    rw [h0, map_zero]
    exact hasDerivAt_const _ _
  | add x y _ _ hx hy =>
    have h0 : (fun t => f t (x + y)) = fun t => f t x + f t y := funext fun t => map_add (f t) x y
    rw [h0, map_add (f := _)]
    exact hx.add hy
  | smul a x _ hx =>
    have h0 : (fun t => f t (a • x)) = fun t => a * f t x := funext fun t => map_smul (f t) a x
    rw [h0, map_smul, smul_eq_mul]
    exact hx.const_mul a

theorem der_span₂ {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    {s : Set E} (hs : Submodule.span ℂ s = ⊤) {s' : Set F} (hs' : Submodule.span ℂ s' = ⊤)
    (f : ℝ → E →ₗ[ℂ] F →ₗ[ℂ] ℂ) (g : E →ₗ[ℂ] F →ₗ[ℂ] ℂ)
    (h : ∀ e ∈ s, ∀ x ∈ s', HasDerivAt (fun t => f t e x) (g e x) 0) (e : E) (x : F) :
    HasDerivAt (fun t => f t e x) (g e x) 0 := by
  have h1 : ∀ x ∈ s', ∀ e', HasDerivAt (fun t => f t e' x) (g e' x) 0 := fun x hx e' =>
    der_span hs (fun t => (f t).flip x) (g.flip x) (fun e'' he'' => h e'' he'' x hx) e'
  exact der_span hs' (fun t => f t e) (g e) (fun x hx => h1 x hx e) x

variable {D : D7}

open Classical in
theorem glue_update {a b : ℕ} (P : D.what₂.Tau → LPol b a) (τ : D.what₂.Tau) (p : LPol b a) :
    glue (Function.update P τ p) = MvPolynomial.rename (fun s => (τ, s)) p *
      ∏ ρ ∈ Finset.univ.erase τ, MvPolynomial.rename (fun s => (ρ, s)) (P ρ) := by
  unfold glue
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
  congr 1
  · simp
  · exact Finset.prod_congr rfl fun ρ hρ => by simp [Finset.ne_of_mem_erase hρ]

open Classical in
theorem glue_update_add_smul {a b : ℕ} (P : D.what₂.Tau → LPol b a) (τ : D.what₂.Tau) (p : LPol b a) (c : ℂ) :
    glue (Function.update P τ p) + c • glue P = glue (Function.update P τ (p + c • P τ)) := by
  have h0 : glue P = glue (Function.update P τ (P τ)) := by rw [Function.update_eq_self]
  rw [h0, glue_update, glue_update, glue_update, map_add (f := _), map_smul, add_mul, smul_mul_assoc]

variable {V : HSp D} {S : D.what₂.Tau → SPar}

theorem ellT_tprod' (M : DSModel V S) (w v : ∀ τ, M.H τ) :
    ellT M w (PiTensorProduct.tprod ℂ v) = ∏ τ, ⟪w τ, v τ⟫_ℂ := by
  unfold ellT
  rw [PiTensorProduct.lift.tprod]
  simp

open Classical in
theorem ellT_update (M : DSModel V S) (w v : ∀ τ, M.H τ) (τ : D.what₂.Tau) (u : M.H τ) :
    ellT M w (PiTensorProduct.tprod ℂ (Function.update v τ u)) =
      ⟪w τ, u⟫_ℂ * ∏ ρ ∈ Finset.univ.erase τ, ⟪w ρ, v ρ⟫_ℂ := by
  rw [ellT_tprod', ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
  congr 1
  · simp
  · exact Finset.prod_congr rfl fun ρ hρ => by simp [Finset.ne_of_mem_erase hρ]

open Classical in
theorem actT_tprod (M : DSModel V S) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v : ∀ τ, M.H τ) :
    actT M τ g (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v τ (M.rep τ g (v τ))) := by
  unfold actT
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext ρ
  by_cases hρ : ρ = τ
  · subst hρ; simp
  · simp [Function.update_of_ne hρ]

theorem der_inner {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {c : ℝ → H} {y : H}
    (h : HasDerivAt c y 0) (w : H) (k : ℂ) : HasDerivAt (fun t => ⟪w, c t⟫_ℂ * k) (⟪w, y⟫_ℂ * k) 0 := by
  have h1 : HasDerivAt (fun t => ⟪w, c t⟫_ℂ) ⟪w, y⟫_ℂ 0 := by
    simpa [Function.comp_def] using ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  exact h1.mul_const k


open Classical in
theorem exists_globIt : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (aS aT : D.what₂.Tau → ℚ) (A : ∀ τ, LPol W.rank V.rank →ₗ[ℂ] M'.H τ →ₗ[ℂ] M.H τ), GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels.ContrTensor → GlueLaw D V.rank W.rank → (∀ τ, LocIt M M' τ (aS τ) (aT τ) (A τ)) → ∃ It I, GlobIt M M' aS aT It I := by
  intro D V W S S' M M' aS aT A hC hG hL
  have hs := hG.1
  have hs' : Submodule.span ℂ (Set.range (PiTensorProduct.tprod ℂ : (∀ τ, M'.H τ) → ⨂[ℂ] τ, M'.H τ)) = ⊤ :=
    PiTensorProduct.span_tprod_eq_top
  obtain ⟨I, hI, -⟩ := hC D.what₂.Tau (fun _ => Fin W.rank × Fin V.rank) (FVar D W.rank V.rank)
    (Equiv.sigmaEquivProd D.what₂.Tau (Fin W.rank × Fin V.rank) :
      (Σ _ : D.what₂.Tau, Fin W.rank × Fin V.rank) ≃ FVar D W.rank V.rank)
    (fun τ => M'.H τ) (fun τ => M.H τ) A
  have hIg : ∀ (P : D.what₂.Tau → LPol W.rank V.rank) (v : ∀ τ, M'.H τ),
      I (glue P) (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ fun ρ => A ρ (P ρ) (v ρ) :=
    fun P v => hI P v
  let Itl : ∀ τ, LPol W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.sm τ := fun τ =>
    LinearMap.mk₂ ℂ (fun P y => (⟨A τ P (y : M'.H τ), (hL τ).sm P (y : M'.H τ)⟩ : M.sm τ))
      (fun P Q y => Subtype.ext (by simp)) (fun c P y => Subtype.ext (by simp))
      (fun P y z => Subtype.ext (by simp)) (fun c P y => Subtype.ext (by simp))
  have hItl : ∀ τ P y, ((Itl τ P y : M.sm τ) : M.H τ) = A τ P (y : M'.H τ) := fun _ _ _ => rfl
  obtain ⟨It, hIt, hItne⟩ := hC D.what₂.Tau (fun _ => Fin W.rank × Fin V.rank) (FVar D W.rank V.rank)
    (Equiv.sigmaEquivProd D.what₂.Tau (Fin W.rank × Fin V.rank) :
      (Σ _ : D.what₂.Tau, Fin W.rank × Fin V.rank) ≃ FVar D W.rank V.rank)
    (fun τ => ↥(M'.sm τ)) (fun τ => ↥(M.sm τ)) Itl
  have hItg : ∀ (P : D.what₂.Tau → LPol W.rank V.rank) (v : ∀ τ, M'.sm τ),
      It (glue P) (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ fun ρ => Itl ρ (P ρ) (v ρ) :=
    fun P v => hIt P v
  have hupdP : ∀ (P : D.what₂.Tau → LPol W.rank V.rank) (τ : D.what₂.Tau) (Q : LPol W.rank V.rank)
      (v : ∀ τ, M'.H τ), (PiTensorProduct.tprod ℂ fun ρ => A ρ (Function.update P τ Q ρ) (v ρ)) =
        PiTensorProduct.tprod ℂ (Function.update (fun ρ => A ρ (P ρ) (v ρ)) τ (A τ Q (v τ))) := by
    intro P τ Q v
    congr 1
    funext ρ
    by_cases hρ : ρ = τ
    · subst hρ; simp
    · simp [Function.update_of_ne hρ]
  have hupdV : ∀ (P : D.what₂.Tau → LPol W.rank V.rank) (τ : D.what₂.Tau) (v : ∀ τ, M'.H τ) (y : M'.H τ),
      (PiTensorProduct.tprod ℂ fun ρ => A ρ (P ρ) (Function.update v τ y ρ)) =
        PiTensorProduct.tprod ℂ (Function.update (fun ρ => A ρ (P ρ) (v ρ)) τ (A τ (P τ) y)) := by
    intro P τ v y
    congr 1
    funext ρ
    by_cases hρ : ρ = τ
    · subst hρ; simp
    · simp [Function.update_of_ne hρ]
  refine ⟨It, I, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro φ v
    have h1 : It.compr₂ (inclT M) = I.compl₂ (inclT M') := by
      refine LinearMap.ext_on hs ?_
      rintro _ ⟨P, rfl⟩
      refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.compr₂_apply, LinearMap.compl₂_apply, hItg]
      unfold inclT
      simp only [PiTensorProduct.map_tprod, Submodule.subtype_apply, hItl, hIg]
    exact DFunLike.congr_fun (DFunLike.congr_fun h1 φ) v
  · apply hItne
    intro τ h0
    obtain ⟨P, y, hy, hne⟩ := (hL τ).ne
    apply hne
    have h2 := congrArg (fun B : LPol W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.sm τ =>
      ((B P ⟨y, hy⟩ : M.sm τ) : M.H τ)) h0
    simpa [hItl] using h2
  · intro φ w
    have hφ : φ ∈ Submodule.span ℂ (Set.range (glue : (D.what₂.Tau → LPol W.rank V.rank) → PolF D W.rank V.rank)) :=
      hs ▸ Submodule.mem_top
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨P, rfl⟩ := hx
      choose w' hw' using fun τ => (hL τ).adj (P τ) (w τ)
      refine Submodule.subset_span ⟨w', ?_⟩
      refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, hIg, ellT_tprod', hw']
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _), LinearMap.comp_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [map_smul, LinearMap.comp_smul]
      exact Submodule.smul_mem _ a hx
  · intro τ X hX φ x w
    have key := der_span₂ hs hs' (fun t => I.compr₂ (ellT M w ∘ₗ actT M τ (NormedSpace.exp (t • X))))
      ((I ∘ₗ srcOp M M' τ (aT τ) X).compr₂ (ellT M w)) ?hyp φ x
    · simpa only [LinearMap.compr₂_apply, LinearMap.comp_apply] using key
    case hyp =>
      rintro _ ⟨P, rfl⟩ _ ⟨v, rfl⟩
      simp only [LinearMap.compr₂_apply, LinearMap.comp_apply, srcOp, LinearMap.add_apply,
        LinearMap.smul_apply, Module.End.one_apply, (hG.2 τ (M.ε τ) (M'.ε τ) P).1, glue_update_add_smul,
        hIg, hupdP, actT_tprod, ellT_update]
      rw [neg_smul, ← sub_eq_add_neg]
      exact der_inner ((hL τ).src X hX (P τ) (v τ)) (w τ) _
  · intro τ Y hY φ x w
    have key := der_span₂ hs hs'
      (fun t => (I.compl₂ (actT M' τ (NormedSpace.exp (t • Y)))).compr₂ (ellT M w))
      (-((I ∘ₗ tgtOp M M' τ (aS τ) Y).compr₂ (ellT M w))) ?hyp φ x
    · simpa only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
        LinearMap.neg_apply] using key
    case hyp =>
      rintro _ ⟨P, rfl⟩ _ ⟨v, rfl⟩
      simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply, LinearMap.neg_apply,
        tgtOp, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
        (hG.2 τ (M.ε τ) (M'.ε τ) P).2, glue_update_add_smul, hIg, hupdP, hupdV, actT_tprod, ellT_update]
      rw [← neg_mul, ← inner_neg_right]
      exact der_inner ((hL τ).tgt Y hY (P τ) (v τ)) (w τ) _

end GlobalTheory.Chain.RealIt.TensorGlob

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHoweDualityIntertwinerUnitaryPairLocal
section
open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct InnerProductSpace

noncomputable section

namespace GlobalTheory.CompactHowe.Lift

open MvPolynomial

theorem map_star_subst2 {N n : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (Fin N × Fin n) ℂ) :
    MvPolynomial.map (starRingEnd ℂ) (subst2 A B P) =
      subst2 (A.map star) (B.map star) (MvPolynomial.map (starRingEnd ℂ) P) := by
  have key : (MvPolynomial.map (starRingEnd ℂ)).comp (subst2 A B).toRingHom =
      (subst2 (A.map star) (B.map star)).toRingHom.comp (MvPolynomial.map (starRingEnd ℂ)) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun p => ?_)
    · simp
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_X, subst2_X,
        map_sum, map_mul, map_C, Matrix.map_apply, starRingEnd_apply]
  exact congrArg (fun f => f P) key

theorem map_star_map_star_poly {N n : ℕ} (P : MvPolynomial (Fin N × Fin n) ℂ) :
    MvPolynomial.map (starRingEnd ℂ) (MvPolynomial.map (starRingEnd ℂ) P) = P := by
  rw [MvPolynomial.map_map]
  have : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := RingHom.ext fun z => by simp
  rw [this, MvPolynomial.map_id]

theorem map_star_smul {N n : ℕ} (c : ℂ) (P : MvPolynomial (Fin N × Fin n) ℂ) :
    MvPolynomial.map (starRingEnd ℂ) (c • P) = star c • MvPolynomial.map (starRingEnd ℂ) P := by
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, map_C]
  rfl

end GlobalTheory.CompactHowe.Lift

namespace GlobalTheory.CompactHowe

open Contraction Lift

theorem exists_local_lift : ∀ (N n : ℕ) (hn : n ≤ N) (ν : Fin N → ℕ) (x₁ x₃ : ℤ) (Λ : Fin n → ℝ) (Λ' : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H'] (σ' : Matrix (Fin N) (Fin N) ℂ → (H' →L[ℂ] H')), Antitone ν → (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) → (∀ a, Λ a = -(x₃ : ℝ) + ν (Fin.castLE hn a)) → (∀ b, Λ' b = (x₁ : ℝ) + ν b) → Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos n)) σ → Formalism.MainNotions.S.IsKTypeOf (Formalism.MainNotions.S.allPos n) σ Λ ⊤ → Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos N)) σ' → Formalism.MainNotions.S.IsKTypeOf (Formalism.MainNotions.S.allPos N) σ' Λ' ⊤ → ∃ I : MvPolynomial (Fin N × Fin n) ℂ →ₗ[ℂ] H →ₗ[ℂ] H', I ≠ 0 ∧ ∀ h ∈ Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos N), ∀ g ∈ Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos n), ∀ P v, I ((h.det ^ x₁ * g.det ^ x₃) • GlobalTheory.CompactHowe.subst2 h (g⁻¹)ᵀ P) (σ g v) = σ' h (I P v) := by
  intro N n hn ν x₁ x₃ Λ Λ' H _ _ _ σ H' _ _ _ σ' hν hν0 hΛ hΛ' hσ hK hσ' hK'
  obtain ⟨hτ, hτK⟩ := _root_.GlobalTheory.ConjTwist.conj_twist_isKTypeOf n Λ 0 H σ hσ hK
  obtain ⟨hτ', hτK'⟩ := _root_.GlobalTheory.ConjTwist.conj_twist_isKTypeOf N Λ' 0 H' σ' hσ' hK'
  obtain ⟨I₀, hI₀0, hI₀⟩ := _root_.GlobalTheory.CompactHowe.exists_local_contraction N n hn ν x₁ x₃ (fun a => ((0 : ℤ) : ℝ) - Λ (Fin.rev a))
    (fun b => ((0 : ℤ) : ℝ) - Λ' (Fin.rev b)) H (fun g => g.det ^ (0 : ℤ) • σ (g.map star)) H'
    (fun g => g.det ^ (0 : ℤ) • σ' (g.map star)) hν hν0
    (fun a => by simp only [hΛ, Int.cast_zero]; ring) (fun b => by simp only [hΛ', Int.cast_zero]; ring)
    hτ hτK hτ' hτK'
  let cj : MvPolynomial (Fin N × Fin n) ℂ →+* MvPolynomial (Fin N × Fin n) ℂ :=
    MvPolynomial.map (starRingEnd ℂ)
  refine ⟨{ toFun := fun P => LinearMap.adjoint (I₀ (cj P)),
            map_add' := fun P Q => by simp only [map_add (f := _)]
            map_smul' := fun c P => by
              simp only [cj, map_star_smul, map_smul, LinearEquiv.map_smulₛₗ, RingHom.id_apply]
              simp }, fun h0 => hI₀0 ?_, fun h hh g hg P v => ?_⟩
  · refine LinearMap.ext fun P => ?_
    have := congrArg (fun f => f (cj P)) h0
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply, cj, map_star_map_star_poly] at this
    simpa using this
  · have hQ : cj ((h.det ^ x₁ * g.det ^ x₃) • subst2 h (g⁻¹)ᵀ P) =
        ((h.map star).det ^ x₁ * (g.map star).det ^ x₃) • subst2 (h.map star) ((g.map star)⁻¹)ᵀ (cj P) := by
      simp only [cj]
      rw [map_star_smul, map_star_subst2, Contraction.inv_transpose hg,
        Contraction.inv_transpose (map_star_mem hg)]
      simp only [Contraction.det_map_star, star_mul', star_zpow₀]
    have key := hI₀ (h.map star) (map_star_mem hh) (g.map star) (map_star_mem hg) (cj P)
    simp only [zpow_zero, one_smul, map_star_map_star] at key
    show LinearMap.adjoint (I₀ (cj _)) (σ g v) = σ' h (LinearMap.adjoint (I₀ (cj P)) v)
    rw [hQ]
    refine ext_inner_left ℂ fun w => ?_
    obtain ⟨u, rfl⟩ : ∃ u, σ' h u = w := by
      refine ⟨σ' hᴴ w, ?_⟩
      have := hσ'.1.2 h hh _ (conjTranspose_mem hh)
      rw [mul_eq_one_comm.1 ((mem_iff h).1 hh), hσ'.1.1] at this
      simpa using (congrArg (fun f => f w) this).symm
    have iso1 : ∀ a b : H, inner ℂ (σ g a) (σ g b) = inner ℂ a b := fun a b =>
      (LinearIsometry.mk (σ g : H →ₗ[ℂ] H) (hσ.2.1 g hg)).inner_map_map a b
    have iso2 : ∀ a b : H', inner ℂ (σ' h a) (σ' h b) = inner ℂ a b := fun a b =>
      (LinearIsometry.mk (σ' h : H' →ₗ[ℂ] H') (hσ'.2.1 h hh)).inner_map_map a b
    rw [LinearMap.adjoint_inner_right, key u, iso1, iso2, LinearMap.adjoint_inner_right]

end GlobalTheory.CompactHowe
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GUnitOfModels
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem gUnit_of_models : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.toRealDat.IsModels → R.PGUnit F := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hM
  have hE := GlobalTheory.norm_gE_rows R.toRealDat hM.HE hM.gE hM.ν0
  have hW := GlobalTheory.gW_norm_eq R.toRealDat hM.HW hM.gW hM.νW
  refine ⟨fun g x y => ?_, fun j g x y => ?_⟩
  ·     exact congrArg _ (LinearIsometry.inner_map_map (⟨R.gE g, hE g⟩ : R.HE.H →ₗᵢ[ℂ] R.HE.H) (Tw.out x) (Tw.out y))
  ·     exact congrArg _ (LinearIsometry.inner_map_map
      (⟨R.gW j (sg0 D A3.A) g, hW j (sg0 D A3.A) g⟩ : (R.HW j (sg0 D A3.A)).H →ₗᵢ[ℂ] (R.HW j (sg0 D A3.A)).H) (Tw.out x) (Tw.out y))

end GlobalTheory
end

