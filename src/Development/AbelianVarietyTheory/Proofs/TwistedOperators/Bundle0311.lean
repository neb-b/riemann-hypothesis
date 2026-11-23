module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleQuotientsIsoOfIntertwinedSemisimple
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.RealQuot

theorem simpleQuot_iso_of_intertwined : ∀ (ι Fm Q Q' Pi : Type) [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Q'] [Module ℂ Q'] [AddCommGroup Pi] [Module ℂ Pi]
  (ρ : ι → Module.End ℂ Q) (C : Submodule ℂ Q) (ρ' : ι → Module.End ℂ Q') (C' : Submodule ℂ Q') (σ : ι → Module.End ℂ Pi)
  (β : Fm → Q →ₗ[ℂ] Pi) (β₁ : Q' →ₗ[ℂ] Pi),
  (∀ f i, β f ∘ₗ ρ i = σ i ∘ₗ β f) → (∀ i, β₁ ∘ₗ ρ' i = σ i ∘ₗ β₁) →
  (∀ f, GlobalTheory.RealQuot.rad ρ C ≤ LinearMap.ker (β f)) → GlobalTheory.RealQuot.rad ρ' C' ≤ LinearMap.ker β₁ → β₁ ≠ 0 →
  (⨆ f, LinearMap.range (β f)) = ⊤ →
  (∀ N : Submodule ℂ Q, GlobalTheory.RealQuot.IsStab ρ N → GlobalTheory.RealQuot.rad ρ C ≤ N → N = GlobalTheory.RealQuot.rad ρ C ∨ N = ⊤) →
  (∀ N : Submodule ℂ Q', GlobalTheory.RealQuot.IsStab ρ' N → GlobalTheory.RealQuot.rad ρ' C' ≤ N → N = GlobalTheory.RealQuot.rad ρ' C' ∨ N = ⊤) →
  (∀ N : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N → ∃ N' : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N' ∧ IsCompl N N') →
  ∃ e : (Q ⧸ GlobalTheory.RealQuot.rad ρ C) ≃ₗ[ℂ] (Q' ⧸ GlobalTheory.RealQuot.rad ρ' C'),
    ∀ i, e.toLinearMap ∘ₗ GlobalTheory.RealQuot.radAct ρ C i = GlobalTheory.RealQuot.radAct ρ' C' i ∘ₗ e.toLinearMap := by
  intro ι Fm Q Q' Pi _ _ _ _ _ _ ρ C ρ' C' σ β β₁ hβ hβ₁ hkβ hkβ₁ hβ₁0 hspan hQ hQ' hss
  set R := rad ρ C with hRdef
  set R' := rad ρ' C' with hR'def

  have kerStab : ∀ {X : Type} [AddCommGroup X] [Module ℂ X] (τ : ι → Module.End ℂ X) (g : X →ₗ[ℂ] Pi),
      (∀ i, g ∘ₗ τ i = σ i ∘ₗ g) → IsStab τ (LinearMap.ker g) := by
    intro X _ _ τ g hg i x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← LinearMap.comp_apply, hg i, LinearMap.comp_apply, hx, map_zero]
  set U := LinearMap.range β₁ with hUdef
  have hUs : IsStab σ U := by
    rintro i _ ⟨x, rfl⟩
    exact ⟨ρ' i x, by rw [← LinearMap.comp_apply, hβ₁ i, LinearMap.comp_apply]⟩

  have hUsimple : ∀ Wm : Submodule ℂ Pi, IsStab σ Wm → Wm ≤ U → Wm ≠ ⊥ → Wm = U := by
    intro Wm hW hWU hW0
    have hcs : IsStab ρ' (Wm.comap β₁) := fun i x hx => by
      show β₁ (ρ' i x) ∈ Wm
      rw [← LinearMap.comp_apply, hβ₁ i, LinearMap.comp_apply]
      exact hW i _ hx
    have hcR : R' ≤ Wm.comap β₁ := fun x hx => by
      show β₁ x ∈ Wm
      rw [LinearMap.mem_ker.1 (hkβ₁ hx)]
      exact Wm.zero_mem
    rcases hQ' _ hcs hcR with h | h
    · exfalso
      apply hW0
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨x, rfl⟩ := hWU hw
      have : x ∈ Wm.comap β₁ := hw
      rw [h] at this
      exact (Submodule.mem_bot ℂ).2 (LinearMap.mem_ker.1 (hkβ₁ this))
    · refine le_antisymm hWU ?_
      rintro _ ⟨x, rfl⟩
      have : x ∈ Wm.comap β₁ := h ▸ Submodule.mem_top
      exact this
  obtain ⟨N', hN's, hc⟩ := hss U hUs
  let P : Pi →ₗ[ℂ] Pi := U.subtype ∘ₗ Submodule.linearProjOfIsCompl U N' hc
  have hPU : ∀ y ∈ U, P y = y := fun y hy =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨y, hy⟩)
  have hPN : ∀ y ∈ N', P y = 0 := fun y hy => by
    exact (congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_right hc ⟨y, hy⟩) :)
  have hPmem : ∀ y, P y ∈ U := fun y => (Submodule.linearProjOfIsCompl U N' hc y).2
  have hdec : ∀ y : Pi, ∃ u ∈ U, ∃ n ∈ N', y = u + n := by
    intro y
    have : y ∈ U ⊔ N' := hc.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨u, hu, n, hn, h⟩ := Submodule.mem_sup.1 this
    exact ⟨u, hu, n, hn, h.symm⟩
  have hPσ : ∀ i y, P (σ i y) = σ i (P y) := by
    intro i y
    obtain ⟨u, hu, n, hn, rfl⟩ := hdec y
    rw [map_add (f := _), map_add (f := _), map_add (f := _), hPU _ (hUs i u hu), hPN _ (hN's i n hn), hPU u hu, hPN n hn, add_zero, add_zero]

  obtain ⟨f, hf⟩ : ∃ f, P ∘ₗ β f ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hle : ∀ f, LinearMap.range (β f) ≤ N' := by
      rintro f _ ⟨x, rfl⟩
      obtain ⟨u, hu, n, hn, he⟩ := hdec (β f x)
      have h0 : P (β f x) = 0 := by rw [← LinearMap.comp_apply, hall f, LinearMap.zero_apply]
      rw [he, map_add (f := _), hPU u hu, hPN n hn, add_zero] at h0
      rw [he, h0, zero_add]; exact hn
    have hN'top : N' = ⊤ := eq_top_iff.2 (hspan ▸ iSup_le hle)
    have hU0 : U = ⊥ := by
      have := hc.inf_eq_bot
      rwa [hN'top, inf_top_eq] at this
    apply hβ₁0
    ext x
    have : β₁ x ∈ U := LinearMap.mem_range_self β₁ x
    rw [hU0, Submodule.mem_bot] at this
    exact this
  set γ := P ∘ₗ β f with hγdef
  have hγi : ∀ i, γ ∘ₗ ρ i = σ i ∘ₗ γ := by
    intro i; ext x
    show P (β f (ρ i x)) = σ i (P (β f x))
    have h := LinearMap.congr_fun (hβ f i) x
    simp only [LinearMap.comp_apply] at h
    rw [h, hPσ]
  have hRγ : R ≤ LinearMap.ker γ := fun x hx => by
    rw [LinearMap.mem_ker, hγdef, LinearMap.comp_apply, LinearMap.mem_ker.1 (hkβ f hx), map_zero]
  have hkerγ : LinearMap.ker γ = R := by
    rcases hQ _ (kerStab ρ γ hγi) hRγ with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.1 h) hf
  have hkerβ₁ : LinearMap.ker β₁ = R' := by
    rcases hQ' _ (kerStab ρ' β₁ hβ₁) hkβ₁ with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.1 h) hβ₁0
  have hrangeγ : LinearMap.range γ = U := by
    apply hUsimple
    · rintro i _ ⟨x, rfl⟩
      exact ⟨ρ i x, by rw [← LinearMap.comp_apply, hγi i, LinearMap.comp_apply]⟩
    · rintro _ ⟨x, rfl⟩; exact hPmem _
    · intro h
      apply hf
      ext x
      have : γ x ∈ LinearMap.range γ := LinearMap.mem_range_self γ x
      rw [h, Submodule.mem_bot] at this
      exact this
  let φ := R.liftQ γ hRγ
  let ψ := R'.liftQ β₁ hkβ₁
  have hφi : Function.Injective φ := LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ hkerγ.le)
  have hψi : Function.Injective ψ := LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ hkerβ₁.le)
  have hrφ : LinearMap.range φ = LinearMap.range ψ := by
    rw [Submodule.range_liftQ, Submodule.range_liftQ, hrangeγ]
  let e : (Q ⧸ R) ≃ₗ[ℂ] (Q' ⧸ R') :=
    (LinearEquiv.ofInjective φ hφi).trans ((LinearEquiv.ofEq _ _ hrφ).trans (LinearEquiv.ofInjective ψ hψi).symm)
  have he : ∀ x, ψ (e x) = φ x := by
    intro x
    have h1 := LinearEquiv.ofInjective_apply (f := ψ) (h := hψi)
      ((LinearEquiv.ofInjective ψ hψi).symm ((LinearEquiv.ofEq _ _ hrφ) (LinearEquiv.ofInjective φ hφi x)))
    rw [LinearEquiv.apply_symm_apply] at h1
    exact h1.symm
  refine ⟨e, fun i => ?_⟩
  apply Submodule.linearMap_qext
  ext q
  apply hψi
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe]
  rw [he, radAct_mk]
  obtain ⟨q', hq'⟩ := Submodule.Quotient.mk_surjective R' (e (Submodule.Quotient.mk q))
  rw [← hq', radAct_mk]
  have h2 := he (Submodule.Quotient.mk q)
  rw [← hq'] at h2
  simp only [φ, ψ, Submodule.liftQ_apply] at h2 ⊢
  have hb := LinearMap.congr_fun (hβ₁ i) q'
  have hg := LinearMap.congr_fun (hγi i) q
  simp only [LinearMap.comp_apply] at hb hg
  rw [hb, h2]
  exact hg

end GlobalTheory.RealQuot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticHomTransposeGramDarboux
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DarbouxSymp

variable {D : D7}

theorem cA_incA_eq (a : D.host.E) : cA D (incA D a) = incA D (star a) := by
  simp only [cA, sigR, incA, inclR]
  simp
  rfl

theorem gram_star_eq (V : HSp D) (i j) : star (V.gram i j) = V.gram j i :=
  V.herm.eq (V.frame i) (V.frame j)

theorem gram_det_ne_zero (V : HSp D) : V.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have : V.frame.equivFun.symm v = 0 := by
    apply V.nondeg.2
    intro x
    have hx : x = ∑ i, V.frame.repr x i • V.frame i := (V.frame.sum_repr x).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h1 : ∑ j, V.gram i j * v j = 0 := congr_fun h0 i
    have h2 : V.hT (V.frame i) (V.frame.equivFun.symm v) = ∑ j, V.gram i j * v j := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Module.Basis.equivFun_symm_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]; rfl
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, h2, h1, smul_zero]
  exact V.frame.equivFun.symm.injective (this.trans (map_zero _).symm)

theorem gram_map_mul_inv (V : HSp D) :
    HMul.hMul (V.gram.map (incA D) : Matrix (Fin V.rank) (Fin V.rank) (AE D)) (V.gram⁻¹.map (incA D) : Matrix (Fin V.rank) (Fin V.rank) (AE D)) = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (gram_det_ne_zero V))]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem hO_rearr (S T : HSp D) (X Y : WO S T) : hO S T X Y =
    ∑ b, ∑ c, ∑ d, cA D (Y c b) * incA D (T.gram c d) * ∑ a, X d a * incA D (S.gram⁻¹ a b) := by
  unfold hO
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem hO_darboux (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank) (e₂ : Fin S'.rank ≃ Fin T.rank)
    (hT' : T'.gramᵀ = -(S.gram.submatrix e₁ e₁)) (hS' : S'.gram⁻¹ = -(T.gramᵀ.submatrix e₂ e₂)) (x y : WO S' T') :
    hO S T (HMul.hMul (xᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))
      (HMul.hMul (yᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) =
    hO S' T' x y := by
  have L1 : ∀ d b, ∑ a, (HMul.hMul (xᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) d a
      * incA D (S.gram⁻¹ a b) = x (e₁.symm b) (e₂.symm d) := by
    intro d b
    have h := congrFun (congrFun (show HMul.hMul (HMul.hMul (xᵀ.submatrix e₂.symm e₁.symm : Matrix (Fin T.rank) (Fin S.rank) (AE D))
      (S.gram.map (incA D) : Matrix (Fin S.rank) (Fin S.rank) (AE D))) (S.gram⁻¹.map (incA D) : Matrix (Fin S.rank) (Fin S.rank) (AE D))
      = (xᵀ.submatrix e₂.symm e₁.symm : Matrix (Fin T.rank) (Fin S.rank) (AE D)) by
        rw [Matrix.mul_assoc, gram_map_mul_inv, Matrix.mul_one]) d) b
    rw [Matrix.mul_apply] at h
    simpa using h
  have L2 : ∀ c b, cA D ((HMul.hMul (yᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) c b)
      = ∑ k, cA D (y (e₁.symm k) (e₂.symm c)) * incA D (S.gram b k) := by
    intro c b
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, Matrix.map_apply, cA_incA_eq, gram_star_eq]
    rfl
  have E1 : ∀ a b, S'.gram⁻¹ a b = -T.gram (e₂ b) (e₂ a) := fun a b => by
    rw [hS']; rfl
  have E2 : ∀ c d, T'.gram c d = -S.gram (e₁ d) (e₁ c) := fun c d => by
    have := congrFun (congrFun hT' d) c
    simpa using this
  rw [hO_rearr]
  simp_rw [L1, L2]
  unfold hO
  simp_rw [E1, E2]
  have hR : ∀ F : Fin S.rank → Fin T.rank → Fin T.rank → Fin S.rank → AE D,
      (∀ a b c d, incA D (-T.gram (e₂ b) (e₂ a)) * cA D (y c b) * incA D (-S.gram (e₁ d) (e₁ c)) * x d a
        = F (e₁ d) (e₂ b) (e₂ a) (e₁ c)) →
      ∑ a, ∑ b, ∑ c, ∑ d, incA D (-T.gram (e₂ b) (e₂ a)) * cA D (y c b) * incA D (-S.gram (e₁ d) (e₁ c)) * x d a
        = ∑ d, ∑ c, ∑ k, ∑ b, F b c d k := by
    intro F hF
    refine Fintype.sum_equiv e₂ _ _ fun a => ?_
    refine Fintype.sum_equiv e₂ _ _ fun b => ?_
    refine Fintype.sum_equiv e₁ _ _ fun c => ?_
    refine Fintype.sum_equiv e₁ _ _ fun d => ?_
    exact hF a b c d
  rw [hR (fun b c d k => cA D (y (e₁.symm k) (e₂.symm c)) * incA D (S.gram b k) * incA D (T.gram c d) * x (e₁.symm b) (e₂.symm d))
    (fun a b c d => by simp only [Equiv.symm_apply_apply, map_neg]; ring)]
  simp only [Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, c]; rw [Finset.sum_comm]
  conv_lhs => enter [2, c, 2, d]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]

theorem symplO_darboux : ∀ (D : D7) (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank) (e₂ : Fin S'.rank ≃ Fin T.rank),
    T'.gramᵀ = -(S.gram.submatrix e₁ e₁) → S'.gram⁻¹ = -(T.gramᵀ.submatrix e₂ e₂) → ∀ x y : WO S' T',
      symplO S T (HMul.hMul (xᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))
        (HMul.hMul (yᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) =
      symplO S' T' x y := by
  intro D S T S' T' e₁ e₂ hT' hS' x y
  unfold symplO
  rw [hO_darboux S T S' T' e₁ e₂ hT' hS' x y]

end GlobalTheory.DarbouxSymp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorLatticeMulTransposeStableIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.LatStab

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem gen_mul_transpose {n d : ℕ} (x : Fin n → E) (y : Fin d → E) (a : AF F)
    (K : Matrix (Fin d) (Fin d) (AE F E)) :
    (a • incM F (Matrix.vecMulVec x y)) * Kᵀ =
      Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i))
        (a • (K *ᵥ fun i => inclR (F := F) (AF F) (y i))) := by
  ext i j
  simp only [incM, Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.vecMulVec_apply,
    Matrix.transpose_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, map_mul, Finset.smul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  ring

theorem vecMulVec_mem {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (x : Fin n → E) (hx : x ∈ X.L) (u : Fin d → AE F E)
    (hu : u ∈ AddSubgroup.closure {z | ∃ b : AF F, At (evFin F w) b ∧
          evFin F w b ∈ w.adicCompletionIntegers F ∧
          ∃ y' ∈ W.L, z = b • fun i => inclR (F := F) (AF F) (y' i)}) :
    Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) u ∈ latAtV X W w := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨b, hb, hbi, y', hy', rfl⟩ := hu
    apply AddSubgroup.subset_closure
    refine ⟨b, hb, hbi, x, hx, y', hy', ?_⟩
    ext i j
    simp only [incM, Matrix.smul_apply, Matrix.map_apply, Matrix.vecMulVec_apply, Pi.smul_apply, map_mul]
    rw [mul_smul_comm]
  | zero =>
    have : Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (0 : Fin d → AE F E) = 0 := by
      ext i j; simp [Matrix.vecMulVec_apply]
    rw [this]; exact zero_mem _
  | add u v _ _ hu hv =>
    have : Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (u + v) =
        Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) u +
          Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) v := by
      ext i j; simp [Matrix.vecMulVec_apply, mul_add]
    rw [this]; exact add_mem hu hv
  | neg u _ hu =>
    have : Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (-u) =
        -Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) u := by
      ext i j; simp [Matrix.vecMulVec_apply]
    rw [this]; exact neg_mem hu

theorem mul_transpose_mem {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (K : Matrix (Fin d) (Fin d) (AE F E))
    (hK : ∀ a : AF F, At (evFin F w) a → evFin F w a ∈ w.adicCompletionIntegers F →
      ∀ y ∈ W.L, a • (K *ᵥ fun i => inclR (F := F) (AF F) (y i)) ∈
        AddSubgroup.closure {z | ∃ b : AF F, At (evFin F w) b ∧
          evFin F w b ∈ w.adicCompletionIntegers F ∧
          ∃ y' ∈ W.L, z = b • fun i => inclR (F := F) (AF F) (y' i)})
    (γ : Matrix (Fin n) (Fin d) (AE F E)) (hγ : γ ∈ latAtV X W w) : γ * Kᵀ ∈ latAtV X W w := by
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hai, x, hx, y, hy, rfl⟩ := hz
    rw [gen_mul_transpose]
    exact vecMulVec_mem X W w x hx _ (hK a ha hai y hy)
  | zero => simp
  | add u v _ _ hu hv => rw [Matrix.add_mul]; exact add_mem hu hv
  | neg u _ hu => rw [Matrix.neg_mul]; exact neg_mem hu

theorem latAtV_mul_transpose_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (K K' : Matrix (Fin d) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), K' * K = 1 →
    (∀ a : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) a → GlobalTheory.AdelicU.evFin F w a ∈ w.adicCompletionIntegers F →
      ∀ y ∈ W.L, a • (K *ᵥ fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y i)) ∈
        AddSubgroup.closure {z | ∃ b : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) b ∧
          GlobalTheory.AdelicU.evFin F w b ∈ w.adicCompletionIntegers F ∧
          ∃ y' ∈ W.L, z = b • fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y' i)}) →
    (∀ a : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) a → GlobalTheory.AdelicU.evFin F w a ∈ w.adicCompletionIntegers F →
      ∀ y ∈ W.L, a • (K' *ᵥ fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y i)) ∈
        AddSubgroup.closure {z | ∃ b : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) b ∧
          GlobalTheory.AdelicU.evFin F w b ∈ w.adicCompletionIntegers F ∧
          ∃ y' ∈ W.L, z = b • fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y' i)}) →
    ∀ γ, γ * Kᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W w := by
  intro F E _ _ _ _ _ n d X W w K K' hKK hK hK' γ
  constructor
  · intro h
    have h2 := mul_transpose_mem X W w K' hK' _ h
    rwa [Matrix.mul_assoc, ← Matrix.transpose_mul, hKK, Matrix.transpose_one, Matrix.mul_one] at h2
  · exact mul_transpose_mem X W w K hK γ

end GlobalTheory.LatStab
end

