module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0039
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeviRep
section
noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
open scoped TensorProduct

namespace GlobalTheory.GodementJacquet

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r t : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def eMat (k : Type) [Field k] (r t : ℕ) : Matrix (Fin (r + t)) (Fin r) k :=
  Matrix.of fun i j => if (i : ℕ) = j then 1 else 0

end GlobalTheory.GodementJacquet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OmQuotientTransposeInverse
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.HoweTranspose

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def trH (a b : ℕ) : Matrix (Fin a) (Fin b) k ≃ₜ Matrix (Fin b) (Fin a) k where
  toFun := Matrix.transpose
  invFun := Matrix.transpose
  left_inv := Matrix.transpose_transpose
  right_inv := Matrix.transpose_transpose
  continuous_toFun := continuous_id.matrix_transpose
  continuous_invFun := continuous_id.matrix_transpose

theorem comp_trH_mem {a b : ℕ} {f : Matrix (Fin b) (Fin a) k → ℂ}
    (hf : f ∈ SB (Matrix (Fin b) (Fin a) k)) : f ∘ trH a b ∈ SB (Matrix (Fin a) (Fin b) k) :=
  ⟨hf.1.comp_continuous (trH a b).continuous, hf.2.comp_homeomorph (trH a b)⟩

def trL (a b : ℕ) : SB (Matrix (Fin b) (Fin a) k) →ₗ[ℂ] SB (Matrix (Fin a) (Fin b) k) where
  toFun Ψ := ⟨Ψ.1 ∘ trH a b, comp_trH_mem Ψ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem trL_trL (a b : ℕ) (Φ : SB (Matrix (Fin a) (Fin b) k)) : trL a b (trL b a Φ) = Φ := by
  apply Subtype.ext
  funext x
  show Φ.1 x.transpose.transpose = Φ.1 x
  rw [Matrix.transpose_transpose]

theorem det_transInv {m : ℕ} (θ : GL (Fin m) k →* GL (Fin m) k)
    (hθ : ∀ g, (θ g).val = (g⁻¹).val.transpose) (g : GL (Fin m) k) :
    Matrix.GeneralLinearGroup.det (θ g) = (Matrix.GeneralLinearGroup.det g)⁻¹ := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, hθ, Matrix.det_transpose, ← Matrix.GeneralLinearGroup.val_det_apply,
    map_inv]

theorem nabs_det_transInv {m : ℕ} (θ : GL (Fin m) k →* GL (Fin m) k)
    (hθ : ∀ g, (θ g).val = (g⁻¹).val.transpose) (g : GL (Fin m) k) :
    nabs k (Matrix.GeneralLinearGroup.det (θ g)) = (nabs k (Matrix.GeneralLinearGroup.det g))⁻¹ := by
  rw [det_transInv θ hθ]
  simp [nabs, map_inv]

theorem rpow_inv_half {a : ℝ} (ha : 0 < a) (c : ℝ) : (a⁻¹) ^ (c / 2) = a ^ (-c / 2) := by
  rw [Real.inv_rpow ha.le, ← Real.rpow_neg ha.le, neg_div]

theorem om_trans {r n : ℕ} (θr : GL (Fin r) k →* GL (Fin r) k) (θn : GL (Fin n) k →* GL (Fin n) k)
    (hr : ∀ g, (θr g).val = (g⁻¹).val.transpose) (hn : ∀ g, (θn g).val = (g⁻¹).val.transpose)
    (g : GL (Fin n) k) (h : GL (Fin r) k) (Ψ : Matrix (Fin r) (Fin n) k → ℂ) :
    om 1 g h Ψ ∘ trH n r = om 1 (θr h) (θn g) (Ψ ∘ trH n r) := by
  funext x
  have hm : ((θn g)⁻¹ : GL (Fin n) k).val * x * (θr h).val = (h⁻¹.val * x.transpose * g.val).transpose := by
    rw [← map_inv, hn, hr, inv_inv, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
  simp only [om, Function.comp_apply, map_one, MonoidHom.one_apply, Units.val_one, inv_one, one_mul,
    Fintype.card_fin]
  rw [nabs_det_transInv θr hr, nabs_det_transInv θn hn, rpow_inv_half (nabs_pos' k _),
    rpow_inv_half (nabs_pos' k _), neg_neg, hm]
  have e1 : trH n r (h⁻¹.val * x.transpose * g.val).transpose = h⁻¹.val * x.transpose * g.val :=
    Matrix.transpose_transpose _
  have e2 : trH n r x = x.transpose := rfl
  rw [e1, e2]
  ring

end GlobalTheory.HoweTranspose


open GlobalTheory.HoweTranspose in
theorem GlobalTheory.omQuot_transpose : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r n : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) V) (τ : Representation ℂ (GL (Fin n) k) W) (θr : GL (Fin r) k →* GL (Fin r) k) (θn : GL (Fin n) k →* GL (Fin n) k), (∀ g, (θr g).val = (g⁻¹).val.transpose) → (∀ g, (θn g).val = (g⁻¹).val.transpose) → OmQuot 1 σ τ → OmQuot 1 (τ.comp θn : Representation ℂ (GL (Fin n) k) W) (σ.comp θr : Representation ℂ (GL (Fin r) k) V) := by
  intro k _ _ _ _ r n V W _ _ _ _ σ τ θr θn hr hn ⟨f, hf0, hf⟩
  refine ⟨(TensorProduct.comm ℂ V W).toLinearMap ∘ₗ f ∘ₗ trL n r, ?_, ?_⟩
  · intro h0
    apply hf0
    ext Φ
    have := LinearMap.congr_fun h0 (trL r n Φ)
    simp only [LinearMap.coe_comp, Function.comp_apply, trL_trL, LinearEquiv.coe_coe,
      LinearMap.zero_apply] at this
    simpa using this
  · intro g h Ψ Ψ' hΨ
    have key : f (trL n r Ψ') = TensorProduct.map (σ (θr h)) (τ (θn g)) (f (trL n r Ψ)) := by
      refine hf (θr h) (θn g) _ _ ?_
      show Ψ'.1 ∘ trH n r = om 1 (θr h) (θn g) (Ψ.1 ∘ trH n r)
      rw [hΨ]
      exact om_trans θr θn hr hn g h Ψ.1
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, key, MonoidHom.coe_comp]
    exact (TensorProduct.map_comm _ _ _).symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OmQuotientTrivialRankZero
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HoweZero

section Gen

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem nontrivial_of_isIrreducible {σ : Representation ℂ G V} (hσ : σ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  obtain ⟨a, b, hab⟩ := hσ.toNontrivial.exists_pair_ne
  exact hab (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem equiv_trivial_of_fixed {σ : Representation ℂ G V} (hσ : σ.IsIrreducible) {v : V} (hv : v ≠ 0)
    (hfix : ∀ g, σ g v = v) : Nonempty (σ.Equiv (Representation.trivial ℂ G ℂ)) := by
  let S : Subrepresentation σ := ⟨ℂ ∙ v, fun g x hx => by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [map_smul, hfix]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)⟩
  have hS : S = ⊤ := by
    rcases hσ.eq_bot_or_eq_top S with h | h
    · exfalso
      apply hv
      have : v ∈ S.toSubmodule := Submodule.mem_span_singleton_self v
      rw [h] at this
      exact (Submodule.mem_bot ℂ).1 this
    · exact h
  have htop : (ℂ ∙ v) = ⊤ := congrArg Subrepresentation.toSubmodule hS
  have hall : ∀ g (x : V), σ g x = x := by
    intro g x
    have : x ∈ ℂ ∙ v := htop ▸ Submodule.mem_top
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 this
    rw [map_smul, hfix]
  let e : ℂ ≃ₗ[ℂ] V := (LinearEquiv.toSpanNonzeroSingleton ℂ V v hv).trans (LinearEquiv.ofTop _ htop)
  exact ⟨Representation.Equiv.mk e.symm fun g => by
    ext x
    simp [hall]⟩

theorem fixed_of_tensor_left (e : V ≃ₗ[ℂ] ℂ) (τ : Representation ℂ H W) (t : V ⊗[ℂ] W) (ht0 : t ≠ 0)
    (ht : ∀ h, TensorProduct.map (1 : Module.End ℂ V) (τ h) t = t) : ∃ w : W, w ≠ 0 ∧ ∀ h, τ h w = w := by
  let L : V ⊗[ℂ] W ≃ₗ[ℂ] W := (TensorProduct.congr e (LinearEquiv.refl ℂ W)).trans (TensorProduct.lid ℂ W)
  refine ⟨L t, fun h => ht0 (L.injective (by rw [h, map_zero])), fun h => ?_⟩
  have key : ∀ s : V ⊗[ℂ] W, L (TensorProduct.map (1 : Module.End ℂ V) (τ h) s) = τ h (L s) := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [L]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  rw [← key, ht]

theorem fixed_of_tensor_right (e : W ≃ₗ[ℂ] ℂ) (σ : Representation ℂ G V) (t : V ⊗[ℂ] W) (ht0 : t ≠ 0)
    (ht : ∀ g, TensorProduct.map (σ g) (1 : Module.End ℂ W) t = t) : ∃ v : V, v ≠ 0 ∧ ∀ g, σ g v = v := by
  let L : V ⊗[ℂ] W ≃ₗ[ℂ] V := (TensorProduct.congr (LinearEquiv.refl ℂ V) e).trans (TensorProduct.rid ℂ V)
  refine ⟨L t, fun h => ht0 (L.injective (by rw [h, map_zero])), fun g => ?_⟩
  have key : ∀ s : V ⊗[ℂ] W, L (TensorProduct.map (σ g) (1 : Module.End ℂ W) s) = σ g (L s) := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [L]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  rw [← key, ht]

end Gen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem gl_zero_eq_one (g : GL (Fin 0) k) : g = 1 :=
  Units.ext (Matrix.ext fun i => Fin.elim0 i)

theorem nabs_one' : nabs k 1 = 1 := by simp [nabs]

theorem detRep_one (m : ℕ) : detRep (Fin m) (1 : kˣ →* ℂˣ) = Representation.trivial ℂ (GL (Fin m) k) ℂ := by
  unfold detRep ofChar detChar
  rw [MonoidHom.one_comp, twist_one]

theorem om_left (n : ℕ) (h : GL (Fin n) k) (Φ : Matrix (Fin n) (Fin 0) k → ℂ) :
    om (1 : kˣ →* ℂˣ) (1 : GL (Fin 0) k) h Φ = Φ := by
  funext x
  simp [om, nabs_one']
  exact congrArg Φ (Matrix.ext fun i j => Fin.elim0 j)

theorem om_right (r : ℕ) (g : GL (Fin r) k) (Φ : Matrix (Fin 0) (Fin r) k → ℂ) :
    om (1 : kˣ →* ℂˣ) g (1 : GL (Fin 0) k) Φ = Φ := by
  funext x
  simp [om, nabs_one']
  exact congrArg Φ (Matrix.ext fun i j => Fin.elim0 i)

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r n : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) V) (τ : Representation ℂ (GL (Fin n) k) W), r = 0 ∨ n = 0 → σ.IsIrreducible → τ.IsIrreducible → OmQuot 1 σ τ → Nonempty (σ.Equiv (detRep (Fin r) (1 : kˣ →* ℂˣ))) ∧ Nonempty (τ.Equiv (detRep (Fin n) (1 : kˣ →* ℂˣ))) := by
  intro k _ _ _ _ r n V W _ _ _ _ σ τ hrn hσ hτ hq
  obtain ⟨f, hf0, hf⟩ := hq
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, f Φ ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hf0 (LinearMap.ext hc)
  rw [detRep_one, detRep_one]
  rcases hrn with rfl | rfl
  · haveI := nontrivial_of_isIrreducible hσ
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    obtain ⟨eσ⟩ := equiv_trivial_of_fixed hσ hv (fun g => by rw [gl_zero_eq_one g, map_one]; rfl)
    have ht : ∀ h, TensorProduct.map (1 : Module.End ℂ V) (τ h) (f Φ) = f Φ := fun h => by
      have := hf 1 h Φ Φ (om_left n h Φ).symm
      rw [map_one] at this
      exact this.symm
    obtain ⟨w, hw0, hw⟩ := fixed_of_tensor_left eσ.toLinearEquiv τ _ hΦ ht
    exact ⟨⟨eσ⟩, equiv_trivial_of_fixed hτ hw0 hw⟩
  · haveI := nontrivial_of_isIrreducible hτ
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    obtain ⟨eτ⟩ := equiv_trivial_of_fixed hτ hw (fun h => by rw [gl_zero_eq_one h, map_one]; rfl)
    have ht : ∀ g, TensorProduct.map (σ g) (1 : Module.End ℂ W) (f Φ) = f Φ := fun g => by
      have := hf g 1 Φ Φ (om_right r g Φ).symm
      rw [map_one] at this
      exact this.symm
    obtain ⟨v, hv0, hv⟩ := fixed_of_tensor_right eτ.toLinearEquiv σ _ hΦ ht
    exact ⟨equiv_trivial_of_fixed hσ hv0 hv, ⟨eτ⟩⟩

end GlobalTheory.HoweZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OmQuotientTwistDet
section
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
open scoped TensorProduct

namespace GlobalTheory.OmTwist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem om_mul {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ χ : kˣ →* ℂˣ)
    (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ) :
    om (μ * χ) g h Φ =
      (((χ (Matrix.GeneralLinearGroup.det g)) * (χ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ) •
        om μ g h Φ := by
  funext x
  simp only [om, MonoidHom.mul_apply, Pi.smul_apply, smul_eq_mul, Units.val_mul, mul_inv]
  ring

theorem tmap_twist {r n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin r) k) V) (τ : Representation ℂ (GL (Fin n) k) W) (χ : kˣ →* ℂˣ)
    (g : GL (Fin r) k) (h : GL (Fin n) k) :
    TensorProduct.map (twist σ (detChar (Fin r) χ) g) (twist τ (detChar (Fin n) χ⁻¹) h) =
      (((χ (Matrix.GeneralLinearGroup.det g)) * (χ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ) •
        TensorProduct.map (σ g) (τ h) := by
  apply TensorProduct.ext'
  intro v w
  simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, mul_comm]

theorem omQuot_mul {r n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (μ χ : kˣ →* ℂˣ) (σ : Representation ℂ (GL (Fin r) k) V) (τ : Representation ℂ (GL (Fin n) k) W)
    (hq : OmQuot μ σ τ) :
    OmQuot (μ * χ) (twist σ (detChar (Fin r) χ)) (twist τ (detChar (Fin n) χ⁻¹)) := by
  obtain ⟨f, hf0, hf⟩ := hq
  refine ⟨f, hf0, fun g h Φ Φ' hΦ' => ?_⟩
  set c : ℂˣ := χ (Matrix.GeneralLinearGroup.det g) * (χ (Matrix.GeneralLinearGroup.det h))⁻¹ with hc
  let Ψ : SB (Matrix (Fin n) (Fin r) k) := ((c⁻¹ : ℂˣ) : ℂ) • Φ'
  have hΨ : (Ψ : Matrix (Fin n) (Fin r) k → ℂ) = om μ g h Φ := by
    show ((c⁻¹ : ℂˣ) : ℂ) • (Φ' : Matrix (Fin n) (Fin r) k → ℂ) = _
    rw [hΦ', om_mul, ← hc, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  have hΦΨ : Φ' = (c : ℂ) • Ψ := by
    show Φ' = (c : ℂ) • (((c⁻¹ : ℂˣ) : ℂ) • Φ')
    rw [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
  rw [tmap_twist, ← hc, hΦΨ, map_smul, hf g h Φ Ψ hΨ, LinearMap.smul_apply]

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r n : ℕ) (μ : kˣ →* ℂˣ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) V) (τ : Representation ℂ (GL (Fin n) k) W), OmQuot μ σ τ ↔ OmQuot 1 (twist σ (detChar (Fin r) μ⁻¹)) (twist τ (detChar (Fin n) μ)) := by
  intro k _ _ _ _ r n μ V W _ _ _ _ σ τ
  constructor
  · intro hq
    have := omQuot_mul μ μ⁻¹ σ τ hq
    rwa [mul_inv_cancel, inv_inv] at this
  · intro hq
    have := omQuot_mul 1 μ _ _ hq
    have e1 : detChar (Fin r) μ * detChar (Fin r) μ⁻¹ = (1 : GL (Fin r) k →* ℂˣ) := by
      ext g; simp
    have e2 : detChar (Fin n) μ⁻¹ * detChar (Fin n) μ = (1 : GL (Fin n) k →* ℂˣ) := by
      ext g; simp
    rwa [one_mul, twist_twist, twist_twist, e1, e2, twist_one, twist_one] at this

end GlobalTheory.OmTwist
end
end

