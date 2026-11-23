module

public import Mathlib
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle0004

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ScalarInertia
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Polynomial Module
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.WeilDeligne

namespace UpperTheory.TNZ.ScalarInertia

theorem eq_algebraMap_of_charpoly {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : End ℂ V) (hs : f.IsSemisimple) (c : ℂ) (m : ℕ) (hc : f.charpoly = (X - C c) ^ m) :
    f = algebraMap ℂ (End ℂ V) c := by
  have hg : (f - algebraMap ℂ (End ℂ V) c).IsSemisimple :=
    Module.End.isSemisimple_sub_algebraMap_iff.mpr hs
  have hn : IsNilpotent (f - algebraMap ℂ (End ℂ V) c) := by
    refine ⟨m, ?_⟩
    have := LinearMap.aeval_self_charpoly f
    rw [hc] at this
    simpa [map_pow, map_sub, aeval_X, aeval_C] using this
  exact sub_eq_zero.mp (Module.End.eq_zero_of_isNilpotent_isSemisimple hn hg)

variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem isSmooth_inv {ψ : Weil h →* ℂˣ} (hψ : IsSmooth ψ) : IsSmooth ψ⁻¹ :=
  hψ.of_le fun σ hσ => by simp [hσ]

variable [IsAlgClosure E Ω]

theorem unr_twist {n : ℕ} (a : WDRep h (Fin n → ℂ)) (ψ : Weil h →* ℂˣ) (hψ : IsSmooth ψ) (hN : a.N = 0)
    (m : ℕ) (hc : ∀ t : Ine (F := E) A,
      (a.ρ (ineIncl h t)).charpoly = (X - C ((ψ (ineIncl h t) : ℂˣ) : ℂ)) ^ m) :
    (a.twist ψ⁻¹ (isSmooth_inv hψ)).Unr := by
  refine ⟨hN, fun t => ?_⟩
  rw [WDRep.twist_ρ, eq_algebraMap_of_charpoly _ (a.semisimple _) _ _ (hc t),
    Algebra.algebraMap_eq_smul_one, smul_smul, MonoidHom.inv_apply, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, one_smul]

theorem iso_tensor {n : ℕ} (a : WDRep h (Fin n → ℂ)) (ψ : Weil h →* ℂˣ) (hψ : IsSmooth ψ) (hN : a.N = 0) :
    ((a.twist ψ⁻¹ (isSmooth_inv hψ)).tensor
      (WDRep.ofChars h (ι := Fin 1) (fun _ => ψ) fun _ => hψ)).Iso a := by
  refine ⟨(TensorProduct.congr (LinearEquiv.refl ℂ (Fin n → ℂ)) (LinearEquiv.funUnique (Fin 1) ℂ ℂ)).trans
    (TensorProduct.rid ℂ (Fin n → ℂ)), fun σ x => ?_, fun x => ?_⟩
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp only [WDRep.tensor_ρ, TensorProduct.map_tmul, WDRep.twist_ρ, WDRep.ofChars_ρ,
        LinearEquiv.trans_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply, TensorProduct.rid_tmul,
        LinearEquiv.funUnique_apply, Function.eval, diagEnd_apply, LinearMap.smul_apply, map_smul, smul_smul,
        MonoidHom.inv_apply]
      congr 1
      rw [mul_comm, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · simp [WDRep.twist, hN]

end UpperTheory.TNZ.ScalarInertia

namespace UpperTheory.TNZ

open ScalarInertia in
theorem step_scalarInertia : ScalarOnInertiaProp := by
  intro E Ω _ _ _ _ _ A w h v ψ hψ hv hc
  obtain ⟨n, a, rfl⟩ := WD.exists_rep v
  rw [WD.monodromyZero_ofWeilDeligneRepClass_iff] at hv
  simp only [WD.charPol_mk, WD.lpDim_mk] at hc
  refine ⟨WD.mk (a.twist ψ⁻¹ (isSmooth_inv hψ)), (WD.unr_mk _).mpr (unr_twist a ψ hψ hv _ hc), by simp, ?_⟩
  rw [WD.lpOfChar, WD.lpChar_mk]
  exact WD.sound (iso_tensor a ψ hψ hv).symm

end UpperTheory.TNZ
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.SphericalUnramified
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.TNZ

namespace SphericalUnramified

theorem isSpherical_of_equiv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {d : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin d) k) V} {π : Representation ℂ (GL (Fin d) k) W} (e : ρ.Equiv π)
    (h : IsSpherical ρ) : IsSpherical π := by
  unfold IsSpherical IsSphericalFor at *
  obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨e x, ?_, ?_⟩
  · intro g
    have hg := hx g
    have hint : e (ρ (g : GL (Fin d) k) x) = π (g : GL (Fin d) k) (e x) :=
      LinearMap.congr_fun (e.isIntertwining' (g : GL (Fin d) k)) x
    rw [← hint, hg, map_smul]
  · intro h1
    apply h0
    have : e x = e 0 := by rw [h1, map_zero]
    exact EquivLike.injective e this

end SphericalUnramified

theorem step_sphUnr : SphericalUnramifiedProp := by
  intro E Ω _ _ _ _ _ A w h a ha ε rc hL d X _ _ σ hs hi hsph
  exact (hL.sph (IrrGL.of σ hs hi)).1 (SphericalUnramified.isSpherical_of_equiv (IrrGL.equivOf σ hs hi) hsph)

end UpperTheory.TNZ
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.StepV0Stable
section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

namespace Grp

namespace P_V0stable

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem alg_inj : Function.Injective (algebraMap 𝒪[k] k) := Subtype.val_injective

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem coe_map_apply {n : ℕ} (A : GL (Fin n) 𝒪[k]) (i j : Fin n) :
    ((Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k) A : GL (Fin n) k) :
      Matrix (Fin n) (Fin n) k) i j = algebraMap 𝒪[k] k ((A : Matrix (Fin n) (Fin n) 𝒪[k]) i j) := rfl

theorem conj_mem_KC {n r : ℕ} (g u : GL (Fin n) k) (hg : g ∈ KO k (Fin n)) (hu : u ∈ KC k n r) :
    g⁻¹ * u * g ∈ KC k n r := by
  obtain ⟨A, rfl⟩ := hg
  obtain ⟨⟨B, rfl⟩, hB⟩ := hu
  have hB' : ∀ i j, (B : Matrix (Fin n) (Fin n) 𝒪[k]) i j - (1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j ∈ 𝓂[k] ^ r := by
    intro i j
    obtain ⟨y, hy, hyx⟩ := hB i j
    have hyeq : y = (B : Matrix (Fin n) (Fin n) 𝒪[k]) i j - (1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j := by
      apply alg_inj
      rw [hyx, coe_map_apply, map_sub, Matrix.one_apply]
      split_ifs <;> simp
    exact hyeq ▸ hy
  have key : ∀ i j, ((A⁻¹ * B * A : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) i j
      - (1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j ∈ 𝓂[k] ^ r := by
    intro i j
    have h : ((A⁻¹ * B * A : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) - 1
        = ((A⁻¹ : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k])
          * ((B : Matrix (Fin n) (Fin n) 𝒪[k]) - 1) * (A : Matrix (Fin n) (Fin n) 𝒪[k]) := by
      rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, Units.inv_mul]
    rw [← Matrix.sub_apply, h, Matrix.mul_apply]
    refine Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ ?_
    rw [Matrix.mul_apply]
    refine Ideal.sum_mem _ fun m _ => Ideal.mul_mem_left _ _ ?_
    rw [Matrix.sub_apply]
    exact hB' m l
  rw [← map_inv, ← map_mul, ← map_mul]
  refine ⟨⟨_, rfl⟩, fun i j => ⟨_, key i j, ?_⟩⟩
  rw [coe_map_apply, map_sub, Matrix.one_apply]
  split_ifs <;> simp

end P_V0stable

theorem step_V0stable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (G : Grp k n) : FixedSubspaceStableProp G := by
  intro _ _ g φ hφ
  obtain ⟨h1, h2⟩ : (∀ p : ↥(KO k (Fin n)), (p : GL (Fin n) k) ∈ G.PO → ∀ x, φ (p * x) = G.lam p * φ x) ∧
      ∀ x (u : ↥(KO k (Fin n))), (u : GL (Fin n) k) ∈ KC k n G.lev → φ (x * u) = φ x := hφ
  show (∀ p : ↥(KO k (Fin n)), (p : GL (Fin n) k) ∈ G.PO →
      ∀ x, Rreg (k := k) (n := n) g φ (p * x) = G.lam p * Rreg (k := k) (n := n) g φ x) ∧
    ∀ x (u : ↥(KO k (Fin n))), (u : GL (Fin n) k) ∈ KC k n G.lev →
      Rreg (k := k) (n := n) g φ (x * u) = Rreg (k := k) (n := n) g φ x
  refine ⟨fun p hp x => ?_, fun x u hu => ?_⟩
  · show φ (p * x * g) = G.lam p * φ (x * g)
    rw [mul_assoc]
    exact h1 p hp (x * g)
  · show φ (x * u * g) = φ (x * g)
    have hc : ((g⁻¹ * u * g : ↥(KO k (Fin n))) : GL (Fin n) k) ∈ KC k n G.lev := by
      change ((g : GL (Fin n) k))⁻¹ * (u : GL (Fin n) k) * (g : GL (Fin n) k) ∈ KC k n G.lev
      exact P_V0stable.conj_mem_KC _ _ g.2 hu
    have e : x * u * g = x * g * (g⁻¹ * u * g) := by group
    rw [e]
    exact h2 _ _ hc

end Grp

end UpperTheory.TNZ
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.UnramifiedTwist
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

namespace UpperTheory.TNZ

namespace UnramifiedTwist

theorem charpoly_smul_one {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (c : ℂ) :
    (c • (1 : Module.End ℂ V)).charpoly = (X - C c) ^ Module.finrank ℂ V := by
  have h1 := LinearMap.charpoly_sub_smul (c • (1 : Module.End ℂ V)) c
  rw [sub_self, LinearMap.charpoly_zero] at h1
  calc (c • (1 : Module.End ℂ V)).charpoly
      = ((c • (1 : Module.End ℂ V)).charpoly.comp (X + C c)).comp (X - C c) := by
        rw [Polynomial.comp_assoc]; simp
    _ = (X - C c) ^ Module.finrank ℂ V := by rw [← h1, Polynomial.X_pow_comp]

theorem diagEnd_const (c : ℂ) :
    diagEnd (fun _ : Fin 1 => c) = c • (1 : Module.End ℂ (Fin 1 → ℂ)) :=
  LinearMap.ext fun v => funext fun i => by simp

end UnramifiedTwist

open UnramifiedTwist in
theorem step_unrTwist : UnramifiedTwistProp := by
  intro E Ω _ _ _ _ _ A w h u ψ hψ hu
  obtain ⟨n, a, rfl⟩ := WD.exists_rep u
  rw [WD.unr_mk] at hu
  obtain ⟨hN, hI⟩ := hu
  simp only [WD.lpOfChar, WD.lpChar_mk, WD.monodromyZero_ofWeilDeligneRepClass_iff, WD.charPol_mk, WD.lpDim_mk]
  refine ⟨?_, fun t => ?_⟩
  · rw [WDRep.tensor_N, hN, WDRep.ofChars_N]
    simp
  · rw [WDRep.tensor_ρ, hI t, WDRep.ofChars_ρ, diagEnd_const, TensorProduct.map_smul_right,
      TensorProduct.map_one, charpoly_smul_one, Module.finrank_tensorProduct]
    simp

end UpperTheory.TNZ
end
end

