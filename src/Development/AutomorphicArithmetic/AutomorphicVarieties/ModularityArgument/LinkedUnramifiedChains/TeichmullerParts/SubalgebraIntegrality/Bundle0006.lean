module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2Sph
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConj
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.AtSame
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.J.D

private theorem ev_of_gen {M : Type} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) (μ a : ℂ) (F : M) (hF : F ≠ 0)
    (h : F ∈ T.maxGenEigenspace μ) (ha : T F = a • F) : a = μ := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace T μ F).1 h
  have h1 : ∀ j : ℕ, ((T - μ • 1) ^ j) F = (a - μ) ^ j • F := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, ha]
      simp only [LinearMap.smul_apply, Module.End.one_apply]
      rw [← sub_smul, smul_smul, pow_succ]
  rw [h1 k] at hk
  have h2 := (smul_eq_zero.1 hk).resolve_right hF
  by_contra hne
  exact pow_ne_zero k (sub_ne_zero.2 hne) h2

private theorem sat_eq (n q : ℕ) (hq : q ≠ 0) (B B' : Multiset ℂˣ) (a a' : ℕ → ℂ) (haa : ∀ j ≤ n, a j = a' j)
    (h : ((UpperTheory.V.Af.algSat n q B).map fun b => X - C b).prod = heckePol n q a)
    (h' : ((UpperTheory.V.Af.algSat n q B').map fun b => X - C b).prod = heckePol n q a') : B = B' := by
  have hp : heckePol n q a = heckePol n q a' := by
    rw [UpperTheory.V.Hi.heckePol, UpperTheory.V.Hi.heckePol]
    exact Finset.sum_congr rfl fun j hj => by rw [haa j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]
  have hr : UpperTheory.V.Af.algSat n q B = UpperTheory.V.Af.algSat n q B' := by
    rw [← Polynomial.roots_multiset_prod_X_sub_C (UpperTheory.V.Af.algSat n q B), h, hp, ← h',
      Polynomial.roots_multiset_prod_X_sub_C]
  have hc : ((((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ)) ≠ 0 := by
    have : (0 : ℝ) < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq
    exact_mod_cast (Real.rpow_pos_of_pos this _).ne'
  unfold UpperTheory.V.Af.algSat at hr
  simp only [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map] at hr
  exact Multiset.map_injective (fun x y hxy => Units.ext (mul_left_cancel₀ hc hxy)) hr

private theorem mem_gen {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {c : Coef l} (H : HSet L Ω l n c) {A : Type} [CommRing A] [Algebra c.O A] (θ : H.X.I.T →* Aˣ) (ι : Qbar l ≃+* ℂ)
    (x : A →+* Qbar l) (lam : Wt L l n) {d : ℕ} (ξ : GV n H.Sl →* GL (Fin d) ℂ) (K : H.Lev) (b : ℕ) (ev : H.Op → ℂ) (i : H.Op)
    (F : Fin H.m → H.X.Fn ℂ d) (hF : F ∈ zPart H θ ι x lam ξ K b ev) : F ∈ (H.opC ι lam d i).maxGenEigenspace (ev i) :=
  (Submodule.mem_iInf _).1 hF.2 i

private theorem vals (hN : GlobalTheory.Mem.LiteralAutomorphy.LitN) {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ) (hn : 1 ≤ n) (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ) (hξ : IsBasis ι e ξ) (Z : Submodule ℂ (Fin m → (hset Q τ₀).X.Fn ℂ d))
    (ev : (hset Q τ₀).Op → ℂ) (hZ : ∀ i, ∀ F ∈ Z, F ∈ ((hset Q τ₀).opC ι lam d i).maxGenEigenspace (ev i))
    (σ : Submodule ℂ (UA L n → ℂ)) (hσ : IsAutRepU σ) (hY : YOf Q ι τ₀ e ξ σ ⊓ Z ≠ ⊥)
    (w : (hset Q τ₀).Wp) (τ : SmIrr (GLw n w.1)) (hτ : Cp σ w.1 τ) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w.1 τ.ρ B) :
    ∃ a : ℕ → ℂ, a 0 = 1 ∧ (∀ j : Fin n, a (j + 1) = ev (.inl (w, j))) ∧
      ((UpperTheory.V.Af.algSat n (normV w.1) B).map fun b => X - C b).prod = heckePol n (normV w.1) a := by
  obtain ⟨-, a, ha0, ha, hp⟩ := satT L n w.1 τ B hB
  refine ⟨a, ha0, fun j => ?_, hp⟩
  obtain ⟨F, hF, hF0⟩ := (Submodule.ne_bot_iff _).1 hY
  have hAx : (hset Q τ₀).Ax := axU hN l L Ω s n hn V Q c m τ₀
  have h1 := partUR2Sph l L Ω s n hn V Q c ι m τ₀ lam d e ξ hξ σ hσ hAx w.1 w.2.1 w.2.2 τ hτ (j + 1) _ (ha (j + 1)) F hF.1
  exact ev_of_gen _ _ _ F hF0 (hZ (.inl (w, j)) F hF.2) h1

end UpperTheory.V.Z.J.D
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.SphSame
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.J.D

private theorem lat {α : Type*} [Lattice α] {Y B f z E : α} (h1 : Y ≤ B) (h2 : Y ≤ f) (h3 : Y ≤ E) :
    Y ⊓ (B ⊓ f ⊓ z ⊓ E) = Y ⊓ z :=
  le_antisymm (le_inf inf_le_left (inf_le_right.trans (inf_le_left.trans inf_le_right)))
    (le_inf inf_le_left (le_inf (le_inf (le_inf (inf_le_left.trans h1) (inf_le_left.trans h2)) inf_le_right)
      (inf_le_left.trans h3)))

private theorem eig_eq {M : Type*} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) {a b : ℂ} {F : M} (h0 : F ≠ 0)
    (hT : T F = a • F) (hF : F ∈ T.maxGenEigenspace b) : a = b := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace T b F).1 hF
  have h1 : (T - b • (1 : Module.End ℂ M)) F = (a - b) • F := by
    simp [hT, sub_smul]
  have h : ∀ i : ℕ, ((T - b • (1 : Module.End ℂ M)) ^ i) F = (a - b) ^ i • F := fun i => by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, Module.End.mul_apply, h1, map_smul, ih, smul_smul, pow_succ']
  rw [h k] at hk
  by_contra hne
  exact smul_ne_zero (pow_ne_zero k (sub_ne_zero.2 hne)) h0 hk

private theorem eig_mem {M : Type*} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) {b : ℂ} {F : M}
    (hT : T F = b • F) : F ∈ T.maxGenEigenspace b :=
  (Module.End.mem_maxGenEigenspace T b F).2 ⟨1, by simp [hT]⟩

private theorem eig_le {M I : Type*} [AddCommGroup M] [Module ℂ M] (T : I → Module.End ℂ M) (ev : I → ℂ) (i : I) (a : ℂ)
    (O Y Y' : Submodule ℂ M) (hne : Y ⊓ (O ⊓ ⨅ i, (T i).maxGenEigenspace (ev i)) ≠ ⊥)
    (h1 : ∀ F ∈ Y, T i F = a • F) (h2 : ∀ F ∈ Y', T i F = a • F) : Y' ≤ (T i).maxGenEigenspace (ev i) := by
  obtain ⟨F, hF, hF0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hFe : F ∈ (T i).maxGenEigenspace (ev i) :=
    (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 (Submodule.mem_inf.1 hF).2).2 i
  have hae : a = ev i := eig_eq _ hF0 (h1 F (Submodule.mem_inf.1 hF).1) hFe
  intro F' hF'
  exact eig_mem _ (hae ▸ h2 F' hF')

private theorem scalar (L : Type) [Field L] [NumberField L] (n : ℕ) (w : Plc L) (τ : SmIrr (GLw n w)) (j : ℕ) :
    ∃ a : ℂ, ∀ v ∈ fixd τ.ρ (KO (w.adicCompletion L) (Fin n)), sphOp τ.ρ j v = a • v := by
  by_cases h : GlobalTheory.LGrp.IsSpherical τ.ρ (GlobalTheory.LFun.KGL w (n := n))
  · obtain ⟨B, hB⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible τ.smooth τ.irred h
    obtain ⟨-, a, -, ha, -⟩ := UpperTheory.V.Hi.satT L n w τ B hB
    exact ⟨a j, ha j⟩
  · refine ⟨0, fun v hv => ?_⟩
    have hv0 : v = 0 := by
      by_contra h0
      rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n] at hv
      exact h ((Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 hv, h0⟩)
    simp [hv0]

end UpperTheory.V.Z.J.D
end
end

