module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.AutomorphicFormsLeSm
public import GroundTheory.AutomorphicForms.TensorProductTheorem.CuspidalRep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0623
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HasFixedVector

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FoundBridge
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace UpperTheory.V.Fb

attribute [local instance 100] LieRing.ofAssociativeRing

variable (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (a : ℕ)

def ofCusp : cuspForms E a →ₗ[ℂ] TR.Sm E a := Submodule.inclusion cuspForms_le_Sm

variable {E a}

theorem ofCusp_injective : Function.Injective (ofCusp E a) := Submodule.inclusion_injective _

theorem isCuspForm_ofCusp (ψ : cuspForms E a) : TR.IsCuspForm (ofCusp E a ψ) := (isCuspForm_iff _).2 ψ.2

theorem mem_range_ofCusp {φ : TR.Sm E a} : φ ∈ LinearMap.range (ofCusp E a) ↔ TR.IsCuspForm φ :=
  ⟨fun ⟨ψ, h⟩ => h ▸ isCuspForm_ofCusp ψ, fun h => ⟨⟨φ.1, (isCuspForm_iff φ).1 h⟩, rfl⟩⟩

theorem ofCusp_uAction (u : UEnv E a) (ψ : cuspForms E a) :
    ofCusp E a (uActionCusp E a u ψ) = uTR E a u (ofCusp E a ψ) := rfl

theorem ofCusp_ρ (X : TR.Lie E a) (ψ : cuspForms E a) :
    ofCusp E a ((gkModuleCusp E a).ρ (lieEq E a X) ψ) = TR.act (.lie X) (ofCusp E a ψ) := by
  rw [gkModuleCusp_ρ_apply, ofCusp_uAction, uTR_ι]
  rfl

theorem ofCusp_σ (k : TR.Kinf E a) (ψ : cuspForms E a) :
    ofCusp E a ((gkModuleCusp E a).σ (cptEq E a k) ψ) = TR.act (.cpt k) (ofCusp E a ψ) :=
  Subtype.ext (funext fun g => congrArg (fun x => ψ.1 (g * x)) (infEmb_cptEq k))

theorem ofCusp_τ (k : GL (Fin a) (Af E)) (ψ : cuspForms E a) :
    ofCusp E a (finRepCusp E a k ψ) = TR.act (.fin k) (ofCusp E a ψ) :=
  Subtype.ext (funext fun g => congrArg (fun f : GL (Fin a) (Af E) →* GA E a => ψ.1 (g * f k)) finEmb_eq)



omit [IsTotallyReal E] in
structure Stab (U : Submodule ℂ (cuspForms E a)) : Prop where
  ρ : ∀ X, ∀ φ ∈ U, (gkModuleCusp E a).ρ X φ ∈ U
  σ : ∀ k, ∀ φ ∈ U, (gkModuleCusp E a).σ k φ ∈ U
  τ : ∀ g, ∀ φ ∈ U, finRepCusp E a g φ ∈ U

omit [IsTotallyReal E] in
theorem stab_central : Stab (centralCuspForms E a) :=
  ⟨fun X _ h => ρ_mem_centralCuspForms X h, fun k _ h => σ_mem_centralCuspForms k h,
    fun g _ h => finRepCusp_mem_centralCuspForms g h⟩

theorem Stab.map {U : Submodule ℂ (cuspForms E a)} (h : Stab U) : TR.IsStable (U.map (ofCusp E a)) := by
  rintro o _ ⟨ψ, hψ, rfl⟩
  cases o with
  | fin k => exact ⟨_, h.τ k ψ hψ, ofCusp_τ k ψ⟩
  | cpt k => exact ⟨_, h.σ _ ψ hψ, ofCusp_σ k ψ⟩
  | lie X => exact ⟨_, h.ρ _ ψ hψ, ofCusp_ρ X ψ⟩

theorem stab_comap {V : Submodule ℂ (TR.Sm E a)} (h : TR.IsStable V) : Stab (V.comap (ofCusp E a)) := by
  refine ⟨fun X ψ hψ => ?_, fun k ψ hψ => ?_, fun k ψ hψ => ?_⟩
  · obtain ⟨X, rfl⟩ := (lieEq E a).surjective X
    rw [Submodule.mem_comap, ofCusp_ρ]
    exact h _ _ hψ
  · obtain ⟨k, rfl⟩ := (cptEq E a).surjective k
    rw [Submodule.mem_comap, ofCusp_σ]
    exact h _ _ hψ
  · rw [Submodule.mem_comap, ofCusp_τ]
    exact h _ _ hψ


omit [IsTotallyReal E] in
theorem Stab.isIrreducible_iff {U : Submodule ℂ (cuspForms E a)} (h : Stab U) :
    (cuspSubmodule E a U h.ρ h.σ h.τ).IsIrreducible ↔ U ≠ ⊥ ∧ ∀ W ≤ U, Stab W → W = ⊥ ∨ W = U := by
  refine ⟨fun hi => ?_, fun hi => isIrreducible_cuspSubmodule_of U h.ρ h.σ h.τ hi.1
    fun W hW h1 h2 h3 => hi.2 W hW ⟨h1, h2, h3⟩⟩
  set M := cuspSubmodule E a U h.ρ h.σ h.τ
  have hs : IsSimpleOrder (Subrepresentation M.fullRep) := hi
  refine ⟨fun e => ?_, fun W hW hst => ?_⟩
  · have : Subsingleton U := by rw [e]; infer_instance
    exact bot_ne_top (α := Subrepresentation M.fullRep)
      (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  · have h1 : ∀ (w : FreeMonoid ((isExpLieAlgebra E a).lieSubalgebra ⊕ archCompact E a)) (y : U),
        y.1 ∈ W → (M.gk.rep w y).1 ∈ W := fun w => by
      induction w using FreeMonoid.inductionOn' with
      | one => intro y hy; rwa [map_one]
      | of_mul x w ih =>
        intro y hy
        rw [map_mul, Module.End.mul_apply]
        rcases x with X | k
        · exact hst.ρ X _ (ih y hy)
        · exact hst.σ k _ (ih y hy)
    let Y : Subrepresentation M.fullRep := ⟨W.comap U.subtype, fun p y hy => h1 p.1 _ (hst.τ p.2 _ hy)⟩
    have e : (W.comap U.subtype).map U.subtype = W := by
      rw [Submodule.map_comap_subtype, inf_eq_right.2 hW]
    rcases eq_bot_or_eq_top Y with h0 | h0
    · left
      rw [← e, show W.comap U.subtype = ⊥ from congrArg Subrepresentation.toSubmodule h0, Submodule.map_bot]
    · right
      rw [← e, show W.comap U.subtype = ⊤ from congrArg Subrepresentation.toSubmodule h0, Submodule.map_subtype_top]

def carrier (π : TR.CuspSub E a) : Submodule ℂ (cuspForms E a) := π.V.comap (ofCusp E a)

theorem mem_carrier {π : TR.CuspSub E a} {ψ : cuspForms E a} : ψ ∈ carrier π ↔ ofCusp E a ψ ∈ π.V := Iff.rfl

theorem map_carrier (π : TR.CuspSub E a) : (carrier π).map (ofCusp E a) = π.V :=
  Submodule.map_comap_eq_self fun φ h => mem_range_ofCusp.2 (π.cusp φ h)

theorem stab_carrier (π : TR.CuspSub E a) : Stab (carrier π) := stab_comap π.stable

def ofIrr (U : Submodule ℂ (cuspForms E a)) (h : Stab U) (hi : (cuspSubmodule E a U h.ρ h.σ h.τ).IsIrreducible) :
    TR.CuspSub E a where
  V := U.map (ofCusp E a)
  cusp := by rintro _ ⟨ψ, -, rfl⟩; exact isCuspForm_ofCusp ψ
  stable := h.map
  ne_bot e := (h.isIrreducible_iff.1 hi).1
    (Submodule.map_injective_of_injective ofCusp_injective (e.trans (Submodule.map_bot _).symm))
  irred W hW hst := by
    have e : (W.comap (ofCusp E a)).map (ofCusp E a) = W :=
      Submodule.map_comap_eq_self (hW.trans LinearMap.map_le_range)
    refine ((h.isIrreducible_iff.1 hi).2 _ ((Submodule.comap_mono hW).trans
      (Submodule.comap_map_eq_of_injective ofCusp_injective U).le) (stab_comap hst)).imp (fun e' => ?_) fun e' => ?_
    · rw [← e, e', Submodule.map_bot]
    · rw [← e, e']

theorem carrier_ofIrr (U : Submodule ℂ (cuspForms E a)) (h : Stab U) (hi) : carrier (ofIrr U h hi) = U :=
  Submodule.comap_map_eq_of_injective ofCusp_injective U

theorem centralZ_eq :
    UnitaryAdmissible.centralZ E a = UnitaryAdmissible.centralExp E a • lieEq E a (TR.oneL E a) :=
  Subtype.ext (by rw [UnitaryAdmissible.coe_centralZ, Algebra.algebraMap_eq_smul_one, ← lieEq_oneL]; rfl)

theorem mem_centralCuspForms_of {ψ : cuspForms E a} (h : TR.lie E a (TR.oneL E a) (ofCusp E a ψ) = 0) :
    ψ ∈ centralCuspForms E a := fun s x => by
  have h1 : (gkModuleCusp E a).ρ (lieEq E a (TR.oneL E a)) ψ = 0 :=
    ofCusp_injective ((ofCusp_ρ _ _).trans (h.trans (map_zero _).symm))
  have h2 : lieActionCusp E a (UnitaryAdmissible.centralZ E a) ψ = (0 : ℂ) • ψ := by
    rw [centralZ_eq, map_smul, zero_smul, LinearMap.smul_apply]
    exact (congrArg _ h1).trans (smul_zero _)
  rw [Reduction.centralSection_mul_comm, UnitaryAdmissible.apply_mul_centralSection h2 x s]
  simp

theorem carrier_le_central (π : TR.CuspSub E a) (h : ∀ φ ∈ π.V, TR.lie E a (TR.oneL E a) φ = 0) :
    carrier π ≤ centralCuspForms E a := fun _ hψ => mem_centralCuspForms_of (h _ hψ)

end UpperTheory.V.Fb
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HasSatOfFixed
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG

namespace UpperTheory.V.Af

variable {F : Type} [Field F] [NumberField F]

private theorem sLoc_mem (w : HeightOneSpectrum (𝓞 F)) (x : Ov F w) : sLoc F w x ∈ Ohat F := by
  classical
  refine Subring.mem_iInf.2 fun v => ?_
  change (Pi.single w (x : w.adicCompletion F) : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F) v ∈
    v.adicCompletionIntegers F
  by_cases h : v = w
  · subst h
    rw [Pi.single_eq_same]
    exact x.2
  · rw [Pi.single_eq_of_ne h]
    exact zero_mem _

private def sInt (w : HeightOneSpectrum (𝓞 F)) : Ov F w →ₙ+* Ohat F where
  toFun x := ⟨sLoc F w x, sLoc_mem w x⟩
  map_mul' x y := Subtype.ext (map_mul (sLoc F w) x.1 y.1)
  map_zero' := Subtype.ext (map_zero (sLoc F w))
  map_add' x y := Subtype.ext (map_add (sLoc F w) x.1 y.1)

theorem LocIsotypic.hasFixed {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin n) (Af F)) V} {w : HeightOneSpectrum (𝓞 F)}
    {σ : SmIrr (GL (Fin n) (w.adicCompletion F))} (h : LocIsotypic ρ w σ)
    {U : Subgroup (GL (Fin n) (w.adicCompletion F))} (hU : IsCompact (U : Set (GL (Fin n) (w.adicCompletion F))))
    (hf : HasFixed (ρ.comp (locGL F n w)) U) : HasFixed σ.ρ U :=
  _root_.UpperTheory.Reformulated.B.HasFixedVector.hasFixed h hU hf

end UpperTheory.V.Af
end
end

