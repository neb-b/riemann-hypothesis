module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.IsotypQuot

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp

theorem UpperTheory.ConvolutionTheory.R2.Pp.isotyp :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], UpperTheory.ConvolutionTheory.R2.Pp.Isotyp F := by
  intro F _ _ _ π v σ h x
  have h1 : (⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g u, f (σ.ρ g u) = π.locRep v g (f u)}, LinearMap.range f.1) = ⊤ := by
    have cpt_fin (k : TR.Kinf F 2) (g : GL (Fin 2) (Af F)) (y : π.V) :
        π.op (.cpt k) (π.finPart g y) = π.finPart g (π.op (.cpt k) y) := by
      refine Subtype.ext ?_
      change (TR.rt F 2 (TR.infGL F 2 (Unitary.toUnits k)) * TR.rt F 2 (GlobalTheory.CuspRep.finGL F 2 g)) y.1 =
        (TR.rt F 2 (GlobalTheory.CuspRep.finGL F 2 g) * TR.rt F 2 (TR.infGL F 2 (Unitary.toUnits k))) y.1
      rw [← map_mul, ← map_mul, TR.infGL_comm]
    have fin_loc {k : GL (Fin 2) (Af F)}
        (hk : GeneralLinearGroup.map (GlobalTheory.CuspRep.pLoc F v) k = 1)
        (g : GL (Fin 2) (v.adicCompletion F)) (y : π.V) :
        π.finPart k (π.locRep v g y) = π.locRep v g (π.finPart k y) := by
      simp only [TR.CuspSub.locRep, MonoidHom.comp_apply]
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, GlobalTheory.CuspRep.LocUniq.comm_locGL v hk]
    let W : Submodule ℂ π.V := ⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g u, f (σ.ρ g u) = π.locRep v g (f u)}, LinearMap.range f.1
    have hact : ∀ g, ∀ x ∈ W, π.locRep v g x ∈ W := by
      intro g x hx
      refine Submodule.mem_comap.1 ((iSup_le (a := Submodule.comap (π.locRep v g) _) fun f => ?_) hx)
      rintro _ ⟨u, rfl⟩
      exact Submodule.mem_iSup_of_mem f ⟨σ.ρ g u, f.2 g u⟩
    have hcomm : ∀ T : Module.End ℂ π.V, (∀ g x, T (π.locRep v g x) = π.locRep v g (T x)) → ∀ x ∈ W, T x ∈ W := by
      intro T hT x hx
      refine Submodule.mem_comap.1 ((iSup_le (a := Submodule.comap T _) fun f => ?_) hx)
      rintro _ ⟨u, rfl⟩
      exact Submodule.mem_iSup_of_mem ⟨T ∘ₗ f.1, fun g u => by
        rw [LinearMap.comp_apply, f.2]; exact hT g _⟩ ⟨u, rfl⟩
    have hop : ∀ o, ∀ x ∈ W, π.op o x ∈ W := fun o x hx => by
      cases o with
      | fin k =>
        have h3 := hact (GeneralLinearGroup.map (GlobalTheory.CuspRep.pLoc F v) k) _ (hcomm
          (π.finPart ((GlobalTheory.CuspRep.locGL F 2 v (GeneralLinearGroup.map (GlobalTheory.CuspRep.pLoc F v) k))⁻¹ * k))
          (fin_loc (GlobalTheory.CuspRep.LocEx.map_pLoc_inv_mul v k)) x hx)
        rwa [TR.CuspSub.locRep, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at h3
      | cpt k => exact hcomm _ (fun g y => cpt_fin k _ y) x hx
      | lie X => exact hcomm _ (fun g y => Subtype.ext (LinearMap.congr_fun (TR.lie_rt_fin X (GlobalTheory.CuspRep.locGL F 2 v g)) y.1)) x hx
    have hi := Submodule.map_injective_of_injective π.V.injective_subtype
    rcases π.irred (W.map π.V.subtype) (Submodule.map_subtype_le _ _) (by
      rintro o _ ⟨y, hy, rfl⟩
      exact ⟨_, hop o y hy, rfl⟩) with hb | ht
    · have e : W = ⊥ := hi (hb.trans (Submodule.map_bot _).symm)
      obtain ⟨f, h0, hf⟩ := h
      exact False.elim (h0 (LinearMap.range_eq_bot.1 ((iSup_eq_bot.1 e) ⟨f, hf⟩)))
    · exact hi (ht.trans (Submodule.map_subtype_top _).symm)
  refine (show (⊤ : Submodule ℂ π.V) ≤ _ from h1 ▸ iSup_le fun f => ?_) Submodule.mem_top
  exact fun y hy => Submodule.subset_span ⟨f.1, f.2, hy⟩
