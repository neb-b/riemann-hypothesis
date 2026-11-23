module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairOfLiftAlt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0708

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.ContraIrr
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.TP.Loc.contraIrr :
    UpperTheory.Gal.TP.Loc.ContraIrr := by
  intro k _ _ _ _ n V _ _ ρ hs hi
  have hadm := (GlobalTheory.Laid.bzfin_holds k).1 (Fin n) V ρ hs hi
  have hG := GlobalTheory.SqIntUnit.compactOpen_basis k n
  exact ⟨GlobalTheory.ContraRefl.contra_isIrreducible hG hadm hi, ⟨GlobalTheory.ContraRefl.evEquiv hG hadm⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.ContraUnit
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc

theorem UpperTheory.Gal.TP.Loc.contraUnit :
    UpperTheory.Gal.TP.Loc.ContraIrr → UpperTheory.Gal.TP.Loc.ContraUnit := by
  intro hci k _ _ _ _ n V _ _ ρ hsm hirr hu
  obtain ⟨B, hherm, hpos, hinv⟩ := hu
  have hnd : ∀ w : V, (∀ v : V, B v w = 0) → w = 0 := by
    intro w hw
    by_contra hne
    have h1 := hpos w hne
    rw [hw w] at h1
    simp at h1
  obtain ⟨w0, hw0⟩ : ∃ w : V, w ≠ 0 := by
    by_contra hne
    push_neg at hne
    haveI : IsSimpleOrder (Subrepresentation ρ) := hirr
    apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
    generalize (⊥ : Subrepresentation ρ) = a
    generalize (⊤ : Subrepresentation ρ) = b
    obtain ⟨A, hA⟩ := a
    obtain ⟨A', hA'⟩ := b
    congr 1
    ext x
    rw [hne x]
    simp only [Submodule.zero_mem]
  have hcirr : (contra ρ).IsIrreducible := (hci k n V ρ hsm hirr).1
  let S : V →ₗ⋆[ℂ] smoothPart ρ.dual :=
    LinearMap.codRestrict (smoothPart ρ.dual) B.flip fun w =>
      mem_smoothPart_of_nhds (Filter.mem_of_superset ((hsm w).mem_nhds (by simp)) fun g hg => by
        have hg' : ρ g w = w := hg
        ext a
        show B (ρ g⁻¹ a) w = B a w
        have h := hinv g (ρ g⁻¹ a) w
        rw [hg'] at h
        rw [← h, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply])
  have hSapply (w a : V) : ((S w : smoothPart ρ.dual) : Module.Dual ℂ V) a = B a w := rfl
  have hcomm (g : GL (Fin n) k) (w : V) : S (ρ g w) = contra ρ g (S w) := by
    refine Subtype.ext (LinearMap.ext fun a => ?_)
    rw [contra_apply, hSapply, hSapply]
    have h := hinv g (ρ g⁻¹ a) w
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
    exact h
  have hbij : Function.Bijective S := by
    have hi : Function.Injective S := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro w hw
      refine hnd w fun v => ?_
      have h := congrArg (fun l : smoothPart ρ.dual => (l : Module.Dual ℂ V) v) hw
      simpa [hSapply] using h
    refine ⟨hi, ?_⟩
    let R : Subrepresentation (contra ρ) :=
      { toSubmodule := LinearMap.range S
        apply_mem_toSubmodule := fun g l hl => by
          obtain ⟨w, rfl⟩ := hl
          exact ⟨ρ g w, hcomm g w⟩ }
    rcases hcirr.eq_bot_or_eq_top R with hR | hR
    · exfalso
      have h : S w0 ∈ R.toSubmodule := ⟨w0, rfl⟩
      rw [hR] at h
      exact hw0 (hi (by rw [(Submodule.mem_bot ℂ).1 h, map_zero]))
    · intro l
      have h : l ∈ R.toSubmodule := by rw [hR]; exact Submodule.mem_top
      obtain ⟨w, hw⟩ := h
      exact ⟨w, hw⟩
  let e := LinearEquiv.ofBijective S hbij
  let T : ↥(GlobalTheory.PRep.smoothPart ρ.dual) →ₗ⋆[ℂ] V := e.symm.toLinearMap
  have hST : ∀ f, S (T f) = f := fun f => e.apply_symm_apply f
  have hTS : ∀ w, T (S w) = w := fun w => e.symm_apply_apply w
  have hTg : ∀ g f, T (contra ρ g f) = ρ g (T f) := by
    intro g f
    rw [← hST f, ← hcomm, hTS, hTS]
  refine ⟨⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun f f' => B (T f') (T f))
    ?_ ?_ ?_ ?_, ?_, ?_, ?_⟩, ⟨e, fun g x => hcomm g x⟩⟩
  · intro f₁ f₂ f'
    simp [map_add (f := _)]
  · intro c f f'
    simp [LinearMap.map_smulₛₗ]
  · intro f f₁ f₂
    simp [map_add (f := _)]
  · intro c f f'
    simp [LinearMap.map_smulₛₗ]
  · intro f f'
    simp only [LinearMap.mk₂'ₛₗ_apply]
    exact hherm (T f') (T f)
  · intro f hf
    simp only [LinearMap.mk₂'ₛₗ_apply]
    exact hpos _ (fun h => hf (by rw [← hST f, h, map_zero]))
  · intro g f f'
    simp only [LinearMap.mk₂'ₛₗ_apply]
    rw [hTg, hTg]
    exact hinv g _ _
end

