module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.Bundle0003

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.GramUnitG
section
noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

def GramUnitG : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L) (r : ℕ) (T T' : F) (TT : M.R)
    (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z Zσ : M.Mat (r + 1)),
    GHyp M g T T' TT Zh Z Zσ →
    IsUnit (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
      (algebraMap F E T')).det

def StepDuF : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L) (hs : M.split = some g) (r : ℕ) (T T' : F) (TT : M.R)
    (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ Zσ₁ Zσ₂ : M.Mat (r + 1)),
    GHyp M g T T' TT Zh₁ Z₁ Zσ₁ → GHyp M g T T' TT Zh₂ Z₂ Zσ₂ → KapEq Zh₁ Zh₂ →
    ∀ γ : IsoMbe Z₁.Z Z₂.Z, ∃ γ' : IsoMbe Zσ₁.Z Zσ₂.Z,
      ∀ (θ₁ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (θ₂ : DD1 hs Zσ₁ TT ≃+ DD1 hs Zσ₂ TT),
        Ind hs γ θ₁ → Ind hs γ' θ₂ →
        ∀ l l₂ w w₂ : Fin (r + 1) → M.R, θ₁ (mk1 hs Z₁ TT l) = mk1 hs Z₂ TT l₂ →
          θ₂ (mk1 hs Zσ₁ TT w) = mk1 hs Zσ₂ TT w₂ →
          dotProduct (uV g l₂) (Matrix.mulVec (gHat g Zh₂ T T')⁻¹ (uV g w₂)) -
            dotProduct (uV g l) (Matrix.mulVec (gHat g Zh₁ T T')⁻¹ (uV g w)) ∈ 𝒪[F]

theorem stepDu_of (hU : GramUnitG) (h : StepDuF) : StepDu := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' TT Zh₁ Zh₂ Z₁ Z₂ Zσ₁ Zσ₂ h₁ h₂ hk γ
  obtain ⟨γ', hγ'⟩ := h F E M g hs r T T' TT Zh₁ Zh₂ Z₁ Z₂ Zσ₁ Zσ₂ h₁ h₂ hk γ
  exact ⟨γ', fun θ₁ θ₂ i₁ i₂ => isoB_of hs Zh₁ Zh₂ T T'
    (hU F E M g r T T' TT Zh₁ Z₁ Zσ₁ h₁) (hU F E M g r T T' TT Zh₂ Z₂ Zσ₂ h₂) θ₁ θ₂ (hγ' θ₁ θ₂ i₁ i₂)⟩

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.LiftRepMem
section
noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

theorem supp_inl (Y : Ix r → O) (h : ∀ a : Fin r, Y (Sum.inl a.castSucc) = 0) :
    (fun j => Y (Sum.inl j)) = Y (Sum.inl (Fin.last r)) • Pi.single (Fin.last r) 1 := by
  funext j
  induction j using Fin.lastCases with
  | last => simp
  | cast a => simp [h a, Pi.single_eq_of_ne (Fin.castSucc_lt_last a).ne]

theorem supp_inr (Y : Ix r → O) (h : ∀ a : Fin r, Y (Sum.inr a.castSucc) = 0) :
    (fun j => Y (Sum.inr j)) = Y (Sum.inr (Fin.last r)) • Pi.single (Fin.last r) 1 := by
  funext j
  induction j using Fin.lastCases with
  | last => simp
  | cast a => simp [h a, Pi.single_eq_of_ne (Fin.castSucc_lt_last a).ne]

theorem elim_eta (Y : Ix r → O) : Y = Sum.elim (fun j => Y (Sum.inl j)) (fun j => Y (Sum.inr j)) := by
  funext i
  cases i <;> rfl

theorem lift_e_mem {Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) O} (f : MbMod Z →ₗ[O] MbMod Z')
    (he : f (eCl Z) = eCl Z') (s : O) :
    liftOf O f (s • Pi.single (Fin.last r) 1) - s • Pi.single (Fin.last r) 1 ∈ headCols Z' := by
  rw [← Submodule.Quotient.eq, liftOf_spec, Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul, map_smul]
  exact congrArg (s • ·) he

theorem lift_rep_mem {Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) O} (f : MbMod Z ≃ₗ[O] MbMod Z')
    (y : Fin (r + 1) → O) (y₂ : Fin (r + 1) → O)
    (hy : (Submodule.Quotient.mk y : MbMod Z) = f.symm (Submodule.Quotient.mk y₂)) :
    liftOf O f.toLinearMap y - y₂ ∈ headCols Z' := by
  rw [← Submodule.Quotient.eq, liftOf_spec, hy, LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
end
end

