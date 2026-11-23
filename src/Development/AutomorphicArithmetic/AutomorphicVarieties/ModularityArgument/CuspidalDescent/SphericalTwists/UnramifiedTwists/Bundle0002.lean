module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.ExtraV
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinGLMemOfPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0165

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.UnramifiedTwists.PrinTw
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.Zero.LLC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Desc.W

section Lc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private def prinTw {n : ℕ} (χ : Fin n → kˣ →* ℂˣ) {μ : kˣ →* ℂˣ} (hμ : IsSmoothChar μ) :
    (twist (prinSeries χ) (detChar (Fin n) μ)).Equiv (prinSeries fun i => χ i * μ) :=
  (GlobalTheory.LocGL.parIndTwistEquiv _ _ hμ).trans (GlobalTheory.LocGL.parIndEquiv _ (.mk (.refl ℂ _) fun g => by
    ext
    simp [torusChar_apply, det_leviEmb, map_prod, Finset.prod_mul_distrib]
    exact mul_comm _ _))

private theorem ps_tw {n : ℕ} (ω : Fin n → kˣ →* ℂˣ) {μ : kˣ →* ℂˣ} (hμ : IsSmoothChar μ) :
    Nonempty ((twist (Hi.PS ω) (detChar (Fin n) μ)).Equiv (Hi.PS fun i => ω i * μ)) := by
  have e : (fun i => ω i * μ * absPow k (((n : ℂ) - 1) / 2)) = fun i => ω i * absPow k (((n : ℂ) - 1) / 2) * μ :=
    funext fun i => mul_right_comm _ _ _
  show Nonempty ((twist (Hi.PS ω) (detChar (Fin n) μ)).Equiv (prinSeries fun i => ω i * μ * absPow k (((n : ℂ) - 1) / 2)))
  rw [e]
  exact ⟨prinTw _ hμ⟩

end Lc

end UpperTheory.V.Z.Desc.W

open UpperTheory.V.Z.Desc.W in
theorem UpperTheory.V.Z.Desc.W.ordTw :
    UpperTheory.V.Z.Desc.W.OrdTw := by
  intro K Ω _ _ _ _ _ _ l _ ι n art κ μ hart hμ hL w A h a ha τ τ' ω hh ψ ⟨e⟩ ho ⟨e'⟩
  have hs : IsSmoothChar (κ.loc w) := GlobalTheory.HeckeComp.smooth_loc κ w
  obtain ⟨E⟩ := ps_tw ω hs
  refine ⟨fun i => ω i * κ.loc w, ⟨(e'.trans (twistEquiv e _)).trans E⟩, fun i => ⟨(ho i).smooth.mul hs, ?_, ?_⟩⟩
  · exact (ho i).cont.mul (hμ.comp continuous_subtype_val)
  · intro s g hg _
    have v := (ho i).val s g hg trivial
    have m := hL.loc_away (Or.inr rfl) (a s) (g : G K Ω) (by rw [hg]; exact ha.glob art hart s)
    simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply, MonoidHom.mul_apply, Units.val_mul,
      Subgroup.coe_subtype, map_mul] at v ⊢
    rw [v, m]
    ring
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.UnramifiedTwists.TwAway
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem det_rank_one_rep {Γ k : Type} [Group Γ] [Field k] (μ : Γ →* kˣ) :
    Matrix.GeneralLinearGroup.det.comp (GlobalTheory.TripleGal.rk1 μ) = μ := by
  ext g
  simp [GlobalTheory.TripleGal.rk1, Matrix.det_unique]

private theorem tw_eq {Γ : Type} [Group Γ] {l : ℕ} [Fact l.Prime] {n : ℕ} (R : Γ →* GL (Fin n) (Qbar l)) (μ : Γ →* (Qbar l)ˣ) :
    Af.tw R μ = Formalism.MainNotions.SumRepresentations.At.twGL R (Matrix.GeneralLinearGroup.det.comp (GlobalTheory.TripleGal.rk1 μ)) := by
  rw [det_rank_one_rep]
  ext g i j
  simp [Formalism.MainNotions.SumRepresentations.At.twGL, Af.tw_val, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply]

private theorem continuous_rank_one_rep {Γ : Type} [Group Γ] [TopologicalSpace Γ] {l : ℕ} [Fact l.Prime] {μ : Γ →* (Qbar l)ˣ}
    (hμ : Continuous μ) :
    Continuous fun g => ((GlobalTheory.TripleGal.rk1 μ g : GL (Fin 1) (Qbar l)) : Matrix (Fin 1) (Fin 1) (Qbar l)) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i; fin_cases j
  have := Units.continuous_val.comp hμ
  simpa [GlobalTheory.TripleGal.rk1, Function.comp_def] using this
end

