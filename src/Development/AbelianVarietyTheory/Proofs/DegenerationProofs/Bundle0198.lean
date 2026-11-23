module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsExtendValuation
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSinglePolarisationGeneratorAllTraits
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemRangeIffOfFinite
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0197
public import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcFamilyPointWithFramesOfLaws
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex

theorem arcFam : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt →
    ThetaUnifAV → GlobalTheory.LN.ArcFamSt := by
  intro h₁ h₂ h₃ h₄ h₅ h₆ h₇ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a hb m hm hmu
  have pt := GlobalTheory.ArcPoint.exists_point h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D l Xo c W₀ Y O' b ϖ a hb
  have bad := GlobalTheory.Ex.Trait.hasArcData_at_trait h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D l Xo c W₀ Y O' b ϖ a hb
  have good := GlobalTheory.Ex.GoodTrait.range_subset_abLocus h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D l Xo c W₀ Y O' b ϖ a hb
  have fr₁ := _root_.GlobalTheory.Ex.OneGen.main h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D l Xo c W₀ Y O' b ϖ a hb
  have frm := GlobalTheory.OneBasis.exists_isFrame_pow_sq h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D l Xo c W₀ Y O' b ϖ a hb
  have mono := GlobalTheory.Ex.Mono.mono h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D l Xo c W₀ Y O' b ϖ a hb
  obtain ⟨R₁, _, _, g, y₁, gi, gf, n₁, hy, hr, ht⟩ := pt
  have td : GlobalTheory.LN.TraitData Y a g y₁ := ⟨hy, fun W _ _ _ hW φ gam hg χ hχ =>
    ⟨good R₁ g y₁ gi gf n₁ ht hy W hW φ gam hg χ hχ, bad R₁ g y₁ gi gf n₁ hr hy W hW φ gam hg χ hχ⟩⟩
  obtain ⟨R₂, _, _, h, h', hi, hf, n₂, hh, hθ⟩ := fr₁ R₁ g y₁ gi gf n₁ td ht
  obtain ⟨td₂, hr₂, -⟩ := mono R₁ g y₁ gi gf n₁ R₂ h h' hf hh
  have gi₂ : Function.Injective (h.comp g) := hi.comp gi
  have gf₂ : (h.comp g).Finite := hf.comp gf
  obtain ⟨R₃, _, _, k, k', ki, kf, n₃, kk, hfm⟩ :=
    frm R₂ (h.comp g) (spMap h' ≫ y₁) gi₂ gf₂ n₂ (td₂ td) (hr₂ hr) hθ m hm hmu
  obtain ⟨td₃, -, hfr⟩ := mono R₂ (h.comp g) (spMap h' ≫ y₁) gi₂ gf₂ n₂ R₃ k k' kf kk
  obtain ⟨θ, hθ⟩ := hθ
  obtain ⟨f', hf'⟩ := hfr 1 1 _ hθ
  refine ⟨R₃, inferInstance, inferInstance, k.comp (h.comp g), spMap k' ≫ spMap h' ≫ y₁, ki.comp gi₂, kf.comp gf₂, n₃,
    td₃ (td₂ td), ⟨f' 0, ?_⟩, hfm⟩
  have e : (fun _ : Fin 1 => f' 0) = f' := funext fun i => by rw [Subsingleton.elim i 0]
  rw [e]; exact hf'
end GlobalTheory.Ex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaDividedByConstantNonvanishingFibresStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaDividedByConstant_nonvanishing_fibres : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Big → S.Over₀ M U₀ → Q.Sec → Q.LocTheta → ∀ (W : M.Z.Opens) (x₀ : S.Gam), (∀ z ∈ W, x₀ ∈ S.supI M z) → ∃ σ ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => 1)) (Q.G.hom ⁻¹ᵁ W), GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w 1 (fun _ : Unit => ρ.th₁) (fun _ => (S.th x₀)⁻¹) _ σ ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ M.Z), Set.range x ⊆ W → ∃ (g : Sp K ⟶ Q.G.left) (j : _), g ≫ Q.G.hom = x ∧ valF g _ (σ j) ≠ 0 := by
  first | exact @GlobalTheory.ZH.ZHPre.exists_theta_div | exact GlobalTheory.ZH.ZHPre.exists_theta_div | (intros; apply GlobalTheory.ZH.ZHPre.exists_theta_div <;> assumption)
end

