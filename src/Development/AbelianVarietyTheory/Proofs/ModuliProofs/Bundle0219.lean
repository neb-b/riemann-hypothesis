module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBigThetaSysWithAction
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0196
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0082
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.HeckeInFamilies
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0206
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModelTripleAmpleFramesComponent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory

theorem exists_zon_ampFrames_component :
    Out.Laws → Out.Laws2 → GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ThmUSt → GlobalTheory.ZH.UTorsSt → GlobalTheory.ZH.ZHGeoSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g n : ℕ), n.Prime → Odd n → ∃ k j₀ : ℕ, ∀ j ≥ j₀, ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (R : Subalgebra o Ω) (J : Type) (b : TBase o ((n ^ j) ^ 2)) (u : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap o R))) (t₀ : SAB H (Sp R)) (e : t₀.G ≅ u.A) (v : GlobalTheory.ZM.Ix g ((n ^ j) ^ 2) → R), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ c ∈ R, x = a / c) → IsMonHom e.hom → LBIso t₀.PP.L (u.L.pull e.hom.left) → u.HasTh (𝟙 _) v → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i i', x = (v i : Ω) / (v i' : Ω)})) Ω → ∃ C : ZOn (spMap (algebraMap o R)) t₀ (n ^ k), IsIntegral C.Z ∧ C.amp.s = 1 ∧ ∀ r : ℤ, C.amp.r ≤ r → ∃ A : GlobalTheory.LN.AmpFrames C.t.G C.t.PP.L ((n ^ k) ^ 2), A.r = r ∧ A.s = 1 := by
  intro h1 h2 hss hU hT hG E _ _ _ H g n hn ho
  obtain ⟨k, j₀, hk⟩ := GlobalTheory.exists_big_thetaSys_with_action h1 h2 E H g n hn ho
  refine ⟨k, j₀, ?_⟩
  intro j hj o Ω _ _ _ _ R J b u t₀ e v hR hfr he hL hth hfin
  obtain ⟨S, ρ, h, φ, act, hbig, hN, hfin', hcart, hLφ, hact, hadj, hprim⟩ :=
    hk j hj o Ω R J b u t₀ e v hR hfr he hL hth hfin
  have htests : S.HasTests := (_root_.GlobalTheory.ZH.hasTests_of_real hss hU h1 h2 hT o Ω S ρ).1
  obtain ⟨m, a, GG, X, Z, U₀, EE, f, Xab, -, -, hNm, hO, hEE, -, -, -, hgen, hlast⟩ :=
    GlobalTheory.ZH.exists_minor_model o Ω S htests hfin'
  obtain ⟨Y⟩ := hG o Ω S ρ hbig Z U₀ EE hO hEE ⟨m, a, GG, hgen⟩
  have hopen : IsOpen (abLocus Y.G) := by
    rw [Y.ab]
    exact GlobalTheory.isOpen_setOf_TT_eq_bot o Ω S Z _ _ _ hO.div (fun z x₀ hx => (hlast z x₀ hx).2)
  obtain ⟨r₀, hr⟩ := GlobalTheory.exists_ampFrames_exponents h1 o Ω S ρ Z U₀ EE m a GG Y hNm hO hgen
  rw [hN] at hr
  exact GlobalTheory.T.exists_birationalModel_semiAbelian_ampleFrames h1 h2 E H o Ω R t₀ S ρ h φ act Z U₀ EE Y (n ^ k) r₀ hR hfr hO hopen hcart hLφ
    hact hadj hprim hr

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeInFamilies
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

theorem heckeInFamilies : HeckeInFamilies := by
  intro E _ _ _ H D l Xo 𝔓 p i hr hA
  refine ⟨?_, fun S s o C j h₁ h₂ h₃ h₄ h₅ => _root_.GlobalTheory.HkFam.existsUnique_heckeQuot E H D l Xo 𝔓 p i S s o C j hr hA h₁ h₂ h₃ h₄ h₅⟩
  obtain ⟨Z⟩ := _root_.GlobalTheory.HkFam.corr_nonempty E H D l Xo 𝔓 p i hr hA
  obtain ⟨a, b, c⟩ := _root_.GlobalTheory.HkFam.second_projection_finite_etale E H D l Xo 𝔓 p i Z hr hA
  obtain ⟨d, e⟩ := _root_.GlobalTheory.kerScheme_points E H D l Xo 𝔓 p i Z.toKerScheme hA
  exact ⟨Z, a, b, fun h => ⟨e h, c h⟩, fun k _ _ y C hC =>
    ⟨d k y C hC, fun z hz => pointQuot_snd E H D l Xo 𝔓 p i Z hA k z y C hz⟩⟩

end GlobalTheory.HkFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePoints
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.moduliScheme_levelMaps_heckePoints : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.N1 := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.N1
  exact ⟨_root_.GlobalTheory.Moduli.moduli_scheme_exists, fun E _ _ _ H D hD =>
    ⟨_root_.GlobalTheory.levelMaps_closed _root_.GlobalTheory.abelianSchemeLaws_all.1 E H D hD,
      _root_.GlobalTheory.heckePoints_of_laws _root_.GlobalTheory.abelianSchemeLaws_all.1
        _root_.GlobalTheory.AbLaw.CubeAssembly.cube_gen E H D hD⟩⟩

end GlobalTheory
end

