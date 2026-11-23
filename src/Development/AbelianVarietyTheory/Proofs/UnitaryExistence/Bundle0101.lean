module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimilitudeOfAutModLevelIdeal
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFramedPointMoveUniversalTriple
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspFormsDominantWeightFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0069
public import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0073
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFlagDomainModelsOfFamilyUniformisation
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFinPartMat
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0066

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrMoveTransfer
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory.LevelActionLaws

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H}
  {l : Level H}

attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

theorem exists_levAut (hpq : 1 ≤ D.p + D.q) (Xo : Moduli D l) (g : Sim D)
    (hν : (l.A : ℤ) ∣ g.ν l.A - 1) : ∃ ρ : Xo.X ≅ Xo.X, Xo.LevAut g ρ := by
  have hsim := exists_obj_twist_by_similitude SimAlg.sim_group
  have hred : IsReduced Xo.X := by
    haveI := Xo.smooth
    exact (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ Xo.s
      (SmoothOfRelativeDimension.smooth D.dim _)).1
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨i, hi⟩ := (ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ Xo.univ Xo.univ).1
  obtain ⟨g', hg'⟩ := (SimAlg.sim_group E H D hpq).2.2.2 g
  have hν' : (l.A : ℤ) ∣ g'.ν l.A - 1 := by
    have h₁ := (hg' l.A l.A_pos).2
    have : g'.ν l.A - 1 = (g.ν l.A * g'.ν l.A - 1) - (g.ν l.A - 1) * g'.ν l.A := by ring
    rw [this]
    exact dvd_sub h₁ (hν.mul_right _)
  obtain ⟨o₁, m₁, a₁, b₁⟩ := hsim E H D l _ _ _ _ Xo.univ g hpq hν
  obtain ⟨o₂, m₂, a₂, b₂⟩ := hsim E H D l _ _ _ _ Xo.univ g' hpq hν'
  obtain ⟨f, hf⟩ := Moduli.LevelAction.exists_twists Xo g hred i.toSABMap hi o₁ m₁ a₁ b₁
  obtain ⟨f', hf'⟩ := Moduli.LevelAction.exists_twists Xo g' hred i.toSABMap hi o₂ m₂ a₂ b₂
  exact ⟨⟨f, f', Moduli.LevelAction.comp_eq_id_of_twists Xo hred i hf hf' (fun a => ((hg' _ hM).1 a).2)
      (fun a => ((hg' _ l.A_pos).1 a).2),
    Moduli.LevelAction.comp_eq_id_of_twists Xo hred i hf' hf (fun a => ((hg' _ hM).1 a).1)
      (fun a => ((hg' _ l.A_pos).1 a).1)⟩, hf⟩

theorem eta_congr (Xo : Moduli D l) {a b : D.La} (h : a - b ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) :
    Xo.univ.eta a = Xo.univ.eta b := by
  have e : a = (a - b) + b := by abel
  rw [e, Xo.univ.eta_add, Xo.univ.eta_ker _ h, one_mul]

theorem etaA_congr (Xo : Moduli D l) {a b : D.La} (h : D.ModN l.A (a - b)) :
    Xo.univ.etaA a = Xo.univ.etaA b := by
  obtain ⟨x, hx⟩ := h
  have e : a = (a - b) + b := by abel
  rw [e, Xo.univ.etaA_add, hx, Xo.univ.etaA_ker, one_mul]

theorem exists_sim (hpq : 1 ≤ D.p + D.q) (hA : l.A.Coprime l.M) (γ : LaMod D l ≃ₗ[𝓞 E] LaMod D l) :
    ∃ g : Sim D, (∀ a, g.f l.M a - liftLa γ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) ∧
      (∀ a, D.ModN l.A (g.f l.A a - a)) ∧ (l.A : ℤ) ∣ g.ν l.A - 1 := by
  refine GlobalTheory.exists_sim_of_aut_mod E H D l l.A (liftLa γ) hpq l.A_pos hA fun x hx => ?_
  have h := liftLa_spec γ x
  rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 hx] at h
  have h2 := γ.map_eq_zero_iff.1 h.symm
  exact (Submodule.Quotient.mk_eq_zero _).1 h2

theorem exists_move (hpq : 1 ≤ D.p + D.q) (hA : l.A.Coprime l.M) (Xo : Moduli D l)
    (γ : LaMod D l ≃ₗ[𝓞 E] LaMod D l) :
    ∃ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), IsIso ρ ∧
      IsLevMove ρ ν (liftLa γ) LinearMap.id := by
  obtain ⟨g, h1, h2, h3⟩ := exists_sim hpq hA γ
  obtain ⟨ρ, hs, ν, hM, hAA⟩ := exists_levAut hpq Xo g h3
  refine ⟨ρ.hom, ν, inferInstance, hs, fun a => ?_, fun a => ?_⟩
  · rw [← eta_congr Xo (h1 a)]; exact hM a
  · have e := hAA a
    rw [etaA_congr Xo (h2 a)] at e
    exact e

theorem move_unique (hpq : 1 ≤ D.p + D.q) (hA : l.A.Coprime l.M) (Xo : Moduli D l) (c : Coeff l)
    (γ : LaMod D l ≃ₗ[𝓞 E] LaMod D l) {ρ ρ' : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ}
    {ν' : SABMap Xo.univ.t Xo.univ.t ρ'} (i : IsIso ρ) (i' : IsIso ρ')
    (h : IsLevMove ρ ν (liftLa γ) LinearMap.id) (h' : IsLevMove ρ' ν' (liftLa γ) LinearMap.id) :
    ρ = ρ' ∧ ν.φ = ν'.φ :=
  GlobalTheory.T.levelMove_moduli_unique_universalTriple E H D l Xo c ρ ρ' ν ν' _ _ _ _ hpq (fun a => by simp) (fun a => ⟨0, by simp⟩) i i' h h'
    (exists_sim hpq hA γ)

theorem frMove_transfer (hpq : 1 ≤ D.p + D.q) (hA : l.A.Coprime l.M) (Xo : Moduli D l) (c : Coeff l)
    (γ : LaMod D l ≃ₗ[𝓞 E] LaMod D l) {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ} (i : IsIso ρ)
    (h : IsLevMove ρ ν (liftLa γ) LinearMap.id) {S : Type} [CommRing S] [Algebra c.F S] {y y' : FrPt Xo c S}
    (hy : levR (liftLa γ, LinearMap.id) y y') : FrMove ρ ν y y' := by
  obtain ⟨ρ', ν', i', h', hm⟩ := hy
  obtain ⟨rfl, e⟩ := move_unique hpq hA Xo c γ i i' h h'
  obtain ⟨⟨w, hw⟩, hu⟩ := _root_.GlobalTheory.exists_unique_frMove E H D l Xo c ρ ν h.1 S y
  rwa [← hu w y' ν' e.symm hw hm]

theorem liftLa_one_sub (a : D.La) :
    liftLa (1 : LaMod D l ≃ₗ[𝓞 E] LaMod D l) a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  rw [← Submodule.Quotient.eq]
  exact liftLa_spec 1 a

theorem liftLa_mul_sub (γ δ : LaMod D l ≃ₗ[𝓞 E] LaMod D l) (a : D.La) :
    liftLa (γ * δ) a - liftLa γ (liftLa δ a) ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  rw [← Submodule.Quotient.eq]
  have h1 := liftLa_spec (γ * δ) a
  have h2 := liftLa_spec γ (liftLa δ a)
  rw [liftLa_spec δ a] at h2
  exact h1.trans h2.symm

end GlobalTheory.LevelActionLaws
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormEmbeddingHostFormConstantEq
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.ExtCore

theorem isDetRoot_mul {D : D7} (V : HSp D) (g g' : GA D V) (x x' : (AE D)ˣ) (hx : IsDetRoot V g x)
    (hx' : IsDetRoot V g' x') : IsDetRoot V (g * g') (x * x') := by
  unfold IsDetRoot at *
  rw [Units.val_mul, (matHom V).map_mul, Units.val_mul, Matrix.det_mul, RingHom.map_mul]
  conv_lhs => rw [hx, hx']
  ring


end GlobalTheory.ExtCore
end

