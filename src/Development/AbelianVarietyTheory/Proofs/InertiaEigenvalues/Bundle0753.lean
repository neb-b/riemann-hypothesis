module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0116
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesFinal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0748
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0699
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0731
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0205
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
public import GroundTheory.LocalFields.LocalZetaGauss
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0499
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftHasPointAtLocalisationSamePlace
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0103
public import GroundTheory.LocalFields.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKummerField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0749
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaCellsDisjointOffFinset
section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CellDec

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem compV_mem_unipB (v : HeightOneSpectrum (𝓞 E)) {u : GA E n} (hu : u ∈ NA E n) :
    compV E n v u ∈ GlobalTheory.SmGL.unipB (v.adicCompletion E) (Fin n) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
  refine (GlobalTheory.SmGL.mem_unipB _).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · simp [compV, h1 i j hij]
  · simp [compV, h2 i]

theorem compV_tl (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (v : HeightOneSpectrum (𝓞 E)) :
    compV E n v (tl n ϖ l) = GlobalTheory.IwaCell.tD (ϖ v) (l v) := by
  rw [tl_eq_diagT]
  apply Units.ext
  rw [GlobalTheory.IwaCell.val_tD]
  ext i j
  simp [compV, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    have hc : ∀ x : Af E, pFin E (GlobalTheory.CuspRep.corner (sFin E) x) = x := fun x => by
      show ((1 : InfiniteAdeleRing E × Af E) - ((0 : InfiniteAdeleRing E), (1 : Af E)) + ((0 : InfiniteAdeleRing E), x)).2 = x
      simp
    have hf : ∀ y : (Af E)ˣ, ((finId E y : Ad E)) = GlobalTheory.CuspRep.corner (sFin E) (y : Af E) := fun y => rfl
    rw [hf, hc]
    congr 1
    show ((ϖ v ^ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l) v : (v.adicCompletion E)ˣ) : v.adicCompletion E) = _
    rw [Finsupp.mapRange_apply, Units.val_zpow_eq_zpow_val]
  · simp

end GlobalTheory.CellDec

namespace GlobalTheory.CellDec

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem ord_of_isUnifV {v : HeightOneSpectrum (𝓞 E)} {x : (v.adicCompletion E)ˣ}
    (hx : IsUnifV E v (x : v.adicCompletion E)) : GlobalTheory.SmGL.ord (v.adicCompletion E) x = 1 := by
  rw [GlobalTheory.SmGL.SphCompletion.ord_completion, hx]
  rfl

theorem compV_mem_cell (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) {S : Finset (HeightOneSpectrum (𝓞 E))}
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) {g : GA E n} (h : (tl n ϖ l)⁻¹ * g ∈ C0 E n S)
    {v : HeightOneSpectrum (𝓞 E)} (hv : v ∉ S) : compV E n v g ∈ GlobalTheory.IwaCell.cell (ϖ v) (l v) := by
  obtain ⟨u, hu, k, hk, e⟩ := h
  have hg : g = tl n ϖ l * u * (tl n ϖ l)⁻¹ * tl n ϖ l * k := by
    rw [inv_mul_eq_iff_eq_mul] at e
    rw [e]; group
  have hkv : compV E n v k ∈ GlobalTheory.SplitWeil.KO (v.adicCompletion E) (Fin n) := by
    rw [GlobalTheory.HeckeEigConj.KO_eq_KGL]
    have := (Subgroup.mem_iInf.1 hk) v
    exact Subgroup.mem_comap.1 ((Subgroup.mem_iInf.1 this) hv)
  refine ⟨compV E n v (tl n ϖ l * u * (tl n ϖ l)⁻¹), compV_mem_unipB v (tl_conj_mem ϖ l hu), compV E n v k, hkv, ?_⟩
  rw [hg, map_mul, map_mul, compV_tl]

end GlobalTheory.CellDec

theorem GlobalTheory.CellDec.eq_of_tl_inv_mul_mem_C0_of_tl_inv_mul_mem_C0 : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ), (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) →
    ∀ (l l' : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (g : GA E n), (∀ v ∈ S, l v = 0) → (∀ v ∈ S, l' v = 0) →
      (GlobalTheory.CellDec.tl n ϖ l)⁻¹ * g ∈ GlobalTheory.CellDec.C0 E n S → (GlobalTheory.CellDec.tl n ϖ l')⁻¹ * g ∈ GlobalTheory.CellDec.C0 E n S → l = l' := by
  intro E _ _ n S ϖ hϖ l l' g hl hl' h h'
  ext v : 1
  by_cases hv : v ∈ S
  · rw [hl v hv, hl' v hv]
  · exact GlobalTheory.IwaCell.eq_of_mem_cell (GlobalTheory.CellDec.ord_of_isUnifV (hϖ v))
      (GlobalTheory.CellDec.compV_mem_cell ϖ l h hv) (GlobalTheory.CellDec.compV_mem_cell ϖ l' h' hv)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleArcDatumGivesArcProperty
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem admissibleArcDatum_gives_arcProperty : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    UnusedSlot80.AdmArcA D HW F Cm → DeltaInvariantLattices.WachLatticeFreeGlobal D HW F → RamifiedCoefficientChains.adm11 D → UnusedSlot80.ArcLiftingCoordinates D HW F Cm :=
  fun D HW F Cm hA h1f h11 => UnusedSlot80.arc_coordinates_final D HW F Cm hA h1f h11

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSplittingAlongArcsOfAdmissible
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem classSplitAlongArcs : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.AdmSplitA D HW F Cm → UnusedSlot80.AdmArcA D HW F Cm → DeltaInvariantLattices.WachLatticeFreeGlobal D HW F → DeltaInvariantLattices.P6 D HW F → LiftingTheory.WachKillsQuotients D HW F → InvariantsGenerators.LitFont D HW F → LiftingTheory.adm23 D HW F → TruncatedSeriesCountingBounds.adm9 D → RamifiedCoefficientChains.adm11 D → UnusedSlot80.SplittingArcLifting D HW F Cm :=
  UnusedSlot80.split_case_A_final

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EpsilonFactorRecCompatibleStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.epsilon_factor_rec_compatible : LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (k := w.adicCompletion E) → WD h), LawsLit a ha e rc → ∀ (x : IrrGL (k := w.adicCompletion E)) (α : Fin x.1 → ℂˣ), HasSatake x.rep α → rc x = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := by
  first | exact @GlobalTheory.LocLanglands.SatakeLaw.sat_of_lawsLit | exact GlobalTheory.LocLanglands.SatakeLaw.sat_of_lawsLit | (intros; apply GlobalTheory.LocLanglands.SatakeLaw.sat_of_lawsLit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EpsilonFactorsAtOneHalf
section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
open GroundTheory.Global (HeckeCharacter localAdelicChar)
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DelEps.GaussBridge

open GroundTheory.LocalField (valBall unitFiltrationUnits addCharConductor quasiCharConductor
  IsUnramifiedChar unifUnit unitsModRep unitsModFiltration unitsModCoset gaussSum)

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem continuous_of_isSmoothChar {χ : Fˣ →* ℂˣ} (hχ : IsSmoothChar χ) : Continuous χ := by
  refine continuous_def.2 fun U _ => isOpen_iff_forall_mem_open.2 fun x hx => ?_
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (χ.ker : Set Fˣ), fun y hy => ?_,
    hχ.preimage (continuous_const_mul _), by simp⟩
  have h : χ (x⁻¹ * y) = 1 := hy
  rw [map_mul, map_inv, inv_mul_eq_one] at h
  show χ y ∈ U
  rw [← h]
  exact hx

variable {χ : Fˣ →* ℂˣ} {ψ : AddChar F Circle}

end GlobalTheory.DelEps.GaussBridge

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EveryHeckeRowGoodAtGoodPointLocalisation
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.ExhaustRows

theorem main : ∀ (D : D7) (M : MtFam D), HeckeTied D M → AVTied D M → ∀ Tn : NormalizedLocalCompatibility D M, HeckeStdTw Tn.B → SumRepresentations.Conclusion42 D → GoodFTAll D → ∀ (i : D.nd.Loc) (σ : D.what₂.FT), D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ ∧ ∃ i' ∈ D.nd.locs (D.nd.j i) (D.nd.w i), HG D.nd D.naut i' ∧ AtM D.nd D.naut i' σ := by
  intro D M hT hA Tn hS h42 hG i σ hne
  have hg : D.nd.goodRow σ := hG σ
  obtain ⟨P, hP⟩ := ((h42 i) σ hne).1.2
  obtain ⟨i', hi', P', x', hth, hx⟩ := _root_.GlobalTheory.LiftPoint.main D M hT hA Tn hS i σ P hP
  obtain ⟨hxg, hat⟩ := _root_.GlobalTheory.GoodLiftPoint.good_of_lift D h42 i' σ P' x' hg hth hx
  exact ⟨hg, i', hi', ⟨x', hxg⟩, hat⟩

end GlobalTheory.ExhaustRows
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFactorComponentsOfAdelicInvariantFunction
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat

namespace GlobalTheory.CompFactor


set_option maxHeartbeats 1000000 in
theorem exists_factor_comp : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (hr : V.rank = r) (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ), IotaOK Dw V io → 1 ≤ Dw.p + Dw.q → l.A = 1 → GoodEmb c σ → (∀ k, ModelW V hr (U.X k)) → DictLat U V hr dict io e F ik φ th x₀ → (∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) → ∀ w : GA D V → c.F, (∀ h h' : GA D V, finHom V h = finHom V h' → w h = w h') → (∀ γ ∈ GQ V, ∀ h, w (γ * h) = w h) → (∀ u : GA D V, gLat V u = latHat V → FinCong V l.M u → ∀ h, w (h * u) = w h) → ∃ v : U.Comp → c.F, ∀ h : GA D V, w h = v (dict h).1 := by
  intro D H Dw l Xo c σ V r hr U dict io g e F ik φ th x₀ hio _ _ _ hW hD _ w _ h2 h3
  subst hr
  have hG : ∀ k, (U.X k).Gm = -V.gramᵀ := fun k => (hW k).1
  have htr : ∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E
      (-(-D.host.xi0) * herm (-V.gramᵀ) (φ k a : Fin V.rank → D.host.E) (φ k b)) := fun k a b => by
    rw [hD.1.1 k a b, hG k, (hW k).2]
  have key : ∀ h h', ik (dict h).1 = ik (dict h').1 → w h = w h' := by
    intro h h' hi
    obtain ⟨γ, hγ, hΛ, hm, -⟩ := hD.2 h
    obtain ⟨γ', hγ', hΛ', hm', -⟩ := hD.2 h'
    have hξ : -(-D.host.xi0) ≠ 0 := by
      rw [← (hW (dict h).1).2]
      exact neg_ne_zero.2 (U.X _).ξ0_ne
    obtain ⟨δ, hδ, u, hu, hc, eu⟩ := GlobalTheory.CompRead.exists_rat_finCong_of_index F V io hio.emb _ _ hi _ _ _ _
      (SetLike.ext' (hΛ.trans (Set.image_id _))) (SetLike.ext' (hΛ'.trans (Set.image_id _))) (φ _) (φ _) _ hξ
      (htr _) (htr _) hm hm'
    rw [← h2 γ' hγ' h', eu, h3 u hu hc, h2 δ hδ, h2 γ hγ]
  have hv : ∀ k : U.Comp, ∃ a : c.F, ∀ h, (dict h).1 = k → w h = a := by
    intro k
    by_cases hex : ∃ h, (dict h).1 = k
    · obtain ⟨h, hi⟩ := hex
      exact ⟨w h, fun h' hi' => key h' h (congrArg ik (hi'.trans hi.symm))⟩
    · exact ⟨0, fun h hi => absurd ⟨h, hi⟩ hex⟩
  choose v hv using hv
  exact ⟨v, fun h => hv _ h rfl⟩

end GlobalTheory.CompFactor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHcharPrescribedTrivial
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocLanglands

namespace GlobalTheory.DelEps.Twist

section Local

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def filtSub (a : ℕ) : Subgroup kˣ where
  carrier := unitFilt k a
  one_mem' := ⟨by simp, by simp⟩
  mul_mem' := fun {x y} hx hy => ⟨by rw [Units.val_mul, map_mul, hx.1, hy.1, one_mul], by
    have e : ((x * y : kˣ) : k) - 1 = (x : k) * ((y : k) - 1) + ((x : k) - 1) := by rw [Units.val_mul]; ring
    rw [e]
    refine Valuation.map_add_le _ ?_ hx.2
    rw [map_mul, hx.1, one_mul]
    exact hy.2⟩
  inv_mem' := fun {x} hx => by
    have h1 : valuation k ((x⁻¹ : kˣ) : k) = 1 := by rw [Units.val_inv_eq_inv_val, map_inv₀, hx.1, inv_one]
    refine ⟨h1, ?_⟩
    have e : ((x⁻¹ : kˣ) : k) - 1 = -(((x⁻¹ : kˣ) : k) * ((x : k) - 1)) := by
      linear_combination x.inv_mul
    rw [e, Valuation.map_neg, map_mul, h1, one_mul]
    exact hx.2

theorem isOpen_filtSub (a : ℕ) : IsOpen (filtSub k a : Set kˣ) :=
  (GroundTheory.LocalField.isOpen_setOf_valuation_eq_one.inter (GroundTheory.LocalField.isOpen_setOf_valuation_sub_le (a := (1 : k))
    (pow_ne_zero a uniformizer_ne_zero))).preimage Units.continuous_val

theorem ord_zpow (p : kˣ) (n : ℤ) : ord k (p ^ n) = n * ord k p := by
  let f : kˣ →* Multiplicative ℤ :=
    { toFun := fun x => Multiplicative.ofAdd (ord k x)
      map_one' := by rw [ord_eq_zero (by simp)]; rfl
      map_mul' := fun x y => by rw [ord_mul]; rfl }
  have := congrArg Multiplicative.toAdd (map_zpow f p n)
  simpa [f] using this

end Local

section Global

open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {k : Type} [Field k] [NumberField k]

def comp (w : HeightOneSpectrum (𝓞 k)) : Ideles k →* (w.adicCompletion k)ˣ :=
  Units.map
    { toFun := fun a : AdeleRing (𝓞 k) k => a.2 w
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

theorem continuous_comp (w : HeightOneSpectrum (𝓞 k)) : Continuous (comp w) :=
  Continuous.units_map _ ((RestrictedProduct.continuous_eval w).comp continuous_snd)

theorem comp_diag (w : HeightOneSpectrum (𝓞 k)) (x : kˣ) : comp w (diagUnits k x) = atFin w x := Units.ext rfl

theorem comp_local_self (w : HeightOneSpectrum (𝓞 k)) (x : (w.adicCompletion k)ˣ) : comp w (localIdele k w x) = x :=
  Units.ext (localIdele_snd_self k w x)

theorem comp_local_ne {w w' : HeightOneSpectrum (𝓞 k)} (h : w' ≠ w) (x : (w.adicCompletion k)ˣ) :
    comp w' (localIdele k w x) = 1 :=
  Units.ext ((localIdele_isSupportedAt k w x).2 w' h)

theorem comp_inf (w : HeightOneSpectrum (𝓞 k)) (u : InfinitePlace k) (x : (u.Completion)ˣ) : comp w (infIdele k u x) = 1 :=
  Units.ext rfl

theorem exists_hchar_prescribed (k : Type) [Field k] [NumberField k] (S : Finset (HeightOneSpectrum (𝓞 k)))
    (θ : ∀ w : HeightOneSpectrum (𝓞 k), (w.adicCompletion k)ˣ →* ℂˣ) (hs : ∀ w ∈ S, IsSmoothChar (θ w))
    (hf : ∀ w ∈ S, ∃ N : ℕ, 0 < N ∧ θ w ^ N = 1) :
    ∃ η : HChar k, (∃ n : ℕ, 0 < n ∧ η.OrderDvd n) ∧ (∀ u : InfinitePlace k, η.locInf u = 1) ∧ ∀ w ∈ S, η.loc w = θ w := by
  classical
  choose! N hN0 hN using hf
  have hm0 : 0 < ∏ w ∈ S, N w := Finset.prod_pos hN0
  have hm : ∀ w ∈ S, ∀ x, θ w x ^ (∏ w ∈ S, N w) = 1 := fun w hw x => by
    obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem N hw
    rw [hd, pow_mul, ← MonoidHom.pow_apply, hN w hw, MonoidHom.one_apply, one_pow]
  set m := ∏ w ∈ S, N w
  obtain ⟨T, hST, hT⟩ := GlobalTheory.ChevalleySUnits.exists_places k S m hm0
  let U : Subgroup (Ideles k) := GlobalTheory.LevelChars.levSub k T 1 ⊓ ⨅ w : S, (θ w).ker.comap (comp w.1)
  have hU : IsOpen (U : Set (Ideles k)) := by
    have h1 : IsOpen (GlobalTheory.LevelChars.levSub k T 1 : Set (Ideles k)) := by
      convert (GlobalTheory.Mem.UnitOpen.unit_open_and_congr_open k).2 T 1 using 1
      ext a
      exact ⟨fun h => ⟨fun v => (h v).1, fun v hv => (h v).2 hv⟩, fun h v => ⟨h.1 v, h.2 v⟩⟩
    rw [Subgroup.coe_inf, Subgroup.coe_iInf]
    exact h1.inter (isOpen_iInter_of_finite fun w => (hs w w.2).preimage (continuous_comp w.1))
  let β : (∀ w : S, (w.1.adicCompletion k)ˣ) →* Ideles k :=
    ∏ w : S, (localIdele k w.1).comp (Pi.evalMonoidHom (fun w : S => (w.1.adicCompletion k)ˣ) w)
  let γ : (∀ w : S, (w.1.adicCompletion k)ˣ) →* ℂˣ :=
    ∏ w : S, (θ w.1).comp (Pi.evalMonoidHom (fun w : S => (w.1.adicCompletion k)ˣ) w)
  have hβ : ∀ y, β y = ∏ w : S, localIdele k w.1 (y w) := fun y => MonoidHom.finsetProd_apply _ _ _
  have hγ : ∀ y, γ y = ∏ w : S, θ w.1 (y w) := fun y => MonoidHom.finsetProd_apply _ _ _
  have hβS : ∀ y (w : S), comp w.1 (β y) = y w := fun y w => by
    rw [hβ, map_prod, Finset.prod_eq_single w, comp_local_self]
    · exact fun w' _ h => comp_local_ne (fun e => h (Subtype.ext e.symm)) _
    · simp
  have hβn : ∀ y v, v ∉ S → comp v (β y) = 1 := fun y v hv => by
    rw [hβ, map_prod]
    exact Finset.prod_eq_one fun w _ => comp_local_ne (fun e : v = w.1 => hv (e ▸ w.2)) _
  obtain ⟨χ, hχ, -, hχU, hχα⟩ := GlobalTheory.exists_unitary_char_of_open_subgroup_and_hom (Ideles k)
    (kˣ × ∀ w : S, (w.1.adicCompletion k)ˣ) U hU ((diagUnits k).coprod β) ((1 : kˣ →* ℂˣ).coprod γ) 1 continuous_const
    (fun _ => by simp)
    (fun y => by
      have h1 : γ y.2 ^ m = 1 := by
        rw [hγ, ← Finset.prod_pow]
        exact Finset.prod_eq_one fun w _ => hm w w.2 _
      have h2 : ((γ y.2 : ℂˣ) : ℂ) ^ m = 1 := by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
      simpa using Complex.norm_eq_one_of_pow_eq_one h2 hm0.ne')
    (by
      rintro ⟨x, y⟩ ⟨h1, h2⟩
      have hval : ∀ (v : HeightOneSpectrum (𝓞 k)) (z : k),
          Valued.v (algebraMap k (v.adicCompletion k) z) = v.valuation k z := fun v z =>
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v z
      have hc : ∀ v, v ∉ S → GlobalTheory.LevelChars.compAt k v ((diagUnits k).coprod β (x, y)) =
          algebraMap k (v.adicCompletion k) (x : k) := fun v hv => by
        have e : comp v ((diagUnits k).coprod β (x, y)) = atFin v x := by
          rw [MonoidHom.coprod_apply, map_mul, comp_diag, hβn _ v hv, mul_one]
        exact congrArg Units.val e
      obtain ⟨z, hz⟩ := hT x (fun v hv => by rw [← hval, ← hc v hv]; exact (h1 v).1) (fun t ht => by
        have h3 := (h1 t).2 ht
        rw [hc t (Finset.disjoint_right.1 hST ht), ← map_one (algebraMap k (t.adicCompletion k)), ← map_sub, hval] at h3
        refine h3.trans_lt ?_
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
        simp)
      have hz0 : z ≠ 0 := by
        rintro rfl
        exact x.ne_zero (by rw [← hz, zero_pow hm0.ne'])
      have hxz : x = Units.mk0 z hz0 ^ m := Units.ext (by simp [hz])
      rw [MonoidHom.coprod_apply, MonoidHom.one_apply, MonoidHom.one_apply, one_mul, hγ]
      refine Finset.prod_eq_one fun w _ => ?_
      have h4 : θ w.1 (comp w.1 ((diagUnits k).coprod β (x, y))) = 1 := Subgroup.mem_iInf.1 h2 w
      rwa [MonoidHom.coprod_apply, map_mul, comp_diag, hβS, map_mul, hxz, map_pow, map_pow, hm w w.2, one_mul] at h4)
  let η : HChar k := ⟨χ, hχ, fun x => by simpa using hχα (x, 1)⟩
  have hinf : ∀ u : InfinitePlace k, η.locInf u = 1 := fun u => by
    ext x
    refine congrArg Units.val (hχU (infIdele k u x) ⟨fun v => ⟨map_one _, fun _ => ?_⟩, Subgroup.mem_iInf.2 fun w => ?_⟩)
    · change Valued.v ((1 : v.adicCompletion k) - 1) ≤ _
      simp
    · rw [Subgroup.mem_comap, comp_inf]
      exact one_mem _
  refine ⟨η, GlobalTheory.Mem.FinOrder.finite_order_of_inf_eq_one k η fun x => ?_, hinf, fun w hw => ?_⟩
  · change χ (infDiag x) = 1
    rw [infDiag, MonoidHom.finsetProd_apply, map_prod]
    exact Finset.prod_eq_one fun u _ => DFunLike.congr_fun (hinf u) (atInf u x)
  · refine MonoidHom.ext fun x => ?_
    have h := hχα (1, Pi.mulSingle (⟨w, hw⟩ : S) x)
    rw [MonoidHom.coprod_apply, MonoidHom.coprod_apply, map_one, map_one, one_mul, one_mul] at h
    dsimp only at h
    rw [hβ, hγ, Finset.prod_eq_single (⟨w, hw⟩ : S), Finset.prod_eq_single (⟨w, hw⟩ : S), Pi.mulSingle_eq_same] at h
    · exact h
    · intro w' _ h'
      rw [Pi.mulSingle_eq_of_ne h', map_one]
    · simp
    · intro w' _ h'
      rw [Pi.mulSingle_eq_of_ne h', map_one]
    · simp

end Global

end GlobalTheory.DelEps.Twist

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLiftSatakeVectorLocalHeckeEigenStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_satake_vector_local_hecke_eigen : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.SatAt π Dv α → (∀ x : L, Dv.σw (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → ∀ (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w (n := n) → Formalism.UG.cT Dv.σw b.val * b.val = Formalism.UG.antiJ (w.adicCompletion L) n → ∀ p : locU n w →* Formalism.UG.GU Dv.σw n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → ∃ φ ∈ U, φ ≠ 0 ∧ (∀ x : locU n w, p x ∈ Formalism.UG.KU Dv.σw n → RU L n x.val φ = φ) ∧ ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) ((Formalism.UG.KU Dv.σw n).comap p) (fun x => h (p x)) φ = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • φ := by
  first | exact @GlobalTheory.InertHeckeTransfer.exists_lift_eigen | exact GlobalTheory.InertHeckeTransfer.exists_lift_eigen | (intros; apply GlobalTheory.InertHeckeTransfer.exists_lift_eigen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPendingObjectsDepthZeroAdmissibleEigenSpanStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pending_objects_depthZero_admissible_eigenSpan : ∀ (D : D7) (M : MtFam D), HeckeTied D M → HeckeRational D M → AVTied D M → (∀ S : Formalism.L2.ParC D, ∃ σ' : D.ntypes.Par, ∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut S.1 w) → SumRepresentations.tie0 D → SumRepresentations.adm5 D → IneRep D → LabDepth D → LabGen D → ZLStable D → CenInt D → OnMtPreservesTypeV D → SerLL D → CoeffRingsHaveRootsOfUnity D → DepthZ D → PairedCharacterCondition.RT.AdmDepthZeroTypes (D := D) → ∃ P : PairedCharacterCondition.Pend D, PairedCharacterCondition.admDZ P ∧ EigSpan P := by
  first | exact @GlobalTheory.PendClose.main | exact GlobalTheory.PendClose.main | (intros; apply GlobalTheory.PendClose.main <;> assumption)
end

