module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3139
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3035
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1302
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1332
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionBlowup
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2475
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointsAdditiveParametrization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3135
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageTriangleFactorStepFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2837
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomFramesChangeStageZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTowerConstantsDifferByFactor

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTripleChartUnitaryBoundaryPointRigid
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem uPre_of_boundary_pointRigid {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) (hpq : 1 ≤ Dw.p + Dw.q)
    (hφ : IsPolFan H.bar (min Dw.p Dw.q) φ) (hns : NoSelfInt H.bar (min Dw.p Dw.q) φ)
    {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData)
    {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S)
    (hP : GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD) (hS : SepB Xo c φ j)
    (x : S) (hx : x ∉ Set.range j) : UPre Xo c φ j BD d x := by
  obtain ⟨k, _, m, e, C, ξ, hT, hy, hξ⟩ :=
    _root_.GlobalTheory.UCanon.exists_tautB_chart_at Xo c φ hpq hφ hns zs i OZ N d J π j BD hP hS x hx
  have hE := _root_.GlobalTheory.TautEtaleB.tautB_isEtaleCompletion Xo c φ hpq hφ hns zs i OZ N d J π j BD hP hS C hT ξ hy
  obtain ⟨hset, hred, a, ha, hbd⟩ :=
    _root_.GlobalTheory.UCanonBd.boundary_eq Xo c φ hpq hφ hns zs i OZ N d J π j BD hP hS C hT ξ hy
  exact ⟨k, inferInstance, m, e, C, ξ, a, hT.1, hy, hξ, hE, hred, hset, ha, hbd⟩

end GlobalTheory.UCanon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalTangentHarrisTaylorRepresentingFa
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.RepTangent

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (Sp A) := by
  simp only [spMap]; exact Spec.map_id _

theorem exists_univ_tangent : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ F : RepFam b N, IsQProjOver F.s → Smooth F.s → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ F.X), ∃ u : Sp (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k)) ⟶ F.X, spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom ≫ u = x ∧ u ≫ F.s = spMap (algebraMap k (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k))) ≫ x ≫ F.s ∧ ∀ v : Sp (DualNumber k) ⟶ F.X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v = x → v ≫ F.s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ F.s → ∃! c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u := by
  intro p _ D R _ _ b N hN hNp F _ _ k _ _ x
  obtain ⟨o₀, ⟨m₀⟩⟩ := _root_.GlobalTheory.UPel.HT.Pull.exists_objMap p D R b N F.X (Sp k) F.s x F.univ
  obtain ⟨o, ⟨mo⟩, huniv⟩ := GlobalTheory.T.exists_universal_firstOrder_deformation_harrisTaylor p D R b N hN hNp k (x ≫ F.s) o₀
  obtain ⟨u, ⟨hu1, ⟨mu⟩⟩, -⟩ := F.rep _ _ o
  have hfst : spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom ≫
      spMap (algebraMap k (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k))) = 𝟙 _ := by
    rw [spMap_comp_spMap]
    convert spMap_id' k
    ext a; simp
  refine ⟨u, ?_, hu1, ?_⟩
  · obtain ⟨f, -, hf⟩ := F.rep _ _ o₀
    have e1 := hf x ⟨rfl, ⟨m₀⟩⟩
    have e2 := hf (spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom ≫ u)
      ⟨by rw [Category.assoc, hu1, ← Category.assoc, hfst, Category.id_comp], ⟨MapComp.comp mo mu⟩⟩
    exact e2.trans e1.symm
  · intro v hv1 hv2
    obtain ⟨o', ⟨m'⟩⟩ := _root_.GlobalTheory.UPel.HT.Pull.exists_objMap p D R b N F.X (Sp (DualNumber k)) F.s v F.univ
    have main : ∀ (s₁ : Sp (DualNumber k) ⟶ Sp R) (o' : Obj b N s₁), s₁ = v ≫ F.s → ObjMap o' F.univ v →
        ∃! c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u := by
      intro s₁ o' hs m'
      rw [hv2] at hs
      subst hs
      have h0 : Nonempty (ObjMap o₀ F.univ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v)) := by
        rw [hv1]; exact ⟨m₀⟩
      have m'' := (GlobalTheory.UPel.HT.objMap_comp_cancel p D R b N _ _ _ _ _ _ o₀ o' F.univ _ v).2 h0 ⟨m'⟩
      obtain ⟨c, ⟨mc⟩, hc⟩ := huniv o' m''
      have hbase : ∀ c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k,
          (spMap (TrivSqZeroExt.map c).toRingHom ≫ u) ≫ F.s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ F.s := by
        intro c
        rw [Category.assoc, hu1, ← Category.assoc, spMap_comp_spMap]
        congr 2
        exact (TrivSqZeroExt.map c).comp_algebraMap
      refine ⟨c, ?_, ?_⟩
      · obtain ⟨f, -, hf⟩ := F.rep _ _ o'
        exact (hf v ⟨hv2, ⟨m'⟩⟩).trans (hf _ ⟨hbase c, ⟨MapComp.comp mc mu⟩⟩).symm
      · intro c' hc'
        apply hc
        rw [hc'] at m'
        exact (GlobalTheory.UPel.HT.objMap_comp_cancel p D R b N _ _ _ _ _ _ o' o F.univ _ u).2 ⟨m'⟩ ⟨mu⟩
    exact main _ o' rfl m'

end GlobalTheory.UPel.HT.RepTangent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinimalBlowupSmoothWithSemiAbelianCharts
section
namespace GlobalTheory.SiegJoin

theorem chartSt5_holds : ChartSt5 :=
  fun g hg φ h₁ h₂ n hn ho F Z z i OZ d S π j _ BD hM hB =>
    ⟨_root_.GlobalTheory.BlowSmooth.smoothOfRelativeDimension_blowup g hg φ h₁ h₂ n hn ho F Z z i OZ d S π j BD hM hB,
      _root_.GlobalTheory.AllChart.preChart_all g hg φ h₁ h₂ n hn ho F Z z i OZ d S π j BD hM hB⟩

end GlobalTheory.SiegJoin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiesNoetherian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelNoeth

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap (b.comp a) = spMap b ≫ spMap a := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_id_eq (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (Sp A) := by
  simp only [spMap]
  exact Spec.map_id _

theorem classify_noetherian : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ f : Sp R ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F R _ _ β c hc
  refine _root_.GlobalTheory.SiegZar.classified_of_local g n hg hn hodd F (Sp R) (spMap β) c hc ?_
  intro x
  let 𝔭 : Ideal R := x.asIdeal
  haveI : 𝔭.IsPrime := x.isPrime
  have loc : ∀ c' : SiegPre g n (zetaAway n) (spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β)),
      SiegPB c' c (spMap (algebraMap R (Localization.AtPrime 𝔭))) →
      ∃ f : Sp (Localization.AtPrime 𝔭) ⟶ F.X, f ≫ F.s = spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β) ∧
        SiegPB c' F.univ f := by
    intro c' hc'
    have hP := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n) (zetaAway n)
      (RingHom.id _) (Sp R) (Sp (Localization.AtPrime 𝔭)) (spMap β)
      (spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β)) (spMap (algebraMap R (Localization.AtPrime 𝔭))) rfl
      (by rw [spMap_id_eq, Category.comp_id]; exact (spMap_comp_eq _ _).symm)).2.1 c c' hc' hc
    exact _root_.GlobalTheory.SiegelFamLocal.exists_point_of_principal g n hg hn hodd F (Localization.AtPrime 𝔭) ((algebraMap R (Localization.AtPrime 𝔭)).comp β) c' hP
  obtain ⟨r, hr, H⟩ := _root_.GlobalTheory.SiegSpread.classified_basicOpen g n hg hn hodd F R β c 𝔭 hc loc
  let j : Sp (Localization.Away r) ⟶ Sp R := spMap (algebraMap R (Localization.Away r))
  have e : spMap ((algebraMap R (Localization.Away r)).comp β) = j ≫ spMap β := spMap_comp_eq _ _
  rw [e] at H
  obtain ⟨cV, hcV⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n) (zetaAway n)
      (RingHom.id _) (Sp R) (Sp (Localization.Away r)) (spMap β) (j ≫ spMap β) j rfl
      (by rw [spMap_id_eq, Category.comp_id])).1 c
  obtain ⟨f, hf, hfu⟩ := H cV hcV
  refine ⟨Sp (Localization.Away r), j, cV, IsOpenImmersion.of_isLocalization r, ?_, hcV, f, hf, hfu⟩
  have hu : Set.range j = (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away r) r
  rw [hu]
  exact hr

end GlobalTheory.SiegelNoeth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFanKodairaSpencerOfRigidBoundaryCharts
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.RigChart.toroidalForFanKS_of_rigidForFan : GlobalTheory.RigChart.RigidForFan → GlobalTheory.Published.ToroidalForFanKS := by
  intro h E _ _ _ H Dw hr φ h₁ h₂ l Xo c
  obtain ⟨Y, BD, d, k, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩ := h E H Dw hr φ h₁ h₂ l Xo c
  exact ⟨Y, BD, d, k, a₁, a₂, a₃, a₄, a₅, a₆, a₇, _root_.GlobalTheory.LogKSAssembly.hasLogKS E H Dw l Xo c Y hr a₃ a₄ a₈⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointsAdditiveParametrizationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_points_additive_parametrization : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ),
  IsEtPlace b w0 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S),
  ∃ f : (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) → (Over.mk x ⟶ o.A), (∀ a a', f (a + a') = f a * f a') ∧
    (∀ (c : 𝓞 D.F) a, f (Ideal.Quotient.mk (w0 ^ r) c • a) = f a ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) ∧
    Function.Injective f ∧
    ∀ g : Over.mk x ⟶ o.A, (∀ c ∈ w0 ^ r, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃ a, f a = g := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.TorFree.free_torsion_geomPt) | (exact GlobalTheory.UPel.HT.EtLev.TorFree.free_torsion_geomPt) | (intros; apply GlobalTheory.UPel.HT.EtLev.TorFree.free_torsion_geomPt  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerOfThetaMatching
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqTower

theorem gbig_and {Q₁ Q₂ : GP} (h₁ : GBig Q₁) (h₂ : GBig Q₂) : GBig (fun G μ C x b => Q₁ G μ C x b ∧ Q₂ G μ C x b) := by
  obtain ⟨F1, h1⟩ := h₁
  obtain ⟨F2, h2⟩ := h₂
  refine ⟨max F1 F2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, k1⟩ := h1 ε CF (le_of_max_le_left hCF)
  obtain ⟨C2, x2, k2⟩ := h2 ε CF (le_of_max_le_right hCF)
  exact ⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hR T Lc μ₀ hμ G =>
    ⟨k1 C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ₀ hμ G,
      k2 C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ₀ hμ G⟩⟩

theorem gbig_mono {Q₁ Q₂ : GP} (h : GBig Q₁)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Lc.Is μ₀ → Q₁ G μ₀ C x b → Q₂ G μ₀ C x b) : GBig Q₂ := by
  obtain ⟨F, h⟩ := h
  refine ⟨F, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, k⟩ := h ε CF hCF
  exact ⟨C0, x0, fun C hC D large₂ he hx hR T Lc μ₀ hμ G => H G μ₀ C _ _ hμ (k C hC D large₂ he hx hR T Lc μ₀ hμ G)⟩

section Units

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem isAwayUnit_inv {m : ℕ} {x : K} (h : GlobalTheory.Square.IsAwayUnit m x) (hx : x ≠ 0) : GlobalTheory.Square.IsAwayUnit m x⁻¹ := by
  obtain ⟨a, k, k', ⟨b, hb⟩, e⟩ := h
  refine ⟨(m : 𝓞 K) ^ k * b, k', k + k', ⟨a, by rw [pow_add, hb]; ring⟩, ?_⟩
  have e2 : ((m : 𝓞 K) : K) ^ k' = (a : K) * (b : K) := by
    rw [← map_pow, hb]; push_cast; ring
  have e3 : ((m : 𝓞 K) : K) = (m : K) := by simp
  rw [e3] at e2
  rw [e2, ← e]
  push_cast
  field_simp

theorem stepRatio_self {T' : Type} (σ₀ : K →+* ℂ) (Qn : ℕ) (S0 : Finset T') (cc qq : T' → ℕ) (x : ℂ) :
    GlobalTheory.Square.StepRatio σ₀ Qn S0 cc qq x x :=
  ⟨1, fun _ => 1, fun _ => 1, GlobalTheory.Square.IsAwayUnit.one Qn, fun _ _ => ⟨one_dvd _, one_dvd _⟩, by simp⟩

theorem stepRatio_div {T' : Type} {σ₀ : K →+* ℂ} {Qn : ℕ} {S0 : Finset T'} {cc qq : T' → ℕ} {y y₀ : ℂ}
    (h : GlobalTheory.Square.StepRatio σ₀ Qn S0 cc qq y y₀) (h₀ : y₀ ≠ 0) : GlobalTheory.Square.StepRatio σ₀ Qn S0 cc qq (y / y₀) 1 := by
  obtain ⟨b, g, g', hb, hg, e⟩ := h
  exact ⟨b, g, g', hb, hg, by rw [e, mul_div_assoc, div_self h₀]⟩

end Units

section Descent

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} {W : G.Weil} {μ₀ : T}

def FacIn (W : G.Weil) : Prop := ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), IsStageC W i j p q X →
  ∃ lam : T → ℂ, Factor X W.ψ W.θ lam

def SmallIn (W : G.Weil) (μ₀ : T) : Prop := ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW) (lam : T → ℂ)
  (e : ℕ) (Lf : T → ℂ → ℂ), IsStageC W i j p (q + 1) X → Factor X W.ψ W.θ lam → A.rank = A'.rank + 2 * e →
    (∀ t, IsHeckeL (nuH G t i j) (Lf t)) → ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c y : T → ℂ),
      IsStageC W i j p q Y ∧ Y.IsConst W.ψ W.θ c ∧ (∀ t, y t ≠ 0 ∧ lam t * Lf t ((e + 1 : ℕ) : ℂ) = y t * c t) ∧
      ∀ t, GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal) (y t) (y μ₀)

def BigIn (W : G.Weil) (μ₀ : T) : Prop := ∀ (i j : Fin D.R.m) (p : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW) (lam : T → ℂ)
  (e : ℕ) (Lf : T → ℂ → ℂ), IsStageC W i j (p + 1) 0 X → Factor X W.ψ W.θ lam → A.rank = A'.rank + 2 * e →
    (∀ t, IsHeckeL (nuH G t i j) (Lf t)) → ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c y : T → ℂ),
      IsStageC W i j p 0 Y ∧ Y.IsConst W.ψ W.θ c ∧ (∀ t, y t ≠ 0 ∧ lam t = y t * Lf t (e : ℂ) * c t) ∧
      ∀ t, GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal) (y t) (y μ₀)

def cons (y : T → ℂ) (u : ℕ → T → ℂ) : ℕ → T → ℂ
  | 0 => y
  | k + 1 => u k

theorem cons_zero (y : T → ℂ) (u : ℕ → T → ℂ) : cons y u 0 = y := rfl

theorem cons_succ (y : T → ℂ) (u : ℕ → T → ℂ) (k : ℕ) : cons y u (k + 1) = u k := rfl

theorem descent (hF : FacIn W) (hs : SmallIn W μ₀) (hb : BigIn W μ₀) (i j : Fin D.R.m) (Lf : T → ℂ → ℂ)
    (hL : ∀ t, IsHeckeL (nuH G t i j) (Lf t)) :
    ∀ (q p e : ℕ) {A A' WW : HSp D} (X : Tri T A A' WW) (c : T → ℂ), IsStageC W i j p q X → X.IsConst W.ψ W.θ c →
      A.rank = A'.rank + 2 * e → p ≤ e →
      ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (cY : T → ℂ) (u : ℕ → T → ℂ) (κ : ℂ),
        IsStageC W i j 0 0 Y ∧ Y.IsConst W.ψ W.θ cY ∧ κ ≠ 0 ∧ (∀ k t, u k t ≠ 0 ∧ GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal) (u k t) (u k μ₀)) ∧
        ∀ t, c t * ∏ k ∈ range q, Lf t ((e + k + 1 : ℕ) : ℂ) =
          κ * (∏ k ∈ range (p + q), u k t) * cY t * ∏ k ∈ range p, Lf t ((e + q - k : ℕ) : ℂ) := by
  intro q
  induction q with
  | zero =>
    intro p
    induction p with
    | zero =>
      intro e A A' WW X c hX hc _ _
      refine ⟨A, A', WW, X, c, fun _ _ => 1, 1, hX, hc, one_ne_zero, fun k t => ⟨one_ne_zero, stepRatio_self _ _ _ _ _ _⟩,
        fun t => by simp⟩
    | succ p ih =>
      intro e A A' WW X c hX hc he hpe
      obtain ⟨lam, hl⟩ := hF i j _ _ A A' WW X hX
      obtain ⟨κ₁, hκ₁, e1⟩ := hl.eq_mul hc
      obtain ⟨B, B', W₁, Y, cY', y, hY, hcY', hy, hyr⟩ := hb i j p A A' WW X lam e Lf hX hl he hL
      have hr : B.rank = B'.rank + 2 * (e - 1) := by
        obtain ⟨-, -, a1, a2, -⟩ := hX
        obtain ⟨-, -, b1, b2, -⟩ := hY
        omega
      obtain ⟨B₂, B₂', W₂, Y₂, cY, u, κ, hY₂, hcY, hκ, hu, hid⟩ := ih (e - 1) Y cY' hY hcY' hr (by omega)
      refine ⟨B₂, B₂', W₂, Y₂, cY, cons y u, κ₁ * κ, hY₂, hcY, mul_ne_zero hκ₁ hκ,
        fun k t => ?_, fun t => ?_⟩
      · rcases k with _ | k
        · exact ⟨(hy t).1, hyr t⟩
        · exact hu k t
      · have h1 := hid t
        have h2 := (hy t).2
        simp only [range_zero, prod_empty, mul_one, add_zero] at h1 ⊢
        simp only [prod_range_succ', cons_succ, cons_zero, Nat.sub_zero]
        have e3 : ∏ k ∈ range p, Lf t ((e - (k + 1) : ℕ) : ℂ) = ∏ k ∈ range p, Lf t ((e - 1 - k : ℕ) : ℂ) :=
          prod_congr rfl fun k _ => by rw [show e - (k + 1) = e - 1 - k by omega]
        rw [e3, e1 t]
        linear_combination κ₁ * h2 + (κ₁ * y t * Lf t (e : ℂ)) * h1
  | succ q ih =>
    intro p e A A' WW X c hX hc he hpe
    obtain ⟨lam, hl⟩ := hF i j _ _ A A' WW X hX
    obtain ⟨κ₁, hκ₁, e1⟩ := hl.eq_mul hc
    obtain ⟨B, B', W₁, Y, cY', y, hY, hcY', hy, hyr⟩ := hs i j p q A A' WW X lam e Lf hX hl he hL
    have hr : B.rank = B'.rank + 2 * (e + 1) := by
      obtain ⟨-, -, a1, a2, -⟩ := hX
      obtain ⟨-, -, b1, b2, -⟩ := hY
      omega
    obtain ⟨B₂, B₂', W₂, Y₂, cY, u, κ, hY₂, hcY, hκ, hu, hid⟩ := ih p (e + 1) Y cY' hY hcY' hr (by omega)
    refine ⟨B₂, B₂', W₂, Y₂, cY, cons y u, κ₁ * κ, hY₂, hcY, mul_ne_zero hκ₁ hκ,
      fun k t => ?_, fun t => ?_⟩
    · rcases k with _ | k
      · exact ⟨(hy t).1, hyr t⟩
      · exact hu k t
    · have h1 := hid t
      have h2 := (hy t).2
      rw [show p + (q + 1) = p + q + 1 by omega]
      simp only [prod_range_succ', cons_succ, cons_zero]
      have e3 : ∏ k ∈ range q, Lf t ((e + (k + 1) + 1 : ℕ) : ℂ) = ∏ k ∈ range q, Lf t ((e + 1 + k + 1 : ℕ) : ℂ) :=
        prod_congr rfl fun k _ => by rw [show e + (k + 1) + 1 = e + 1 + k + 1 by omega]
      have e4 : ∏ k ∈ range p, Lf t ((e + (q + 1) - k : ℕ) : ℂ) = ∏ k ∈ range p, Lf t ((e + 1 + q - k : ℕ) : ℂ) :=
        prod_congr rfl fun k _ => by rw [show e + (q + 1) - k = e + 1 + q - k by omega]
      simp only [add_zero] at e3 ⊢
      rw [e3, e4, e1 t]
      linear_combination (κ₁ * ∏ k ∈ range q, Lf t ((e + 1 + k + 1 : ℕ) : ℂ)) * h2 + (κ₁ * y t) * h1

end Descent

end GlobalTheory.SqTower

namespace GlobalTheory.SqTower

open GlobalTheory.SqTower

end GlobalTheory.SqTower
end
end

