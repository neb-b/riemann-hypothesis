module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0687
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3140
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparationNormalizedBlowupUnitaryCompactificatio
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2730
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1982
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2475
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2884
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0141
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2649
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2995
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3110
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2955
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2563

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleLevelStructureAtGeometricPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section
namespace GlobalTheory.UPel.HT.EtLev

theorem epi_sp_field {k k' : Type} [Field k] [Field k'] (x' : Sp k' ⟶ Sp k) : Epi x' := by
  rw [← Spec.map_preimage x']
  have : Flat (Spec.map (Spec.preimage x')) := by
    rw [show Spec.preimage x' = CommRingCat.ofHom (Spec.preimage x').hom from rfl]; infer_instance
  have : Surjective (Spec.map (Spec.preimage x')) :=
    ⟨fun _ => ⟨IsLocalRing.closedPoint k', Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem pt_ext_of_pullback {S : Scheme.{0}} {A : Over S} {k k' : Type} [Field k] [Field k'] (x : Sp k ⟶ S)
    (x' : Sp k' ⟶ Sp k) (g₁ g₂ : Over.mk x ⟶ A)
    (h : (Over.homMk x' rfl : Over.mk (x' ≫ x) ⟶ Over.mk x) ≫ g₁ =
      (Over.homMk x' rfl : Over.mk (x' ≫ x) ⟶ Over.mk x) ≫ g₂) : g₁ = g₂ := by
  haveI := epi_sp_field x'
  apply Over.OverMorphism.ext
  have := congrArg CommaMorphism.left h
  simp only [Over.comp_left, Over.homMk_left] at this
  exact (cancel_epi x').1 this

theorem exists_etLevOver_geomPt : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), N.Coprime p → IsEtPlace b w0 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), ∃ l : D.La → (Over.mk x ⟶ o.A), IsEtLevOver o w0 r l := by
  intro p _ D R _ b N w0 r _hN hw S s o k _ _ x
  have hw0 : w0 ≠ ⊥ := by
    intro h
    have hp : (p : 𝓞 D.F) ∈ w0 := hw.2.1
    rw [h, Ideal.mem_bot] at hp
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hp)
  haveI : Finite (𝓞 D.F ⧸ w0 ^ r) := Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ hw0)
  obtain ⟨f, fadd, fsm, finj, fsurj⟩ := GlobalTheory.T.torsion_points_additive_parametrization p D R b N w0 r hw S s o k x
  have hmul : ∀ (c : D.O) (g h : Over.mk x ⟶ o.A), (g * h) ≫ o.act.act c = (g ≫ o.act.act c) * (h ≫ o.act.act c) := by
    intro c g h; haveI := o.act.hom c; exact MonObj.mul_comp _ _ _
  obtain ⟨l, ladd, llin, lker, lsurj⟩ := GlobalTheory.T.exists_morita_lattice_quotient_torsion p D w0 r hw.1 hw.2.1 (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c)
    (fun c g h => hmul c g h) (fun g => by simp only [o.act.one, Category.comp_id])
    (fun b c g => by simp only [o.act.mul, Category.assoc])
    (fun b c g => by simp only [o.act.add]; exact MonObj.comp_mul _ _ _) f fadd fsm finj fsurj
  have f0 : f 0 = 1 := by
    have h := fadd 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have tor : ∀ a, ∀ c ∈ w0 ^ r, f a ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
    intro a c hc
    rw [← fsm, (Ideal.Quotient.eq_zero_iff_mem).2 hc, zero_smul, f0]
  refine ⟨l, ladd, llin, fun y hy => (lker y).2 hy, ?_⟩
  intro k' _ _ x'
  refine ⟨fun y hy => ?_, fun g hg => ?_⟩
  · apply (lker y).1
    apply pt_ext_of_pullback x x'
    rw [hy]
    exact (MonObj.comp_one _).symm
  · obtain ⟨f', -, -, -, f'surj⟩ := GlobalTheory.T.torsion_points_additive_parametrization p D R b N w0 r hw S s o k' (x' ≫ x)
    let π : Over.mk (x' ≫ x) ⟶ Over.mk x := Over.homMk x' rfl
    have tor' : ∀ a, ∀ c ∈ w0 ^ r, (π ≫ f a) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
      intro a c hc
      rw [Category.assoc, tor a c hc, MonObj.comp_one]
    let φ : (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) → (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) :=
      fun a => (f'surj _ (tor' a)).choose
    have hφ : ∀ a, f' (φ a) = π ≫ f a := fun a => (f'surj _ (tor' a)).choose_spec
    have φinj : Function.Injective φ := fun a a' h =>
      finj (pt_ext_of_pullback x x' _ _ (by rw [← hφ, ← hφ, h]))
    obtain ⟨a', rfl⟩ := f'surj g hg
    obtain ⟨a, ha⟩ := (Finite.injective_iff_surjective.1 φinj) a'
    obtain ⟨y, hy⟩ := lsurj (f a) (tor a)
    exact ⟨y, by rw [hy, ← ha, hφ]⟩
end GlobalTheory.UPel.HT.EtLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTripleChartUnitaryBoundaryPointRigidStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tripleChart_unitary_boundary_pointRigid : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x := by
  first | exact @GlobalTheory.UCanon.uPre_of_boundary_pointRigid | exact GlobalTheory.UCanon.uPre_of_boundary_pointRigid | (intros; apply GlobalTheory.UCanon.uPre_of_boundary_pointRigid <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalTangentHarrisTaylorRepresentingFaStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_universal_tangent_harrisTaylor_representingFamily : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ F : RepFam b N, IsQProjOver F.s → Smooth F.s → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ F.X), ∃ u : Sp (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k)) ⟶ F.X, spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom ≫ u = x ∧ u ≫ F.s = spMap (algebraMap k (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k))) ≫ x ≫ F.s ∧ ∀ v : Sp (DualNumber k) ⟶ F.X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v = x → v ≫ F.s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ F.s → ∃! c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u := by
  first | (exact @GlobalTheory.UPel.HT.RepTangent.exists_univ_tangent) | (exact GlobalTheory.UPel.HT.RepTangent.exists_univ_tangent) | (intros; apply GlobalTheory.UPel.HT.RepTangent.exists_univ_tangent  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparationNormalizedBlowupUnitaryCompactificatioStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separation_normalizedBlowup_unitaryCompactification : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (d : ℕ) (J : C.Z.IdealSheafData), 1 ≤ d → (∀ x ∈ J.support, x ∉ Set.range C.i) → UValOn Xo c C.i φ J d → ∀ (S : Scheme.{0}) (π : S ⟶ pullback C.z (spMap C.b)) (j : Xo.XF c ⟶ S), GlobalTheory.Poinc.IsNormBl π (J.comap (pullback.fst C.z (spMap C.b))) → IsProper π → j ≫ π = C.iF → IsOpenImmersion j → π ⁻¹' Set.range C.iF = Set.range j → GlobalTheory.UChart.SepB Xo c φ j) := by
  first | exact @GlobalTheory.USep.sepB_of_normBl | exact GlobalTheory.USep.sepB_of_normBl | (intros; apply GlobalTheory.USep.sepB_of_normBl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyExistsUniqueClassifyScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegFamAll

theorem exists_classify_affine {g n : ℕ} (hg : 1 ≤ g) (hn : 3 ≤ n) (hodd : Odd n) (F : SFam g n (zetaAway n))
    (R : Type) [CommRing R] (t : Sp R ⟶ Sp (cycAway n)) (d : SiegPre g n (zetaAway n) t) (hd : d.Principal) :
    ∃ f : Sp R ⟶ F.X, f ≫ F.s = t ∧ SiegPB d F.univ f := by
  obtain ⟨β, rfl⟩ := GlobalTheory.SiegelRingChange.exists_spMap t
  obtain ⟨R₀, β₀, c₀, hft, hβ, hp₀, hpb⟩ := GlobalTheory.T.principalSiegel_descends_finiteType_subring g n hn hodd R β d hd
  haveI : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing ℤ R₀
  obtain ⟨f₀, hf₀, hpb₀⟩ := _root_.GlobalTheory.SiegelNoeth.classify_noetherian g n hg hn hodd F R₀ β₀ c₀ hp₀
  refine ⟨spMap R₀.subtype ≫ f₀, ?_, GlobalTheory.TChart.AbLevel.siegPB_trans hpb hpb₀⟩
  rw [Category.assoc, hf₀, ← GlobalTheory.SiegelRingChange.spMap_comp', hβ]

theorem existsUnique_classify : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n),
    ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (cycAway n)) (c : SiegPre g n (zetaAway n) s'), c.Principal →
      ∃! f : S ⟶ F.X, f ≫ F.s = s' ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F S s' c hc
  obtain ⟨f, hf, hpf⟩ := _root_.GlobalTheory.SiegZar.classified_of_local g n hg hn hodd F S s' c hc (fun x => by
    let 𝒰 := S.affineOpenCover
    let j : Sp (𝒰.X (𝒰.idx x)) ⟶ S := 𝒰.f (𝒰.idx x)
    have hid : j ≫ s' = (j ≫ s') ≫ spMap (RingHom.id (cycAway n)) := by simp [spMap]
    have key := GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n) (zetaAway n)
      (RingHom.id _) S (Sp (𝒰.X (𝒰.idx x))) s' (j ≫ s') j rfl hid
    obtain ⟨cV, hcV⟩ := key.1 c
    have hpV : cV.Principal := key.2.1 c cV hcV hc
    obtain ⟨fV, hfV, hpbV⟩ := exists_classify_affine hg hn hodd F (𝒰.X (𝒰.idx x)) (j ≫ s') cV hpV
    exact ⟨Sp (𝒰.X (𝒰.idx x)), j, cV, inferInstance, 𝒰.covers x, hcV, fV, hfV, hpbV⟩)
  exact ⟨f, ⟨hf, hpf⟩, fun f' hf' => _root_.GlobalTheory.SiegUniq.eq_of_siegPB g n hg hn hodd F S s' c f' f hf'.1 hf hf'.2 hpf⟩

end GlobalTheory.SiegFamAll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelToroidalCompactificationPolarisedCharts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.SiegJoin.siegelToroidalPolCharts : GlobalTheory.Published.SiegelToroidalPolCharts :=
  GlobalTheory.SiegJoin.siegelToroidalPolCharts_of_steps5 _root_.GlobalTheory.SiegelTor.exists_sFam_cycAway _root_.GlobalTheory.SiegMinTop.minSt5 _root_.GlobalTheory.PoincTop.poinSt
    _root_.GlobalTheory.SiegJoin.chartSt5_holds GlobalTheory.SiegDescent.descSt5
end

