module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIntegralFramedPointBaseChangeCdvrTransitiv
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmallPointsSubstitutionAlgHomSinglePoint
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SymmetricTranslatesMultiplicationPullbackDescrip
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0130
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0017

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsFiniteExtensionIntegralFramedPointLiftCove
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.CoverPoint

theorem exists_finite_subfield {R F k : Type} [CommRing R] [Field F] [Field k] [Algebra F k] [Algebra.IsAlgebraic F k]
    {X : Scheme.{0}} (s : X ⟶ Sp R) [LocallyOfFiniteType s] (ρ : R →+* F) (p : Sp k ⟶ X)
    (hp : p ≫ s = spMap ((algebraMap F k).comp ρ)) :
    ∃ K : IntermediateField F k, FiniteDimensional F K ∧ ∃ q : Sp K ⟶ X, spMap (algebraMap K k) ≫ q = p := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hpt, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (p (IsLocalRing.closedPoint k))) isOpen_univ
  have hU : IsAffineOpen U := hU
  obtain ⟨f, hf⟩ : ∃ f : Γ(X, U) ⟶ CommRingCat.of k, Spec.map f ≫ hU.fromSpec = p := by
    refine ⟨Spec.preimage (IsOpenImmersion.lift hU.fromSpec p ?_), ?_⟩
    · rintro _ ⟨y, rfl⟩
      rw [hU.range_fromSpec, Subsingleton.elim (α := PrimeSpectrum k) y (IsLocalRing.closedPoint k)]
      exact hpt
    · rw [Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _
  obtain ⟨g, hg⟩ : ∃ g : CommRingCat.of R ⟶ Γ(X, U), Spec.map g = hU.fromSpec ≫ s :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  have hgf : g ≫ f = CommRingCat.ofHom ((algebraMap F k).comp ρ) :=
    Spec.map_injective (by
      rw [Spec.map_comp, hg, ← Category.assoc, hf]
      exact hp)
  have hV : ∀ r : R, f.hom (g.hom r) = algebraMap F k (ρ r) := fun r =>
    congrArg (fun q => q.hom r) hgf
  have hft : g.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map g) := by rw [hg]; infer_instance
    exact HasRingHomProperty.Spec_iff.1 this
  let _ : Algebra R Γ(X, U) := g.hom.toAlgebra
  obtain ⟨t, ht⟩ := (show Algebra.FiniteType R Γ(X, U) from hft).out
  let S : Set k := (t.image f.hom : Finset k)
  let K := IntermediateField.adjoin F S
  refine ⟨K, IntermediateField.finiteDimensional_adjoin fun x _ =>
    (Algebra.IsAlgebraic.isAlgebraic x).isIntegral, ?_⟩
  have hr : ∀ a, f.hom a ∈ K := fun a => by
    have ha : a ∈ Algebra.adjoin R (t : Set Γ(X, U)) := ht ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin F S (Finset.mem_image_of_mem _ hx)
    | algebraMap r => exact (hV r).symm ▸ K.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  let f' : Γ(X, U) ⟶ CommRingCat.of K := CommRingCat.ofHom (f.hom.codRestrict K hr)
  refine ⟨Spec.map f' ≫ hU.fromSpec, ?_⟩
  change Spec.map _ ≫ Spec.map f' ≫ hU.fromSpec = _
  rw [← hf, ← Spec.map_comp_assoc]
  rfl

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem epi_spMap {K k : Type} [Field K] [Field k] (f : K →+* k) : Epi (spMap f) := by
  have h1 : Flat (spMap f) := by
    let _ := f.toAlgebra
    exact HasRingHomProperty.Spec_iff.2 (show (algebraMap K k).Flat from
      RingHom.flat_algebraMap_iff.2 inferInstance)
  have h2 : Surjective (spMap f) := ⟨fun x => ⟨IsLocalRing.closedPoint k, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem exists_ext_lift_to_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), T.FinRes → ∃ (T' : CDVR) (iT : T.Fr →+* T'.Fr) (e : ℕ) (y' : IntFr Xo c T' (iT.comp io)) (io₂ : d.c₂.F →+* T'.Fr) (y₂ : IntFr d.Xo₂ d.c₂ T' io₂), IsExt y iT e y' ∧ T'.FinRes ∧ (∀ a : c.F, io₂ (d.eF a) = iT (io a)) ∧ (letI := (iT.comp io).toAlgebra; letI := io₂.toAlgebra; FrOver d y₂.1 y'.1) := by
  intro E _ _ _ H Dw l Xo c n d hd T io y hT
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  let j : d.c₂.F →+* c.F := d.eF.symm.toAlgHom.toRingHom
  have hj : ∀ a : c.F, j (d.eF a) = a := fun a => d.eF.symm_apply_apply a
  let k := AlgebraicClosure T.Fr
  have key : ∃ p : Sp k ⟶ d.Xo₂.X, p ≫ d.r = spMap (algebraMap T.Fr k) ≫ xOf y ∧
      p ≫ d.Xo₂.s = spMap ((algebraMap T.Fr k).comp
        ((io.comp j).comp (IntermediateField.inclusion d.c₂.le).toRingHom)) := by
    letI := io.toAlgebra
    letI : Algebra c.F k := ((algebraMap T.Fr k).comp io).toAlgebra
    letI : Algebra d.c₂.F k := ((algebraMap T.Fr k).comp (io.comp j)).toAlgebra
    let ψ : T.Fr →ₐ[c.F] k := { algebraMap T.Fr k with commutes' := fun _ => rfl }
    obtain ⟨z, hz⟩ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c T.Fr k ψ y.1
    obtain ⟨z₂, hz₂⟩ := hd.2.2.2.2.2.2.1 k (fun a => by
      change algebraMap T.Fr k (io (j (d.eF a))) = algebraMap T.Fr k (io a)
      rw [hj]) z
    exact ⟨z₂.x, hz₂.1.trans hz.1, z₂.x_over⟩
  obtain ⟨p, hp1, hp2⟩ := key
  haveI := d.Xo₂.smooth
  haveI : Smooth d.Xo₂.s := SmoothOfRelativeDimension.smooth Dw.dim _
  obtain ⟨K, hK, q, hq⟩ := exists_finite_subfield d.Xo₂.s _ p hp2
  haveI := epi_spMap (algebraMap K k)
  have hKk : (algebraMap K k).comp (algebraMap T.Fr K) = algebraMap T.Fr k := rfl
  have hq1 : q ≫ d.r = spMap (algebraMap T.Fr K) ≫ xOf y := by
    rw [← cancel_epi (spMap (algebraMap K k)), ← Category.assoc, hq, hp1, ← Category.assoc, spMap_comp', hKk]
  have hq2 : q ≫ d.Xo₂.s = spMap ((algebraMap T.Fr K).comp
      ((io.comp j).comp (IntermediateField.inclusion d.c₂.le).toRingHom)) := by
    rw [← cancel_epi (spMap (algebraMap K k)), ← Category.assoc, hq, hp2, spMap_comp']
    rfl
  obtain ⟨T', iT, e, ψ, φ, he, hv, hψ, -, hfin⟩ := GlobalTheory.PlaceExtField.exists_cdvr_finite_extension T K
  have hψ' : ψ.toRingHom.comp (algebraMap T.Fr K) = iT := RingHom.ext hψ
  obtain ⟨⟨y', hy'⟩, hx⟩ := _root_.GlobalTheory.PlaceInt.exists_isExt_and_trans E H Dw l Xo c T T' io y iT e he hv
  have hx' := (hx y' hy').1
  let io₂ : d.c₂.F →+* T'.Fr := iT.comp (io.comp j)
  have hio : ∀ a : c.F, io₂ (d.eF a) = iT (io a) := fun a => by
    change iT (io (j (d.eF a))) = _
    rw [hj]
  letI := (iT.comp io).toAlgebra
  letI := io₂.toAlgebra
  obtain ⟨y₂, -, hy₂⟩ := (GlobalTheory.frames_lift_to_cover hL E H Dw l Xo c n d).1 T'.Fr hio y'.1
    (spMap ψ.toRingHom ≫ q)
    (by rw [Category.assoc, hq1, ← Category.assoc, spMap_comp', hψ']; exact hx'.symm)
    (by rw [Category.assoc, hq2, spMap_comp', ← RingHom.comp_assoc, hψ']; rfl)
  exact ⟨T', iT, e, y', io₂, ⟨y₂, GlobalTheory.Frames.allTest_of_secBaseChange hL.secBaseChange E H Dw d.l₂ d.Xo₂ d.c₂ _ y₂,
    GlobalTheory.T.integral_of_framed_point_over_integral E H Dw l Xo c n d T' (iT.comp io) io₂ y' hio y₂ hy₂⟩, hy', hfin hT, hio, hy₂⟩

end GlobalTheory.CoverPoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.GeneratorSectionExpansionNuNonneg
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
namespace GlobalTheory.GeneratorNu

theorem nuGe_of_thFrame {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
    (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ) (hQ : IsQ D.toPre ϖ Q) (F : Type) [Field F]
    [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v) (θ : Fam D.toPre F 1)
    (hθ : GlobalTheory.PowGerm.ThFrame D ϖ F θ) : NuGe D Q F v 1 θ 0 := by
  obtain ⟨g, gF, hg, he, -⟩ := hθ
  refine (n1a V ϖ hϖ D Q hQ F v hv 1 le_rfl {0} (fun χ => ⟨0, Finset.mem_singleton_self _, χ, by simp⟩) θ 0).2 ?_
  intro α hα
  rw [Finset.mem_singleton] at hα
  subst hα
  refine ⟨1, fun _ => 1, fun _ => g, fun _ => gF, fun _ => hg, fun _ => ?_, fun j => ?_⟩
  · rw [QForm.Q_zero hϖ D hQ]; simp
  · simp [DegPre.constBF, he j]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (P : PELUnif (maximalIdeal T.V) I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (xF : Sp F ⟶ Xo.X) (h : ptO Xo xF ⟶ ptO Xo (xOf y)), h.left = spMap (algebraMap T.Fr F) → ∀ hh : SecN Xo xF 1, IsPullSec Xo.univ.t.G Xo.univ.t.PP.L ((1 : ℕ) : ℤ) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (sOf1 y) hh → (∀ σ s, SecTieF I P F xF 1 σ hh → P.U.toUnifPre.ExpandsG F 1 σ s → NuGe P.D Q F v 1 s 0) := by
  intro E _ _ _ H Dw l Xo c T io y I P _ ϖ hϖ Q hQ F _ _ _ _ _ v hv xF h hl hh hpull σ s htie hexp
  letI := io.toAlgebra
  letI : Algebra c.F F := ((algebraMap T.Fr F).comp io).toAlgebra
  let φ : T.Fr →ₐ[c.F] F := { algebraMap T.Fr F with commutes' := fun _ => rfl }
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ φ y.1
  have hx : xF = z.x := by
    have := Over.w h
    rw [hl] at this
    exact this.symm.trans hz.1.symm
  subst hx
  have hs : ∀ j, hh.f j = z.s.f j := by
    obtain ⟨-, -, pm, h1, h2, h3⟩ := hz
    have e : pm = (h ▷ Xo.univ.t.G).left := by
      apply pullback.hom_ext
      · refine h2.trans ?_
        have := congrArg Over.Hom.left (whiskerRight_fst h Xo.univ.t.G)
        rw [Over.comp_left, Over.comp_left, hl] at this
        exact this.symm
      · refine h1.trans ?_
        have := congrArg Over.Hom.left (whiskerRight_snd h Xo.univ.t.G)
        rw [Over.comp_left] at this
        exact this.symm
    subst e
    intro j
    exact (hpull j).trans (h3 j _)
  have hs' : hh = z.s := by
    cases hh
    rcases hzs : z.s with ⟨f, hf⟩
    rw [hzs] at hs
    congr
    exact funext hs
  subst hs'
  exact nuGe_of_thFrame hϖ P.D Q hQ F v hv s (GlobalTheory.T.thetaFrame_expansion_framedPoint_generator E H Dw l Xo c T io y.1 I P ϖ hϖ F φ rfl z hz σ s htie hexp)

end GlobalTheory.GeneratorNu
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.GermSymmetricTranslateFibreEqModelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.germ_symmetricTranslate_fibre_eq_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (k : ℕ), Odd k → ∀ (a : ptO Xo (xOf y) ⟶ Xo.univ.t.G) (aV : baseOver (Sp T.V) ⟶ C.I.G.G) (r : Sp T.Fr ⟶ C.I.t'.G.left), r ≫ C.I.t'.G.hom = 𝟙 _ → r ≫ C.I.m1.φ = a.left → r ≫ C.I.m2.φ = spMap (algebraMap T.V T.Fr) ≫ aV.left → ∀ U : ThetaGrp C.I.G.G C.I.G.PP.L (k : ℤ) (baseOver (Sp T.V)), SymLift C.I.G.G C.I.G.PP.L (k : ℤ) k aV U → ∀ (F F' : SecN Xo (xOf y) k) (f f' : PS T.V 1 (chD C.ch)), Regular C k F → GermIs C k F f → Moves Xo a F F' → (∀ σ σ' : LB.Sec (LPow C.I.G.G C.I.G.PP.L (k : ℤ) (baseOver (Sp T.V))), IsGermG C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.actT C.eT C.wPT k σ f → IsActOf C.I.G.G C.I.G.PP.L (k : ℤ) U σ σ' → IsGermG C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.actT C.eT C.wPT k σ' f') → GermIs C k F' f' := by
  first | exact @GlobalTheory.TransportGerm.germIs_translate | exact GlobalTheory.TransportGerm.germIs_translate | (intros; apply GlobalTheory.TransportGerm.germIs_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MixedTranslatePullbackEqReachedSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

theorem uu_eq_pull_reach : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (N n' A Bn : ℕ) (α β : 𝓞 E), Odd N → (N : 𝓞 E) = β * α * n' → α * H.bar α = (A : 𝓞 E) → β * H.bar β = (Bn : 𝓞 E) → ∀ (s : SecN Xo x 1) (x₁ x₂ : (ptO Xo x ⟶ Xo.univ.t.G)) (F), x₁ ^ (N ^ 2) = 1 → x₂ ^ (N ^ 2) = 1 → (x₁ ≫ Xo.univ.t.act.act (α * β)) ^ (n' ^ 2) = 1 → (x₂ ≫ Xo.univ.t.act.act β) ^ (n' ^ 2 * A) = 1 → IsUUOver Xo.univ.t.G Xo.univ.t.PP N s x₁ x₂ F → N ^ 2 = n' ^ 2 * A * Bn ∧ ∃ hh : SecN Xo x (n' ^ 2 * A), Reach Xo s (n' ^ 2 * A) hh ∧ Pulls Xo β hh (sqN Xo N F) := by
  intro E _ _ _ H Dw l Xo S _ x N n' A Bn α β hodd hN hα hβ s x₁ x₂ F h₁ h₂ h₁' h₂' hUU
  have hαβ : (α * β) * H.bar (α * β) = ((A * Bn : ℕ) : 𝓞 E) := by
    rw [map_mul, Nat.cast_mul, ← hα, ← hβ]; ring
  have hn : (n' : 𝓞 E) * H.bar (n' : 𝓞 E) = ((n' ^ 2 : ℕ) : 𝓞 E) := by
    rw [map_natCast, Nat.cast_pow]; ring
  have hNN : (N : 𝓞 E) * H.bar (N : 𝓞 E) = ((N ^ 2 : ℕ) : 𝓞 E) := by
    rw [map_natCast, Nat.cast_pow]; ring
  have hN' : (n' : 𝓞 E) * (α * β) = (N : 𝓞 E) := by rw [hN]; ring
  have hsq : N ^ 2 = n' ^ 2 * A * Bn := by
    have h : ((N ^ 2 : ℕ) : 𝓞 E) = ((n' ^ 2 * A * Bn : ℕ) : 𝓞 E) := by
      rw [← hNN, ← hN', map_mul, mul_assoc (n' ^ 2), Nat.cast_mul (n' ^ 2), ← hn, ← hαβ]; ring
    exact_mod_cast h
  have hoN : Odd (N ^ 2) := hodd.pow
  have ho3 : Odd (n' ^ 2 * A * Bn) := hsq ▸ hoN
  have ho2 : Odd (n' ^ 2 * A) := (Nat.odd_mul.1 ho3).1
  have ho1 : Odd (n' ^ 2) := (Nat.odd_mul.1 ho2).1
  have hoA : Odd A := (Nat.odd_mul.1 ho2).2
  have hlev : n' ^ 2 = 1 ∨ 4 ≤ n' ^ 2 := by
    rcases n' with _ | _ | m
    · simp at ho1
    · left; rfl
    · right; exact Nat.pow_le_pow_left (n := 2) (by omega) 2
  refine ⟨hsq, ?_⟩
  obtain ⟨F₀, F₁, hF₀, hF₁, hF₂⟩ := ((_root_.GlobalTheory.PlaceInt.uu_through_moves E H Dw l Xo S x N hodd s).1 x₁ x₂ F h₁ h₂).1 hUU
  obtain ⟨G₀, hG₀, -⟩ := _root_.GlobalTheory.existsUnique_pulls E H Dw l Xo S x (n' : 𝓞 E) (n' ^ 2) 1 (n' ^ 2) hn (Nat.one_mul _).symm s
  obtain ⟨G₁, hG₁, -⟩ := (_root_.GlobalTheory.existsUnique_moves E H Dw l Xo S x (n' ^ 2) ho1 _ h₁' G₀).1
  obtain ⟨K₁, hK₁, -⟩ := _root_.GlobalTheory.existsUnique_pulls E H Dw l Xo S x α A (n' ^ 2) (n' ^ 2 * A) hα rfl G₁
  obtain ⟨hh, hhh, -⟩ := (_root_.GlobalTheory.existsUnique_moves E H Dw l Xo S x (n' ^ 2 * A) ho2 _ h₂' K₁).1
  refine ⟨hh, ?_, ?_⟩
  · refine Reach.move _ _ K₁ hh (Reach.pull (n' ^ 2) A _ α G₁ K₁ ?_ hlev hoA hα rfl hK₁) hhh
    refine Reach.move _ _ G₀ G₁ ?_ hG₁
    exact Reach.pull 1 (n' ^ 2) _ _ s G₀ Reach.base (Or.inl rfl) ho1 hn (Nat.one_mul _).symm hG₀
  · have hsq' : N ^ 2 = n' ^ 2 * (A * Bn) := by rw [hsq, Nat.mul_assoc]
    obtain ⟨P, hP, -⟩ := _root_.GlobalTheory.existsUnique_pulls E H Dw l Xo S x (α * β) (A * Bn) (n' ^ 2) (N ^ 2) hαβ hsq' G₀
    obtain ⟨Q, hQ, -⟩ := _root_.GlobalTheory.existsUnique_pulls E H Dw l Xo S x β Bn (n' ^ 2 * A) (N ^ 2) hβ hsq K₁
    obtain ⟨R, hR, -⟩ := _root_.GlobalTheory.existsUnique_pulls E H Dw l Xo S x β Bn (n' ^ 2 * A) (N ^ 2) hβ hsq hh
    have hPN : Pulls Xo (N : 𝓞 E) s P := hN' ▸ _root_.GlobalTheory.PullComp.pulls_mul E H Dw l Xo S x _ _ _ _ _ s G₀ P hG₀ hP
    have hPF : P = F₀ :=
      (_root_.GlobalTheory.existsUnique_pulls E H Dw l Xo S x (N : 𝓞 E) (N ^ 2) 1 (N ^ 2) hNN (Nat.one_mul _).symm s).unique hPN hF₀
    have hQ' : Pulls Xo (α * β) G₁ Q := _root_.GlobalTheory.PullComp.pulls_mul E H Dw l Xo S x _ _ _ _ _ G₁ K₁ Q hK₁ hQ
    have hm₁ : Moves Xo x₁ P Q :=
      _root_.GlobalTheory.PlaceInt.moves_of_pulls E H Dw l Xo S x (α * β) (A * Bn) _ _ hαβ hsq' hoN _ x₁ rfl h₁ G₀ G₁ P Q hG₁ hP hQ'
    have hQF : Q = F₁ := (_root_.GlobalTheory.existsUnique_moves E H Dw l Xo S x (N ^ 2) hoN x₁ h₁ F₀).1.unique (hPF ▸ hm₁) hF₁
    have hm₂ : Moves Xo x₂ Q R :=
      _root_.GlobalTheory.PlaceInt.moves_of_pulls E H Dw l Xo S x β Bn _ _ hβ hsq hoN _ x₂ rfl h₂ K₁ hh Q R hhh hQ hR
    have hRF : R = sqN Xo N F := (_root_.GlobalTheory.existsUnique_moves E H Dw l Xo S x (N ^ 2) hoN x₂ h₂ F₁).1.unique (hQF ▸ hm₂) hF₂
    exact hRF ▸ hR

end GlobalTheory.PlaceInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NormalisedPullbackSectionNuNonneg
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm

namespace GlobalTheory.NuPull

theorem nuGe_zero_of_pulls : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (P : PELUnif (maximalIdeal T.V) I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (xF : Sp F ⟶ Xo.X) (h : ptO Xo xF ⟶ ptO Xo (xOf y)), h.left = spMap (algebraMap T.Fr F) → ∀ (k N k' : ℕ) (a : 𝓞 E) (hh : SecN Xo xF k) (hh' : SecN Xo xF k'), (k = 1 ∨ 4 ≤ k) → 0 < N → a * H.bar a = (N : 𝓞 E) → k' = k * N → Pulls Xo a hh hh' → (∀ σ s, SecTieF I P F xF k σ hh → P.U.toUnifPre.ExpandsG F k σ s → NuGe P.D Q F v k s 0) → (∀ σ s, SecTieF I P F xF k' σ hh' → P.U.toUnifPre.ExpandsG F k' σ s → NuGe P.D Q F v k' s 0) := by
  intro E _ _ _ H Dw l Xo c T io y I P hT ϖ hϖ Q hQ F _ _ _ _ _ v hv xF h hl k N k' a hh hh' hk hN ha e hP h0 σ' s' ht' hs'
  letI := H.starRing
  subst e
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hk₁ : 1 ≤ k := by omega
  have ha' : a * star a = (N : 𝓞 E) := ha
  have hex := _root_.GlobalTheory.tied_section_expansion_existsUnique E H Dw l Xo c T io y I P hT ϖ hϖ Q hQ F v hv xF h hl
  obtain ⟨⟨σ, hσ, -⟩, hu⟩ := hex k hk₁ hh
  obtain ⟨s, hs, -⟩ := hu σ hσ
  obtain ⟨uΨ, huΨ, -, -⟩ := P.w0
  have hLB : P.D.toPre.P.L.IsLB := P.D.toPre.P.isLB
  obtain ⟨s'', hs''⟩ := exists_pullAl P.D F hLB P.oD H.w0 uΨ huΨ a N ha' hN k s
    (pullSecs_fe' P.D F hL.globalFns hLB P.oD H.w0 P.w0 uΨ huΨ a N ha' hN k s)
  have hE := GlobalTheory.T.normalisedPullback_section_expands_family E H Dw l Xo c T io y.1 I P F xF hσ.1 a N k (k * N) rfl ha' hN hk σ hh s σ' hh' s''
    hσ hs hP ht' hs''
  obtain rfl : s' = s'' := ((hex (k * N) (Nat.mul_pos hk₁ hN) hh').2 σ' ht').unique hs' hE
  exact (GlobalTheory.twisting_statements_of_laws hL GlobalTheory.twistBaseChange).2.2 T.V ϖ hϖ P.D Q hQ F v hv (𝓞 E) P.oD H.w0 P.w0
    a N hN ha' (by rw [_root_.mul_comm]; exact ha') k hk₁ s s' hs'' 0 (h0 σ s hσ hs)

end GlobalTheory.NuPull
end

