module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1979
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0539
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0529
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1944
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0508
public import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1044
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1896
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1995
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcVarZpowInjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.BetaAtClosedPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1998
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1966
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0556
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverRefinementGenericDegree
section
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

namespace GlobalTheory.CoverDeg

theorem residueDegree_eq_one_of_surjectiveOnStalks {X Y : Scheme} (f : X ⟶ Y) [SurjectiveOnStalks f]
    (x : X) : f.residueDegree x = 1 := by
  have hs : Function.Surjective (f.residueFieldMap x).hom := by
    intro y
    obtain ⟨s, rfl⟩ := Scheme.residue_surjective X x y
    obtain ⟨t, rfl⟩ := SurjectiveOnStalks.stalkMap_surjective (f := f) x s
    exact ⟨Y.residue (f x) t, rfl⟩
  letI : Algebra (Y.residueField (f x)) (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
  have hb : Function.Bijective (algebraMap (Y.residueField (f x)) (X.residueField x)) :=
    ⟨RingHom.injective (algebraMap (Y.residueField (f x)) (X.residueField x)), hs⟩
  have e := (AlgEquiv.ofBijective (Algebra.ofId (Y.residueField (f x)) (X.residueField x)) hb).toLinearEquiv
  unfold Scheme.Hom.residueDegree
  rw [← e.finrank_eq, Module.finrank_self]

end GlobalTheory.CoverDeg

namespace GlobalTheory.CoverDeg

theorem j_genericPoint {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) :
    V.j (genericPoint V.G) = genericPoint V.X := by
  haveI := V.int
  haveI := V.intG

  let η : Sp F := ⟨⊥, Ideal.isPrime_bot⟩
  have hη : ∀ w : Sp F, (spMap (algebraMap (𝓞 F) F) w).asIdeal = ⊥ := by
    intro w
    have hw : w.asIdeal = ⊥ := by
      rcases Ideal.eq_bot_or_top w.asIdeal with h | h
      · exact h
      · exact absurd h w.isPrime.ne_top
    change Ideal.comap _ w.asIdeal = ⊥
    rw [hw, ← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).mp (NumberField.RingOfIntegers.coe_injective)
  have hw := V.pb.w
  have hpj : ∀ z : V.G, (V.p (V.j z)).asIdeal = ⊥ := by
    intro z
    have : V.p (V.j z) = spMap (algebraMap (𝓞 F) F) ((V.π ≫ Y.str) z) := by
      rw [← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply]
    rw [this, hη]
  have hpX : V.p (genericPoint V.X) = spMap (algebraMap (𝓞 F) F) η := by
    apply PrimeSpectrum.ext
    rw [hη]
    have hs : genericPoint V.X ⤳ V.j (genericPoint V.G) := genericPoint_specializes _
    have := (PrimeSpectrum.le_iff_specializes _ _).mpr (hs.map V.p.continuous)
    exact le_bot_iff.mp ((hpj _) ▸ this)
  obtain ⟨w, hw'⟩ : genericPoint V.X ∈ Set.range (Limits.pullback.fst V.p (spMap (algebraMap (𝓞 F) F))) := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨η, hpX.symm⟩
  have hz : V.j (V.pb.isoPullback.inv w) = genericPoint V.X := by
    have e : V.pb.isoPullback.inv ≫ V.j = Limits.pullback.fst V.p (spMap (algebraMap (𝓞 F) F)) := by
      rw [Iso.inv_comp_eq, V.pb.isoPullback_hom_fst]
    rw [← hw', ← e, Scheme.Hom.comp_apply]
  have h1 : V.j (genericPoint V.G) ⤳ genericPoint V.X := by
    rw [← hz]; exact (genericPoint_specializes _).map V.j.continuous
  exact (h1.antisymm (genericPoint_specializes _)).eq

end GlobalTheory.CoverDeg

namespace GlobalTheory.CoverDeg

theorem j_residueDegree {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) (x : V.G) :
    V.j.residueDegree x = 1 := by
  haveI := CoverHt.isPreimmersion_j V
  exact residueDegree_eq_one_of_surjectiveOnStalks V.j x

theorem map_genericPoint_and_deg : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y)
    (V' : Cover Y) (b : V'.X ⟶ V.X) (hb : b ≫ V.p = V'.p) (g : V'.G ⟶ V.G),
    V'.j ≫ b = g ≫ V.j → g ≫ V.π = V'.π → g (genericPoint V'.G) = genericPoint V.G →
    b (genericPoint V'.X) = genericPoint V.X ∧ b.residueDegree (genericPoint V'.X) * V.deg = V'.deg := by
  intro F _ _ Y V V' b _ g hjb hπ hg
  have hpt : b (genericPoint V'.X) = genericPoint V.X := by
    rw [← j_genericPoint V', ← Scheme.Hom.comp_apply, hjb, Scheme.Hom.comp_apply, hg, j_genericPoint V]
  refine ⟨hpt, ?_⟩
  have h1 := CurveDegreesCompare.residueDegree_comp V'.j b (genericPoint V'.G)
  have h2 := CurveDegreesCompare.residueDegree_comp g V.j (genericPoint V'.G)
  have h3 := CurveDegreesCompare.residueDegree_comp g V.π (genericPoint V'.G)
  rw [hjb, h2] at h1
  rw [j_residueDegree, j_residueDegree, mul_one, one_mul, j_genericPoint V'] at h1
  unfold Cover.deg
  rw [← hπ, h3, hg, h1, mul_comm]

end GlobalTheory.CoverDeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineEqDeRhamOfSmoothLiftComparison
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

namespace GlobalTheory.CrysLift

variable {R : Type} [CommRing R] {X : Scheme.{0}}

def diagSec (X : Scheme.{0}) : AffOp X ⥤ (Pair (𝟙 X))ᵒᵖ :=
  (Monotone.functor (f := fun U : X.affineOpens ↦ (⟨(U, U), by simp⟩ : Pair (𝟙 X))) fun _ _ h ↦
      Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨h, h⟩)).op

def diagCoef (s : X ⟶ Sp R) : CoefMap (RingHom.id R) (OPair (𝟙 X) s) (OAff s) where
  G := diagSec X
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

theorem diag_res_degree_one (s : X ⟶ Sp R) (c : HH1 s) :
    pullHyp1 (diagCoef s) (pullHyp1 (pairRes (𝟙 X) s) c) = c := by
  rw [← pullHyp1_comp]
  exact (pullHyp1_eq_of_natTrans _ (CoefMap.id _) { app U := 𝟙 U }
    (fun U b ↦ mp_id (OAff s) U b) c).trans (pullHyp1_id c)

theorem diag_res_degree_two (s : X ⟶ Sp R) (c : HH2 s) :
    pullHyp2 (diagCoef s) (pullHyp2 (pairRes (𝟙 X) s) c) = c := by
  rw [← pullHyp2_comp]
  exact (pullHyp2_eq_of_natTrans _ (CoefMap.id _) { app U := 𝟙 U }
    (fun U b ↦ mp_id (OAff s) U b) c).trans (pullHyp2_id c)

theorem eq_of_isPull1 {s : X ⟶ Sp R} (h : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R)) {c c' : HH1 s}
    (e : IsPull1 h c c') : c = c' := by
  have e' : pullHyp1 (pairRes (𝟙 X) s) c = pullHyp1 (pairRes (𝟙 X) s) c' :=
    (isPull1_id h c).symm.trans e
  rw [← diag_res_degree_one s c, e', diag_res_degree_one]

theorem eq_of_isPull2 {s : X ⟶ Sp R} (h : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R)) {c c' : HH2 s}
    (e : IsPull2 h c c') : c = c' := by
  have e' : pullHyp2 (pairRes (𝟙 X) s) c = pullHyp2 (pairRes (𝟙 X) s) c' :=
    (isPull2_id h c).symm.trans e
  rw [← diag_res_degree_two s c, e', diag_res_degree_two]

theorem red_of {R₀ : Type} [CommRing R₀] {I : Ideal R} {π : R →+* R₀} (hπ : Function.Surjective π)
    (hI : RingHom.ker π = I) {X₀ : Scheme.{0}} {s : X ⟶ Sp R} {s₀ : X₀ ⟶ Sp R₀} {i : X₀ ⟶ X}
    (hp : IsPullback i s₀ s (spMap π)) :
    ∃ s₀' : X₀ ⟶ Sp (R ⧸ I), IsPullback i s₀' s (spMap (Ideal.Quotient.mk I)) ∧
      s₀ ≫ spMap π = s₀' ≫ spMap (Ideal.Quotient.mk I) := by
  subst hI
  let e := RingHom.quotientKerEquivOfSurjective hπ
  have he : (e : R ⧸ RingHom.ker π →+* R₀).comp (Ideal.Quotient.mk _) = π := RingHom.ext fun _ ↦ rfl
  have hs : spMap π = spMap (e : R ⧸ RingHom.ker π →+* R₀) ≫ spMap (Ideal.Quotient.mk _) := by
    conv_lhs => rw [← he]
    show Spec.map _ = Spec.map _ ≫ Spec.map _; rw [← Spec.map_comp]; rfl
  have : IsIso (CommRingCat.ofHom (e : R ⧸ RingHom.ker π →+* R₀)) := e.toCommRingCatIso.isIso_hom
  refine ⟨s₀ ≫ spMap (e : R ⧸ RingHom.ker π →+* R₀), ?_, by rw [hs, Category.assoc]⟩
  exact hp.of_iso (Iso.refl _) (Iso.refl _) (asIso (spMap (e : R ⧸ RingHom.ker π →+* R₀))) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp [hs])

end GlobalTheory.CrysLift

namespace GlobalTheory.CrysLift

open GlobalTheory.SmoothLift

theorem crystallineDeRham_of_smoothLift : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.CrystallineDeRham := by
  rintro ⟨e₁, e₂, -, -, hnat⟩ R _ I κ hκ R₀ _ π hπ hI X X₀ s s₀ i hs hsep hqc hp m
  have hid : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _
  have : IsIso (spMap (RingHom.id R)) := by rw [hid]; infer_instance
  let D : Data :=
    { R := R, I := ⊥, κ := dp0 R, nil := isDPNilpotent_bot R, X := X, X₀ := X, s := s, t := s, i := 𝟙 X,
      smooth := hs, sep := hsep, qc := hqc,
      red := by
        obtain ⟨s', h1, h2⟩ := red_of (π := RingHom.id R) Function.surjective_id
          ((RingHom.injective_iff_ker_eq_bot _).1 Function.injective_id)
          (IsPullback.of_horiz_isIso (fst := 𝟙 X) (g := spMap (RingHom.id R)) (snd := s) (f := s)
            ⟨by rw [show spMap (RingHom.id R) = 𝟙 _ from Spec.map_id _, Category.id_comp, Category.comp_id]⟩)
        refine ⟨s', h1, ?_⟩
        rw [← h2, show spMap (RingHom.id R) = 𝟙 _ from Spec.map_id _, Category.comp_id] }
  let D' : Data :=
    { R := R, I := I, κ := κ, nil := hκ, X := X, X₀ := X₀, s := s, t := s₀ ≫ spMap π, i := i,
      smooth := hs, sep := hsep, qc := hqc,
      red := by
        obtain ⟨s', h1, h2⟩ := red_of hπ hI hp
        exact ⟨s', h1, h2⟩ }
  have h : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R) := by
    rw [show spMap (RingHom.id R) = 𝟙 _ from Spec.map_id _, Category.id_comp, Category.comp_id]
  obtain ⟨h1, h2⟩ := hnat D D' (RingHom.id R) (𝟙 X) i h m (by simp [D, D'])
  have k1 : ∀ c, m.pull1 c = ((e₁ D).trans (e₁ D').symm) c := fun c ↦
    ((e₁ D').symm_apply_apply _).symm.trans (congrArg (e₁ D').symm (eq_of_isPull1 h (h1 c)).symm)
  have k2 : ∀ c, m.pull2 c = ((e₂ D).trans (e₂ D').symm) c := fun c ↦
    ((e₂ D').symm_apply_apply _).symm.trans (congrArg (e₂ D').symm (eq_of_isPull2 h (h2 c)).symm)
  exact ⟨(funext k1 : (⇑m.pull1 : _ → _) = _) ▸ ((e₁ D).trans (e₁ D').symm).bijective,
    (funext k2 : (⇑m.pull2 : _ → _) = _) ▸ ((e₂ D).trans (e₂ D').symm).bijective⟩

end GlobalTheory.CrysLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeValueTimesThetaFramesEntire
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.CubHol

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

theorem cubF_differentiable (ν : NumOf D ℂ N) (d : AB N.toNumB g) (geo : Geo ν d) (x y : Fin g → ℂ) :
    Differentiable ℂ (cubF d x y) := by
  intro z₀
  let j : thK → D.P.L.ι := fun I => ν.J (pt3 ν d x y z₀ ≫ thφ D.P.A (x3 D.P.A) I)
  let V : Set (Fin g → ℂ) := {z | ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j}
  have hz₀ : z₀ ∈ V := fun w _ =>
    Good.mem (L := D.P.L) (z := w) (J := ν.J) (fun ψ => ν.good ψ trivial) (thφ D.P.A (x3 D.P.A)) (pt3 ν d x y z₀)
  obtain ⟨hV, hval⟩ := _root_.GlobalTheory.MBLow.Cl.CubHol.isOpen_and_differentiableOn_valF_pt3_cubW ν d geo x y j
  have hP : ∀ z ∈ V, ∏ I : thK, geo.frG (j I) (wI x y z I) ^ thε I ≠ 0 := fun z hz =>
    Finset.prod_ne_zero_iff.2 fun I _ => zpow_ne_zero _ ((GlobalTheory.T.holomorphicFrame_partialSum_diff_ne_zero ν d geo x y j I).2 z hz)
  have hG : DifferentiableOn ℂ (fun z => valF (pt3 ν d x y z) (cubW D j) (D.cub.t.s j).val *
      (∏ I : thK, geo.frG (j I) (wI x y z I) ^ thε I)⁻¹) V := by
    refine hval.mul (DifferentiableOn.inv ?_ hP)
    have e : (fun z => ∏ I : thK, geo.frG (j I) (wI x y z I) ^ thε I) =
        ∏ I : thK, fun z => geo.frG (j I) (wI x y z I) ^ thε I := by
      ext z; rw [Finset.prod_apply]
    rw [e]
    refine Finset.prod_induction _ (fun f => DifferentiableOn ℂ f V) (fun f h hf hh => hf.mul hh)
      (differentiableOn_const 1) fun I _ => ?_
    exact (GlobalTheory.T.holomorphicFrame_partialSum_diff_ne_zero ν d geo x y j I).1.zpow (Or.inl fun z hz => (GlobalTheory.T.holomorphicFrame_partialSum_diff_ne_zero ν d geo x y j I).2 z hz)
  have heq : ∀ z ∈ V, cubF d x y z = valF (pt3 ν d x y z) (cubW D j) (D.cub.t.s j).val *
      (∏ I : thK, geo.frG (j I) (wI x y z I) ^ thε I)⁻¹ := fun z hz => by
    rw [← div_eq_mul_inv]
    exact (eq_div_iff (hP z hz)).2 (GlobalTheory.T.cubeValueTimesThetaFrames_chartGauge ν d geo x y z j hz)
  have hn : V ∈ nhds z₀ := hV.mem_nhds hz₀
  exact ((hG z₀ hz₀).differentiableAt hn).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem hn fun z hz => heq z hz)

theorem cubF_entire : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g : ℕ) (d : AB N.toNumB g), Nonempty (Geo ν d) → ∀ x y : Fin g → ℂ, Differentiable ℂ (cubF d x y) := by
  intro R _ _ _ _ D _ _ _ N ν g d ⟨geo⟩ x y
  exact cubF_differentiable ν d geo x y

end GlobalTheory.MBLow.Cl.CubHol

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataOfMonomialEvenBimultiplicative
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DegFromMonomial

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (m : ℕ) (r : Fin m → R) (β : Fin m → LinearMap.BilinForm ℤ D.X), D.PsiEven → D.TauBimult → IsMonomial D r β → (∀ i, r i ∈ maximalIdeal R) → (∀ i y z, β i y z = β i z y) → (∀ y, y ≠ 0 → ∃ i, 0 < β i y y) → ∃ DD : DegData R (maximalIdeal R), DD.toPre = D := by
  intro R _ _ _ D m r β hE hT hM hr hs hp
  have hmem : ∀ (y : D.X) (u : Rˣ) (n : Fin m → ℕ) (k : ℕ), k ≤ ∑ i, n i →
      (u : R) * ∏ i, r i ^ n i ∈ maximalIdeal R ^ k := by
    intro y u n k hk
    refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hk ?_)
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hr i) _
  let S : LinearMap.BilinForm ℤ D.X := ∑ i, β i
  have hS : ∀ y z, S y z = ∑ i, β i y z := fun y z => by
    simp [S, LinearMap.sum_apply]
  have hSs : ∀ y z, S y z = S z y := fun y z => by
    rw [hS, hS]; exact Finset.sum_congr rfl fun i _ => hs i y z
  have hSp : ∀ y, y ≠ 0 → 0 < S y y := fun y hy => by
    rw [hS]
    obtain ⟨i, hi⟩ := hp y hy
    exact Finset.sum_pos' (fun j _ => hM.nonneg j y) ⟨i, Finset.mem_univ _, hi⟩
  refine ⟨{ toPre := D, psi_even := hE, tau_bimult := hT, psi_pos := ?_, psi_tendsto := ?_ }, rfl⟩
  · intro y hy
    obtain ⟨u, n, hn, hc⟩ := hM y
    refine (GlobalTheory.PeriodFormEdge.psiIn_iff hc _).2 ?_
    have h1 := hmem y u n 1 ?_
    · rwa [pow_one] at h1
    · obtain ⟨i, hi⟩ := hp y hy
      have : 1 ≤ n i := by have := hn i; omega
      exact this.trans (Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i))
  · intro k
    refine (GlobalTheory.ToricData.finite_form_le S hSs hSp (2 * k)).subset fun y hy => ?_
    simp only [Set.mem_setOf_eq] at hy ⊢
    by_contra hlt
    obtain ⟨u, n, hn, hc⟩ := hM y
    refine hy ((GlobalTheory.PeriodFormEdge.psiIn_iff hc _).2 (hmem y u n k ?_))
    have e : S y y = 2 * ((∑ i, n i : ℕ) : ℤ) := by
      rw [hS, Nat.cast_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => hn i
    omega

end GlobalTheory.DegFromMonomial
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationTaylorPowerSeriesDerivationEqPderivStatement
section
open IsLocalRing GlobalTheory.FormalOrigin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivationTaylorPowerSeries_derivation_eq_pderiv : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B) (ds : Fin n → Derivation ℤ A A), (∀ a b f, ds a (ds b f) = ds b (ds a f)) → ∀ a f, taylor ev (fun i => ⇑(ds i)) (ds a f) = MvPowerSeries.pderiv (R := B) a (taylor ev (fun i => ⇑(ds i)) f) := by
  first | exact @GlobalTheory.FormalOrigin.TaylorDeriv.taylor_deriv_eq_pderiv | exact GlobalTheory.FormalOrigin.TaylorDeriv.taylor_deriv_eq_pderiv | (intros; apply GlobalTheory.FormalOrigin.TaylorDeriv.taylor_deriv_eq_pderiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedGroupAbelianLocusAndRelDim
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.DescAb

theorem abLocus_eq (X S : Scheme.{0}) (j : X ⟶ S) (G : Over S) [GrpObj G] (hG : IsSemiAbelian G)
    (hc : ∀ (x : S), ∃ (R : Type) (_ : CommRing R) (_ : IsLocalRing R) (ξ : Sp R ⟶ S) (G₁ : Over (Sp R)) (_ : GrpObj G₁)
      (π : G₁.left ⟶ G.left), ξ (closedPoint R) = x ∧ IsGrpPullback G₁ G ξ π ∧
        ∀ p : Sp R, p ∈ abLocus G₁ ↔ ξ p ∈ Set.range j) :
    abLocus G = Set.range j := by
  ext x
  obtain ⟨R, _, _, ξ, G₁, _, π, hx, hp, hab⟩ := hc x
  have h := abLocus_pullback abLocusOne hG hp.1 (closedPoint R)
  rw [hx] at h
  have h' := hab (closedPoint R)
  rw [hx] at h'
  exact h.trans h'

theorem relDim (X S : Scheme.{0}) (j : X ⟶ S) [IsOpenImmersion j] (hj : IsDominant j) (A : Over X) [GrpObj A]
    (G : Over S) [GrpObj G] (e : A.left ⟶ G.left) (g : ℕ) (hA : SmoothOfRelativeDimension g A.hom)
    (hG : IsSemiAbelian G) (hpb : IsGrpPullback A G j e) : SmoothOfRelativeDimension g G.hom := by
  have : Smooth G.hom := hG.smooth
  have hopen : IsOpenMap G.hom := G.hom.isOpenMap
  choose n W hW hd using H1.exists_dim G.hom
  have key : ∀ y, n y = g := by
    intro y
    obtain ⟨x, w, hwW, hx⟩ := j.denseRange.exists_mem_open (hopen _ (W y).isOpen) ⟨_, ⟨y, hW y, rfl⟩⟩
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback w x hx
    refine H1.dim_base hpb.1 (hd y) hA (hpb.1.isoPullback.inv z) ?_
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hz₁]
    exact hwW
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  rw [← key y]; exact hd y

end GlobalTheory.DescAb

theorem GlobalTheory.DescAb.abLocus_eq_range_and_relDim : ∀ (X S : Scheme.{0}) (j : X ⟶ S) [IsOpenImmersion j], IsDominant j → ∀ (A : Over X) [GrpObj A] (G : Over S) [GrpObj G] (e : A.left ⟶ G.left) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsSemiAbelian G → IsGrpPullback A G j e → (∀ (x : S), ∃ (R : Type) (_ : CommRing R) (_ : IsLocalRing R) (ξ : Sp R ⟶ S) (G₁ : Over (Sp R)) (_ : GrpObj G₁) (π : G₁.left ⟶ G.left), ξ (closedPoint R) = x ∧ IsGrpPullback G₁ G ξ π ∧ ∀ p : Sp R, p ∈ abLocus G₁ ↔ ξ p ∈ Set.range j) → abLocus G = Set.range j ∧ SmoothOfRelativeDimension g G.hom := by
  intro X S j _ hj A _ G _ e g _ hA hG hpb hc
  exact ⟨GlobalTheory.DescAb.abLocus_eq X S j G hG hc, GlobalTheory.DescAb.relDim X S j hj A G e g hA hG hpb⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFrameChangeBalancedTensorsCmTypeStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_frameChange_balancedTensors_cmType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (K : Type) [Field K] (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) (n n' : ℕ)
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n')
    (ε ε' : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw) (L : Matrix (Fin Dw.dim) (Fin Dw.dim) K),
    (∀ j, _root_.Matrix.transpose (GlobalTheory.LogKSDiv.flatFrame A e e') * GlobalTheory.LogKSDiv.symPair (R := K) e (ε j) * GlobalTheory.LogKSDiv.flatFrame A e e' =
      ∑ k, L k j • GlobalTheory.LogKSDiv.symPair (R := K) e' (ε' k)) →
    ∃ u : K, (u = 1 ∨ u = -1) ∧
      L.det = u * ∏ τ : E →+* ℂ, (A τ).det ^ (if τ (H.rt : E) = H.rt0 then Dw.q else Dw.p) := by
  first | exact @GlobalTheory.LogKSDiv.det_frameChange_balanced | exact GlobalTheory.LogKSDiv.det_frameChange_balanced | (intros; apply GlobalTheory.LogKSDiv.det_frameChange_balanced <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorPotentialIsSNCBoundary
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O
open GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh

namespace GlobalTheory.DivSec

theorem exists_affine_germ_eq : ∀ (Y : Scheme.{0}) (y : Y) (n : ℕ) (r : Fin n → Y.presheaf.stalk y),
    ∃ (V : Y.affineOpens) (hy : y ∈ V.1) (F : Fin n → Γ(Y, V.1)), ∀ j, Y.presheaf.germ V.1 y hy (F j) = r j := by
  intro Y y n r
  classical
  choose U hU s hs using fun j => TopCat.Presheaf.germ_exist Y.presheaf (r j)
  have hmem : ∀ t : Finset (Fin n), y ∈ t.inf U := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      rw [Finset.inf_insert]
      exact ⟨hU a, ih⟩
  obtain ⟨V, hV, hyV, hVO⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens (hmem Finset.univ)
  have hle : ∀ j, V ≤ U j := fun j => le_trans hVO (Finset.inf_le (Finset.mem_univ j))
  refine ⟨⟨V, hV⟩, hyV, fun j => resG Y (hle j) (s j), fun j => ?_⟩
  rw [← hs j]
  exact Y.presheaf.germ_res_apply (homOfLE (hle j)) y hyV (s j)

theorem isCompatChart_of_holAlong : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (n : ℕ)
    (B : FinHolAtlas n (CxPts p σ)), IsAlgAtlas B → ∀ (e : OpenPartialHomeomorph (CxPts p σ) (Fin n → ℂ)),
    (∀ j, HolAlong e.source fun x => e x j) → IsHolTo e.target (fun z => (e.symm z).1) → IsCompatChart B e := by
  intro k _ Y p σ n B hB e hhol hsymm j
  obtain ⟨c, hcj⟩ := hB j
  rw [hcj]
  constructor
  · refine (c.analyticOnNhd_finChart_iff e.open_source e).2 ?_
    refine differentiableOn_pi.2 fun i => ?_
    have hO := GlobalTheory.ChartGlue.isOpen_over c.e e.open_source
    exact hhol i _ _ c.e.symm hO (GlobalTheory.ShFam.Hor.Sec.isHolTo_symm c hO Set.inter_subset_left) (fun b hb => hb.2)
  · have hO : IsOpen (e.target ∩ e.symm ⁻¹' c.finChart.source) := e.isOpen_inter_preimage_symm c.finChart.open_source
    refine (SCV.analyticOnNhd_iff_differentiableOn hO).2 ?_
    intro b hb
    have h1 := GlobalTheory.TrueCx.TorHolo.differentiableAt_chart e.open_target hsymm c hb.1 hb.2
    exact ((EuclideanSpace.equiv (Fin n) ℂ).differentiable.differentiableAt.comp b h1).differentiableWithinAt

end GlobalTheory.DivSec
end
end

