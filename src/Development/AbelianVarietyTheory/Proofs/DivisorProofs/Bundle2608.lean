module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2385
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2541
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2449
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2477
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2499
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2120
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2433
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2527
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2565
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2574
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2545
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2546
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelPairSumEqOfSumEqOtherPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.DescKP

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S} [GrpObj G]

theorem ι_mem {X : Scheme.{0}} (U : X.Opens) (x : U.toScheme) : U.ι x ∈ U := x.2

theorem surjective_Wk (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π)
    (V : (N.U ⊗ N.U).left.Opens) (h : Surjective ((VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom)) :
    Surjective ((Wk N p hp V).ι ≫ (Pk N p hp).hom) := by
  obtain ⟨z, h1, h2⟩ := exists_lift N p hp (VT N V).toScheme (VT N V).ι (VT N V).ι rfl
  have hr : Set.range z ⊆ Set.range (Wk N p hp V).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine ⟨?_, ?_⟩
    · show (abP N p hp).left (z x) ∈ VT N V
      rw [← Scheme.Hom.comp_apply, h1]; exact ι_mem _ x
    · show (cdP N p hp).left (z x) ∈ VT N V
      rw [← Scheme.Hom.comp_apply, h2]; exact ι_mem _ x
  let z' := IsOpenImmersion.lift (Wk N p hp V).ι z hr
  have e : z' ≫ (Wk N p hp V).ι ≫ (Pk N p hp).hom = (VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac, ← h1, Category.assoc, Over.w (abP N p hp)]
  have : Surjective (z' ≫ (Wk N p hp V).ι ≫ (Pk N p hp).hom) := by rw [e]; exact h
  exact Surjective.of_comp z' _

theorem agree_Wk (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) (m : V.toScheme ⟶ N.U.left)
    (hm : m ≫ N.U.hom = V.ι ≫ (N.U ⊗ N.U).hom) (p p' : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π)
    (hp' : p' ≫ π = pullback.fst π π ≫ π)
    (h : (VT N V).ι ≫ (Desc.sum N p hp).left = mT N V m hm ≫ (Desc.emb N p hp).left)
    (h' : (VT N V).ι ≫ (Desc.sum N p' hp').left = mT N V m hm ≫ (Desc.emb N p' hp').left) :
    (Wk N p hp V).ι ≫ (abP N p hp ≫ Desc.sum N p' hp').left =
      (Wk N p hp V).ι ≫ (cdP N p hp ≫ Desc.sum N p' hp').left := by
  let a' := IsOpenImmersion.lift (VT N V).ι ((Wk N p hp V).ι ≫ (abP N p hp).left) (by
    rintro _ ⟨x, rfl⟩; rw [Scheme.Opens.range_ι]; exact (ι_mem _ x).1)
  let c' := IsOpenImmersion.lift (VT N V).ι ((Wk N p hp V).ι ≫ (cdP N p hp).left) (by
    rintro _ ⟨x, rfl⟩; rw [Scheme.Opens.range_ι]; exact (ι_mem _ x).2)
  have ea : a' ≫ (VT N V).ι = (Wk N p hp V).ι ≫ (abP N p hp).left := IsOpenImmersion.lift_fac _ _ _
  have ec : c' ≫ (VT N V).ι = (Wk N p hp V).ι ≫ (cdP N p hp).left := IsOpenImmersion.lift_fac _ _ _
  have e0 := congrArg (fun f => (Wk N p hp V).ι ≫ Over.Hom.left f) (abP_sum N p hp)
  simp only [Over.comp_left] at e0
  have hemb := GlobalTheory.Mum.DescHom.isOpenImmersion_emb N p hp
  have e2 : a' ≫ mT N V m hm = c' ≫ mT N V m hm := by
    refine (cancel_mono (Desc.emb N p hp).left).1 ?_
    simp only [Category.assoc]
    rw [← h, ← Category.assoc, ea, ← Category.assoc, ec, Category.assoc, Category.assoc]
    exact e0
  simp only [Over.comp_left]
  rw [← Category.assoc, ← ea, Category.assoc, h', ← Category.assoc, e2, Category.assoc, ← h', ← Category.assoc, ec,
    Category.assoc]

end GlobalTheory.Mum.DescKP


open GlobalTheory.Mum.DescKP in
theorem GlobalTheory.Mum.DescKP.sum_eq_of_sum_eq : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∀ (p p' : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) (hp' : p' ≫ π = pullback.fst π π ≫ π), ∀ (Z : Scheme.{0}) (g g' : Z ⟶ (Desc.UT N ⊗ Desc.UT N).left), g ≫ (Desc.sum N p hp).left = g' ≫ (Desc.sum N p hp).left → g ≫ (Desc.sum N p' hp').left = g' ≫ (Desc.sum N p' hp').left := by
  intro R _ _ _ _ S π _ _ _ G _ _ hG N hLaw p p' hp hp' Z g g' hgg
  obtain ⟨V, m, hV, hm, hL⟩ := hLaw
  have hlaw := fun (q : pullback π π ⟶ S) (hq : q ≫ π = pullback.fst π π ≫ π) => _root_.GlobalTheory.Mum.DescKP.sum_eq_mT_emb N V m hm hL q hq
  have : Smooth N.U.hom := N.smooth
  have : Surjective N.U.hom := DescHom.surjective_near N
  have : Smooth G.hom := hG.smooth
  have : IsSeparated G.hom := hG.separated
  have := DescHom.geometricallyIrreducible_of_semiAbelian G hG

  have sV := _root_.GlobalTheory.Mum.NearSurj.surjective_of_open_closedFibre N.U N.smooth inferInstance V hV
  have sq : IsPullback (DescKP.pairU N ∣_ V) ((VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom)
      (V.ι ≫ (N.U ⊗ N.U).hom) (pullback.fst π π ≫ π) :=
    (isPullback_morphismRestrict (DescKP.pairU N) V).paste_vert (GlobalTheory.T.isPullback_descentSquarePairToOpenSquare N)
  have sVT : Surjective ((VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom) :=
    MorphismProperty.of_isPullback (P := @Surjective) sq sV
  have sW := DescKP.surjective_Wk N p hp V sVT

  have : Smooth (Desc.UT N).hom := inferInstanceAs (Smooth (pullback.snd N.U.hom (pullback.fst π π ≫ π)))
  have : Surjective (Desc.UT N).hom := inferInstanceAs (Surjective (pullback.snd N.U.hom (pullback.fst π π ≫ π)))
  have hGp : GeometricallyIrreducible ((Over.pullback p).obj G).hom :=
    inferInstanceAs (GeometricallyIrreducible (pullback.snd G.hom p))
  have := DescHom.isOpenImmersion_emb N p hp
  have : GeometricallyIrreducible (Desc.UT N).hom := by
    have e : (Desc.emb N p hp).left ≫ ((Over.pullback p).obj G).hom = (Desc.UT N).hom := Over.w _
    have h := _root_.GlobalTheory.OpenGeomIrr.geometricallyIrreducible_comp_of_isOpenImmersion _ _ _ (Desc.emb N p hp).left inferInstance _ hGp (by rw [e]; infer_instance)
    rwa [e] at h
  have : Smooth (Desc.UT N ⊗ Desc.UT N).hom :=
    inferInstanceAs (Smooth (pullback.fst (Desc.UT N).hom (Desc.UT N).hom ≫ (Desc.UT N).hom))
  have : GeometricallyIrreducible (Desc.UT N ⊗ Desc.UT N).hom :=
    GeometricallyIrreducible.comp (pullback.fst (Desc.UT N).hom (Desc.UT N).hom) (Desc.UT N).hom
  have : Smooth ((Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N).hom :=
    inferInstanceAs (Smooth (pullback.fst (Desc.UT N ⊗ Desc.UT N).hom (Desc.UT N).hom ≫ (Desc.UT N ⊗ Desc.UT N).hom))
  have h3 : GeometricallyIrreducible ((Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N).hom :=
    GeometricallyIrreducible.comp (pullback.fst (Desc.UT N ⊗ Desc.UT N).hom (Desc.UT N).hom) (Desc.UT N ⊗ Desc.UT N).hom
  have : Surjective (DescKP.Pk N p hp).hom := Surjective.of_comp (DescKP.Wk N p hp V).ι _
  have : Smooth (DescKP.Pk N p hp).hom :=
    inferInstanceAs (Smooth (pullback.snd (Desc.emb N p hp).left (DescKP.trip N p hp).left ≫
      ((Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N).hom))
  have : GeometricallyIrreducible (DescKP.Pk N p hp).hom :=
    _root_.GlobalTheory.OpenGeomIrr.geometricallyIrreducible_comp_of_isOpenImmersion _ _ _ (pullback.snd (Desc.emb N p hp).left (DescKP.trip N p hp).left) inferInstance _ h3
      (inferInstanceAs (Surjective (DescKP.Pk N p hp).hom))
  have : IsSeparated ((Over.pullback p').obj G).hom := inferInstanceAs (IsSeparated (pullback.snd G.hom p'))

  let j : Over.mk ((DescKP.Wk N p hp V).ι ≫ (DescKP.Pk N p hp).hom) ⟶ DescKP.Pk N p hp :=
    Over.homMk (DescKP.Wk N p hp V).ι rfl
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion (DescKP.Wk N p hp V).ι)
  have : Surjective (Over.mk ((DescKP.Wk N p hp V).ι ≫ (DescKP.Pk N p hp).hom)).hom := sW
  have hF : DescKP.abP N p hp ≫ Desc.sum N p' hp' = DescKP.cdP N p hp ≫ Desc.sum N p' hp' := by
    refine DescHom.ext_of_open j ?_
    ext1
    exact DescKP.agree_Wk N V m hm p p' hp hp' (hlaw p hp) (hlaw p' hp')
  obtain ⟨z, hz, hz'⟩ := DescKP.exists_lift N p hp Z g g' hgg
  rw [← hz, ← hz', Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, hF]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerComparison
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPole

theorem exists_ksCompare : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c), ∃ s : ℚ, s ≠ 0 ∧ KSCompare TF s := by
  intro PP E _ _ _ H Dw l Xo c TF
  obtain ⟨s, hs0, hcore⟩ := _root_.GlobalTheory.CechKS.exists_const_isKSValue PP
  refine ⟨s, hs0, ?_⟩
  intro U n e v hv D Θ hΘ K _ _ P hU hP y' hU' hy' hev
  obtain ⟨A, _, A', _, π, π', i, h, ψ, ub, hb, g, hπ, hπ', hi, hpol, hu, hbl, hrow, hA, hgA, hA', hgA', hL⟩ :=
    _root_.GlobalTheory.KSPkg.ksPackage PP E H Dw l Xo c TF U D.1 K P hU y' hU' hy' hev
  have hC := _root_.GlobalTheory.CechTransport.cech_of_logKS E H Dw l Xo c TF U n e v hv D Θ hΘ K P hU hP y' hU' hy' hev A A' π π' i ub h hπ hπ' hi hu
  have hbal := _root_.GlobalTheory.LogPole.ksMatrix_eq_zero_of_ne_conj E H Dw l Xo c TF U n e v hv D Θ hΘ
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
  have hK := hcore K A A' i h g hA hgA hA' hgA' _ hL ψ hpol n (fun a => ub (e.symm a).1 (e.symm a).2)
    (Matrix.of fun a b => ev (frX P ≫ TF.Y.j) U.1 hU (Θ a b)) (fun a => (hbl _ _).1) hC
    (fun b => hb (e.symm b)) (fun b => hbl _ _)
  refine ⟨A, inferInstance, A', inferInstance, π, π', i, h, ψ, ub, hb, hπ, hπ', hi, hpol, hu, fun σ k => hbl σ k,
    fun τ a => ?_⟩
  exact _root_.GlobalTheory.KSRowsFil.isKSRow_of_isKSValue E H Dw K A A' i h hA ψ ub hb n e _ (s : K) (fun σ k => (hbl σ k).1)
    (fun a b hab => by simp only [Matrix.of_apply, hbal a b hab, map_zero]) hK τ.1 a (hrow τ a)

end GlobalTheory.LogPole
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelCongruenceEndoAllAlgClosedFieldsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.labelCongruence_endo_all_algClosed_fields : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (eA : u.A.A ⟶ u.A.A) (s : u.D.toPre.X →+ u.D.toPre.X), (∀ (m : ℕ) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → x'.left = x.left ≫ eA.left → CongMod m pk'.y (s pk.y)) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing u.V) F] (k : ℕ), 1 ≤ k → IsUnit (k : u.V) → ∀ (q q' : QkPt u.D.toPre F k) (a a' : TFK (R := u.V) F ⟶ u.A.A), QkToAkU u.U.toUnifPre F k q a → QkToAkU u.U.toUnifPre F k q' a' → a.left = a'.left ≫ eA.left → CongMod k q.y (s q'.y) := by
  first | exact @GlobalTheory.LabelTransfer.main | exact GlobalTheory.LabelTransfer.main | (intros; apply GlobalTheory.LabelTransfer.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtIffOfSpecializes
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.FibLat

open GlobalTheory.SplitTorus (torusMap bcMap)

theorem ringHom_eq_of_spMap {A B : Type} [CommRing A] [CommRing B] {a b : A →+* B} (h : spMap a = spMap b) : a = b := by
  have h1 := Spec.map_injective h
  have h2 := congrArg CommRingCat.Hom.hom h1
  simpa using h2

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (s : Sp B ⟶ Sp A) : ∃ a : A →+* B, s = spMap a := ⟨(Spec.preimage s).hom, by simp [spMap]⟩

private theorem isGrpPullback_pullback_fst {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] :
    IsGrpPullback ((Over.pullback f).obj G) G f (pullback.fst G.hom f) := by
  refine ⟨IsPullback.of_hasPullback _ _, ?_⟩
  intro T x y x₀ y₀ hx hy
  have key : ∀ (z : T ⟶ (Over.pullback f).obj G) (z₀ : (Over.map f).obj T ⟶ G),
      z₀.left = z.left ≫ pullback.fst G.hom f → z = (Over.mapPullbackAdj f).unit.app T ≫ (Over.pullback f).map z₀ := by
    intro z z₀ hz
    ext
    apply pullback.hom_ext
    · simp only [Over.pullback_obj_left, Over.mapPullbackAdj_unit_app, Over.comp_left, Over.pullback_map_left,
        Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp, hz, Over.homMk_left]
      erw [pullback.lift_fst_assoc, Category.id_comp]
    · simp only [Over.pullback_obj_left, Over.mapPullbackAdj_unit_app, Over.comp_left, Over.pullback_map_left,
        Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.id_comp, Over.homMk_left]
      erw [pullback.lift_snd]
      exact Over.w z
  rw [key x x₀ hx, key y y₀ hy, ← MonObj.comp_mul, ← Functor.map_mul]
  simp

theorem exists_common_pullback {Y : Scheme.{0}} {G : Over Y} [GrpObj G] {κ κ' : Type} [Field κ] [Field κ'] {s : Sp κ ⟶ Y}
    {s' : Sp κ' ⟶ Y} (hs : s (closedPoint κ) = s' (closedPoint κ')) {G₀ : Over (Sp κ)} [GrpObj G₀] {φ : G₀.left ⟶ G.left}
    {G₀' : Over (Sp κ')} [GrpObj G₀'] {φ' : G₀'.left ⟶ G.left} (hφ : IsGrpPullback G₀ G s φ)
    (hφ' : IsGrpPullback G₀' G s' φ') :
    ∃ (K : Type) (_ : Field K) (b : κ →+* K) (b' : κ' →+* K) (GK : Over (Sp K)) (_ : GrpObj GK) (ψ : GK.left ⟶ G₀.left)
      (ψ' : GK.left ⟶ G₀'.left), spMap b ≫ s = spMap b' ≫ s' ∧ IsGrpPullback GK G₀ (spMap b) ψ ∧
      IsGrpPullback GK G₀' (spMap b') ψ' ∧ ψ ≫ φ = ψ' ≫ φ' := by
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := s) (g := s') _ _ hs
  obtain ⟨K, _, ⟨p⟩⟩ : ∃ (K : Type) (_ : Field K), Nonempty (Sp K ⟶ pullback s s') :=
    ⟨_, inferInstance, ⟨(pullback s s').fromSpecResidueField z⟩⟩
  obtain ⟨b, hb⟩ := exists_spMap (p ≫ pullback.fst s s')
  obtain ⟨b', hb'⟩ := exists_spMap (p ≫ pullback.snd s s')
  have e : spMap b ≫ s = spMap b' ≫ s' := by
    rw [← hb, ← hb', Category.assoc, Category.assoc, pullback.condition]
  have hψ := isGrpPullback_pullback_fst (spMap b) G₀
  set ψ := pullback.fst G₀.hom (spMap b)
  set GK := (Over.pullback (spMap b)).obj G₀
  have w0 : (ψ ≫ φ) ≫ G.hom = (GK.hom ≫ spMap b') ≫ s' := by
    simp only [Category.assoc]
    rw [hφ.1.w, ← Category.assoc ψ, hψ.1.w, Category.assoc, e]
  refine ⟨K, inferInstance, b, b', GK, inferInstance, ψ, hφ'.1.lift (ψ ≫ φ) (GK.hom ≫ spMap b') w0, e, hψ, ?_,
    (hφ'.1.lift_fst _ _ _).symm⟩
  have n := hψ.comp hφ
  rw [e, ← hφ'.1.lift_fst (ψ ≫ φ) (GK.hom ≫ spMap b') w0] at n
  exact IsGrpPullback.cancel hφ' n (hφ'.1.lift_snd _ _ _)

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {G : Over M.Z} [GrpObj G]
  {I T : Type} {f : I → (G ⟶ G)} {gγ : T → (Over.mk M.pt ⟶ G)} {ζ : oˣ} {L : ℕ}

theorem RkAt.unique {w : M.Z} {r r' : ℕ} (h : RkAt G w r) (h' : RkAt G w r') : r = r' := by
  obtain ⟨X, _, _, _, κ, _, s, G₀, _, φ, tι, hs, hφ, ht, rfl⟩ := h
  obtain ⟨X', _, _, _, κ', _, s', G₀', _, φ', tι', hs', hφ', ht', rfl⟩ := h'
  obtain ⟨K, _, b, b', GK, _, ψ, ψ', -, hψ, hψ', -⟩ := exists_common_pullback (hs.trans hs'.symm) hφ hφ'
  obtain ⟨e, -⟩ := IsTorPart.exists_equiv (ht.pull hψ) (ht'.pull hψ')
  exact e.toIntLinearEquiv.finrank_eq

theorem LatAt.transfer {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {m : I → X →+ X}
    {c : T → X →+ ZMod L} {w : M.Z} (h : LatAt f gγ ζ L m c w) {κ' : Type} [Field κ'] {s' : Sp κ' ⟶ M.Z}
    (hs' : s' (closedPoint κ') = w) {a' : o →+* κ'} (ha' : s' ≫ M.s = spMap a') {G₀' : Over (Sp κ')} [GrpObj G₀']
    {φ' : G₀'.left ⟶ G.left} (hφ' : IsGrpPullback G₀' G s' φ') {X' : Type} [AddCommGroup X'] [Module.Free ℤ X']
    [Module.Finite ℤ X'] {t' : splitTorus (Sp κ') X' ⟶ G₀'} (ht' : IsTorPart t') :
    ∃ (e : X' ≃+ X) (K : Type) (_ : Field K) (b : κ' →+* K) (GK : Over (Sp K)) (_ : GrpObj GK) (ψ : GK.left ⟶ G₀'.left)
      (hψ : IsGrpPullback GK G₀' (spMap b) ψ),
      Compat f gγ ζ L m c (spMap b ≫ s') (b.comp a') (ψ ≫ φ') (torusMap _ e.toAddMonoidHom ≫ pullTorus hψ t') := by
  obtain ⟨κ, _, s, a, G₀, _, φ, tι, hs, ha, hφ, ht, hc⟩ := h
  obtain ⟨K, _, b, b', GK, _, ψ, ψ', e1, hψ, hψ', e2⟩ := exists_common_pullback (hs.trans hs'.symm) hφ hφ'
  obtain ⟨e, he⟩ := IsTorPart.exists_equiv (ht'.pull hψ') (ht.pull hψ)
  have hab : b.comp a = b'.comp a' := by
    apply ringHom_eq_of_spMap
    rw [← spMap_comp', ← spMap_comp', ← ha, ← ha', reassoc_of% e1]
  refine ⟨e, K, inferInstance, b', GK, inferInstance, ψ', hψ', ?_⟩
  have hc2 := hc.pull b hψ
  rw [he, e1, hab, e2] at hc2
  exact hc2

theorem Compat.unique [IsSeparated G.hom] (hL : 0 < L) {X : Type} [AddCommGroup X] {m m' : I → X →+ X}
    {c c' : T → X →+ ZMod L} {K : Type} [Field K] {s : Sp K ⟶ M.Z} {a : o →+* K} (hζ : IsPrimitiveRoot (a ζ) L)
    {G₀ : Over (Sp K)} [GrpObj G₀] {φ : G₀.left ⟶ G.left} (hφ : IsGrpPullback G₀ G s φ) {t : splitTorus (Sp K) X ⟶ G₀}
    (ht : IsTorPart t) (h : Compat f gγ ζ L m c s a φ t) (h' : Compat f gγ ζ L m' c' s a φ t) : m = m' ∧ c = c' := by
  obtain ⟨hm, hc⟩ := h
  obtain ⟨hm', hc'⟩ := h'
  constructor
  · funext e
    apply ht.cancel
    apply hom_ext_of_pullback hφ
    rw [← hm e, ← hm' e]
  · funext tt
    obtain ⟨z, hz, hv⟩ := hc tt
    obtain ⟨z', hz', hv'⟩ := hc' tt
    have hzz : z = z' := by
      have := ht.mono
      apply (cancel_mono t).1
      apply hom_ext_of_pullback hφ
      exact ValAt.unique hv hv'
    subst hzz
    ext χ
    have h3 := congrArg Units.val (GlobalTheory.ZH.TorusPerp.unitOn_injective ((hz χ).symm.trans (hz' χ)))
    simp only [Units.val_pow_eq_pow_val, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at h3
    haveI : NeZero L := ⟨hL.ne'⟩
    exact ZMod.val_injective _ (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h3)

theorem LatAt.unique [IsSeparated G.hom] (hL : 0 < L) (hζ : ∀ (κ : Type) [Field κ] (a : o →+* κ), IsPrimitiveRoot (a ζ) L)
    {X X' : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup X'] [Module.Free ℤ X']
    [Module.Finite ℤ X'] {m : I → X →+ X} {c : T → X →+ ZMod L} {m' : I → X' →+ X'} {c' : T → X' →+ ZMod L} {w : M.Z}
    (h : LatAt f gγ ζ L m c w) (h' : LatAt f gγ ζ L m' c' w) :
    ∃ θ : X ≃+ X', (∀ e x, θ (m e x) = m' e (θ x)) ∧ ∀ t x, c' t (θ x) = c t x := by
  obtain ⟨κ', _, s', a', G₀', _, φ', tι', hs', ha', hφ', ht', hc'⟩ := h'
  obtain ⟨e, K, _, b, GK, _, ψ, hψ, hc⟩ := h.transfer hs' ha' hφ' ht'
  have hc2 := (hc'.pull b hψ).equiv e (m' := fun i => (e : X' →+ X).comp ((m' i).comp (e.symm : X →+ X')))
    (c' := fun t => (c' t).comp (e.symm : X →+ X')) (fun i x => by simp) (fun t x => by simp)
  obtain ⟨h1, h2⟩ := Compat.unique hL (hζ K (b.comp a')) (hψ.comp hφ') ((ht'.pull hψ).equiv e) hc hc2
  subst h1 h2
  refine ⟨e.symm, fun i x => ?_, fun t x => ?_⟩ <;> simp

theorem LatAt.equiv {X X' : Type} [AddCommGroup X] [AddCommGroup X'] {m : I → X →+ X} {c : T → X →+ ZMod L}
    {m' : I → X' →+ X'} {c' : T → X' →+ ZMod L} {w : M.Z} (h : LatAt f gγ ζ L m c w)
    (e : X ≃+ X') (hm : ∀ i x, e (m i x) = m' i (e x)) (hc : ∀ t x, c' t (e x) = c t x) : LatAt f gγ ζ L m' c' w := by
  obtain ⟨κ, _, s, a, G₀, _, φ, tι, hs, ha, hφ, ht, hcc⟩ := h
  exact ⟨κ, _, s, a, G₀, _, φ, _, hs, ha, hφ, ht.equiv e, hcc.equiv e hm hc⟩

private theorem ratModel_isLocallyNoetherian {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [IsNoetherianRing o]
    (M : RatModel o Ω) : IsLocallyNoetherian M.Z := by
  have := M.lft
  constructor
  intro U
  have h1 := HasRingHomProperty.appLE @LocallyOfFiniteType M.s this ⟨⊤, isAffineOpen_top _⟩ U (by simp)
  have : IsNoetherianRing Γ(Sp o, ⊤) := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  letI := (M.s.appLE ⊤ U.1 (by simp)).hom.toAlgebra
  have : Algebra.FiniteType Γ(Sp o, ⊤) Γ(M.Z, U.1) := h1
  exact Algebra.FiniteType.isNoetherianRing Γ(Sp o, ⊤) Γ(M.Z, U.1)

theorem latAt_iff_of_specializes [IsNoetherianRing o] [IsCommMonObj G] (hG : IsSemiAbelian G) (hL : 0 < L) (hζ : ζ ^ L = 1)
    (hu : IsUnit (L : o)) (hf : ∀ e, IsMonHom (f e)) (hγ : ∀ t, gγ t ^ L = 1) {X : Type} [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (m : I → X →+ X) (c : T → X →+ ZMod L) {w w' : M.Z} (hw : w ⤳ w') {r : ℕ}
    (hr : RkAt G w r) (hr' : RkAt G w' r) (hext : ∀ t, ExtNear (gγ t) w') :
    LatAt f gγ ζ L m c w ↔ LatAt f gγ ζ L m c w' := by
  by_cases hww : w = w'
  · subst hww
    exact Iff.rfl
  have := ratModel_isLocallyNoetherian M
  obtain ⟨V, _, _, _, ξ, G₁, _, _, φ₁, X₁, _, _, _, j, GK, _, ψ, hψ, hξ', hξ, hφ₁, hj, hjt⟩ :=
    _root_.GlobalTheory.Poinc.FibLat.exists_trait_torusPart M.Z G hG w w' hw hww
  have := hj
  obtain ⟨a, ha⟩ := exists_spMap (ξ ≫ M.s)
  have hG₁ : IsSemiAbelian G₁ := GlobalTheory.Mum.isSemiAbelian_of_isGrpPullback_square _ _ ξ G G₁ φ₁ hφ₁ hG
  have hgen : IsGrpPullback GK G (spMap (algebraMap V (FractionRing V)) ≫ ξ) (ψ ≫ φ₁) := hψ.comp hφ₁
  have hrX : r = Module.finrank ℤ X₁ :=
    RkAt.unique hr ⟨X₁, _, inferInstance, inferInstance, FractionRing V, inferInstance, _, GK, inferInstance, _, _, hξ,
      hgen, hjt, rfl⟩
  obtain ⟨X₀, _, _, _, κ₀, _, s₀, G₀, _, φ₀, t₀, hs₀, hφ₀, ht₀, hrk₀⟩ := hr'
  have hGc := isGrpPullback_pullback_fst (spMap (IsLocalRing.residue V)) G₁
  have hcl : (spMap (IsLocalRing.residue V) ≫ ξ) (closedPoint (IsLocalRing.ResidueField V)) = w' :=
    (congrArg (fun x => ξ x) (GtDescent.spMap_cpt (IsLocalRing.residue V))).trans hξ'
  obtain ⟨K, _, b₀, b₁, GK', _, ψ₀, ψ₁, -, hψ₀, hψ₁, -⟩ := exists_common_pullback (hs₀.trans hcl.symm) hφ₀ (hGc.comp hφ₁)
  have hψc : IsGrpPullback GK' G₁ (spMap (b₁.comp (IsLocalRing.residue V)))
      (ψ₁ ≫ pullback.fst G₁.hom (spMap (IsLocalRing.residue V))) := by
    rw [← spMap_comp']
    exact hψ₁.comp hGc
  have ht0 : IsTorPart (pullTorus hψc j) :=
    _root_.GlobalTheory.Poinc.FibClosed.isTorPart_pullTorus_closed V G₁ hG₁ X₁ j hj GK ψ hψ hjt K (b₁.comp (IsLocalRing.residue V)) inferInstance GK' _ hψc X₀ _
      (ht₀.pull hψ₀) (hrk₀.trans hrX)
  have hsc : (spMap (b₁.comp (IsLocalRing.residue V)) ≫ ξ) (closedPoint K) = w' :=
    (congrArg (fun x => ξ x) (GtDescent.spMap_cpt (b₁.comp (IsLocalRing.residue V)))).trans hξ'
  have ha_gen : (spMap (algebraMap V (FractionRing V)) ≫ ξ) ≫ M.s = spMap ((algebraMap V (FractionRing V)).comp a) := by
    rw [Category.assoc, ha, spMap_comp']
  have ha_cl : (spMap (b₁.comp (IsLocalRing.residue V)) ≫ ξ) ≫ M.s = spMap ((b₁.comp (IsLocalRing.residue V)).comp a) := by
    rw [Category.assoc, ha, spMap_comp']
  have hextV : ∀ t, ExtNear (gγ t) (ξ (closedPoint V)) := by
    rw [hξ']
    exact hext
  constructor
  · intro h
    obtain ⟨e, K₂, _, b₂, GK₂, _, ψ₂, hψ₂, hc⟩ := h.transfer hξ ha_gen hgen hjt
    have hψ₂' : IsGrpPullback GK₂ G₁ (spMap (b₂.comp (algebraMap V (FractionRing V)))) (ψ₂ ≫ ψ) := by
      rw [← spMap_comp']
      exact hψ₂.comp hψ
    have hinj : Function.Injective (b₂.comp (algebraMap V (FractionRing V))) :=
      b₂.injective.comp (IsFractionRing.injective V (FractionRing V))
    have hcV : Compat f gγ ζ L m c ξ a φ₁ (torusMap _ e.toAddMonoidHom ≫ j) := by
      refine _root_.GlobalTheory.Poinc.FibLat.compat_of_compat_field o Ω M G hG I T f gγ ζ L hL hζ X m c V ξ a G₁ φ₁ hφ₁ _ hextV K₂ _ hinj GK₂ _ hψ₂' ?_
      rw [pullTorus_torusMap_comp, ← pullTorus_pullTorus hψ₂ hψ hψ₂' (spMap_comp' _ _).symm rfl, ← spMap_comp']
      simpa only [Category.assoc, RingHom.comp_assoc] using hc
    have hc2 := hcV.pull (b₁.comp (IsLocalRing.residue V)) hψc
    rw [pullTorus_torusMap_comp] at hc2
    exact ⟨K, _, _, _, GK', _, _, _, hsc, ha_cl, hψc.comp hφ₁, ht0.equiv e, hc2⟩
  · intro h
    obtain ⟨e, K₂, _, b₂, GK₂, _, ψ₂, hψ₂, hc⟩ := h.transfer hsc ha_cl (hψc.comp hφ₁) ht0
    have hψ₃ : IsGrpPullback GK₂ G₁ (spMap (b₂.comp (b₁.comp (IsLocalRing.residue V))))
        (ψ₂ ≫ ψ₁ ≫ pullback.fst G₁.hom (spMap (IsLocalRing.residue V))) := by
      rw [← spMap_comp']
      exact hψ₂.comp hψc
    have hcV : Compat f gγ ζ L m c ξ a φ₁ (torusMap _ e.toAddMonoidHom ≫ j) := by
      refine _root_.GlobalTheory.Poinc.FibLat.ClosedLift.compat_of_closed o Ω M G hG I T f gγ ζ L hL hζ hu hf hγ X m c V ξ a G₁ φ₁ hφ₁ _ inferInstance hextV GK ψ hψ
        ?_ K₂ _ inferInstance GK₂ _ hψ₃ ?_ ?_
      · rw [pullTorus_torusMap_comp]
        exact hjt.equiv e
      · rw [pullTorus_torusMap_comp, ← pullTorus_pullTorus hψ₂ hψc hψ₃ (spMap_comp' _ _).symm rfl]
        exact (ht0.pull hψ₂).equiv e
      · rw [pullTorus_torusMap_comp, ← pullTorus_pullTorus hψ₂ hψc hψ₃ (spMap_comp' _ _).symm rfl, ← spMap_comp']
        simpa only [Category.assoc, RingHom.comp_assoc] using hc
    have hc3 := hcV.pull (algebraMap V (FractionRing V)) hψ
    rw [pullTorus_torusMap_comp] at hc3
    exact ⟨FractionRing V, _, _, _, GK, _, _, _, hξ, ha_gen, hgen, hjt.equiv e, hc3⟩

end GlobalTheory.Poinc.FibLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeOfUniformisationEqModelLatticeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_of_uniformisation_eq_model_lattice : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (G : Over M.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (I T : Type) (f : I → (G ⟶ G)) (gγ : T → (Over.mk M.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → ζ ^ L = 1 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (Gu : Over (Sp V)) [GrpObj Gu] [IsCommMonObj Gu], IsSemiAbelian Gu → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A Gu) (F : I → (Gu ⟶ Gu)) (m : I → D.toPre.X →+ D.toPre.X), (∀ e, EndChar U (F e) (m e)) → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (fV : V →+* V'), IsLocalHom fV → ∀ (ξ : Sp V' ⟶ M.Z) (a : o →+* V'), ξ ≫ M.s = spMap a → ∀ (G' : Over (Sp V')) [GrpObj G'] (β : G'.left ⟶ Gu.left) (β' : G'.left ⟶ G.left), IsGrpPullback G' Gu (spMap fV) β → IsGrpPullback G' G ξ β' → (∀ e, ∃ F' : G' ⟶ G', F'.left ≫ β = β ≫ (F e).left ∧ F'.left ≫ β' = β' ≫ (f e).left) → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing V) K] (iK : V' →+* K), Function.Injective iK → iK.comp fV = (algebraMap (FractionRing V) K).comp (algebraMap V (FractionRing V)) → ∀ c : T → D.toPre.X →+ ZMod L, (∀ t, ExtNear (gγ t) (ξ (closedPoint V')) ∧ ∃ (q : QkPt D.toPre K L) (τ : Multiplicative D.toPre.X →* Kˣ) (x : TFK (R := V) K ⟶ A.A) (x' : Sp K ⟶ G'.left), q.y = 0 ∧ GlobalTheory.UT.IsTor τ q.g ∧ QkToAkU U.toUnifPre K L q x ∧ (∀ χ, (τ (Multiplicative.ofAdd χ) : K) = iK (a ((ζ : o) ^ (c t χ).val))) ∧ x' ≫ G'.hom = spMap iK ∧ x' ≫ β = x.left ≫ genMap U ∧ ValAt (gγ t) (spMap iK ≫ ξ) (x' ≫ β')) → LatAt f gγ ζ L m c (ξ (closedPoint V')) := by
  first | exact @GlobalTheory.Poinc.FibLat.latAt_of_unif | exact GlobalTheory.Poinc.FibLat.latAt_of_unif | (intros; apply GlobalTheory.Poinc.FibLat.latAt_of_unif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiePairingCanonicalRigidifiedExtensionTangentStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_pairing_canonical_rigidified_extension_tangent :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 →
    ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ (G : PDivGroup p R) (t : PDivGroup.TorsionTower G A)
      (ψ : PrimitiveSubmodule A →ₗ[R] G.omega),
    (∀ c : PrimitiveSubmodule A, PtExt.IsCan t c.1 (G.rigOfOmega (ψ c))) →
    ∀ (β : Form (A.hom ≫ 𝟙 _)) (hβ : Form.cl _ β ∈ primDR A)
      (hF : (⟨_, hβ⟩ : primDR A) ∈ PrimitiveSubmodule A) (x : G.Lie) (v : epsR R ⟶ A),
    t.LieCorr x v → x (ψ ⟨_, hF⟩) = tanVal v β :=
  @PtExt.lie_psi_cl_eq_tanVal
end

