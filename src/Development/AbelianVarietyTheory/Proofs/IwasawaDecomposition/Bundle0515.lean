module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0494
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0490
public import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralNthRootTestModelPoint
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0184
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsSmulOfPreservesFrameOrbits
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0497
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalisedDataCoefficientMapInjective
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.Mem GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.RealGeo GlobalTheory.OneMapAll GlobalTheory.FieldBC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.Rw.OmExt

theorem heq_val {Γ W W' : Type} (n : NormedAddCommGroup W) (p : InnerProductSpace ℂ W) (n' : NormedAddCommGroup W')
    (p' : InnerProductSpace ℂ W') (hW : HEq W' W) (hn : HEq n' n) (hp : HEq p' p) (H : HMod (Γ → W)) (H' : HMod (Γ → W'))
    (hH : HEq H' H) (y : H.H) (y' : H'.H) (hy : HEq y' y) (g : Γ) : HEq (H'.e y' g) (H.e y g) ∧ HEq (0 : W') (0 : W) := by
  cases hW; cases hn; cases hp; cases hH; cases hy
  exact ⟨HEq.rfl, HEq.rfl⟩

theorem heq_app {K V W W' : Type} [Field K] [AddCommGroup V] [Module K V] {σ : K →+* ℂ}
    (n : NormedAddCommGroup W) (p : InnerProductSpace ℂ W) (n' : NormedAddCommGroup W') (p' : InnerProductSpace ℂ W')
    (hW : HEq W' W) (hn : HEq n' n) (hp : HEq p' p) (c' : V →ₛₗ[σ] W') (c : V →ₛₗ[σ] W) (h : HEq c' c) (v : V) :
    HEq (c' v) (c v) := by
  cases hW; cases hn; cases hp; cases h
  exact HEq.rfl

def RepsOver (D : D7) (i : Fin D.R.m) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (βV : ∀ i, GL (Fin (Vc D i).rank) (Lev.EAf D))
    {K' : Type} [Field K'] (bad : ℕ) {Cl : Type} (h : Cl → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i)))
    (Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)) (gam : Cl → ℕ) (vol : K') : Prop :=
  bad ≠ 0 ∧ (∀ PP, PP ∈ Pg ∨ PP ∈ Q → ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧
    J' ≤ (levEnv (Vc D i) (βV i) (datY _ D.R.r D.R.t 1 (r_le_V i) Pg Q (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.A)).J ∧
    J'.relIndex (levEnv (Vc D i) (βV i)
      (datY _ D.R.r D.R.t 1 (r_le_V i) Pg Q (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.A)).J ≠ 0 ∧
    vol = ((J'.relIndex (levEnv (Vc D i) (βV i)
      (datY _ D.R.r D.R.t 1 (r_le_V i) Pg Q (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.A)).J : ℕ) : K')⁻¹ ∧
    Bridge.IsReps (Bridge.ratF (Vc D i)) J' (fun k => fin _ (h k)) ∧
    ∀ k, SplitOffBad (Vc D i) bad (h k) ∧ Lh k = Bridge.hLat (Vc D i) (fin _ (h k)) ∧
      gam k = Nat.card (Bridge.stab (Bridge.ratF (Vc D i)) J' (fin _ (h k)))

theorem repsOver_cast {D : D7} {i : Fin D.R.m} {Pg₁ Pg₂ Q₁ Q₂ : Finset (Formalism.L2.DIV.Pl D.host.E)} {β₁ β₂} {K' : Type} [Field K'] {bad : ℕ}
    {Cl : Type} {h : Cl → GA D (Vc D i)} {J' Lh gam} {vol : K'} (hP : HEq Pg₂ Pg₁) (hQ₁ : Q₁ = ∅) (hQ₂ : Q₂ = ∅) (hβ : HEq β₂ β₁)
    (H : RepsOver D i Pg₁ Q₁ β₁ bad h J' Lh gam vol) : RepsOver D i Pg₂ Q₂ β₂ bad h J' Lh gam vol := by
  cases hP; cases hβ; subst hQ₁ hQ₂
  exact H

theorem inj_of_li {L K I W : Type} [Field L] [CharZero L] [Field K] [Fintype I] [AddCommGroup W] [Module ℂ W] {n : ℕ} (lam : I → DomWeight n)
    {σL : L →+* ℂ} {σK : K →+* ℂ} (jL : L →+* K) (s : Function.Surjective jL)
    {cL : VV L lam →ₛₗ[σL] W} {cK : VV K lam →ₛₗ[σK] W}
    (hc : ∀ v : VV L lam, ∃ v' : VV K lam, (v' : Pol K I n) = MvPolynomial.map jL (v : Pol L I n) ∧ cK v' = cL v)
    (hli : LinearIndependent ℂ fun i => cL (bVV L lam i)) : Function.Injective cK := by
  have hL : ∀ u : VV L lam, cL u = 0 → u = 0 := fun u hu => by
    have e := (bVV L lam).sum_repr u
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e, map_sum] at hu
    simp only [LinearMap.map_smulₛₗ] at hu
    have := Fintype.linearIndependent_iff.1 hli _ hu
    exact (bVV L lam).repr.injective (Finsupp.ext fun i => by
      rw [map_zero]; exact σL.injective ((this i).trans (map_zero _).symm))
  refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
  let q := (RingEquiv.ofBijective jL ⟨jL.injective, s⟩).symm
  have h1 : jL.comp q.toRingHom = RingHom.id K := RingHom.ext fun x => (RingEquiv.ofBijective jL ⟨jL.injective, s⟩).apply_symm_apply x
  obtain ⟨a, a1, a2⟩ := hc ⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV q.toRingHom lam _ v.2⟩
  have e : a = v := Subtype.ext (a1.trans (by rw [MvPolynomial.map_map, h1, MvPolynomial.map_id]))
  subst e
  have h0 := hL _ (a2.symm.trans hv)
  rw [h0] at a1
  exact Subtype.ext (a1.trans (map_zero _))

theorem normalisedData_coefficientMap_injective {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}
    (O : OMDat C R i Unit (fun _ => A.μ0)) {κ v₀ ι x₀} (hOF : O.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange)
    (hO : O.Pins κ v₀ ι x₀) : Function.Injective O.c0' := by
  have sj : Function.Surjective O.jL := fun y => by
    obtain ⟨x, hx⟩ := hOF.le y.2
    exact ⟨x, Subtype.ext ((RingHom.congr_fun hO.lift.field x).trans hx)⟩
  obtain ⟨g, r, c0L, hT, hbc⟩ := hO.lift.c0
  exact inj_of_li (lamV D i) O.jL sj hbc (hT.mapL i).2.1


set_option maxHeartbeats 4000000 in
theorem omOver_of_isBCOf (X X' : Stages) (hP : X'.B.toPre = X.B.toPre)
    {G : Type} [Group G] [Fintype G] {Pl0 T0 Pl0' T0' : Type} {A : FamIn X.toD7.what₂.LL G Pl0 T0 X.toD7.R.m}
    {A' : FamIn X'.toD7.what₂.LL G Pl0' T0' X'.toD7.R.m} (T : CoreJ X.toD7) [Algebra T.Q.c.F X.toD7.what₂.LL]
    (T' : CoreJ X'.toD7) [alg' : Algebra T'.Q.c.F X'.toD7.what₂.LL] (R : RealDat X.toD7 A T.Q.c.F) (R' : RealDat X'.toD7 A' T'.Q.c.F)
    (eH : HEq T'.Q.H T.Q.H) (el : HEq T'.Q.l T.Q.l) (ec : HEq T'.Q.c T.Q.c) (eD : HEq T'.Q.Dw T.Q.Dw) (eX : HEq T'.Q.Xo T.Q.Xo)
    (ePg : HEq R'.Pg R.Pg) (eβV : HEq R'.βV R.βV) (hL : R.toLevCh.Is A.μ0) (hL' : R'.toLevCh.Is A'.μ0)
    (i : Fin X.toD7.R.m) (i' : Fin X'.toD7.R.m) (hi : (i : ℕ) = i')
    (eW : HEq (R'.cV i').W (R.cV i).W) (en : HEq (R'.cV i').nW (R.cV i).nW) (ei : HEq (R'.cV i').iW (R.cV i).iW)
    (eHV : HEq (R'.HV i' A'.μ0) (R.HV i A.μ0))
    (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) (O' : OMDat T'.toCore R' i' Unit (fun _ => A'.μ0))
    {κ ι x₀} {v₀ : (R.MW i (sg0 X.toD7 A)).Vec} {v₀' : (R'.MW i' (sg0 X'.toD7 A')).Vec} (hO : O.Pins κ v₀ ι x₀)
    (hinj : Function.Injective O.c0')
    (h : IsBCOf O' v₀' O v₀ κ ι x₀ (∀ x : A.fam.amb.FL i A.μ0, x = 0)) : GeoTies.OmOver O O' := by
  have hQ := GlobalTheory.RefPins.places_ref R hL
  have hQ' := GlobalTheory.RefPins.places_ref R' hL'
  obtain ⟨c₃, hs, c0₃, io₃, hw₃, h₀, J₀, hB, hS, hor, -⟩ := h
  obtain ⟨B', C', W', V', S', N', G'⟩ := X'
  rcases B' with ⟨P'⟩
  change P' = X.B.toPre at hP
  subst hP
  obtain ⟨⟨⟨H', l', c', Dw', Xo', eO'⟩, U', V'', dict', mu', Kf', pb'⟩, cE', chiW', x₀', iota'⟩ := T'
  dsimp only at eH el ec eD eX
  obtain rfl := eq_of_heq eH
  obtain rfl := eq_of_heq el
  obtain rfl := eq_of_heq ec
  obtain rfl := eq_of_heq eD
  obtain rfl := eq_of_heq eX
  obtain rfl : i = i' := Fin.ext hi
  obtain @⟨c'', hle, jL, hV, c0', lev, dδ, Cl', fCl, bad, Lh, La, Nc, gam, vol, ep, BB, epF, io, hw, φ, w, U₂, dict₂, xi, thAd, Plc⟩ := O'
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, -, -, s15, -, -, s18, -, -, -⟩ := hS
  dsimp only [bc, merge] at s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s15 s18 hor
  obtain rfl := eq_of_heq s1
  subst s4
  subst s6
  obtain rfl := eq_of_heq s3
  obtain rfl := eq_of_heq s5
  obtain rfl := eq_of_heq s7
  obtain rfl := eq_of_heq s8
  obtain rfl := eq_of_heq s9
  obtain rfl := eq_of_heq s10
  obtain rfl := eq_of_heq s11
  obtain rfl := eq_of_heq s12
  obtain rfl := eq_of_heq s15
  obtain rfl := eq_of_heq s18
  refine ⟨s2, c'', hs, HEq.rfl, fun h J hr => ⟨(by with_unfolding_all exact (h :)), (by with_unfolding_all exact (J :)), ?_, fun x₀ x hx y' hy => ?_⟩⟩
  · exact (by with_unfolding_all exact ((repsOver_cast (D := X.toD7) (Pg₂ := R'.Pg) (Q₂ := R'.Q A'.μ0) (β₂ := (R'.βV)) ePg hQ hQ' ((eβV))
      (show RepsOver X.toD7 i R.Pg (R.Q A.μ0) R.βV _ h J _ _ _ from repsR_map (incF O.c' c'' hs) hr)) : _))
  · choose x' hx' using fun k => GlobalTheory.FieldBCModel.exists_over hs (lamV X.toD7 i) (x k)
    refine ⟨(by with_unfolding_all exact (x' :)), ?_, fun a n f hf hfx f' e => ?_⟩
    · intro k
      have hv := heq_val (Γ := Bridge.Gf (Vc X.toD7 i)) (R.cV i).nW (R.cV i).iW (R'.cV i).nW (R'.cV i).iW eW en ei (R.HV i A.μ0)
        ((by with_unfolding_all exact ((R'.HV i A'.μ0) :))) ((by with_unfolding_all exact (eHV :))) (jVx R i A.μ0 x₀) ((by with_unfolding_all exact (y' :))) ((by with_unfolding_all exact (hy :))) (fin _ (h k))
      rcases hor with hc | hp
      · have ha := heq_app (V := VsV X.toD7 i c''.F) (σ := inC c'') (R.cV i).nW (R.cV i).iW (R'.cV i).nW (R'.cV i).iW eW en ei
          ((by with_unfolding_all exact (c0' :))) c0₃ ((by with_unfolding_all exact (hc :))) (x' k)
        exact (by with_unfolding_all exact ((eq_of_heq (hv.1.trans ((heq_of_eq ((hx k).trans (hB.c0 _ _ (hx' k)).symm)).trans ha.symm))) :))
      · have h0 : (R.HV i A.μ0).e (jVx R i A.μ0 x₀) (fin _ (h k)) = 0 := by
          rw [hp x₀]
          unfold jVx
          rw [map_zero, map_zero]
          rfl
        have h1 : x k = 0 := hinj (((hx k).symm.trans h0).trans (map_zero _).symm)
        have h2 : x' k = 0 := Subtype.ext ((hx' k).trans (by rw [h1]; exact map_zero _))
        have h3 := eq_of_heq (hv.1.trans ((heq_of_eq h0).trans hv.2.symm))
        have h4 : ∀ c : VsV X.toD7 i c''.F →ₛₗ[inC c''] (R'.cV i).W, 0 = c (x' k) := fun c => by rw [h2, map_zero]
        exact (by with_unfolding_all exact ((h3.trans (h4 ((c0')))) : _))
    · obtain rfl := eq_of_heq e
      exact (by with_unfolding_all exact ((isThClsD_covBC_one hs (O.dδ ()) rfl _ _ _ _ _ _ O.io io x x' (fun k => hB.io _ _ (hx' k))
        (hO.cov ()).1.2.2.2.2.2.2.2.1 hf hfx) :))

end GlobalTheory.Mem.R3.Rw.OmExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowFlatLocallyQuasiFinite
section
open AlgebraicGeometry CategoryTheory Limits MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemiAbMulFlat

open FibreFlat FiniteFibreFlat


set_option backward.isDefEq.respectTransparency false in
theorem flat_of_flatOver_fields {X Y S : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ S)
    (hY : LocallyOfFinitePresentation g) (h0 : LocallyOfFinitePresentation (f ≫ g))
    (h1 : Flat (f ≫ g)) (h2 : LocallyQuasiFinite f)
    (H : ∀ (k : Type) [Field k] (t : Spec (CommRingCat.of k) ⟶ S), FlatOver f g t) :
    Flat f := by
  wlog hS : ∃ R, S = Spec R generalizing X Y S
  · refine IsZariskiLocalAtTarget.of_openCover (S.affineCover.pullback₁ g) fun i => ?_
    let u := S.affineCover.f i
    have sq := IsPullback.of_hasPullback f (pullback.fst g u)
    have sq' := IsPullback.of_hasPullback g u
    refine this (pullback.snd f (pullback.fst g u)) (pullback.snd g u)
      inferInstance (MorphismProperty.of_isPullback (sq.paste_vert sq') h0)
      (MorphismProperty.of_isPullback (sq.paste_vert sq') h1) inferInstance
      (fun k _ t => flatOver_of_comp_base (u := u) ?_) ⟨_, rfl⟩
    rw [← pullback.condition]
    exact (H k _).target sq
  obtain ⟨R, rfl⟩ := hS
  wlog hA : ∃ A, Y = Spec A generalizing X Y
  · refine IsZariskiLocalAtTarget.of_openCover Y.affineCover fun i => ?_
    have sq := IsPullback.of_hasPullback f (Y.affineCover.f i)
    have e : pullback.snd f (Y.affineCover.f i) ≫ Y.affineCover.f i ≫ g =
        pullback.fst f (Y.affineCover.f i) ≫ f ≫ g := by
      rw [← Category.assoc, ← sq.w, Category.assoc]
    exact this (pullback.snd f (Y.affineCover.f i)) inferInstance (Y.affineCover.f i ≫ g)
      inferInstance (by rw [e]; infer_instance) (by rw [e]; infer_instance)
      (fun k _ t => (H k t).target sq) ⟨_, rfl⟩
  obtain ⟨A, rfl⟩ := hA
  wlog hX : ∃ B, X = Spec B generalizing X
  · refine IsZariskiLocalAtSource.of_openCover X.affineCover fun i => ?_
    exact this (X.affineCover.f i ≫ f) inferInstance (by rw [Category.assoc]; infer_instance)
      (by rw [Category.assoc]; infer_instance)
      (fun k _ t => (H k t).source _) ⟨_, rfl⟩
  obtain ⟨B, rfl⟩ := hX
  obtain ⟨f, rfl⟩ := Spec.map_surjective f
  obtain ⟨g, rfl⟩ := Spec.map_surjective g
  rw [← Spec.map_comp] at h1 h0
  rw [Flat.SpecMap_iff] at h1 ⊢
  rw [HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)] at h2
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)] at hY h0
  letI : Algebra R A := g.hom.toAlgebra
  letI : Algebra A B := f.hom.toAlgebra
  letI : Algebra R B := (g ≫ f).hom.toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Flat R B := h1
  haveI : Algebra.QuasiFinite A B := h2
  haveI : Algebra.FinitePresentation R A := hY
  haveI : Algebra.FinitePresentation R B := h0
  haveI : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R A B
  refine _root_.GlobalTheory.flat_of_quasiFinite_of_flat_fibres R A B fun k C _ _ _ t h e => ?_
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A C B)
  have := H k (Spec.map (CommRingCat.ofHom t)) _ _ _ (Spec.map (CommRingCat.ofHom h)) sq.flip
    (by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext1
      exact e)
  rw [Flat.SpecMap_iff] at this
  exact RingHom.flat_algebraMap_iff.mp this

theorem flat_and_locallyQuasiFinite_pow :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ q : ℕ, q ≠ 0 →
      Flat ((𝟙 G) ^ q : G ⟶ G).left ∧ LocallyQuasiFinite ((𝟙 G) ^ q : G ⟶ G).left := by
  intro S G _ _ hG n hn
  change Flat (Out.mulA G n).left ∧ LocallyQuasiFinite (Out.mulA G n).left
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have hm := AbLaw.MulN.isMonHom_mulA G n
  have : LocallyOfFiniteType ((Out.mulA G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType (Out.mulA G n).left := locallyOfFiniteType_of_comp _ G.hom
  have : QuasiCompact ((Out.mulA G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact (Out.mulA G n).left := QuasiCompact.of_comp _ G.hom
  have hq : LocallyQuasiFinite (Out.mulA G n).left :=
    locallyQuasiFinite_of_finite_geometric_ker _ G G _ hm inferInstance inferInstance fun K _ _ t => by
      simp only [IntDiv.comp_mulA]
      exact HomExt.finite_torsion_points hG t (Nat.pos_of_ne_zero hn)
  refine ⟨flat_of_flatOver_fields _ G.hom inferInstance (by rw [Over.w]; infer_instance)
    (by rw [Over.w]; infer_instance) hq fun k _ t => ?_, hq⟩
  exact flatOver_of_pullback _ _ (IntDiv.flat_fibre G _ k t)

end GlobalTheory.SemiAbMulFlat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreimageConnectedComponentMem
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.PtComp

theorem disjoint_of_smooth {K : Type} [Field K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (hsm : Smooth f)
    (Z Z' : Set X) (hZ : Z ∈ irreducibleComponents X) (hZ' : Z' ∈ irreducibleComponents X) (hne : Z ≠ Z') :
    Disjoint Z Z' := by
  refine CompSplitPfD.cspD_disj (fun x => ?_) Z Z' hZ hZ' hne
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hV' : IsAffineOpen V := hV
  have h1 := HasRingHomProperty.appLE (P := @Smooth) f hsm
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ (fun p _ => by simp)
  let ψ : K →+* Γ(X, V) :=
    (f.appLE ⊤ V (fun p _ => by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have hψ : ψ.Smooth := RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.bijective) h1
  let _ : Algebra K Γ(X, V) := ψ.toAlgebra
  have : Algebra.Smooth K Γ(X, V) := hψ
  obtain ⟨r, hr, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := K)
    (p := (hV'.primeIdealOf ⟨x, hxV⟩).asIdeal)
  refine ⟨PrimeSpectrum (Localization.Away r), inferInstance,
    hV'.fromSpec ∘ PrimeSpectrum.comap (algebraMap Γ(X, V) (Localization.Away r)), ?_, ?_, ?_⟩
  · exact (hV'.fromSpec.isOpenEmbedding).comp (PrimeSpectrum.localization_away_isOpenEmbedding _ r)
  · obtain ⟨z, hz⟩ : hV'.primeIdealOf ⟨x, hxV⟩ ∈
        Set.range (PrimeSpectrum.comap (algebraMap Γ(X, V) (Localization.Away r))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
      exact hr
    refine ⟨z, ?_⟩
    show hV'.fromSpec (PrimeSpectrum.comap (algebraMap Γ(X, V) (Localization.Away r)) z) = x
    rw [hz]
    exact hV'.fromSpec_primeIdealOf ⟨x, hxV⟩
  · intro a b y ha hb hay hby
    have : IsIntegrallyClosed (MvPolynomial (Fin n) K) := UniqueFactorizationMonoid.instIsIntegrallyClosed
    have hmin : ∀ a : PrimeSpectrum (Localization.Away r), (∀ a', a' ⤳ a → a' = a) →
        a.asIdeal ∈ minimalPrimes (Localization.Away r) := by
      intro a ha
      refine ⟨⟨a.isPrime, bot_le⟩, fun J hJ hJa => ?_⟩
      have := ha ⟨J, hJ.1⟩ ((PrimeSpectrum.le_iff_specializes _ _).1 hJa)
      exact (congrArg PrimeSpectrum.asIdeal this).ge
    exact PrimeSpectrum.ext (CompSplitPfC.cspC_minimal_unique (MvPolynomial (Fin n) K) (q := y.asIdeal)
      (hmin a ha) (hmin b hb) ((PrimeSpectrum.le_iff_specializes _ _).2 hay)
      ((PrimeSpectrum.le_iff_specializes _ _).2 hby))

theorem connectedComponent_mem {X : Type} [TopologicalSpace X] (hfin : (irreducibleComponents X).Finite)
    (hd : ∀ Z ∈ irreducibleComponents X, ∀ Z' ∈ irreducibleComponents X, Z ≠ Z' → Disjoint Z Z') (z : X) :
    connectedComponent z ∈ irreducibleComponents X ∧ IsOpen (connectedComponent z) := by
  have hV := irreducibleComponent_mem_irreducibleComponents z
  have hU : irreducibleComponent z = (⋃ W ∈ irreducibleComponents X \ {irreducibleComponent z}, W)ᶜ := by
    ext p
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    constructor
    · intro hp W hW hpW
      exact Set.disjoint_left.1 (hd _ hW.1 _ hV hW.2) hpW hp
    · intro hp
      by_contra hpZ
      exact hp _ ⟨irreducibleComponent_mem_irreducibleComponents p,
        fun h => hpZ ((show irreducibleComponent p = _ from h) ▸ mem_irreducibleComponent)⟩ mem_irreducibleComponent
  have ho : IsOpen (irreducibleComponent z) := by
    rw [hU]
    exact ((hfin.subset Set.diff_subset).isClosed_biUnion fun W hW =>
      isClosed_of_mem_irreducibleComponents _ hW.1).isOpen_compl
  have e : connectedComponent z = irreducibleComponent z :=
    ((IsClopen.connectedComponent_subset ⟨isClosed_irreducibleComponent, ho⟩ mem_irreducibleComponent)).antisymm
      irreducibleComponent_subset_connectedComponent
  rw [e]
  exact ⟨hV, ho⟩

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem preimage_connectedComponent_mem (Z : Model Xo c β) (hsm : Smooth (genStr Z)) (z : gen Z) :
    Z.jQ ⁻¹' connectedComponent z ∈ irreducibleComponents (Xo.XF c) := by
  have := isProper_genStr Z
  have : IsLocallyNoetherian (gen Z) := LocallyOfFiniteType.isLocallyNoetherian (genStr Z)
  have : CompactSpace (gen Z) := QuasiCompact.compactSpace_of_compactSpace (genStr Z)
  have : IsNoetherian (gen Z) := {}
  obtain ⟨h1, h2⟩ := connectedComponent_mem TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
    (fun W hW W' hW' => disjoint_of_smooth (genStr Z) hsm W W' hW hW') z
  have := Z.jQ_open
  exact preimage_mem_irreducibleComponents h1 Z.jQ.isOpenEmbedding
    (Z.jQ_dense.inter_open_nonempty _ h2 ⟨z, mem_connectedComponent⟩)

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ)

theorem exists_equiv : ∃ q : s.Comp ≃ Comp (S.Xo κ.l) κ.c, ∀ k z,
    OnComp s k z ↔ (q k).1 = s.T.Z.jQ ⁻¹' connectedComponent z := by
  have hσ : Formalism.L2.PjFree.GoodEmb κ.c κ.σ₀ := rfl
  have hne : ∀ k, ((s.U κ.σ₀).X k).dom.Nonempty := fun k => GlobalTheory.OrbitScalar.exists_mem_dom _
  obtain ⟨q, hq⟩ := GlobalTheory.UnifComp.exists_equiv_comp _ _ _ _ _ _ κ.σ₀ N (s.U κ.σ₀) hσ (s.unf _ hσ).1 hne s.geo
  have hsm : Smooth (genStr s.T.Z) := haveI := s.T.smooth; SmoothOfRelativeDimension.smooth S.Dw.dim _
  refine ⟨q, fun k z => ⟨?_, fun h => ?_⟩⟩
  · rintro ⟨x, hx⟩
    by_contra hn
    let pt : Sp (CAt κ.σ₀) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
    exact Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj _ _ (q k)
      ⟨_, preimage_connectedComponent_mem s.T.Z hsm z⟩ fun e => hn (congrArg Subtype.val e)) (hq k x pt) (hx pt)
  · obtain ⟨x, hx⟩ := hne k
    refine ⟨⟨x, hx⟩, fun pt => ?_⟩
    have := hq k ⟨x, hx⟩ pt
    rw [h] at this
    exact this

theorem existsUnique_onComp (z : gen s.T.Z) : ∃! k, OnComp s k z := by
  obtain ⟨q, hq⟩ := exists_equiv s
  have hsm : Smooth (genStr s.T.Z) := haveI := s.T.smooth; SmoothOfRelativeDimension.smooth S.Dw.dim _
  refine ⟨q.symm ⟨_, preimage_connectedComponent_mem s.T.Z hsm z⟩, (hq _ _).2 (by rw [Equiv.apply_symm_apply]),
    fun k hk => ?_⟩
  rw [Equiv.eq_symm_apply]
  exact Subtype.ext ((hq _ _).1 hk)

theorem onComp_compPt (y : Pt s) (pt : Sp Qb) : OnComp s (compPt s y) (y.y pt) := by
  obtain ⟨k, hk, -⟩ := existsUnique_onComp s (y.y pt)
  have : ∃ k, ∀ pt', OnComp s k (y.y pt') :=
    ⟨k, fun pt' => (Subsingleton.elim (α := PrimeSpectrum Qb) pt pt') ▸ hk⟩
  exact Classical.epsilon_spec this pt

end GlobalTheory.ShFam.PtComp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionInvariantFrameFunction
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.KeyRel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem evR_sameLie {S : Type} [CommRing S] [Algebra c.F S] [IsLocalRing S] {e : Ix Dw → ℤ} (he : e none = 0)
    {g : Rul Xo c} (hg : g ∈ GlobalTheory.AllWt.secZ Xo c e) {y y' : FrPt Xo c S} (h : SameLie y y') :
    evR Xo c g y' = evR Xo c g y := by
  obtain ⟨g0, a, -, hc⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c S y y').1 h.1.symm
  have h1 := (GlobalTheory.Frames.frChg_calculus E H Dw l Xo c S).2.1 y
  let T : Ix Dw → Sˣ := fun k => k.elim a fun _ => 1
  have hb : FrBor T y y' := ((GlobalTheory.Frames.frChg_calculus E H Dw l Xo c S).2.2.2 T y y').2
    ⟨fun _ => 1, fun τ i => Matrix.one_apply_eq i, fun τ i j hij => Matrix.one_apply_ne hij.ne, hc.1,
      fun τ i => h.2 τ i ▸ h1.2.1 τ i, hc.2.2⟩
  rw [GlobalTheory.FlagTan.evR_frBor hg hb, Fintype.prod_option, he, zpow_zero, _root_.one_mul]
  simp [T]

end GlobalTheory.ShFam.KeyRel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfoldedIsSecZeroKeySection
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries

namespace GlobalTheory.CuspFrom.KeyHol

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem exists_sec_rdU_ne_zero (U : Formalism.L2.PjFree.Unf Xo c σ r) (k : U.Comp) (x₀ : Frame (U.X k).Ψ r)
    (hx₀ : x₀ ∈ (U.X k).dom) :
    ∃ (m : ℕ) (f : Rul Xo c), f ∈ sec Xo c 0 (2 * (m + 1)) ∧ Formalism.L2.PjFree.rdU U f k x₀ ≠ 0 := by
  have hT : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c
  have hR : Odd 3 := by decide
  have h1 : 1 < 3 := by norm_num
  obtain ⟨hfG, hfL, -⟩ := GlobalTheory.EtaCard.card_levGrp_and_span E H Dw 3 h1
  letI hFin : Fintype (GlobalTheory.EtaForm.LatMod Dw 3) := Fintype.ofFinite _
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  obtain ⟨cf, -, hne⟩ := GlobalTheory.EtaForm.exists_small_coeff_etaValAt_ne_zero GlobalTheory.firstFiveLaws.1 E H Dw l Xo c 3 hR h1
    2 0 (CAt σ) 1 (fun _ => U.un k ⟨x₀, hx₀⟩)
  obtain ⟨⟨f, hrule, -⟩, hsec⟩ := GlobalTheory.EtaForm.isEtaRule_existsUnique_mem_sec GlobalTheory.firstFiveLaws.1 E H Dw l Xo c 3 hR
    (Fin 2 → GlobalTheory.EtaForm.LatMod Dw 3) 2 (fun j => (cf j : ℤ)) (GlobalTheory.EtaForm.shiftFam 3 0)
  have hpos : 0 < Nat.card (GlobalTheory.EtaForm.LevGrp Dw (3 ^ 4)) := Nat.card_pos
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  refine ⟨m, f, by have := hsec f hrule; rwa [hm] at this, ?_⟩
  have hv := (GlobalTheory.EtaForm.etaValAt_evR_of_fromTest E H Dw l Xo c 3 hR _ _ _ _ f hrule (CAt σ) (U.un k ⟨x₀, hx₀⟩)
    (hT _ _)).1
  have h0 := hne 0 _ hv
  have e1 : Formalism.L2.PjFree.rdU U f k x₀ = Formalism.L2.PjFree.toC (evR Xo c f (U.un k ⟨x₀, hx₀⟩)) := dif_pos hx₀
  rw [e1]
  exact h0

end GlobalTheory.CuspFrom.KeyHol
end
end

