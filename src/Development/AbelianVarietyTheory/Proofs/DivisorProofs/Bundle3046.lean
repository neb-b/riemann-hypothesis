module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTowerFramesPullbackConstantRoot
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2532
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3026
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2698
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2697
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2692
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2814
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0920
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2995
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3031
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2869
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2926
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2898
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3038
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorusMemOfSepAtBTate
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2994
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1272
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLFunctionBottomPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2871
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2856
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2870

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTowerFramesPullbackConstantRootStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep.BaseTerms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tower_frames_pullback_constant_root : ∀ {I : Type} (X₁ : GlobalTheory.GSep.GSet) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : GlobalTheory.GSep.Tower X₁ act), ∃ k : X₁.S.Gam → ℕ,
    ∀ (z₁ : X₁.M.Z) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X]
      (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ)
      (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V') (f : FractionRing V →+* FractionRing V'),
      (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) →
    ∀ (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (X' : Type) [AddCommGroup X'] (t' : X' → V')
      (δ' : I → X' → X') (𝔪₂ : GlobalTheory.GSep.GMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X' t' δ') (ψ : 𝔪₂.A.A.left ⟶ 𝔪.A.A.left)
      (w : LB.Iso 𝔪₂.A.L (𝔪.A.L.pull ψ)), w.IsGen → 𝔗.Ext ev io ev₂ → 𝔪₂.yK.comp 𝔗.om = f.comp 𝔪.yK →
      IsGrpPullback 𝔪₂.A.A 𝔪.A.A (spMap f) ψ → 𝔪₂.φ ≫ 𝔗.φ = ψ ≫ 𝔪.φ →
    ∀ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)),
      (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) →
      (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
        Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
          val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) →
    ∀ (x₂ : 𝔗.X₂.S.Gam → (TFK (R := V') (FractionRing V') ⟶ 𝔪₂.A.A)) (fr₂ : ∀ a, FrAt (x₂ a)),
      (∀ a, (x₂ a).left ≫ 𝔪₂.φ = spMap 𝔪₂.yK ≫ (𝔗.X₂.ρ.pt a).left) →
      (∀ a, (fr₂ a).IsGen ∧ ∀ z J J', Good 𝔗.X₂.ρ.P.L z J → Good 𝔪₂.A.L z J' →
        Geo.Tor.gw 𝔪₂.wl (x₂ a).left z (J ((x₂ a).left ≫ 𝔪₂.φ)) (J' (x₂ a).left) * val (fr₂ a) (𝟙 _) z J' =
          val (𝔗.X₂.ρ.fr a) (show (TFK (R := V') (FractionRing V')).left ⟶ (baseOver (Sp 𝔗.X₂.S.R)).left from spMap 𝔪₂.yK) z J) →
    ∃ c : (FractionRing V')ˣ, ∀ b, FrPull w f (x₂ (𝔗.lam b)) (fr₂ (𝔗.lam b)) (x b) (fr b)
      ((c : FractionRing V') * 𝔪₂.yK ⟨algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ, 𝔗.X₂.S.R.algebraMap_mem _⟩ ^ k b) := by
  first | exact @GlobalTheory.GSep.exists_frPull_tower | exact GlobalTheory.GSep.exists_frPull_tower | (intros; apply GlobalTheory.GSep.exists_frPull_tower <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTripleMapOfSameUniformisedCoords
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UCanon.sabMap_of_same_coords : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base R → GlobalTheory.Mum.Base V → ∀ (t₁ : SAB H (Sp R)) (P₁ : PELUnif (maximalIdeal R) t₁) (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (iw : L.W →+* R) (θ : R →+* V), IsLocalHom θ → ∀ {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e₁ : P₁.D.toPre.X ≃ₗ[𝓞 E] L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, θ (s k) ≠ 0) → DivFrom L P₁.D.toPre P₁.oD iw s ε e₁ → DivFrom L P.D.toPre P.oD (θ.comp iw) (fun k => θ (s k)) ε e → Nonempty (SABMap t t₁ (spMap θ)) := by
  intro E _ _ _ H D' l c L R V _ _ _ _ _ _ bR bV t₁ P₁ t P iw θ hθ I _ s ε e₁ e hs h₁ h
  classical

  set f : R := ∏ k, s k with hf
  have hfθ : θ f ≠ 0 := by
    rw [hf, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => hs k
  have hdiv : ∀ k, ∃ n : ℕ, s k ∣ f ^ n := fun k =>
    ⟨1, by rw [pow_one, hf]; exact Finset.dvd_prod_of_mem s (Finset.mem_univ k)⟩
  have hpsi := GlobalTheory.T.psiUnitOn_basicOpen_of_comesFromBase L P₁.D.toPre P₁.oD iw s ε e₁ h₁ f hdiv
  obtain ⟨t', P', hD, ⟨m⟩, hx, hact⟩ := GlobalTheory.T.exists_linearUniformisation_pullback_localMap R V bR bV t₁ P₁ θ hθ f hfθ hpsi
  let e' : P'.D.toPre.X ≃ₗ[𝓞 E] L.D.X := (hD.xe.toLinearEquiv hx).trans e₁
  have h' := GlobalTheory.T.comesFromBase_stable_under_pullback_of_data L P₁.D.toPre P₁.oD P'.D.toPre P'.oD iw θ s ε e₁ hD e' (fun y => rfl) hact hs h₁
  obtain ⟨hD₂, he₂, hact₂⟩ := GlobalTheory.T.exists_isPullDeg_id_same_coordinates L P'.D.toPre P'.oD P.D.toPre P.oD (θ.comp iw) (fun k => θ (s k)) ε e' e
    hs h' h
  have hx₂ : ∀ (x : 𝓞 E) y, hD₂.xe (x • y) = x • hD₂.xe y := by
    intro x y
    apply e'.injective
    rw [he₂, map_smul, map_smul, he₂]
  obtain ⟨m₂⟩ := GlobalTheory.T.tripleIso_of_linear_degenerationData_iso V bV t' t P' P hD₂ hx₂ hact₂
  exact GlobalTheory.TraitOrder.comp (Category.id_comp _) m m₂
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryLocalPeriodsThetaModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem GlobalTheory.UPoinc.UPeriods.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (πY : Y.Z ⟶ X₁.M.Z), X₁.S.admitted Y U₀ → X₁.S.IsEE Y U₀ EE → X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → ∀ x : Y.Z, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (j : Y.Z.presheaf.stalk x →+* R) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (p : Λ → R) (c₀ : ℕ), IsNoetherianRing R ∧ CharZero R ∧ GlobalTheory.Poinc.Eq8.IsCpl j ∧ 1 ≤ c₀ ∧ ∀ (T : UTrait Xo c) (ψ : R →+* T.V), IsLocalHom ψ → T.y ≫ C.i = jK T.V ≫ (spMap (ψ.comp j) ≫ Y.Z.fromSpecStalk x) ≫ πY ≫ X₁.π → ∃ e : Λ ≃ₗ[𝓞 E] T.P.D.toPre.X, ∀ a, ∃ k : ℕ, (k : ℤ) = c₀ * T.be (e a) (e a) ∧ Associated (ψ (p a)) (T.ϖ ^ k) := by
  intro E _ _ _ H Dw _ l Xo c C X₁ Y U₀ EE out πY hAdm _ hHom x
  have hpt : Y.pt ≫ πY ≫ X₁.π = X₁.uΩ ≫ C.i := by
    have h1 : Y.pt ≫ πY = X₁.M.pt := by
      have := hHom
      unfold RatModel.IsHom at this
      rw [this]
      show Spec.map (CommRingCat.ofHom (RingHom.id X₁.Ω₁)) ≫ _ = _
      rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    rw [← Category.assoc, h1, X₁.comp]
    exact (Category.assoc _ _ _).symm
  obtain ⟨R, i1, i2, i3, j, Λ, i4, i5, p, hB, hC, h⟩ :=
    GlobalTheory.UPoinc.GPeriods.main E H Dw l Xo c C X₁ Y U₀ EE out (πY ≫ X₁.π) hAdm.1 hpt x
  refine ⟨R, i1, i2, i3, j, Λ, i4, i5, p, 1, hB.1.1, hB.2, hC, le_rfl, fun T ψ hψ ht => ?_⟩
  obtain ⟨e, he⟩ := h T ψ hψ (by rw [ht])
  refine ⟨e, fun a => ?_⟩
  obtain ⟨k, hk, hA⟩ := he a
  exact ⟨k, by rw [hk]; push_cast; ring, hA⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Factorization
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

namespace GlobalTheory.LKGeo.LiftSys

theorem exists_lift_sys : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)), (∀ v ∈ LaHat D, h₀ v ∈ LaHat D) → ∃ h : ℕ → D.La →+ D.La, ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, h₀ (inAf D x) = inAf D (h n x) + n • w := by
  intro p _ D h₀ hh
  classical
  haveI := D.freeLa
  haveI := D.finLa
  let Ix := Module.Free.ChooseBasisIndex ℤ D.La
  let b : Module.Basis Ix ℤ D.La := Module.Free.chooseBasis ℤ D.La
  let iA : D.La →+ AfP p ⊗[ℚ] VQ D :=
    AddMonoidHom.mk' (inAf D) (fun x y => by simp only [inAf, TensorProduct.tmul_add])
  have hiA : ∀ x, iA x = inAf D x := fun _ => rfl
  have key : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ i : Ix, ∃ (x : D.La) (w : AfP p ⊗[ℚ] VQ D),
      w ∈ LaHat D ∧ h₀ (inAf D (b i)) = inAf D x + n • w := fun n hn hnp i =>
    exists_inAf_add_nsmul_of_mem_laHat p D n hn hnp _ (hh _ (AddSubgroup.subset_closure ⟨1, b i, fun v => by rw [map_one]; exact one_mem _, rfl⟩))
  let h : ℕ → D.La →+ D.La := fun n =>
    if hn : 0 < n ∧ n.Coprime p then
      (b.constr ℤ (fun i => (key n hn.1 hn.2 i).choose)).toAddMonoidHom
    else 0
  refine ⟨h, fun n hn hnp x => ?_⟩
  have hx : x ∈ Submodule.span ℤ (Set.range b) := by rw [b.span_eq]; trivial
  have hh' : h n = (b.constr ℤ (fun i => (key n hn hnp i).choose)).toAddMonoidHom := by
    simp only [h, dif_pos (And.intro hn hnp)]
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    obtain ⟨hw, e⟩ := (key n hn hnp i).choose_spec.choose_spec
    have hbi : h n (b i) = (key n hn hnp i).choose := by
      rw [hh']; simp [Module.Basis.constr_basis]
    refine ⟨_, hw, e.trans ?_⟩
    rw [hbi]
  | zero =>
    refine ⟨0, zero_mem _, ?_⟩
    rw [← hiA, ← hiA, map_zero, map_zero, map_zero, map_zero, smul_zero, add_zero]
  | add y z _ _ hy hz =>
    obtain ⟨w₁, hw₁, e₁⟩ := hy
    obtain ⟨w₂, hw₂, e₂⟩ := hz
    refine ⟨w₁ + w₂, add_mem hw₁ hw₂, ?_⟩
    rw [← hiA, ← hiA, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hiA, hiA, hiA, hiA, e₁, e₂, smul_add]
    abel
  | smul c y _ hy =>
    obtain ⟨w, hw, e⟩ := hy
    refine ⟨c • w, zsmul_mem hw c, ?_⟩
    rw [← hiA, ← hiA, map_zsmul, map_zsmul, map_zsmul, hiA, hiA, e, smul_add, smul_comm c (n : ℕ) w]
    rw [← hiA (c • _), map_zsmul, hiA]

end GlobalTheory.LKGeo.LiftSys
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankBalancedSymmIntBilinFormsEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.BalRank.finrank_balForms : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X], Module.finrank ℤ (balForms H.bar X) = Module.finrank ℚ E / 2 * Module.finrank (𝓞 E) X * Module.finrank (𝓞 E) X := by
  intro E _ _ _ H X _ _ _ _
  obtain ⟨f, m, hm, hf, hmf⟩ := _root_.GlobalTheory.latt_free_sub_full_rank (E := E) X
  have h1 := GlobalTheory.T.two_mul_finrank_balancedSymmIntBilinForms H X
  have h2 := GlobalTheory.T.finrank_balancedIntBilinForms_eq_of_finite_index H.bar X _ f m hm hf hmf
  have h3 := _root_.GlobalTheory.BalRank.finrank_balBil_pi H (Fin (Module.finrank (𝓞 E) X))
  rw [Fintype.card_fin] at h3
  obtain ⟨k, hk⟩ : 2 ∣ Module.finrank ℚ E := ⟨_, IsTotallyComplex.finrank E⟩
  rw [hk, Nat.mul_div_cancel_left _ two_pos]
  rw [← h2, h3, hk] at h1
  nlinarith [h1]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorActionFormEqSimilitudeMul
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.LKGeo

theorem actG_form_eq_sim : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (g : G.GAf) (v w : AfP p ⊗[ℚ] VQ D), (D.EF.baseChange ℚ).baseChange (AfP p) (L.actG g v) (L.actG g w) = (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p) * (D.EF.baseChange ℚ).baseChange (AfP p) v w := by
  intro p _ D G L g v w
  set y : (AfP p ⊗[ℚ] G.C)ˣ := (g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 with hy
  set c : AfP p := (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p) with hc
  have hmem : (y : AfP p ⊗[ℚ] G.C) * (starT G.star (AfP p) (y : AfP p ⊗[ℚ] G.C)).unop =
      algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) c := mem_uGroup.1 g.2
  have hsy : (starT G.star (AfP p) (y : AfP p ⊗[ℚ] G.C)).unop * (y : AfP p ⊗[ℚ] G.C) =
      algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) c := by
    have h1 : (starT G.star (AfP p) (y : AfP p ⊗[ℚ] G.C)).unop =
        ((y⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) c := by
      rw [← hmem, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
    rw [h1, _root_.mul_assoc, Algebra.commutes, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
  have hact : ∀ u : AfP p ⊗[ℚ] VQ D, L.actG g u = actOn L.rep (AfP p) (y : AfP p ⊗[ℚ] G.C) u := fun u => rfl
  rw [hact, hact, GlobalTheory.LKGeo.adj_actOn_afP, ← Module.End.mul_apply, ← map_mul, hsy, AlgHom.commutes,
    Module.algebraMap_end_apply, LinearMap.map_smul, smul_eq_mul]

end GlobalTheory.LKGeo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorConjTranslationGaugeStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heatOperator_conj_translation_gauge : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra ℚ R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Fin n → TanM (𝟙 (Sp R)) Y.H) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Q.P.L dd ⇑D), IsBasic Y h → ∀ (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])) (β : Q.X), e.IsGen → (∀ (j : Fin 2 → Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ LB.wchart Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j → IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V))) → ∃ h' : Heat Y.H Y.q.left Q.P.L dd ⇑D, IsBasic Y h' ∧ h'.Θ = h.Θ ∧ h'.u = h.u ∧ ∀ (k : ℕ) (τ τ' ρ ρ' : SecM Y.q.left Q.P.L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval ρ r z J = sval τ (r ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)).left) z J * ((val e r z J) ^ k).val) → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval ρ' r z J = sval τ' (r ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)).left) z J * ((val e r z J) ^ k).val) → h.Acts k τ τ' → h'.Acts k ρ ρ' := by
  first | exact @GlobalTheory.Heat.ConjGauge.conj_gauge | exact GlobalTheory.Heat.ConjGauge.conj_gauge | (intros; apply GlobalTheory.Heat.ConjGauge.conj_gauge <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorSymbolUniquePrincipalPolarisation
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatSym

theorem symbol_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∀ (Λ₁ Λ₂ : Matrix (Fin n) (Fin n) (FractionRing Ω)) (d₁ d₂ : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (u₁ u₂ : Fin n → (FractionRing Ω)) (p₁ p₁' p₂ p₂' : (FractionRing Ω)), Λ₁ᵀ = Λ₁ → Λ₂ᵀ = Λ₂ → (∀ r, d₁ ((algebraMap Ω (FractionRing Ω)) (φ r)) = d₂ ((algebraMap Ω (FractionRing Ω)) (φ r))) → (∀ (k : ℕ), 1 ≤ k → ∀ s : (FractionRing Ω), (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (s)) → (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (ringOp ⇑d₁ (fun a => ⇑(δL a)) Λ₁ u₁ p₁ p₁' k s))) → (∀ (k : ℕ), 1 ≤ k → ∀ s : (FractionRing Ω), (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (s)) → (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (ringOp ⇑d₂ (fun a => ⇑(δL a)) Λ₂ u₂ p₂ p₂' k s))) → Λ₁ = Λ₂ := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam hmon htt hab n v' D Ω _ _ _ φ x' δ dd' hcomp hx hinv hδ hval hinj g hg δL hδL
    Λ₁ Λ₂ d₁ d₂ u₁ u₂ p₁ p₁' p₂ p₂' hΛ₁ hΛ₂ hd h₁ h₂
  have sub := fun j s s' (hs : GlobalTheory.HeatSym.VS φ t.PP.L x' g j s) (hs' : GlobalTheory.HeatSym.VS φ t.PP.L x' g j s') =>
    _root_.GlobalTheory.HeatSym.VS.sub φ t.G.hom t.PP.L x' g hx j s s' hs hs'
  have mul := fun j j' s s' (hs : GlobalTheory.HeatSym.VS φ t.PP.L x' g j s) (hs' : GlobalTheory.HeatSym.VS φ t.PP.L x' g j' s') =>
    _root_.GlobalTheory.HeatSym.VS.mul φ t.PP.L t.PP.isLB x' g j j' s s' hs hs'
  have hQ : ∀ (j : ℕ), 1 ≤ j → ∀ s, GlobalTheory.HeatSym.VS φ t.PP.L x' g j s →
      GlobalTheory.HeatSym.VS φ t.PP.L x' g j (ringOp ⇑d₁ (fun a => ⇑(δL a)) Λ₁ u₁ p₁ p₁' j s -
        ringOp ⇑d₂ (fun a => ⇑(δL a)) Λ₂ u₂ p₂ p₂' j s) :=
    fun j hj s hs => sub j _ _ (h₁ j hj s hs) (h₂ j hj s hs)
  have hsym : (Λ₁ - Λ₂)ᵀ = Λ₁ - Λ₂ := by rw [Matrix.transpose_sub, hΛ₁, hΛ₂]
  have hcoe : (fun y => d₁ y - d₂ y) = ⇑(d₁ - d₂) := rfl
  refine sub_eq_zero.mp (_root_.GlobalTheory.HeatSym.vertical_symbol_zero E H R t P m tt gam hmon htt hab n v' D Ω φ x' δ dd' hcomp hx hinv hδ hval hinj g hg δL hδL
    (d₁ - d₂) (Λ₁ - Λ₂) hsym (fun r => by rw [Derivation.sub_apply, hd, sub_self]) ?_)
  intro k hk b c hb hc
  have hk2 : 1 ≤ k + k := le_add_right hk
  have hbc := hQ (k + k) hk2 _ (mul k k b c hb hc)
  have hbb := hQ (k + k) hk2 _ (mul k k b b hb hb)
  have hBc := sub _ _ _ (sub _ _ _ hbc (mul k k _ _ hb (hQ k hk c hc))) (mul k k _ _ hc (hQ k hk b hb))
  have hBb := sub _ _ _ (sub _ _ _ hbb (mul k k _ _ hb (hQ k hk b hb))) (mul k k _ _ hb (hQ k hk b hb))
  have hX := sub _ _ _ (mul k (k + k) _ _ hb hBc) (mul k (k + k) _ _ hc hBb)
  simp only [GlobalTheory.HeatSym.ringOp_sub, hcoe] at hX
  have key := GlobalTheory.HeatSym.bracket ⇑(d₁ - d₂) (fun a => ⇑(δL a))
    (fun x y => by rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul])
    (fun a x y => by rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul])
    (fun a x y => map_add _ x y) (Λ₁ - Λ₂) hsym (u₁ - u₂) (p₁ - p₂) (p₁' - p₂') k b c
  rw [key] at hX
  have e3 : 3 * k = k + (k + k) := by ring
  rw [e3]
  exact GlobalTheory.HeatSym.VS.half φ hX

end GlobalTheory.HeatSym
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPointRigidBoundaryFamilyOfRigidCoordinates
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtRigid

theorem pointRigid_of_hasRigidCoords : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (C : MonoFam Xo c φ R), HasRigidCoords C → PointRigid C := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ C hC
  obtain ⟨N, s, ε, τ₀, hs, hε, hu, hτ, hPR⟩ := hC
  intro K _ _ ev k₀ hk hemb hsep
  apply hPR K ev k₀ hk hemb
  obtain ⟨h0, B₀, i₁, i₂, M₀, c₀, B', i₃, π₁, π₀, w, c', α, hB, hM, hp₁, hp₀, hw, hc, hrel⟩ := hsep
  refine ⟨fun i => by rw [hs]; exact h0 i, ⟨B₀, i₁, i₂, M₀, c₀, B', i₃, π₁, π₀, w, c', hB, hM, hp₁, hp₀, hw, hc⟩, ?_⟩
  intro W₀ _ ιb hFB hιb j
  let u : Fin N → Rˣ := fun k => (hu k).unit
  have hu' : ∀ k, (u k : R) = s (.inr k) := fun k => (hu k).unit_spec
  let t : Fin C.m ⊕ Fin N → Kˣ := Sum.elim (fun i => (α i)⁻¹) (fun k => Units.map ev.toMonoidHom (u k))
  have key : ∀ a b : C.P.D.toPre.X,
      ((∏ k, t k ^ ((l.M' : ℤ) * (ε k : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b) : Kˣ) : K) ∈ k₀ := by
    intro a b
    have hτ' := _root_.GlobalTheory.UCanon.ScaleTorus.isUnitTau_scaleGen Xo c φ R C N s ε τ₀ hs hε hτ u hu' a b
    obtain ⟨τ₁, hτ₁, hv⟩ := hrel a b _ hτ'
    obtain ⟨x, hx⟩ := GlobalTheory.T.periodGenerators_agree_over_algClosedSubfield R C.P.D.toPre τ₀ K ev k₀ hk W₀ ιb hFB hιb B₀ M₀ c₀ B' π₁ π₀ w c' hB hM hp₁ hp₀ hw hc
      a b τ₁ hτ₁
    let z : Sp K := IsLocalRing.closedPoint K
    choose J hJ using fun χ : Sp K ⟶ C.P.D.toPre.P.A.left => exists_chart C.P.D.toPre.P.isLB (χ z)
    choose J₀ hJ₀ using fun χ : Sp K ⟶ B₀.left => exists_chart hM (χ z)
    have gJ : Good C.P.D.toPre.P.L z J := hJ
    have gJ₀ : Good M₀ z J₀ := hJ₀
    have e₁ := hv z J J₀ gJ gJ₀
    have e₂ := hx z J J₀ gJ gJ₀
    have vs : ∀ (cc : Γ(Sp R, ⊤)ˣ), val (ReciprocityTheory.ChartRestriction.G.DVR.scaleGen cc (τ₀ a b)) (spMap ev) z J =
        gm (spMap ev) z ⊤ cc * val (τ₀ a b) (spMap ev) z J := fun cc =>
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ z le_top (gJ.mem _ _) cc) rfl)
    rw [vs, GlobalTheory.UChart.SepBModel.gm_spMap, e₂] at e₁
    set U' := Units.map ev.toMonoidHom (∏ k, u k ^ ((l.M' : ℤ) * (ε (.inr k) : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b))
    set x' := Units.map k₀.subtype.toMonoidHom x
    set A := ∏ i, α i ^ (((l.M' : ℤ) • C.δ i) a b)
    set L := lamUnit w c' a b z J J₀
    set V := val τ₁ (spMap k₀.subtype) z J₀
    have e₃ : gm (𝟙 (Sp K)) z ⊤ (unitOn U') * gm (𝟙 (Sp K)) z ⊤ (unitOn x') = gm (𝟙 (Sp K)) z ⊤ (unitOn A) := by
      have h₁ : gm (𝟙 (Sp K)) z ⊤ (unitOn U') * (L * gm (𝟙 (Sp K)) z ⊤ (unitOn x') * V) =
          (L * V) * (gm (𝟙 (Sp K)) z ⊤ (unitOn U') * gm (𝟙 (Sp K)) z ⊤ (unitOn x')) := by ac_rfl
      have h₂ : L * gm (𝟙 (Sp K)) z ⊤ (unitOn A) * V = (L * V) * gm (𝟙 (Sp K)) z ⊤ (unitOn A) := by ac_rfl
      rw [h₁, h₂] at e₁
      exact mul_left_cancel e₁
    have e₄ : U' * x' = A := GlobalTheory.UChart.SepBModel.gm_unitOn_inj z (by
      rw [show unitOn (U' * x') = unitOn U' * unitOn x' from map_mul _ _ _, map_mul]; exact e₃)
    have e₅ : (∏ k, t k ^ ((l.M' : ℤ) * (ε k : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b)) = x'⁻¹ := by
      rw [Fintype.prod_sum_type]
      have hA : (∏ i, t (.inl i) ^ ((l.M' : ℤ) * (ε (.inl i) : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b)) = A⁻¹ := by
        simp only [t, Sum.elim_inl, hε, A, inv_zpow, Finset.prod_inv_distrib, LinearMap.smul_apply, smul_eq_mul]
      have hU : (∏ k, t (.inr k) ^ ((l.M' : ℤ) * (ε (.inr k) : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b)) = U' := by
        simp only [t, Sum.elim_inr, U', map_prod, map_zpow]
      rw [hA, hU, ← e₄, mul_inv_rev, inv_mul_cancel_right]
    rw [e₅]
    exact (x⁻¹ : k₀ˣ).val.2
  have := _root_.GlobalTheory.mem_subfield_of_bilinForm_monomials C.P.D.toPre.X (balForms H.bar C.P.D.toPre.X) (Fin C.m ⊕ Fin N) ε K k₀ hk (l.M')
    (by exact_mod_cast (level_pos l).ne') t key (.inr j)
  simpa [t, u] using this

end GlobalTheory.PtRigid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverOfCompactB
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

theorem Model.isProjOver_of_compactB (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    [IsDomain R] [CharZero R] [IsNoetherianRing R] (b : Base D R) (N : ℕ) (_hN : 3 ≤ N) (_hNp : N.Coprime p)
    (hD : D.CompactB) (M : Model b N) : IsProjOver M.s :=
  GlobalTheory.UPel.isProjOver_of_isQProjOver_of_isProper R M.X M.s M.qproj
    (GlobalTheory.T.harrisTaylor_integralModel_isProper_of_compact p D R b N M hD)

end GlobalTheory.UPel.HT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelStalkNormalNoetherianFractionRingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelStalk_normal_noetherian_fractionRing : ∀ (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra; IsDomain (X₁.M.Z.presheaf.stalk z₁) ∧ IsFractionRing (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ ∧ IsIntegrallyClosed (X₁.M.Z.presheaf.stalk z₁) ∧ IsNoetherianRing (X₁.M.Z.presheaf.stalk z₁) := by
  first | exact @GlobalTheory.GSep.stalk_isNoetherian_normal_fractionRing | exact GlobalTheory.GSep.stalk_isNoetherian_normal_fractionRing | (intros; apply GlobalTheory.GSep.stalk_isNoetherian_normal_fractionRing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormBigOfNonvanishing
section
open Finset
open GlobalTheory.SqTop GlobalTheory.FunObj.SqNum
open GlobalTheory.NormSum (Pair)
open GlobalTheory.CMVal (IsHeckeL)

namespace GlobalTheory.NormBigProof

theorem squareBottomHalfRankSum_le_halfRank (D : Formalism.BasicNotions.D7) (i j : ℕ) : h0 D i j ≤ halfRank D i j := by
  unfold h0 halfRank botBig botSmall
  exact Nat.div_le_div_right (Nat.add_le_add (Nat.sub_le _ _) (Nat.sub_le _ _))

end GlobalTheory.NormBigProof
end

