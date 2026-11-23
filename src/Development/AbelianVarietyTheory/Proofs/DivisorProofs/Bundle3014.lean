module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2915
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2906
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2948
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfInvariantDerivativesVanishSemiAbelian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2988
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2361
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2475
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2986
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2944
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2920
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2974
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2961
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2998
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2995
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2991
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0591
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedGroupPointSameDerivations
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

namespace GlobalTheory.FormalPointG

theorem exists_point_sameDerivations : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x : Sp Ω ⟶ Y.H.left) (δ : Fin n → Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω → Function.Injective φ → ∀ (hx : x ≫ Y.H.hom = spMap φ), (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) → ∃ (x' : Sp Ω ⟶ t.G.left) (hx' : x' ≫ t.G.hom = spMap φ) (dd' : Fin n → Fld t.G.left), (∀ a, IsInv t.G (v' a) (dd' a)) ∧ (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) ∧ (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) ∧ GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx)) (Over.homMk x' hx') := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam _ _ _
  letI := H.starRing
  intro Y n vH dd hdd v' hv' Ω _ _ _ φ x δ hΩ hφ hx hδ hxd
  haveI := hΩ
  obtain ⟨x', hx'p, -⟩ :=
    GlobalTheory.FormalPoint.existsUnique_isPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx))
  choose dd' hdd' using fun a => _root_.GlobalTheory.InvFieldSemiAb.exists_isInv E H R t (v' a)
  have hpt : GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx))
      (Over.homMk x'.left (Over.w x')) := hx'p
  have hder := GlobalTheory.T.uniformised_point_from_formal_raynaud_point_same_derivations E H R t P Y n (fun a => vH a) dd hdd v' hv' dd' hdd' Ω φ x δ hΩ hx hδ hxd x'.left
    (Over.w x') hpt
  obtain ⟨b, hb⟩ := GlobalTheory.T.uniformisedTangentBasis_of_raynaudBasis E H R t P Y n vH v' hv'
  refine ⟨x'.left, Over.w x', dd', hdd', hder, ?_, hpt⟩
  intro O f hO h0
  refine _root_.GlobalTheory.InvJet.eq_zero_of_invDer_vanish R t.G t.semi n b dd' (fun a => (hb a).symm ▸ hdd' a) Ω φ hφ x'.left (Over.w x') O f hO
    fun l => ?_
  have key : ∀ l : List (Fin n), valR x'.left O (l.foldr (fun a g => dd' a O g) f) =
      l.foldr (fun a w => δ a w) (valR x'.left O f) := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => simp only [List.foldr_cons]; rw [hder a O _ hO, ih]
  rw [key, h0]
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons]; rw [ih, map_zero]

end GlobalTheory.FormalPointG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedModelLabelsUnitaryTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.UTraitLab

theorem q_eq_of_isMonomial : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (lb : u.Lab) (ϖ : u.V) (be : LinearMap.BilinForm ℤ u.D.toPre.X), ϖ ≠ 0 → IsMonomial u.D.toPre ![ϖ] ![be] → ∀ χ, lb.q χ = -Real.log ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) ϖ)‖ * (be χ χ : ℝ) / 2 := by
  intro o Ω _ _ _ S ρ p _ y₀ u lb ϖ be hϖ hmono χ
  obtain ⟨v, n, hn, hc⟩ := hmono χ
  obtain ⟨jc, hjc, hval⟩ := GlobalTheory.Poinc.valF_psi_of_psiCoord u.V u.D.toPre χ _ hc
  have hq := lb.q_eq χ jc hjc
  rw [hval] at hq
  simp only [Fin.prod_univ_one, Matrix.cons_val_zero] at hq
  have hunit : ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ (v : u.V))‖ = 1 := by
    have h1 : ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ (v : u.V))‖ ≤ 1 := (u.norm_le _).2 ⟨_, rfl⟩
    have h2 : ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ ((v⁻¹ : u.Vˣ) : u.V))‖ ≤ 1 :=
      (u.norm_le _).2 ⟨_, rfl⟩
    have h3 : ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ (v : u.V))‖ *
        ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ ((v⁻¹ : u.Vˣ) : u.V))‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
    nlinarith [norm_nonneg (algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ (v : u.V))),
      norm_nonneg (algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ ((v⁻¹ : u.Vˣ) : u.V)))]
  rw [map_mul, map_mul, norm_mul, hunit, one_mul, map_pow, map_pow, norm_pow] at hq
  set a := ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) ϖ)‖ with ha
  have hapos : 0 < a := by
    rw [ha, norm_pos_iff]
    intro h0
    have h1 : algebraMap u.V (FractionRing u.V) ϖ = 0 :=
      (algebraMap (FractionRing u.V) (PadicAlgCl p)).injective (by rw [h0, map_zero])
    exact hϖ (IsFractionRing.injective u.V (FractionRing u.V) (by rw [h1, map_zero]))
  have hl : -lb.q χ = (n 0 : ℝ) * Real.log a := by
    rw [← Real.log_pow, hq, Real.log_exp]
  have hb : (be χ χ : ℝ) = 2 * (n 0 : ℝ) := by
    have := hn 0
    simp only [Matrix.cons_val_zero] at this
    rw [this]; push_cast; ring
  rw [hb]
  linarith

end GlobalTheory.UPoinc.UTraitLab

namespace GlobalTheory.UPoinc


open GlobalTheory.UPoinc.UTraitLab in
theorem uTraitLabels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (u' : Sp (ratHull S.R) ⟶ Xo.XF cf) (G : Over (Sp (ratHull S.R))) (_ : GrpObj G) (α : G.left ⟶ ρ.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ.P.A (spMap (toRat S.R)) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ.P.L.pull α) (Xo.univ.t.PP.L.pull β) → ∀ (p : ℕ) [Fact p.Prime] (y₁ : ratHull S.R →+* PadicAlgCl p) (T : UTrait Xo cf) (ι : FractionRing T.V →+* PadicAlgCl p), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) → spMap y₁ ≫ u' = spMap ι ≫ T.y → (∀ a : o, ‖y₁ (toRat S.R (algebraMap o S.R a))‖ ≤ 1) → ∃ (u : ρ.UTest p (y₁.comp (toRat S.R))) (lb : u.Lab) (j : u.D.toPre.X ≃+ T.P.D.toPre.X), (∀ χ, lb.q χ = -Real.log ‖ι (algebraMap T.V (FractionRing T.V) T.ϖ)‖ * (T.be (j χ) (j χ) : ℝ) / 2) ∧ ∀ (m : ℕ) (a : 𝓞 E) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (w w' : Sp (PadicAlgCl p) ⟶ G.left), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → w ≫ α = x.left ≫ u.φ → w' ≫ α = x'.left ≫ u.φ → w' ≫ β = w ≫ β ≫ (Xo.univ.t.act.act a).left → CongMod m (j pk'.y) (a • j pk.y) := by
  intro E _ _ _ H Dw hpq l Xo cf o Ω _ _ _ _ S ρ u' G _ α β hα hβ hL p _ y₁ T ι hι hsp hint
  obtain ⟨T', ι', yK, e, k, hι', hfac, hy', hϖ, hbe⟩ := _root_.GlobalTheory.UTraitExtLab.main E H Dw l Xo cf o Ω S u' p y₁ T ι hι hsp
  obtain ⟨φ, cart, lb, hact⟩ := _root_.GlobalTheory.UPoinc.TraitPullAct.exists_pull_act E H Dw l Xo cf o Ω S ρ u' G inferInstance α β hα hβ hL T' yK hy'
  haveI : IsDiscreteValuationRing T'.V := T'.cdvr.1
  letI : Algebra (FractionRing T'.V) (PadicAlgCl p) := ι'.toAlgebra
  let u : ρ.UTest p (y₁.comp (toRat S.R)) :=
    { V := T'.V, complete := T'.cdvr.2.1, norm_le := hι', yK := yK.comp (toRat S.R),
      fac := by rw [← RingHom.comp_assoc, RingHom.algebraMap_toAlgebra, hfac],
      A := T'.P.A, φ := φ, cart := cart, lb := lb, G := T'.t.G, semi := T'.t.semi, D := T'.P.D, U := T'.P.U }
  obtain ⟨lab⟩ := GlobalTheory.ZH.labels_exist GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 GlobalTheory.ZH.uTors_closed o Ω S ρ p _ u
    hint
  refine ⟨u, lab, e.toAddEquiv, ?_, ?_⟩
  · intro χ
    have hq := q_eq_of_isMonomial o Ω S ρ p _ u lab T'.ϖ T'.be T'.irr.ne_zero T'.mono χ
    rw [hq]
    change -Real.log ‖ι' (algebraMap T'.V _ T'.ϖ)‖ * ((T'.be χ χ : ℤ) : ℝ) / 2 =
      -Real.log ‖ι (algebraMap T.V _ T.ϖ)‖ * ((T.be (e χ) (e χ) : ℤ) : ℝ) / 2
    rw [hϖ, Real.log_pow, hbe χ χ]
    push_cast
    ring
  · intro m a pk pk' x x' w w' hm h1 h2 hw hw' hww
    have hx : x' = x ≫ T'.P.oA.act a := hact _ x x' w w' a hw hw' hww
    obtain ⟨z, hz⟩ := GlobalTheory.T.torsionLattice_moves_by_ringAction_completeDVR E H T'.V T'.cdvr T'.t T'.P (PadicAlgCl p) m a pk pk' x x' hm h1 h2 hx
    exact ⟨e z, by simp [hz, map_add (f := _), map_nsmul]⟩

end GlobalTheory.UPoinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitThroughOpenOfStalkCompleteDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem GlobalTheory.UPoinc.exists_uTrait_through_open_of_stalk_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (πY : Y.Z ⟶ X₁.M.Z), X₁.S.admitted Y U₀ → X₁.S.IsEE Y U₀ EE → X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → ∀ (x : Y.Z) (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A], IsAdicComplete (maximalIdeal A) A → ∀ θ : Y.Z.presheaf.stalk x →+* A, Function.Injective θ → IsLocalHom θ → ∃ (T : UTrait Xo c) (f : A →+* T.V), Function.Injective f ∧ IsLocalHom f ∧ (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ (spMap (f.comp θ) ≫ Y.Z.fromSpecStalk x) ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) ∧ T.y ≫ C.i = jK T.V ≫ (spMap (f.comp θ) ≫ Y.Z.fromSpecStalk x) ≫ πY ≫ X₁.π := by
  intro E _ _ _ H Dw _ l Xo c C X₁ Y U₀ EE out πY hAdm _ hHom x A _ _ _ _ hcomp θ hθ _
  haveI : CharZero X₁.Ω₁ := X₁.ar.char
  obtain ⟨T, f, γ, hfi, hfl, -, hpt, hy⟩ :=
    GlobalTheory.UPoinc.exists_uTrait_of_stalk_dvr E H Dw l Xo c X₁.o₁ X₁.Ω₁ Y X₁.uΩ x A hcomp θ hθ
  have hsub : Set.range Y.pt ⊆ Set.range U₀.ι := by
    rw [Y.gen, Scheme.Opens.range_ι, Set.singleton_subset_iff]
    exact (genericPoint_spec Y.Z).mem_open_set_iff U₀.isOpen |>.2 (by simpa using hAdm.1.ne)
  let ξg : Sp X₁.Ω₁ ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι Y.pt hsub
  have hξg : ξg ≫ U₀.ι = Y.pt := IsOpenImmersion.lift_fac _ _ _
  have hu : ξg ≫ out.u₀ = spMap X₁.S.R.val.toRingHom := out.u₀_gen ξg hξg
  have hHom' : Y.pt ≫ πY = X₁.M.pt := by
    rw [hHom]
    show Spec.map (CommRingCat.ofHom (RingHom.id X₁.Ω₁)) ≫ _ = _
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  refine ⟨T, f, hfi, hfl, ⟨spMap γ ≫ ξg, ?_, ?_⟩, ?_⟩
  · rw [hpt, Category.assoc, hξg]
  · refine ⟨spMap γ ≫ spMap (ratHull X₁.S.R).val.toRingHom, ?_, ?_⟩
    · rw [Category.assoc, spMap_val_toRat, Category.assoc, hu]
    · rw [hy, Category.assoc]
  · rw [hy]
    simp only [Category.assoc] at hpt ⊢
    rw [reassoc_of% hpt, reassoc_of% hHom', X₁.comp]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FilLagrangianOfLocal
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLagr


open GlobalTheory GlobalTheory.CatCoh GlobalTheory.PDiv GlobalTheory.PtExt in
theorem mem_fil_of_orth_of_ker (R : Type) [CommRing R] [Nontrivial R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B]
    (g : ℕ) (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (hgA : SmoothOfRelativeDimension g A.hom)
    (hgB : SmoothOfRelativeDimension g B.hom) (P : LB (A ⊗ B).left) (hLB : P.IsLB)
    (hz : GlobalTheory.AbLaw.Triv (AbDual.ev P (𝟙 A) (1 : A ⟶ B))) (e : ℕ) (he : IsUnit (e : R))
    (hker : ∀ v : epsR R ⟶ B, GlobalTheory.AbLaw.Triv (AbDual.ev P (fst A (epsR R)) (snd A (epsR R) ≫ v)) → v ^ e = 1)
    (φ : HdR A →ₗ[R] HdR B →ₗ[R] R) (hφ : AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ) (y : HdR B)
    (hy : ∀ x ∈ Fil A, φ x y = 0) : y ∈ Fil B := by
  have hHDR := GlobalTheory.AbCoh.abelianHodgeDeRham
  obtain ⟨-, hHodge, -⟩ := _root_.GlobalTheory.abelianDeRham_free_hodge_baseChange hHDR
  obtain ⟨v, hv⟩ := ((hHodge R B g hB hgB).1.1 y).exists
  obtain ⟨j, hj⟩ := _root_.GlobalTheory.PtExt.exists_isChoice R A B P hLB
  have horth := _root_.GlobalTheory.PtExt.HodgeOrth.fil_orthogonal hHDR R A B g hA hB hgA hgB P hLB φ hφ
  obtain ⟨k, hk⟩ := _root_.GlobalTheory.PtExt.cohom_fv_neg_tanCoc_of_orthogonal hHDR R A B g hA hB hgA hgB P hLB φ hφ horth y v hv 0
    (fun h hh ↦ by rw [hy h hh, map_zero]) 0 (by simp) j hj
  have hk' : IsCob (chartsA P) (tanCoc P j v) k := by
    intro D _ _ D' _ _ ψ x hx
    have e := hk D D' ψ x hx
    simp only [Fn1.add, Fn1.neg, fv, neg_neg] at e
    rw [show ev (0 : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (trivMap ψ x) = 0 from rfl, zero_add] at e
    exact e
  obtain ⟨s, hs⟩ := _root_.GlobalTheory.PtExt.exists_isPtGen R (A ⊗ B) A P hLB (AbDual.inl A B) hz
  obtain ⟨T, hT⟩ := _root_.GlobalTheory.PtExt.exists_isEpsGen_of_isCob R A B P hLB v hv.1 j hj s hs k hk'
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_pointwiseGenerator_of_dualNumberLineBundleGenerator R A B P hLB v hv.1 T hT
  have htriv := _root_.GlobalTheory.PtExt.triv_pull_of_isPtGen R (A ⊗ B) (A ⊗ epsR R) P hLB _ t ht
  have hv1 : v ^ e = 1 := hker v htriv
  have hpow : ∀ n : ℕ, IsLieImage (n • y) (v ^ n) := by
    intro n
    induction n with
    | zero => rw [zero_smul, pow_zero]; exact isLieImage_one_iff.2 (Submodule.zero_mem _)
    | succ n ih => rw [succ_nsmul, pow_succ]; exact ih.add hv
  have h1 : (e : R) • y ∈ Fil B := by
    rw [Nat.cast_smul_eq_nsmul]
    have := hpow e
    rw [hv1] at this
    exact isLieImage_one_iff.1 this
  obtain ⟨u, hu⟩ := he
  have hyu : y = ((u⁻¹ : Rˣ) : R) • ((e : R) • y) := by
    rw [smul_smul, ← hu, Units.inv_mul, one_smul]
  rw [hyu]
  exact Submodule.smul_mem _ _ h1

theorem fil_lagrangian : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C₀ : Type) [CommRing C₀] (s : Sp C₀ ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s)
    (φ' : HdR o₀.A →ₗ[C₀] HdR o₀.A →ₗ[C₀] C₀), (∃ g : ℕ, SmoothOfRelativeDimension g o₀.A.hom) →
    GlobalTheory.AbDual.IsCorrForm (dp0 C₀) (𝟙 _) o₀.A o₀.A o₀.P φ' →
    (∀ x ∈ Fil o₀.A, ∀ y ∈ Fil o₀.A, φ' x y = 0) ∧ ∀ x, (∀ y ∈ Fil o₀.A, φ' x y = 0) → x ∈ Fil o₀.A := by
  intro p _ D R _ b N C₀ _ s o₀ φ' ⟨g, hg⟩ hφ
  refine ⟨GlobalTheory.PtExt.HodgeOrth.fil_orthogonal GlobalTheory.AbCoh.abelianHodgeDeRham C₀ o₀.A o₀.A g o₀.ab o₀.ab hg hg o₀.P
    o₀.isLB φ' hφ, fun x hx ↦ ?_⟩
  rcases subsingleton_or_nontrivial C₀ with hC | hC
  · haveI : Subsingleton (HdR o₀.A) := Module.subsingleton C₀ _
    rw [Subsingleton.elim x 0]
    exact Submodule.zero_mem _
  obtain ⟨e, hep, hker⟩ := o₀.kerP
  have heu : IsUnit (e : C₀) := by
    have := (b.unit e hep).map (Spec.preimage s).hom
    rwa [map_natCast] at this
  have hs : (AbDual.swap o₀.P).IsLB := pull_isLB o₀.isLB _
  refine mem_fil_of_orth_of_ker C₀ o₀.A o₀.A g o₀.ab o₀.ab hg hg (AbDual.swap o₀.P) hs ?_ e heu ?_ (-φ'.flip)
    (GlobalTheory.SymmPoincare.isCorrForm_swap hφ) x ?_
  · rw [AbDual.triv_ev_iff hs, AbDual.evc_swap o₀.isLB, ← AbDual.triv_ev_iff o₀.isLB]
    exact o₀.rig₁
  · intro v hv
    rw [AbDual.triv_ev_iff hs, AbDual.evc_swap o₀.isLB, ← AbDual.triv_ev_iff o₀.isLB] at hv
    exact hker _ v hv
  · intro y hy
    simp [hx y hy]

end GlobalTheory.HTLagr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnramifiedExtensionGroupLift
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolBundleLoc

open GlobalTheory.PolRoot

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp [spMap, ← Spec.map_comp]

theorem root_congr {S T : Scheme.{0}} {A : Over S} [GrpObj A] {P : LB (G2 A).left} {t t' : T ⟶ S} (e : t = t')
    (h : Root A P t) : Root A P t' := e ▸ h

theorem residue_lift (R R' k'' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] [Algebra R R']
    [IsLocalHom (algebraMap R R')] [Field k''] [Algebra (ResidueField R) k'']
    (ε : ResidueField R ⊗[R] R' ≃ₐ[ResidueField R] k'') :
    ∃ φ : k'' →+* ResidueField R', φ.comp (algebraMap (ResidueField R) k'') =
      algebraMap (ResidueField R) (ResidueField R') := by
  let g₂ : ResidueField R ⊗[R] R' →ₐ[ResidueField R] ResidueField R' :=
    Algebra.TensorProduct.lift (Algebra.ofId (ResidueField R) (ResidueField R'))
      (IsScalarTower.toAlgHom R R' (ResidueField R')) (fun _ _ => Commute.all _ _)
  refine ⟨(g₂.comp ε.symm.toAlgHom).toRingHom, ?_⟩
  ext a
  exact (g₂.comp ε.symm.toAlgHom).commutes a

end GlobalTheory.PolBundleLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankBalancedIntBilinFormsEqOfFiniteIndex
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.BalRank

theorem finrank_balBil_le_of_smul_mem_range {O : Type} [CommRing O] (bar : O → O) (X Y : Type)
    [AddCommGroup X] [Module O X] [Module.Free ℤ X] [Module.Finite ℤ X]
    [AddCommGroup Y] [Module O Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (f : Y →ₗ[O] X) (m : ℕ) (hm : 0 < m) (hf : ∀ x : X, m • x ∈ LinearMap.range f) :
    Module.finrank ℤ (balBil bar X) ≤ Module.finrank ℤ (balBil bar Y) := by
  let f' : Y →ₗ[ℤ] X := f.toAddMonoidHom.toIntLinearMap
  have hf' : ∀ y, f' y = f y := fun y => rfl
  let Φ : balBil bar X →ₗ[ℤ] balBil bar Y :=
    { toFun := fun β => ⟨(β : LinearMap.BilinForm ℤ X).compl₁₂ f' f', by
        intro a y z
        have := β.2 a (f y) (f z)
        simpa [hf', LinearMap.compl₁₂_apply, map_smul] using this⟩
      map_add' := fun β β' => by ext; simp
      map_smul' := fun n β => by ext; simp }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro β hβ
    ext x x'
    obtain ⟨y, hy⟩ := hf x
    obtain ⟨y', hy'⟩ := hf x'
    have h0 : (β : LinearMap.BilinForm ℤ X) (f y) (f y') = 0 := by
      have := congrArg (fun γ : balBil bar Y => (γ : LinearMap.BilinForm ℤ Y) y y') hβ
      simpa [Φ, hf'] using this
    rw [hy, hy'] at h0
    have h1 : ((m : ℤ) * m) * (β : LinearMap.BilinForm ℤ X) x x' = 0 := by
      rw [← h0]
      simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      ring
    have hm' : ((m : ℤ) * m) ≠ 0 := by positivity
    simpa using (mul_eq_zero.mp h1).resolve_left hm'
  exact LinearMap.finrank_le_finrank_of_injective hinj

theorem finrank_balBil_eq_of_finiteIndex {O : Type} [CommRing O] (bar : O → O) (X Y : Type)
    [AddCommGroup X] [Module O X] [Module.Free ℤ X] [Module.Finite ℤ X]
    [AddCommGroup Y] [Module O Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (f : Y →ₗ[O] X) (m : ℕ) (hm : 0 < m) (hf : Function.Injective f)
    (hr : ∀ x : X, m • x ∈ LinearMap.range f) :
    Module.finrank ℤ (balBil bar Y) = Module.finrank ℤ (balBil bar X) := by
  let e := LinearEquiv.ofInjective f hf
  let c : X →ₗ[O] LinearMap.range f :=
    LinearMap.codRestrict (LinearMap.range f) (m • LinearMap.id) (fun x => by simpa using hr x)
  let g : X →ₗ[O] Y := e.symm.toLinearMap ∘ₗ c
  have hfg : ∀ x, f (g x) = m • x := by
    intro x
    have h1 : e (g x) = c x := by simp [g]
    have h2 := congrArg Subtype.val h1
    simpa [e, c] using h2
  have hgf : ∀ y, g (f y) = m • y := by
    intro y; apply hf; rw [hfg, map_nsmul]
  apply le_antisymm
  · exact finrank_balBil_le_of_smul_mem_range bar Y X g m hm (fun y => ⟨f y, hgf y⟩)
  · exact finrank_balBil_le_of_smul_mem_range bar X Y f m hm hr

end GlobalTheory.BalRank
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankBalancedIntBilinFormsPi
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.BalRank

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (J : Type) [Fintype J] [DecidableEq J]

def formOfFamily (φ : J → J → (𝓞 E →ₗ[ℤ] ℤ)) : LinearMap.BilinForm ℤ (J → 𝓞 E) :=
  LinearMap.mk₂ ℤ (fun y z => ∑ i, ∑ j, φ i j (H.bar (y i) * z j))
    (by intro y y' z; simp [map_add (f := _), add_mul, Finset.sum_add_distrib])
    (by intro c y z; simp only [Pi.smul_apply, map_zsmul, smul_mul_assoc, Finset.smul_sum])
    (by intro y z z'; simp [map_add (f := _), mul_add, Finset.sum_add_distrib])
    (by intro c y z; simp only [Pi.smul_apply, map_zsmul, mul_smul_comm, Finset.smul_sum])

theorem formOfFamily_apply (φ : J → J → (𝓞 E →ₗ[ℤ] ℤ)) (y z : J → 𝓞 E) :
    formOfFamily H J φ y z = ∑ i, ∑ j, φ i j (H.bar (y i) * z j) := rfl

theorem formOfFamily_mem (φ : J → J → (𝓞 E →ₗ[ℤ] ℤ)) : formOfFamily H J φ ∈ balBil H.bar (J → 𝓞 E) := by
  intro a y z
  simp only [formOfFamily_apply, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring_nf

def balBilEquiv : balBil H.bar (J → 𝓞 E) ≃ₗ[ℤ] (J → J → (𝓞 E →ₗ[ℤ] ℤ)) where
  toFun β := fun i j => (β.1 (Pi.single i 1)) ∘ₗ LinearMap.single ℤ (fun _ : J => 𝓞 E) j
  map_add' β β' := by ext; simp
  map_smul' c β := by ext; simp
  invFun φ := ⟨formOfFamily H J φ, formOfFamily_mem H J φ⟩
  left_inv β := by
    apply Subtype.ext
    refine LinearMap.ext₂ fun y z => ?_
    simp only [formOfFamily_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single]
    have hy : y = ∑ i, y i • (Pi.single i (1 : 𝓞 E) : J → 𝓞 E) := by
      conv_lhs => rw [← Finset.univ_sum_single y]
      refine Finset.sum_congr rfl fun i _ => ?_
      ext k
      rcases eq_or_ne k i with rfl | h <;> simp [*]
    conv_rhs => rw [hy]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [β.2 (y i) (Pi.single i 1) z]
    conv_rhs => rw [← Finset.univ_sum_single (H.bar (y i) • z)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    rfl
  right_inv φ := by
    funext i j
    refine LinearMap.ext fun c => ?_
    simp only [formOfFamily_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single]
    rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
    · simp
    · intro j' _ hj; simp [Pi.single_apply, hj]
    · simp
    · intro i' _ hi; simp [Pi.single_apply, hi]
    · simp

theorem finrank_balBil_pi : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (J : Type) [Fintype J]
    [DecidableEq J], Module.finrank ℤ (GlobalTheory.BalRank.balBil H.bar (J → 𝓞 E)) =
      Module.finrank ℚ E * Fintype.card J * Fintype.card J := by
  intro E _ _ _ H J _ _
  rw [(balBilEquiv H J).finrank_eq, Module.finrank_pi_fintype]
  simp only [Module.finrank_pi_fintype, Module.finrank_linearMap, Module.finrank_self, mul_one,
    NumberField.RingOfIntegers.rank, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  ring

end GlobalTheory.BalRank
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCoefficientsCongruence
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_coefficients_congruence : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → c ∣ k ^ 2 → (∀ n, 0 < n → n.Coprime p → ∀ (a : D.O) (x : D.La), ∃ z, h n (a • x) = a • h n x + n • z) → (∀ n m, 0 < n → 0 < m → (n * m).Coprime p → (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧ (n : ℤ) ∣ u (n * m) - u n) → (∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧ ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y) → (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z) → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ g ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N, (∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (toUnit o.A ≫ g) (𝟙 o.A)).left).Gen, t.IsGen) ∧ (∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (𝟙 o.A) (toUnit o.A ≫ g)).left).Gen, t.IsGen) := by
  first | (exact @GlobalTheory.UPel.HT.HeckeAd.KerPol.hecke_sections_triv) | (exact GlobalTheory.UPel.HT.HeckeAd.KerPol.hecke_sections_triv) | (intros; apply GlobalTheory.UPel.HT.HeckeAd.KerPol.hecke_sections_triv <;> assumption)
end

