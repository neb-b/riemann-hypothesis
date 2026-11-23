module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2488
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2784
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2476
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolOfSecondQuotient
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameExponentSecondDifferenceConstantMembers
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitPartPsiTauTangentVectorVariation
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedMemberThroughPointOfModelAbove
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.Cmp.Thru

theorem spMap_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'') (g : R →+* R') :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  rw [← Spec.map_comp]; rfl

theorem spMap_stalkHom {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (z : M.Z) :
    spMap (M.stalkHom z) ≫ M.Z.fromSpecStalk z = M.pt := by
  have h1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of Ω) M.pt
  have h2 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk (M.pt_specializes (IsLocalRing.closedPoint Ω) z)
  refine Eq.trans ?_ h1
  rw [← h2, ← Category.assoc, ← Spec.map_comp]
  rfl

theorem isFractionRing_stalk {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (z : M.Z) :
    letI : Algebra (M.Z.presheaf.stalk z) Ω := (M.stalkHom z).toAlgebra
    IsFractionRing (M.Z.presheaf.stalk z) Ω := by
  letI : Algebra (M.Z.presheaf.stalk z) Ω := (M.stalkHom z).toAlgebra
  have : FaithfulSMul (M.Z.presheaf.stalk z) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (M.stalkHom_injective z)
  refine IsFractionRing.of_field _ _ fun x => ?_
  obtain ⟨a, b, -, hx⟩ := IsFractionRing.div_surjective (A := M.O z) x
  refine ⟨(M.stalkEquiv z).symm a, (M.stalkEquiv z).symm b, ?_⟩
  have h : ∀ c : M.O z, algebraMap (M.Z.presheaf.stalk z) Ω ((M.stalkEquiv z).symm c) = c := fun c => by
    change M.stalkHom z _ = _
    rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
  rw [h, h, ← hx]
  rfl

theorem exists_cdvr_thru {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [IsNoetherianRing o] [CharZero Ω]
    (M : RatModel o Ω) (z : M.Z) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (φ : M.Z.presheaf.stalk z →+* V)
      (e : Ω →+* FractionRing V), IsAdicComplete (maximalIdeal V) V ∧ CharZero V ∧ IsLocalHom φ ∧
      jK V ≫ spMap φ ≫ M.Z.fromSpecStalk z = spMap e ≫ M.pt := by
  letI : Algebra (M.Z.presheaf.stalk z) Ω := (M.stalkHom z).toAlgebra
  haveI := isFractionRing_stalk M z
  haveI : CharZero (M.Z.presheaf.stalk z) := (M.stalkHom z).charZero
  haveI := M.lft
  haveI : IsLocallyNoetherian (Sp o) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of o)))
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  obtain ⟨V₀, _, _, _, φ₀, ⟨hdvr, hcpl, hchar⟩, hinj₀, hmax⟩ :=
    GlobalTheory.ClosedPol.exists_cdvr (M.Z.presheaf.stalk z) (maximalIdeal _)
  have hl : IsLocalHom φ₀ := ((IsLocalRing.local_hom_tfae φ₀).out 1 5).2 hmax
  have hg₀ : Function.Injective ((algebraMap V₀ (FractionRing V₀)).comp φ₀) :=
    (IsFractionRing.injective V₀ (FractionRing V₀)).comp hinj₀
  let emb : Ω →+* FractionRing V₀ := IsFractionRing.lift (A := M.Z.presheaf.stalk z) hg₀
  have hemb : ∀ r, emb (M.stalkHom z r) = algebraMap V₀ (FractionRing V₀) (φ₀ r) := fun r =>
    IsFractionRing.lift_algebraMap (A := M.Z.presheaf.stalk z) hg₀ r
  refine ⟨V₀, inferInstance, inferInstance, hdvr, φ₀, emb, hcpl, hchar, hl, ?_⟩
  rw [← spMap_stalkHom, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [show jK V₀ = spMap (algebraMap V₀ (FractionRing V₀)) from rfl, spMap_spMap, spMap_spMap]
  congr 1
  ext r
  exact (hemb r).symm

theorem exists_uMem_thru : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), Cmp.ZHAbove X₁ Y πY → ∀ y : Y.Z, πY y = z₁ → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (_ : IsDiscreteValuationRing V) (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) (_ : AddCommGroup X) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔫 : UMem X₁ z₁ act V ev X t δ) (ξ : Sp V ⟶ Y.Z), ξ ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ∧ ξ (closedPoint V) = y := by
  intro g n F W Z i X₁ z₁ act hact Y πY hY y hy
  subst hy
  obtain ⟨U₀, EE, -, -, -, hhom, -⟩ := hY
  haveI := X₁.imm
  haveI : CharZero X₁.Ω₁ := X₁.ar.char
  haveI : IsDedekindDomain X₁.o₁ := X₁.ar.ded
  obtain ⟨V₀, _, _, hdvr, φ₀, emb, hcpl, hchar, hl₀, hptY⟩ := exists_cdvr_thru Y y
  have hB : GlobalTheory.Mum.Base V₀ := ⟨⟨inferInstance, inferInstance, inferInstance, hcpl⟩, hchar⟩
  have hπ : Y.pt ≫ πY = X₁.M.pt := by
    refine Eq.trans hhom ?_
    exact (congrArg (· ≫ X₁.M.pt) (Spec.map_id _)).trans (Category.id_comp _)
  let s : X₁.M.Z.presheaf.stalk (πY y) →+* Y.Z.presheaf.stalk y := (πY.stalkMap y).hom
  have hs : spMap s ≫ X₁.M.Z.fromSpecStalk (πY y) = Y.Z.fromSpecStalk y ≫ πY :=
    Scheme.SpecMap_stalkMap_fromSpecStalk πY
  haveI hsl : IsLocalHom s := inferInstanceAs (IsLocalHom (πY.stalkMap y).hom)
  let y₀ : Sp (FractionRing V₀) ⟶ F.X := spMap emb ≫ spMap X₁.S.R.val.toRingHom ≫ X₁.u
  obtain ⟨T, f, fK, hf, hfl, hff, hfK, hTy⟩ := _root_.GlobalTheory.Poinc.traitExtSt g n _ (zetaAway n) F V₀ hB hdvr y₀
  haveI := hfl
  let ψ : Y.Z.presheaf.stalk y →+* T.V := f.comp φ₀
  let ev : X₁.M.Z.presheaf.stalk (πY y) →+* T.V := ψ.comp s
  have hξ : (spMap ψ ≫ Y.Z.fromSpecStalk y) ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk (πY y) := by
    rw [Category.assoc, ← hs, ← Category.assoc, spMap_spMap]
  have hkey : jK T.V ≫ spMap ψ = spMap fK ≫ jK V₀ ≫ spMap φ₀ := by
    rw [show jK T.V = spMap (algebraMap T.V (FractionRing T.V)) from rfl,
      show jK V₀ = spMap (algebraMap V₀ (FractionRing V₀)) from rfl, spMap_spMap, spMap_spMap, spMap_spMap]
    congr 1
    ext a
    simp only [RingHom.comp_apply]
    exact (hfK _).symm
  have hpt' : jK T.V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (πY y) = spMap fK ≫ spMap emb ≫ X₁.M.pt := by
    rw [← hξ, ← hπ, ← Category.assoc (spMap emb), ← hptY, Category.assoc (spMap ψ), ← Category.assoc (jK T.V), hkey]
    simp only [Category.assoc]
  have hreg : RegAt X₁ (πY y) ev := by
    intro a _
    rw [hpt']
    change a ∈ X₁.M.O (X₁.M.pt ((spMap fK ≫ spMap emb) (closedPoint (FractionRing T.V))))
    rw [X₁.M.pt_apply, RatModel.O_genericPoint]
    trivial
  have hcomm : jK T.V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (πY y) ≫ X₁.π = T.y ≫ i := by
    have := congrArg (· ≫ X₁.π) hpt'
    simp only [Category.assoc] at this
    rw [this, hTy, X₁.comp]
    simp only [y₀, Category.assoc]
  obtain ⟨hmono, hnn, -, -⟩ := _root_.GlobalTheory.Poinc.TraitTau.main g n _ (zetaAway n) F T
  have hCN : IsCN T.V := ⟨inferInstance, inferInstance, T.complete, inferInstance⟩
  haveI hψ : IsLocalHom ψ := RingHom.isLocalHom_comp _ _
  obtain ⟨𝔪, -⟩ := _root_.GlobalTheory.Poinc.Sep.MkMember.exists_uMem g X₁.one_le n X₁.three_le X₁.odd F Z X₁.z i X₁.proj
    (fun x => ⟨X₁.normalZ.isDomain_stalk x, X₁.normalZ.isIntegrallyClosed_stalk x⟩) X₁.thetaSetup_structureMap_comp X₁.dense W X₁.e8
    X₁.thetaInt X₁ (πY y) act hact T.V
    (Wit.ofDeg T.D.toPre T.D.tau_bimult) 1 ![T.ϖ] ![T.β] (fun k => by fin_cases k; exact T.irr.ne_zero)
    (fun k a b => by fin_cases k; exact T.symm a b) (fun k a => by fin_cases k; exact hnn a) hmono T.V (RingHom.id _)
    hCN Function.injective_id (RingHom.Finite.id T.V) T.D (AddEquiv.refl _) (Wit.refines_ofDeg _ _) T.G T.A T.U T.y T.α T.α₂
    T.semi T.cart T.sq T.lb ev (RingHom.isLocalHom_comp _ _) hreg hcomm
  refine ⟨T.V, inferInstance, inferInstance, inferInstance, inferInstance, ev, _, inferInstance, 1, _, _, 𝔪,
    spMap ψ ≫ Y.Z.fromSpecStalk y, hξ, ?_⟩
  change Y.Z.fromSpecStalk y (spMap ψ (closedPoint T.V)) = y
  have : spMap ψ (closedPoint T.V) = closedPoint (Y.Z.presheaf.stalk y) := IsLocalRing.comap_closedPoint ψ
  rw [this]
  exact Scheme.fromSpecStalk_closedPoint

end GlobalTheory.Poinc.Sep.Cmp.Thru
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryThetaSystemClassicalTraitsClosedPoi
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.PreSys

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c}

theorem rank_le (T : UTrait Xo c) : Module.finrank (𝓞 E) T.P.D.toPre.X ≤ min Dw.p Dw.q := _root_.GlobalTheory.UPoinc.UTrait.finrank_le_min E H Dw l Xo c T

theorem lam (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (hz : IsClosed ({z₁} : Set X₁.M.Z)) :
    ∃ K : ℝ, ∀ (t : UCTrait X₁ p z₁) (x : t.T.P.D.toPre.X), x ≠ 0 →
      ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁), Real.exp (-(K * (t.sc * t.T.be x x))) ≤ ‖t.val h‖ :=
  _root_.GlobalTheory.UPoinc.lam_of_closed E H Dw l Xo c C X₁ p z₁ hz

theorem finite_X (T : UTrait Xo c) : Module.Finite (𝓞 E) T.P.D.toPre.X :=
  Module.Finite.of_restrictScalars_finite ℤ _ _

theorem projective_X (T : UTrait Xo c) : Module.Projective (𝓞 E) T.P.D.toPre.X := by
  have : Module.Finite (𝓞 E) T.P.D.toPre.X := finite_X T
  have : Module.Flat (𝓞 E) T.P.D.toPre.X := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro x ⟨a, hx⟩
    by_contra hx0
    obtain ⟨n, hn, b, hb⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) (a : 𝓞 E)).exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero (nonZeroDivisors.coe_ne_zero a))
    have h : n • x = 0 := by
      have hx' : (a : 𝓞 E) • x = 0 := hx
      rw [← algebraMap_smul (𝓞 E) n x, hb, mul_comm, mul_smul, hx', smul_zero]
    exact hx0 ((smul_eq_zero.1 h).resolve_left hn)
  have : Module.FinitePresentation (𝓞 E) T.P.D.toPre.X := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

variable {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}

def evC (t : UCTrait X₁ p z₁) : X₁.M.Z.presheaf.stalk z₁ →+* PadicAlgCl p :=
  (RatModel.valHomOf (gPt p ≫ t.y) z₁ (RatModel.gPt_specializes t.cen)).comp (X₁.M.stalkEquiv z₁).toRingHom

theorem evC_apply (t : UCTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) : evC t a = t.val a := rfl

theorem norm_evC_le (t : UCTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) : ‖evC t a‖ ≤ 1 :=
  RatModel.norm_val_le_one t.cen (X₁.M.stalkEquiv z₁ a).2

theorem norm_evC_lt (t : UCTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) (ha : a ∈ maximalIdeal _) :
    ‖evC t a‖ < 1 := by
  have h1 : ¬ IsUnit (X₁.M.stalkEquiv z₁ a) := fun hu => ha ((isUnit_map_iff (X₁.M.stalkEquiv z₁) a).1 hu)
  exact (RatModel.norm_val_lt_one_iff t.cen (X₁.M.stalkEquiv z₁ a).2).2 h1

theorem sc_pos (t : UCTrait X₁ p z₁) : 0 < t.sc := by
  have hϖ0 : algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 t.T.irr.ne_zero
  have h0 : t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ) ≠ 0 := (map_ne_zero _).2 hϖ0
  have hlt : ‖t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ)‖ < 1 := by
    by_contra hge
    push_neg at hge
    have hinv : ‖t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ hge
    obtain ⟨w, hw⟩ := (t.int _).1 hinv
    apply t.T.irr.not_isUnit
    refine isUnit_iff_exists_inv.2 ⟨w, IsFractionRing.injective t.T.V (FractionRing t.T.V) ?_⟩
    rw [map_mul, hw, map_one, mul_inv_cancel₀ hϖ0]
  unfold UCTrait.sc
  have := Real.log_neg (norm_pos_iff.2 h0) hlt
  linarith

theorem be_pos (T : UTrait Xo c) (x : T.P.D.toPre.X) (hx : x ≠ 0) : 0 < T.be x x := by
  obtain ⟨j, hj⟩ := IsMonomial.exists_pos (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top T.mono hx
  fin_cases j
  simpa using hj

theorem be_bal (T : UTrait Xo c) : T.be ∈ balForms (H.bar : 𝓞 E → 𝓞 E) T.P.D.toPre.X := by
  rw [balForms_eq_levelForms]; exact T.lev

end GlobalTheory.UPoinc.PreSys

namespace GlobalTheory.UPoinc.PreSys

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c} {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}


variable (E X₁ p) in
abbrev Key : Type :=
  (Sp (OO p) ⟶ X₁.M.Z) × (Σ k : ℕ, (𝓞 E →+* Module.End ℤ (Fin k → ℤ)) × ((Fin k → ℤ) → (Fin k → ℤ) → ℝ))

def Rep (t : UCTrait X₁ p z₁) (q : Key E X₁ p) : Prop :=
  t.y = q.1 ∧ ∃ e : (Fin q.2.1 → ℤ) ≃ₗ[ℤ] t.T.P.D.toPre.X, (∀ (a : 𝓞 E) u, e (q.2.2.1 a u) = a • e u) ∧
    ∀ u v, q.2.2.2 u v = t.sc * t.T.be (e u) (e v)

def coord (t : UCTrait X₁ p z₁) : (Fin (Module.finrank ℤ t.T.P.D.toPre.X) → ℤ) ≃ₗ[ℤ] t.T.P.D.toPre.X :=
  (Module.finBasis ℤ t.T.P.D.toPre.X).equivFun.symm

def actOf (t : UCTrait X₁ p z₁) : 𝓞 E →+* Module.End ℤ (Fin (Module.finrank ℤ t.T.P.D.toPre.X) → ℤ) where
  toFun a := (coord t).symm.toLinearMap ∘ₗ (DistribSMul.toLinearMap ℤ t.T.P.D.toPre.X a) ∘ₗ (coord t).toLinearMap
  map_one' := LinearMap.ext fun u => by simp
  map_mul' a b := LinearMap.ext fun u => by simp [mul_smul]
  map_zero' := LinearMap.ext fun u => by simp
  map_add' a b := LinearMap.ext fun u => by simp [add_smul]

theorem coord_actOf (t : UCTrait X₁ p z₁) (a : 𝓞 E) (u : Fin (Module.finrank ℤ t.T.P.D.toPre.X) → ℤ) :
    coord t (actOf t a u) = a • coord t u := by
  simp [actOf]

def keyOf (t : UCTrait X₁ p z₁) : Key E X₁ p :=
  (t.y, ⟨Module.finrank ℤ t.T.P.D.toPre.X, actOf t, fun u v => t.sc * t.T.be (coord t u) (coord t v)⟩)

theorem rep_keyOf (t : UCTrait X₁ p z₁) : Rep t (keyOf t) := ⟨rfl, coord t, coord_actOf t, fun _ _ => rfl⟩


variable (X₁ p z₁) in
def Pts : Type := {q : Key E X₁ p // ∃ t : UCTrait X₁ p z₁, Rep t q}

noncomputable def pick (y : Pts X₁ p z₁) : UCTrait X₁ p z₁ := Classical.choose y.2

theorem pick_rep (y : Pts X₁ p z₁) : Rep (pick y) y.1 := Classical.choose_spec y.2

theorem exists_equiv_of_rep {t t' : UCTrait X₁ p z₁} {q : Key E X₁ p} (h : Rep t q) (h' : Rep t' q) :
    ∃ e : t.T.P.D.toPre.X ≃ₗ[𝓞 E] t'.T.P.D.toPre.X, ∀ a b, t.sc * t.T.be a b = t'.sc * t'.T.be (e a) (e b) := by
  obtain ⟨-, f, hf, hfb⟩ := h
  obtain ⟨-, f', hf', hfb'⟩ := h'
  let g : t.T.P.D.toPre.X ≃ₗ[ℤ] t'.T.P.D.toPre.X := f.symm.trans f'
  have hg : ∀ (a : 𝓞 E) x, g (a • x) = a • g x := by
    intro a x
    obtain ⟨u, rfl⟩ := f.surjective x
    simp only [g, LinearEquiv.trans_apply, ← hf, LinearEquiv.symm_apply_apply, hf']
  refine ⟨{ g with map_smul' := hg }, fun a b => ?_⟩
  obtain ⟨u, rfl⟩ := f.surjective a
  obtain ⟨v, rfl⟩ := f.surjective b
  show _ = t'.sc * t'.T.be (g (f u)) (g (f v))
  simp only [g, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rw [← hfb, ← hfb']


variable (X₁ p z₁) in
noncomputable def sys : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁) where
  Y := Pts X₁ p z₁
  ev y := evC (pick y)
  ev_le y h := norm_evC_le _ h
  ev_lt y h hh := norm_evC_lt _ h hh
  X y := (pick y).T.P.D.toPre.X
  fin y := finite_X _
  proj y := projective_X _
  rank_le y := rank_le _
  β y := (pick y).T.be
  bal y := be_bal _
  pos y x hx := be_pos _ x hx
  sc y := (pick y).sc
  sc_pos y := sc_pos _

theorem sys_matches : UMatches (sys X₁ p z₁) := by
  intro t
  refine ⟨⟨keyOf t, t, rep_keyOf t⟩, fun a => ?_, ?_⟩
  · obtain ⟨hy, -⟩ := pick_rep ⟨keyOf t, t, rep_keyOf t⟩
    show evC _ a = t.val a
    rw [evC_apply]
    unfold UCTrait.val
    rw [hy]
    rfl
  · exact exists_equiv_of_rep (pick_rep ⟨keyOf t, t, rep_keyOf t⟩) (rep_keyOf t)

theorem sys_lam (hz : IsClosed ({z₁} : Set X₁.M.Z)) : (sys X₁ p z₁).abelian₂ := by
  obtain ⟨K, hK⟩ := lam X₁ p z₁ hz
  exact ⟨K, fun y x hx => hK (pick y) x hx⟩

end GlobalTheory.UPoinc.PreSys


open GlobalTheory Classical in
theorem GlobalTheory.UPoinc.PreSys.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z), IsClosed ({z₁} : Set X₁.M.Z) → ∃ (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁)), UMatches Φ ∧ Φ.abelian₂ ∧ (∀ y, ∃ t : UCTrait X₁ p z₁, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) := by
  intro E _ _ _ H Dw _ l Xo c C X₁ p _ z₁ hz
  exact ⟨GlobalTheory.UPoinc.PreSys.sys X₁ p z₁, GlobalTheory.UPoinc.PreSys.sys_matches, GlobalTheory.UPoinc.PreSys.sys_lam hz,
    fun y => ⟨GlobalTheory.UPoinc.PreSys.pick y, fun a => rfl, LinearEquiv.refl _ _, fun a b => rfl⟩⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameExponentsAffineTwoMembers
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

namespace GlobalTheory.GSep.TransTerms

theorem affine_on_subgroup_of_second_diff {G : Type*} [AddCommGroup G] (H : AddSubgroup G) {R : Type*} [AddCommGroup R]
    (D : G → R) (hD : ∀ a ∈ H, ∀ b ∈ H, D (a + b) - D a - D b + D 0 = 0) :
    ∃ (κ : R) (h : H →+ R), ∀ (a : G) (ha : a ∈ H), D a = κ + h ⟨a, ha⟩ := by
  refine ⟨D 0, AddMonoidHom.mk' (fun x : H => D x - D 0) ?_, ?_⟩
  · intro x y
    have := hD x x.2 y y.2
    simp only [AddSubgroup.coe_add]
    rw [← sub_eq_zero]
    rw [← this]; abel
  · intro a ha
    simp

theorem frExp_affine_two_members : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1), ∀ (V2 : Type) [CommRing V2] [IsDomain V2] [IsLocalRing V2] (ev2 : X₁.M.Z.presheaf.stalk z₁ →+* V2) (Y2 : Type) [AddCommGroup Y2] (t2 : Y2 → V2) (δ2 : I → Y2 → Y2) (𝔪2 : GlobalTheory.GSep.GMem X₁ z₁ act V2 ev2 Y2 t2 δ2), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ E1 E2 : X₁.S.Gam → ℕ, (∀ a ∈ X₁.S.HH X₁.M z₁, GlobalTheory.GSep.TransTerms.FrExp 𝔪1 a τ (E1 a)) → (∀ a ∈ X₁.S.HH X₁.M z₁, GlobalTheory.GSep.TransTerms.FrExp 𝔪2 a τ (E2 a)) → ∃ (κ : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) (h : X₁.S.HH X₁.M z₁ →+ ZMod ((X₁.S.r * X₁.S.N) ^ 2)), ∀ (a : X₁.S.Gam) (ha : a ∈ X₁.S.HH X₁.M z₁), ((E1 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((E2 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = κ + h ⟨a, ha⟩ := by
  intro I X₁ z₁ act x₀ hdiv V1 _ _ _ ev1 Y1 _ t1 δ1 𝔪1 V2 _ _ _ ev2 Y2 _ t2 δ2 𝔪2 τ hτ E1 E2 h1 h2
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.GSep.FrExpCube.frExp_second_diff I X₁ z₁ act x₀ hdiv τ hτ
  have k1 := hc V1 ev1 Y1 t1 δ1 𝔪1 E1 h1
  have k2 := hc V2 ev2 Y2 t2 δ2 𝔪2 E2 h2
  refine affine_on_subgroup_of_second_diff (X₁.S.HH X₁.M z₁)
    (fun a => ((E1 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((E2 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2))) ?_
  intro a ha b hb
  have e1 := k1 a ha b hb
  have e2 := k2 a ha b hb
  rw [← sub_eq_zero.mpr (e1.trans e2.symm)]
  abel

end GlobalTheory.GSep.TransTerms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricFibreThetaConstantsRatiosMemSubfield
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

noncomputable section

namespace GlobalTheory.Poinc.Sep.ModelRatio

theorem main : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (o : Type) [CommRing o] (J : Type) (b : ZM.TBase o ((n ^ j) ^ 2)) (s : Sp K ⟶ Sp o) (t : ZM.TObj g ((n ^ j) ^ 2) J b s) (π₁ : t.A.left ⟶ D.P.A.left), IsGrpPullback t.A D.P.A (spMap ev) π₁ → LBIso t.L (D.P.L.pull π₁) → ∀ v : ZM.Ix g ((n ^ j) ^ 2) → K, t.HasTh (𝟙 _) v → ∀ a a', v a' ≠ 0 → ∃ r ∈ k₀, v a = r * v a' := by
  intro g n hn hodd
  obtain ⟨j₀, hcore⟩ := _root_.GlobalTheory.USep.thetaConst_eq_lam_root_mul n hn hodd
  refine ⟨j₀, fun j hj V₁ _ _ _ hV hunit D hg X C _ e u mo hmo hT K _ _ ev k₀ hk₀ hrat o _ J b s t π₁ hp hL v hv a a' hne => ?_⟩
  haveI : IsAlgClosed k₀ := hk₀
  have := t.ab.comm
  obtain ⟨ρ₀, hρ₀⟩ := D.P.rigid
  obtain ⟨w, hw⟩ := hL
  obtain ⟨ρ, hρ, hr⟩ := GlobalTheory.Ex.OneGen.exists_rigidificationPullbackCompatibleIso hp hw D.P.isLB t.isLB hρ₀
  let x : ZM.Ix g ((n ^ j) ^ 2) → (baseOver (Sp K) ⟶ t.pol.A) :=
    fun a => (Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) ≫ t.lab a
  have hx : ∀ i, x i ^ ((n ^ j) ^ 2) = 1 := fun i => by
    show ((Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) ≫ t.lab i) ^ ((n ^ j) ^ 2) = 1
    rw [← MonObj.comp_pow, GlobalTheory.ThetaPtUp.lab_pow t i, MonObj.comp_one]
  obtain ⟨thP, hg, hth⟩ := _root_.GlobalTheory.Ex.OneGen.exists_gen_thG_of_isThetaPt K t.pol ρ hρ (n ^ j) _ x v hx hv
  let τ : (baseOver (Sp K)).left ⟶ (Over.mk (spMap ev)).left := 𝟙 (Sp K)
  haveI : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp K)))
  have hτ : τ ≫ (Over.mk (spMap ev)).hom = (baseOver (Sp K)).hom ≫ spMap ev := rfl
  have hi : inv τ = 𝟙 (Sp K) := IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)
  obtain ⟨th, hrel⟩ := GlobalTheory.ThetaPtMove.exists_secRel_up hp τ hτ hw D.P.isLB t.isLB thP
  have hgen := GlobalTheory.ThetaPtUp.isGenSec_up hp τ hτ hw D.P.isLB t.isLB hrel hg
  obtain ⟨M, lam, hM, hval⟩ := hcore j hj V₁ hV hunit D X C e u mo hmo hT K ev ρ₀ hρ₀ th hgen
  have up : ∀ i, ∃ c₀ : C, ∃ ζ : K, ζ ^ M = 1 ∧ v i = lam * ζ * ev (u 0 c₀) := fun i => by
    obtain ⟨y, hy, hy'⟩ := GlobalTheory.Ex.OneGen.exists_torsion_up hp τ hτ (x i) (hx i)
    have q := GlobalTheory.Ex.OneGen.ThG.up hp τ hτ hw D.P.isLB t.isLB hr hy hy' hrel (hth i)
    rw [hi] at q
    exact hval y (v i) q
  obtain ⟨c₁, hc₁⟩ := (hmo 0).2
  obtain ⟨c₀, ζ, hζ, hva⟩ := up a
  obtain ⟨c₀', ζ', hζ', hva'⟩ := up a'
  obtain ⟨s₁, hs₁, hs₁e⟩ := hrat 0 c₀ c₁ hc₁
  obtain ⟨s₂, hs₂, hs₂e⟩ := hrat 0 c₀' c₁ hc₁
  have hζk : ζ ∈ k₀ := GlobalTheory.Poinc.Sep.Frames.mem_of_pow_mem k₀ hM (by rw [hζ]; exact k₀.one_mem)
  have hζk' : ζ' ∈ k₀ := GlobalTheory.Poinc.Sep.Frames.mem_of_pow_mem k₀ hM (by rw [hζ']; exact k₀.one_mem)
  rw [hva', hs₂e] at hne
  have h₁ : ζ' * s₂ ≠ 0 := fun h => hne (by rw [show lam * ζ' * (s₂ * ev (u 0 c₁)) = lam * (ζ' * s₂) * ev (u 0 c₁) by ring, h]; ring)
  refine ⟨ζ * s₁ * (ζ' * s₂)⁻¹, k₀.mul_mem (k₀.mul_mem hζk hs₁) (k₀.inv_mem (k₀.mul_mem hζk' hs₂)), ?_⟩
  rw [hva, hva', hs₁e, hs₂e]
  have e₁ : ζ * s₁ * (ζ' * s₂)⁻¹ * (lam * ζ' * (s₂ * ev (u 0 c₁))) =
      ζ * s₁ * ((ζ' * s₂)⁻¹ * (ζ' * s₂)) * (lam * ev (u 0 c₁)) := by ring
  rw [e₁, inv_mul_cancel₀ h₁]
  ring

end GlobalTheory.Poinc.Sep.ModelRatio
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeSectionsIsotropicCommutatorPairingLinearMapStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeSections_isotropic_commutatorPairing_linearMap : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h₁ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ h₂ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (lift h₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) (lift 1 h₂) 1 := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.weilIs_heckeSub_one) | (exact GlobalTheory.UPel.HT.Hecke.weilIs_heckeSub_one) | (intros; apply GlobalTheory.UPel.HT.Hecke.weilIs_heckeSub_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitPartPsiTauTangentVectorVariationStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitPart_psi_tau_tangent_vector_variation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∀ w : LB.Iso (P.D.toPre.P.L.pull π₁) (P.D.toPre.P.L.pull π₂), w.IsGen → ∃ lam : ℕ → P.D.toPre.X → k, ∀ (mu α : P.D.toPre.X) (n : Fin m → ℕ) (ψ₀ : LB.Gen (LB.LinComb P.D.toPre.P.L (K := PUnit) (fun _ => (P.D.toPre.c mu).left) fun _ => -1)) τ₀, GlobalTheory.LogKSChart.IsUnitPart P.D.toPre (bdParam k m d) gam mu n ψ₀ → IsUnitTau P.D.toPre (bdParam k m d) gam mu α τ₀ → ∃ e₀ : ℕ, ∀ e : ℕ, e₀ ≤ e → ∀ ee : (DualNumber k)ˣ, (ee : DualNumber k) = 1 + TrivSqZeroExt.inr (lam e mu - ∑ i, ((e : k) * (n i : k) + (gam i mu α : k)) * MvPowerSeries.constantCoeff (q i)) → ∀ zz J, Good P.D.toPre.P.L zz J → (val ψ₀ (spMap ρ) zz J) ^ e * val τ₀ (spMap ρ) zz J * (val P.D.toPre.rig (spMap ρ) zz J) ^ e = gm (c' (mu)) zz _ (w.s (fun _ => J (c' (mu) ≫ π₂), fun _ => J (c' (mu) ≫ π₁))) ^ ((e : ℤ) - 1) * gm (c' (mu + α)) zz _ (w.s (fun _ => J (c' (mu + α) ≫ π₂), fun _ => J (c' (mu + α) ≫ π₁))) * (gm (c' (α)) zz _ (w.s (fun _ => J (c' (α) ≫ π₂), fun _ => J (c' (α) ≫ π₁))))⁻¹ * gm (c' (0)) zz _ (w.s (fun _ => J (c' (0) ≫ π₂), fun _ => J (c' (0) ≫ π₁))) ^ (1 - (e : ℤ)) * gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn ee) * (val ψ₀ (spMap (constHom ρ)) zz J) ^ e * val τ₀ (spMap (constHom ρ)) zz J * (val P.D.toPre.rig (spMap (constHom ρ)) zz J) ^ e := by
  first | exact @GlobalTheory.UnitsEval.units_eval | exact GlobalTheory.UnitsEval.units_eval | (intros; apply GlobalTheory.UnitsEval.units_eval <;> assumption)
end

