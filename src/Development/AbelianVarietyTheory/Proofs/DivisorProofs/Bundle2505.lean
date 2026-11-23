module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1129
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0488
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenNormalNoetherianCharZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_mem_mul_eq_zero_of_algebraMap_eq_zero {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] (M : Submonoid R) [IsLocalization M S] :
    ∃ f ∈ M, ∀ a : R, algebraMap R S a = 0 → f * a = 0 := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (RingHom.ker (algebraMap R S)) :
    (RingHom.ker (algebraMap R S)).FG)
  have hk : ∀ a ∈ s, ∃ m : M, (m : R) * a = 0 := by
    intro a ha
    have : a ∈ RingHom.ker (algebraMap R S) := hs ▸ Submodule.subset_span ha
    exact (IsLocalization.map_eq_zero_iff M S a).1 this
  choose! m hm using hk
  refine ⟨∏ a ∈ s, (m a : R), Submonoid.prod_mem _ fun a _ => (m a).2, ?_⟩
  have key : ∀ a ∈ Submodule.span R (s : Set R), (∏ a ∈ s, (m a : R)) * a = 0 := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem b hb =>
        rw [← Finset.prod_erase_mul _ _ hb, _root_.mul_assoc, hm b hb, mul_zero]
    | zero => simp
    | add b c _ _ hb hc => rw [mul_add, hb, hc, add_zero]
    | smul r b _ hb => rw [smul_eq_mul, _root_.mul_left_comm, hb, mul_zero]
  intro a ha
  exact key a (hs ▸ ha)

theorem exists_affineOpen_isIntegrallyClosed_charZero (X : Scheme.{0})
    (hN : Geo.Tor.IsNormalScheme X) (hL : IsLocallyNoetherian X)
    (h0 : ∀ x : X, CharZero (X.residueField x)) (x : X) :
    ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ IsDomain Γ(X, U) ∧ IsNoetherianRing Γ(X, U) ∧
      IsIntegrallyClosed Γ(X, U) ∧ CharZero Γ(X, U) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  letI := X.presheaf.algebra_section_stalk (U := V) ⟨x, hxV⟩
  haveI := hV.isLocalization_stalk ⟨x, hxV⟩
  obtain ⟨f, hfM, hf⟩ := exists_mem_mul_eq_zero_of_algebraMap_eq_zero (R := Γ(X, V))
    (S := X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
  have hU : IsAffineOpen (X.basicOpen f) := hV.basicOpen f
  have hxU : x ∈ X.basicOpen f := by
    rw [X.mem_basicOpen f x hxV]
    exact IsLocalization.map_units (X.presheaf.stalk x) ⟨f, hfM⟩

  letI : Algebra Γ(X, V) Γ(X, X.basicOpen f) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
  haveI : IsLocalization.Away f Γ(X, X.basicOpen f) := hV.isLocalization_basicOpen f
  let g : Γ(X, X.basicOpen f) →+* X.presheaf.stalk x := (X.presheaf.germ _ x hxU).hom
  have hcomp : ∀ a : Γ(X, V), g (algebraMap Γ(X, V) Γ(X, X.basicOpen f) a) =
      algebraMap Γ(X, V) (X.presheaf.stalk x) a := fun a =>
    X.presheaf.germ_res_apply (homOfLE (X.basicOpen_le f)) x hxU a
  have hinj : Function.Injective g := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro σ hσ
    obtain ⟨⟨r, m⟩, hrm⟩ := IsLocalization.surj (Submonoid.powers f) σ
    have hr : algebraMap Γ(X, V) (X.presheaf.stalk x) r = 0 := by
      rw [← hcomp, ← hrm, map_mul, hσ, zero_mul]
    have hfr := congrArg (algebraMap Γ(X, V) Γ(X, X.basicOpen f)) (hf r hr)
    rw [map_mul, map_zero] at hfr
    have hu : IsUnit (algebraMap Γ(X, V) Γ(X, X.basicOpen f) f) :=
      IsLocalization.map_units Γ(X, X.basicOpen f) ⟨f, Submonoid.mem_powers f⟩
    have hr0 := hu.mul_right_eq_zero.1 hfr
    have hmu : IsUnit (algebraMap Γ(X, V) Γ(X, X.basicOpen f) (m : Γ(X, V))) :=
      IsLocalization.map_units Γ(X, X.basicOpen f) m
    rw [hr0] at hrm
    exact hmu.mul_left_eq_zero.1 hrm
  haveI : IsDomain (X.presheaf.stalk x) := (hN x).1
  haveI hD : IsDomain Γ(X, X.basicOpen f) := hinj.isDomain g
  haveI : CharZero (X.residueField x) := h0 x
  have hcz : CharZero Γ(X, X.basicOpen f) := by
    refine ⟨fun a b hab => ?_⟩
    have := congrArg ((X.residue x).hom.comp g) hab
    simp only [map_natCast] at this
    exact Nat.cast_injective this
  have hIC : IsIntegrallyClosed Γ(X, X.basicOpen f) := by
    refine IsIntegrallyClosed.of_localization_maximal fun p _ hp ↦ ?_
    let P : Spec Γ(X, X.basicOpen f) := ⟨p, hp.isPrime⟩
    have hy : hU.fromSpec P ∈ X.basicOpen f := hU.range_fromSpec.le ⟨P, rfl⟩
    letI : Algebra Γ(X, X.basicOpen f) (X.presheaf.stalk (hU.fromSpec P)) :=
      X.presheaf.algebra_section_stalk (U := X.basicOpen f) ⟨_, hy⟩
    have h : IsLocalization p.primeCompl (X.presheaf.stalk (hU.fromSpec P)) :=
      hU.isLocalization_stalk' P hy
    haveI := (hN (hU.fromSpec P)).1
    haveI := (hN (hU.fromSpec P)).2
    exact IsIntegrallyClosed.of_equiv (R := X.presheaf.stalk (hU.fromSpec P))
      (IsLocalization.algEquiv p.primeCompl (X.presheaf.stalk (hU.fromSpec P))
        (Localization.AtPrime p)).toRingEquiv
  exact ⟨⟨X.basicOpen f, hU⟩, hxU, hD, IsLocallyNoetherian.component_noetherian ⟨_, hU⟩, hIC, hcz⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseElementThetaTermIntegralPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section

namespace GlobalTheory.Poinc.IntTerm.IntPoint

theorem cst_toUnit (V : Type) [CommRing V] [IsDomain V] (z : (TF (R := V) (FractionRing V)).left) (a : V) :
    Geo.Tor.cst (toUnit (TF (R := V) (FractionRing V))).left z a =
      GlobalTheory.UT.cst (FractionRing V) z (algebraMap V (FractionRing V) a) := by
  have hx : (toUnit (TF (R := V) (FractionRing V))).left = jFK (R := V) (FractionRing V) ≫ jK V := by
    simpa using Over.w (toUnit (TF (R := V) (FractionRing V)))
  rw [hx]
  erw [GlobalTheory.ExpansionValueZero.cst_comp]
  erw [H1.gs_spec]
  rfl

theorem formEq_prod {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) (g : GtPt D (𝟙_ (Over (Sp V)))) (mu : D.X) :
    FormEq (fun k => (D.c mu * g.b).left ≫ D.famφB 0 k) (DegPre.famε 1)
      (Sum.elim (Sum.elim (fun _ : PUnit => (D.c mu).left) (DegPre.gtφT D (𝟙_ _) g.b mu)) ![(η[D.P.A]).left, g.b.left])
      (fun k => -(Sum.elim (Sum.elim (fun _ : PUnit => (-1 : ℤ)) DegPre.gtε) (DegPre.lineε 1)) k) := by
    have hu : toUnit (𝟙_ (Over (Sp V))) = 𝟙 _ := toUnit_unique _ _
    have c0 := ThetaOne.c_zero D
    have e2 : (toUnit D.P.A ≫ D.c 0) = toUnit D.P.A ≫ η[D.P.A] := by
      rw [c0, MonObj.comp_one, Hom.one_def]
    have e1 : (padd D.P.A (𝟙 D.P.A) (toUnit D.P.A ≫ η[D.P.A])) = 𝟙 D.P.A := by
      rw [← e2, c0, MonObj.comp_one, padd, ← Hom.mul_def, _root_.mul_one]
    have e3 : padd D.P.A (DegPre.cT D (𝟙_ _) mu) g.b = D.c mu * g.b := by
      rw [padd, ← Hom.mul_def, DegPre.cT, hu, Category.id_comp]
    have e4 : DegPre.cT D (𝟙_ _) mu = D.c mu := by rw [DegPre.cT, hu, Category.id_comp]
    have e5 : DegPre.zeroT D (𝟙_ (Over (Sp V))) = η[D.P.A] := by rw [DegPre.zeroT, hu, Category.id_comp]
    intro U _ h
    simp [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_two, DegPre.famφB, DegPre.gtφT, DegPre.famε, DegPre.gtε,
      DegPre.lineε, e1, e2, e3, e4, e5]
    have e6 : padd D.P.A (D.c mu) g.b = D.c mu * g.b := by rw [padd, ← Hom.mul_def]
    rw [e6]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (θ : D.SecB 1 0) (g : GtPt D (𝟙_ (Over (Sp V)))) (g' : GtPtF D (FractionRing V)) (w : Frm D (FractionRing V) 1 g'.b) (l : FractionRing V), GtPt.IsPullF (FractionRing V) (toUnit (TF (R := V) (FractionRing V))).left g g' → IntTerm.IntFrm D g.b w l → ∀ (mu : D.X) (gam : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c mu).left) (fun _ => -1))), gam.IsGen → ∃ a : V, (∀ (z : (TF (R := V) (FractionRing V)).left) (J : ((TF (R := V) (FractionRing V)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → GlobalTheory.UT.cst (FractionRing V) z l * (Geo.Tor.val gam (toUnit (TF (R := V) (FractionRing V))).left z J).val * sval θ (padd D.P.A (DegPre.cT D _ mu) g'.b).left z J * (Geo.Tor.val (g'.s mu) (𝟙 _) z J).val * (Geo.Tor.val w (𝟙 _) z J).val = GlobalTheory.UT.cst (FractionRing V) z (algebraMap V (FractionRing V) a)) ∧ (IntTerm.UnitAt D θ (D.c mu * g.b) → IsUnit (Geo.Tor.cst (𝟙 (Sp V)) (closedPoint V) a)) := by
  intro V _ _ _ D θ g g' w l hP hI mu gam hgam
  obtain ⟨t, ht, htv⟩ := hI
  have hL := D.P.isLB
  have hp := mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hgam (g.isGen mu)) ht
  obtain ⟨a, ha⟩ := GlobalTheory.ExpansionValueZero.exists_coeff (A := V) hL θ (D.c mu * g.b).left _ (invGen_isGen _ _ _ _ hp)
    (formEq_prod D g mu)
  refine ⟨a, fun z J hJ => ?_, fun ⟨J, hJ, hU⟩ => ?_⟩
  · have hg' : g'.b = toUnit (TF (R := V) (FractionRing V)) ≫ g.b := Over.OverMorphism.ext hP.1
    have hb : (padd D.P.A (DegPre.cT D _ mu) g'.b).left =
        (toUnit (TF (R := V) (FractionRing V))).left ≫ (D.c mu * g.b).left := by
      rw [← Over.comp_left, hg', Hom.mul_def, padd, ← Category.assoc, comp_lift]
    have hs : Geo.Tor.val (g'.s mu) (𝟙 _) z J = Geo.Tor.val (g.s mu) (toUnit (TF (R := V) (FractionRing V))).left z J :=
      (val_corr hJ (hP.2 mu) (𝟙 _)).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]))
    have e₁ := ha _ (toUnit (TF (R := V) (FractionRing V))).left z J hJ
    rw [hb, e₁, hs, cst_toUnit, val_inv, val_mul hJ, val_mul hJ]
    have h₁ := htv z J hJ
    generalize GlobalTheory.UT.cst (FractionRing V) z l = c₁ at h₁ ⊢
    generalize GlobalTheory.UT.cst (FractionRing V) z (algebraMap V (FractionRing V) a) = c₂
    generalize Geo.Tor.val w (𝟙 _) z J = u₁ at h₁ ⊢
    generalize Geo.Tor.val t (toUnit (TF (R := V) (FractionRing V))).left z J = u₂ at h₁ ⊢
    generalize Geo.Tor.val gam (toUnit (TF (R := V) (FractionRing V))).left z J = u₃
    generalize Geo.Tor.val (g.s mu) (toUnit (TF (R := V) (FractionRing V))).left z J = u₄
    calc c₁ * u₃.val * (c₂ * ((u₃ * u₄ * u₂)⁻¹).val) * u₄.val * u₁.val
        = c₂ * ((c₁ * u₁.val) * (u₃.val * u₄.val) * ((u₃ * u₄ * u₂)⁻¹).val) := by ring
      _ = c₂ := by
        rw [h₁, mul_comm u₂.val, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          _root_.mul_one]
  · have e₁ := ha (Sp V) (𝟙 _) (closedPoint V) J hJ
    rw [Category.id_comp] at e₁
    rw [e₁] at hU
    exact isUnit_of_mul_isUnit_left hU

end GlobalTheory.Poinc.IntTerm.IntPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlowupModelRegularFunctionOrInverse
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

namespace GlobalTheory.RegOrInvModel

theorem exists_idealSheaf_principalises_of_ne_zero : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (n : ℕ) (U : Fin n → X.Opens) (m : Fin n → ℕ) (A : ∀ j, Fin (m j) → Γ(X, U j)), (∀ j, IsAffineOpen (U j)) → (∀ j, ∃ k, A j k ≠ 0) → ∃ J : X.IdealSheafData, genericPoint X ∉ J.support ∧ ∀ (W : Scheme.{0}) (b : W ⟶ X), ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap b) → ∀ (w : W) (j : Fin n), b w ∈ U j → ∃ (V : W.Opens) (hV : V ≤ b ⁻¹ᵁ U j), w ∈ V ∧ IsAffineOpen V ∧ ∃ k, ∀ k', (b.appLE (U j) V hV).hom (A j k) ∣ (b.appLE (U j) V hV).hom (A j k') := by
  intro X _ _ n U m A hU hA
  choose J hJU hJp using fun j => GlobalTheory.Principalise.kerIdealAffine X (U j) (hU j) (Ideal.span (Set.range (A j)))
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hηV₀, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  have hsupp : ∀ I : X.IdealSheafData, genericPoint X ∉ I.support ↔
      ∃ f ∈ I.ideal ⟨V₀, hV₀⟩, genericPoint X ∈ X.basicOpen f := by
    intro I
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V₀, hV₀⟩) hηV₀, Scheme.mem_zeroLocus_iff]
    push_neg
    rfl
  have hmul : ∀ I I' : X.IdealSheafData, genericPoint X ∉ I.support → genericPoint X ∉ I'.support →
      genericPoint X ∉ (I * I').support := by
    intro I I' h h'
    obtain ⟨f, hf, hηf⟩ := (hsupp I).1 h
    obtain ⟨f', hf', hηf'⟩ := (hsupp I').1 h'
    refine (hsupp _).2 ⟨f * f', ?_, ?_⟩
    · rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
      exact Ideal.mul_mem_mul hf hf'
    · rw [Scheme.basicOpen_mul]
      exact ⟨hηf, hηf'⟩
  have hone : genericPoint X ∉ (1 : X.IdealSheafData).support := by
    refine (hsupp _).2 ⟨1, ?_, ?_⟩
    · show (1 : Γ(X, V₀)) ∈ (⊤ : X.IdealSheafData).ideal ⟨V₀, hV₀⟩
      rw [Scheme.IdealSheafData.ideal_top]
      exact Submodule.mem_top
    · rw [Scheme.basicOpen_one]
      exact hηV₀
  have hJj : ∀ j, genericPoint X ∉ (J j).support := by
    intro j
    obtain ⟨k, hk⟩ := hA j
    have hb : X.basicOpen (A j k) ≠ ⊥ := fun h0 => hk ((basicOpen_eq_bot_iff _).1 h0)
    obtain ⟨x, hx⟩ : ∃ x, x ∈ X.basicOpen (A j k) := by
      by_contra hc
      push_neg at hc
      exact hb (eq_bot_iff.2 fun x hx => (hc x hx).elim)
    have hηb : genericPoint X ∈ X.basicOpen (A j k) := gen_mem hx
    have hηU : genericPoint X ∈ U j := X.basicOpen_le _ hηb
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U j, hU j⟩) hηU, Scheme.mem_zeroLocus_iff, hJU j]
    exact fun h => h _ (Ideal.subset_span ⟨k, rfl⟩) hηb
  refine ⟨∏ j, J j, ?_, ?_⟩
  · exact Finset.prod_induction J (fun I => genericPoint X ∉ I.support) hmul hone fun j _ => hJj j
  · intro W b hE w j hw
    obtain ⟨V₁, f, hw₁, hf, hV₁⟩ := hE w
    obtain ⟨g, hgle, hwg⟩ := V₁.2.exists_basicOpen_le (V := V₁.1 ⊓ b ⁻¹ᵁ U j) ⟨w, hw₁, hw⟩ hw₁
    have hDU : (W.affineBasicOpen g).1 ≤ b ⁻¹ᵁ U j := hgle.trans inf_le_right
    have hDV : (W.affineBasicOpen g).1 ≤ V₁.1 := W.basicOpen_le g
    have hfD : (W.presheaf.map (homOfLE hDV).op).hom f ∈ nonZeroDivisors Γ(W, (W.affineBasicOpen g).1) :=
      (GlobalTheory.Cartier.isRegularFn_iff_of_isAffineOpen (W.affineBasicOpen g).2).1
        (((GlobalTheory.Cartier.isRegularFn_iff_of_isAffineOpen V₁.2).2 hf).resG hDV)
    have hI1 := ((∏ i, J i).comap b).map_ideal_basicOpen V₁ g
    rw [hV₁, Ideal.map_span, Set.image_singleton] at hI1
    have hI2 := GlobalTheory.Principalise.comapIdealAffine (∏ i, J i) b ⟨U j, hU j⟩ (W.affineBasicOpen g) hDU
    rw [← Finset.mul_prod_erase Finset.univ J (Finset.mem_univ j), Scheme.IdealSheafData.ideal_mul,
      Pi.mul_apply, Ideal.map_mul, hJU, Ideal.map_span, ← Set.range_comp] at hI2
    rw [← Finset.mul_prod_erase Finset.univ J (Finset.mem_univ j)] at hI1
    have hwD : w ∈ (W.affineBasicOpen g).1 := hwg
    obtain ⟨k, s, hsP, hdiv⟩ := GlobalTheory.Principalise.exists_dvd_of_span_mul_eq
      (Ideal.comap (W.presheaf.germ (W.affineBasicOpen g).1 w hwD).hom (IsLocalRing.maximalIdeal _)) _ _
      (hI2.symm.trans hI1.symm) hfD
    have hsu : w ∈ W.basicOpen s := by
      rw [Scheme.mem_basicOpen _ _ _ hwD]
      by_contra hc
      exact hsP ((IsLocalRing.mem_maximalIdeal _).2 hc)
    have hED : W.basicOpen s ≤ (W.affineBasicOpen g).1 := W.basicOpen_le s
    have hV : W.basicOpen s ≤ b ⁻¹ᵁ U j := fun x hx => hDU (hED hx)
    refine ⟨W.basicOpen s, hV, hsu, (W.affineBasicOpen g).2.basicOpen s, k, fun k' => ?_⟩
    have key : b.appLE (U j) _ hDU ≫ W.presheaf.map (homOfLE hED).op = b.appLE (U j) (W.basicOpen s) hV :=
      Scheme.Hom.appLE_map _ _ _
    have hu := W.toRingedSpace.isUnit_res_basicOpen s
    have h1 := map_dvd (W.presheaf.map (homOfLE hED).op).hom (hdiv k')
    rw [map_mul] at h1
    have h2 := hu.dvd_mul_left.1 h1
    rw [← key]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    exact h2

theorem exists_model_regAt_or_regAt_inv : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ g : X.functionField, g ≠ 0 → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (π : Y ⟶ X) (φ : X.functionField →+* Y.functionField), IsArithVar (π ≫ p) D ∧ IsModel π φ ∧ ∀ y : Y, RegAt y (φ g) ∨ RegAt y (φ g)⁻¹ := by
  intro k _ X _ p D hX g hg
  have := hX.isLocallyNoetherian
  have := hX.isNoetherian
  choose V hVa hxV using fun x : X => (by
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨V, hV, hx⟩ : ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (V x : Set X)) (fun x => (V x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)
  let e := t.equivFin
  let U : Fin t.card → X.Opens := fun j => V (e.symm j).1
  have hU : ∀ j, IsAffineOpen (U j) := fun j => hVa _
  have hη : ∀ j, genericPoint X ∈ U j := fun j => gen_mem (hxV (e.symm j).1)
  have hfr : ∀ j, ∃ a b : Γ(X, U j), b ≠ 0 ∧ fnOf (U j) (hη j) a / fnOf (U j) (hη j) b = g := by
    intro j
    have : Nonempty (U j) := ⟨⟨_, hη j⟩⟩
    have := functionField_isFractionRing_of_isAffineOpen X (U j) (hU j)
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Γ(X, U j)) g
    exact ⟨a, b, nonZeroDivisors.ne_zero hb, hab⟩
  choose a b hb hab using hfr
  let A : ∀ j, Fin 2 → Γ(X, U j) := fun j => ![a j, b j]
  obtain ⟨J, hJη, hJdiv⟩ := exists_idealSheaf_principalises_of_ne_zero X t.card U (fun _ => 2) A hU fun j => ⟨1, hb j⟩
  obtain ⟨Y, ρ, hY, hE, hiso⟩ := GlobalTheory.BlowArith.exists_isArithVar_effCartier_isIso k X p D hX J hJη
  have : IsIntegral Y := hY.isIntegral
  obtain ⟨φ, hφ⟩ := _root_.GlobalTheory.HSNef.isModel_of_isIso_restrict X Y ρ J.support.compl ⟨genericPoint X, hJη⟩ (hiso _ fun _ hx => hx)
  obtain ⟨-, -, hfn, -⟩ := _root_.GlobalTheory.HSNef.model_regAt_unitAt_values k X Y p (ρ ≫ p) ρ rfl φ hφ
  refine ⟨Y, inferInstance, ρ, φ, hY, hφ, fun y => ?_⟩
  obtain ⟨x, hxt, hyx⟩ : ∃ x ∈ t, ρ y ∈ V x := by
    simpa using ht (Set.mem_univ (ρ y))
  set j := e ⟨x, hxt⟩ with hj
  have hyj : ρ y ∈ U j := by simpa [U, j] using hyx
  obtain ⟨W, hW, hyW, -, kk, hdiv⟩ := hJdiv Y ρ hE y j hyj
  have hWη : genericPoint Y ∈ W := gen_mem hyW
  have key : ∀ c : Γ(X, U j), fnOf W hWη ((ρ.appLE (U j) W hW).hom c) = φ (fnOf (U j) (hη j) c) := by
    intro c
    rw [hfn (U j) (hη j) (hW hWη) c]
    exact fnOf_resG hW hWη ((ρ.app (U j)).hom c)
  have hbne : φ (fnOf (U j) (hη j) (b j)) ≠ 0 := by
    rw [map_ne_zero]
    exact fun h0 => hb j (fnOf_injective _ _ (h0.trans (map_zero _).symm))
  have hane : φ (fnOf (U j) (hη j) (a j)) ≠ 0 := by
    rw [map_ne_zero]
    intro h0
    apply hg
    rw [← hab j, h0, zero_div]
  have hφg : φ g = φ (fnOf (U j) (hη j) (a j)) / φ (fnOf (U j) (hη j) (b j)) := by
    rw [← hab j, map_div₀]
  fin_cases kk
  · right
    obtain ⟨c, hc⟩ := hdiv 1
    have e1 := congrArg (fnOf W hWη) hc
    rw [map_mul, key, key] at e1
    have : (φ g)⁻¹ = fnOf W hWη c := by
      rw [hφg, inv_div, div_eq_iff hane]
      exact e1.trans (mul_comm _ _)
    rw [this]
    exact regAt_fnOf hyW hWη c
  · left
    obtain ⟨c, hc⟩ := hdiv 0
    have e1 := congrArg (fnOf W hWη) hc
    rw [map_mul, key, key] at e1
    have : φ g = fnOf W hWη c := by
      rw [hφg, div_eq_iff hbne]
      exact e1.trans (mul_comm _ _)
    rw [this]
    exact regAt_fnOf hyW hWη c

end GlobalTheory.RegOrInvModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCDvrTwoEmbeddings
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section
namespace GlobalTheory.TInj

theorem exists_cDvr_two_embeddings : ∀ (R R₁ R' : Type) [CommRing R] [IsLocalRing R] [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R₁), Function.Injective ρ → ρ.Finite → IsCN R' → ∀ θ₁ θ₂ : R →+* R', Function.Injective θ₁ → Function.Injective θ₂ → IsLocalHom θ₁ → IsLocalHom θ₂ → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : CharZero V) (η' : R' →+* V) (f₁ f₂ : R₁ →+* V), IsAdicComplete (maximalIdeal V) V ∧ Function.Injective η' ∧ Function.Injective f₁ ∧ Function.Injective f₂ ∧ IsLocalHom f₁ ∧ IsLocalHom f₂ ∧ f₁.comp ρ = η'.comp θ₁ ∧ f₂.comp ρ = η'.comp θ₂ := by
  intro R R₁ R' _ _ _ _ _ _ _ _ ρ hρ hfin hR' θ₁ θ₂ hθ₁ hθ₂ hl₁ hl₂
  obtain ⟨hN, hIC, hC, hCZ⟩ := hR'
  have hadm : AdmBase R' (maximalIdeal R') := ⟨hN, inferInstance, hIC, hC⟩
  obtain ⟨V₀, _, _, _, φ₀, hV₀, hφ₀, hI₀⟩ :=
    GlobalTheory.adic_base_embeds_valuation_algebraic_closure.1 R' (maximalIdeal R') hadm
  have hcz₀ : CharZero V₀ := charZero_of_injective_ringHom hφ₀
  have hloc₀ : IsLocalHom φ₀ := by
    refine ⟨fun x hx => ?_⟩
    by_contra hnx
    have hxm : x ∈ maximalIdeal R' := (mem_maximalIdeal x).2 hnx
    have : φ₀ x ∈ maximalIdeal V₀ := hI₀ (Ideal.mem_map_of_mem φ₀ hxm)
    exact (mem_maximalIdeal _).1 this hx
  have hcd₀ : GlobalTheory.LN.CDvr V₀ := ⟨inferInstance, hV₀, hcz₀⟩
  obtain ⟨V₁, _, _, _, g₁, ψ₁, hcd₁, hg₁, hlg₁, hlψ₁, hc₁⟩ :=
    GlobalTheory.LocExt.exists_cDvr_ext_of_finite R R₁ ρ hρ hfin V₀ hcd₀ (φ₀.comp θ₁) inferInstance
  obtain ⟨V, _, _, _, g₂, ψ₂, hcd, hg₂, hlg₂, hlψ₂, hc₂⟩ :=
    GlobalTheory.LocExt.exists_cDvr_ext_of_finite R R₁ ρ hρ hfin V₁ hcd₁ (g₁.comp (φ₀.comp θ₂)) inferInstance
  obtain ⟨hdvr, hcomp, hcz⟩ := hcd
  letI : Algebra R R₁ := ρ.toAlgebra
  haveI : Module.Finite R R₁ := hfin
  haveI : Algebra.IsIntegral R R₁ := Algebra.IsIntegral.of_finite R R₁
  have inj_of : ∀ f : R₁ →+* V, Function.Injective (f.comp ρ) → Function.Injective f := by
    intro f hf
    refine (RingHom.injective_iff_ker_eq_bot f).2 (Ideal.eq_bot_of_comap_eq_bot (R := R) ?_)
    have : Ideal.comap (algebraMap R R₁) (RingHom.ker f) = RingHom.ker (f.comp ρ) := rfl
    change Ideal.comap (algebraMap R R₁) (RingHom.ker f) = ⊥
    rw [this]
    exact (RingHom.injective_iff_ker_eq_bot _).1 hf
  let η' : R' →+* V := g₂.comp (g₁.comp φ₀)
  have hη' : Function.Injective η' := hg₂.comp (hg₁.comp hφ₀)
  have e₁ : (g₂.comp ψ₁).comp ρ = η'.comp θ₁ := by
    rw [RingHom.comp_assoc, hc₁]; rfl
  have e₂ : ψ₂.comp ρ = η'.comp θ₂ := by
    rw [hc₂]; rfl
  refine ⟨V, inferInstance, inferInstance, hdvr, hcz, η', g₂.comp ψ₁, ψ₂, hcomp, hη', ?_, ?_, inferInstance,
    hlψ₂, e₁, e₂⟩
  · exact inj_of _ (by rw [e₁]; exact hη'.comp hθ₁)
  · exact inj_of _ (by rw [e₂]; exact hη'.comp hθ₂)

end GlobalTheory.TInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartDensBc
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.Mix

theorem exists_chart_dens_bc : ∀ (k K : Type) [CommRing k] [CommRing K] (ρ : k →+* K) (X G : Scheme.{0}) (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap ρ)) (τ : K →+* ℂ) (D : ℕ) (c : AlgChart p (τ.comp ρ) D) (z : CxPts q τ), bcPt hp.w τ z ∈ c.e.source → ∃ c' : AlgChart q τ D, z ∈ c'.e.source ∧ ∀ w ∈ c'.e.source, bcPt hp.w τ w ∈ c.e.source ∧ c'.e w = c.e (bcPt hp.w τ w) ∧ ∀ L : Fin D → MLine p (τ.comp ρ), dens (fun i => (L i).bc hp.w τ) c' w = dens L c (bcPt hp.w τ w) := by
  intro k K _ _ ρ X G p q j hp τ D c z hz
  have hm : ∀ w, (bcPt hp.w τ w).1 = w.1 ≫ j := fun _ => rfl
  obtain ⟨c₀, hz₀, h, hx⟩ := c.exists_baseChange hp hm hz
  let c' := c₀.restr (bcPt hp.w τ ⁻¹' c.e.source) (c.e.open_source.preimage (continuous_bcPt hp.w τ))
  have H : ∀ w ∈ c'.e.source, bcPt hp.w τ w ∈ c.e.source ∧ c'.e w = c.e (bcPt hp.w τ w) := by
    intro w hw
    rw [AlgChart.restr_source] at hw
    refine ⟨hw.2, ?_⟩
    change c₀.e w = _
    ext a
    rw [c.apply_eq _ hw.2, c₀.apply_eq _ hw.1, hx, ev_appLE_of_comp hm h _ (c₀.source_subset hw.1)]
  refine ⟨c', by rw [AlgChart.restr_source]; exact ⟨hz₀, hz⟩, fun w hw => ⟨(H w hw).1, (H w hw).2, fun L => ?_⟩⟩
  have hw' := (H w hw).1
  have key (N : MLine p (τ.comp ρ)) :
      c'.hess (N.bc hp.w τ).φ (pick (N.bc hp.w τ).φ.isLB w) w =
        c.hess N.φ (pick N.φ.isLB (bcPt hp.w τ w)) (bcPt hp.w τ w) := by
    have hj := mem_of_mem_linComb (m := fun _ => bcPt hp.w τ w) (fun _ => rfl)
      (mem_pick (N.bc hp.w τ).φ.isLB w) PUnit.unit
    rw [c.hess_eq N.cInf hw' hj (mem_pick _ _), AlgChart.hess,
      AlgChart.hess, ← (H w hw).2, ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr]
    filter_upwards [c'.e.open_target.mem_nhds (c'.e.map_source hw)] with v hv
    obtain ⟨h₁, h₂⟩ := H _ (c'.e.map_target hv)
    rw [c'.e.right_inv hv] at h₂
    have e₁ : c.e.symm v = bcPt hp.w τ (c'.e.symm v) := (congrArg c.e.symm h₂).trans (c.e.left_inv h₁)
    rw [e₁]
    simp [MLine.bc, Weight.linComb]
  simp only [dens, key]

end GlobalTheory.Mix
end

