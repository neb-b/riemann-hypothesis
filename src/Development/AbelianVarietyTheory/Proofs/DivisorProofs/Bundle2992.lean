module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2894
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2963
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2934
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2965
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantHeatOperatorOfSymmetricRelat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2862
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1269
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2659
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2944
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2425
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2972
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2175
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0048

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorShiftDivMonomial
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
namespace GlobalTheory.Heat

theorem heat_div_monomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∀ (e : ℕ), 1 ≤ e → ∀ (mu α : P.D.toPre.X) (N : Fin m → ℕ) (σ σ' : P.D.toPre.SecB e α) (σ₁ σ₁u σ₁' σ₁u' : P.D.toPre.SecB e (α + e • mu)), TActs Y h e α σ σ' → ShiftEq P.D.toPre e mu α σ σ₁ 0 σ₁ → ShiftEq P.D.toPre e mu α σ' σ₁' 0 σ₁' → (∀ (Z : Scheme.{0}) (x : Z ⟶ P.D.toPre.P.A.left) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁ x z J = gs (x ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i ^ N i)) * sval σ₁u x z J) → (∀ (Z : Scheme.{0}) (x : Z ⟶ P.D.toPre.P.A.left) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁' x z J = gs (x ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i ^ N i)) * sval σ₁u' x z J) → ∃ σ₁u'' : P.D.toPre.SecB e (α + e • mu), TActs Y h e (α + e • mu) σ₁u σ₁u'' ∧ ∀ (Z : Scheme.{0}) (x : Z ⟶ P.D.toPre.P.A.left) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁u'' x z J = sval σ₁u' x z J - gs (x ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (2 * (e : ChartRing k m d) * ∑ i, (N i : ChartRing k m d) * q i)) * sval σ₁u x z J := by
  intro E _ _ _ H k _ _ m d t P gam hmon hli hab Y n' v' dd hdd D q hq h hb hdef hΘ ρ hρ B' _ π₁ π₂ c' h1 h2 h3 h4 e he mu α N σ σ' σ₁ σ₁u σ₁' σ₁u' hT hS hS' hv hv'
  letI := H.starRing
  haveI : IsAdicComplete (maximalIdeal k) k := by rw [maximalIdeal_eq_bot]; infer_instance
  haveI : IsAdicComplete (maximalIdeal (ChartRing k m d)) (ChartRing k m d) :=
    GlobalTheory.PlaceInt.isAdicComplete_mvPowerSeries_finite (V := k) _

  clear hρ h1 h2 h3 h4 hΘ hmon hli hab
  have f1 : ∀ x y, D (x + y) = D x + D y := D.map_add
  have f2 : ∀ (z : ℤ) (x : ChartRing k m d), D (z • x) = z • D x := fun z x => map_zsmul D z x
  have f3 : D 1 = 0 := D.map_one_eq_zero
  have f4 : ∀ x y, D (x * y) = x • D y + y • D x := D.leibniz
  generalize (⇑D : ChartRing k m d → ChartRing k m d) = f at f1 f2 f3 f4 hq h hb hdef ⊢
  letI : Algebra ℤ (ChartRing k m d) := Ring.toIntAlgebra _
  let D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d) :=
    { toFun := f, map_add' := f1, map_smul' := fun z x => f2 z x, map_one_eq_zero' := f3, leibniz' := f4 }
  have hA1 := heat_acts_on_terms (ChartRing k m d) P.D (𝓞 E) P.oD Y n' v' dd hdd D' h hb e (α + e • mu) σ₁
  have hA2 := heat_acts_on_terms (ChartRing k m d) P.D (𝓞 E) P.oD Y n' v' dd hdd D' h hb e (α + e • mu) σ₁u
  obtain ⟨σ₁'', hA1⟩ := hA1
  obtain ⟨σ₁u'', hA2⟩ := hA2
  refine ⟨σ₁u'', hA2, ?_⟩
  have hd : ShiftEq P.D.toPre e mu α σ' σ₁'' 0 σ₁ := hdef e mu α σ σ' σ₁ σ₁'' he hS hT hA1
  obtain ⟨⟨u, hu, hc⟩, -⟩ := ReciprocityTheory.ChartRestriction.G.DVR.gen_fe (D := P.D.toPre) (F := FractionRing (ChartRing k m d))
    GlobalTheory.SemiRigid.globalFns e mu α
  have hU : ∀ z J, Good P.D.toPre.P.L z J → sval σ₁'' (DegPre.prB P.D.toPre (FractionRing (ChartRing k m d))).left z J =
      sval σ₁' (DegPre.prB P.D.toPre (FractionRing (ChartRing k m d))).left z J := by
    intro z J hJ
    have E1 := GlobalTheory.HeatDefect.shiftEq_at hd u hu hc (𝟙 _) z J hJ
    have E2 := GlobalTheory.HeatDefect.shiftEq_at hS' u hu hc (𝟙 _) z J hJ
    simp only [Category.id_comp, GlobalTheory.HeatDefect.scal_zero, zero_mul, add_zero] at E1 E2
    rw [E1, E2]
  obtain ⟨τ₁, τ₁'', t1, t1'', a1⟩ := hA1
  obtain ⟨τu, τu'', tu, tu'', a2⟩ := hA2
  have hτ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ P.D.toPre.P.A.left) → P.D.toPre.P.L.ι),
      Good P.D.toPre.P.L z J → sval τ₁ r z J = gs (r ≫ Y.H.hom) z ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i ^ N i)) * sval τu r z J := by
    intro Z r z J hJ
    let x : Over.mk (r ≫ Y.H.hom) ⟶ Y.H := Over.homMk r rfl
    have e1 := t1 _ x z J hJ
    have e2 := tu _ x z J hJ
    have e3 := hv Z (r ≫ Y.q.left) z J hJ
    have hw : (r ≫ Y.q.left) ≫ P.D.toPre.P.A.hom = r ≫ Y.H.hom := by rw [Category.assoc, Over.w]
    rw [hw] at e3
    change sval τ₁ r z J = _ at e1
    change sval τu r z J = _ at e2
    rw [Over.comp_left] at e1 e2
    change _ = sval σ₁ (r ≫ Y.q.left) z J * _ at e1
    change _ = sval σ₁u (r ≫ Y.q.left) z J * _ at e2
    rw [e1, e2, e3, _root_.mul_assoc]

  have hτ'' := _root_.GlobalTheory.HeatOpConst.heat_const_mul (ChartRing k m d) P.D.toPre (𝓞 E) P.oD Y n' (fun a => v' a) dd hdd D' h e
    (∏ i, bdParam k m d i ^ N i) τ₁ τ₁'' τu τu'' a1 a2 hτ
  have hP := _root_.GlobalTheory.TermDescend.main (ChartRing k m d) P.D.toPre (𝓞 E) P.oD Y e (α + e • mu) σ₁'' σ₁u'' σ₁u τ₁'' τu'' τu
    (∏ i, bdParam k m d i ^ N i) (2 * (e : ChartRing k m d) * D' (∏ i, bdParam k m d i ^ N i)) t1'' tu'' tu hτ''
  have hpow : ∀ (x c : ChartRing k m d), D' x = c * x → ∀ n : ℕ, D' (x ^ n) = (n : ChartRing k m d) * c * x ^ n := by
    intro x c hx n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Derivation.leibniz, ih, hx, smul_eq_mul, smul_eq_mul]
      push_cast; ring
  have hDt : ∀ s : Finset (Fin m), D' (∏ i ∈ s, bdParam k m d i ^ N i) =
      (∑ i ∈ s, (N i : ChartRing k m d) * q i) * ∏ i ∈ s, bdParam k m d i ^ N i := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Derivation.leibniz, ih,
        hpow _ (q a) (hq a) (N a), smul_eq_mul, smul_eq_mul]
      ring
  have hne0 : ∀ i, bdParam k m d i ≠ 0 := fun i h => by
    have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i) 1)) h
    simp [MvPowerSeries.coeff_X] at this
  have hne : (∏ i, bdParam k m d i ^ N i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hne0 i)
  have hg : ∀ {Z : Scheme.{0}} (r : Z ⟶ P.D.toPre.P.A.left) (z : Z) (c : ChartRing k m d),
      gs (r ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom c) =
        GlobalTheory.HeatMod.germConstHom (r ≫ P.D.toPre.P.A.hom) z c := fun r z c =>
    (GlobalTheory.HeatTermLin.gs_constFn _ r z c).symm.trans (GlobalTheory.HeatMod.gs_constFn_eq_germConstHom _ r z c)
  have key := _root_.GlobalTheory.SecBGenericAgree.main (ChartRing k m d) P.D.toPre e (α + e • mu) σ₁u''
    (σ₁u' - constFn P.D.toPre.P.A.hom ⊤ (2 * (e : ChartRing k m d) * ∑ i, (N i : ChartRing k m d) * q i) • σ₁u)
    (∏ i, bdParam k m d i ^ N i) hne (by
      intro z J hJ
      have a1 := hP z J hJ
      have a2 := hU z J hJ
      have a3 := hv' _ (DegPre.prB P.D.toPre (FractionRing (ChartRing k m d))).left z J hJ
      rw [GlobalTheory.HeatMod.sval_sub_constFn_smul _ _ _ _ _ _ hJ]
      rw [hDt] at a1
      simp only [hg] at a1 a3 ⊢
      simp only [map_mul, map_natCast, map_ofNat] at a1 ⊢
      linear_combination a2 + a3 - a1)
  intro Z x z J hJ
  rw [key Z x z J hJ, GlobalTheory.HeatMod.sval_sub_constFn_smul _ _ _ _ _ _ hJ, hg]

end GlobalTheory.Heat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomDescent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AlgClosedDescent

theorem hom_descent : ∀ (k₀ K : Type) [Field k₀] [IsAlgClosed k₀] [Field K] [Algebra k₀ K] (B B' : Over (Sp k₀)) [GrpObj B] [GrpObj B'], IsAbelianScheme B → IsAbelianScheme B' → ∀ f : (Over.pullback (spMap (algebraMap k₀ K))).obj B ⟶ (Over.pullback (spMap (algebraMap k₀ K))).obj B', IsMonHom f → ∃! f₀ : B ⟶ B', IsMonHom f₀ ∧ (Over.pullback (spMap (algebraMap k₀ K))).map f₀ = f := by
  intro k₀ K _ _ _ _ B B' _ _ hB hB' f hf
  have hP : IsAbelianScheme (B ⊗ B') := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hB hB'
  let i : B ⟶ B ⊗ B' := lift (𝟙 B) 1
  let j : B' ⟶ B ⊗ B' := lift 1 (𝟙 B')
  have hi : IsMonHom i := by
    have : IsMonHom (1 : B ⟶ B') := by
      rw [Hom.one_def]; infer_instance
    infer_instance
  have hj : IsMonHom j := by
    have : IsMonHom (1 : B' ⟶ B) := by
      rw [Hom.one_def]; infer_instance
    infer_instance
  obtain ⟨F₀, ⟨hF₀, hF⟩, -⟩ := endo_descent (K := K) (B ⊗ B') hP
    ((Over.pullback (spMap (algebraMap k₀ K))).map (fst B B') ≫ f ≫
      (Over.pullback (spMap (algebraMap k₀ K))).map j) inferInstance
  have key : (Over.pullback (spMap (algebraMap k₀ K))).map (i ≫ F₀ ≫ snd B B') = f := by
    rw [Functor.map_comp, Functor.map_comp, hF]
    simp only [Category.assoc]
    rw [← Functor.map_comp, ← Functor.map_comp_assoc, lift_fst, lift_snd,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
      Category.comp_id]
  exact ⟨i ≫ F₀ ≫ snd B B', ⟨inferInstance, key⟩, fun f₁ hf₁ =>
    ActDescent.pullback_map_injective (spMap (algebraMap k₀ K)) B B' (hf₁.2.trans key.symm)⟩

end GlobalTheory.AlgClosedDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealAlongMonomialFamilyEqSpanMonomial
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.UGZero

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {φ : InvFun (𝓞 E)}

theorem s_ne_zero {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V)
    (k : Fin Cm.m) : Cm.s k ≠ 0 := by
  intro hk
  have hδ : Cm.δ k ≠ 0 := Cm.cone.linearIndependent.ne_zero k
  have hsym := (Cm.cone.mem k).1
  obtain ⟨y, hy⟩ : ∃ y, Cm.δ k y y ≠ 0 := by
    by_contra h
    push_neg at h
    apply hδ
    refine LinearMap.ext₂ fun a b => ?_
    have h1 := h (a + b)
    have h2 := h a
    have h3 := h b
    simp only [map_add (f := _), LinearMap.add_apply] at h1
    rw [hsym b a] at h1
    simp only [LinearMap.zero_apply]
    omega
  obtain ⟨u, n, hn, hc⟩ := Cm.mono y
  have hM : (0 : ℤ) < (l.M' : ℤ) := by exact_mod_cast GlobalTheory.LevelExist.M'_pos l
  have hnk : n k ≠ 0 := by
    intro h0
    have e := hn k
    rw [h0] at e
    simp only [LinearMap.smul_apply, smul_eq_mul, Nat.cast_zero, mul_zero] at e
    rcases mul_eq_zero.1 e with e | e
    · omega
    · exact hy e
  apply GlobalTheory.PsiCoordLocal.ne_zero_of_coord hc
  rw [Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hk]; exact zero_pow hnk), mul_zero]

end GlobalTheory.UGZero

namespace GlobalTheory.UGZero

theorem idlAlong_eq_span_monomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (φ : InvFun (𝓞 E)), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (d : ℕ) (J : C.Z.IdealSheafData), (∀ x ∈ J.support, x ∉ Set.range C.i) → UValOn Xo c C.i φ J d → ∀ (S : Scheme.{0}) (π : S ⟶ pullback C.z (spMap C.b)), IsNormBl π (J.comap (pullback.fst C.z (spMap C.b))) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V), GlobalTheory.Mum.Base V → ∀ ξ : Sp V ⟶ S, Cm.y ≫ C.iF = jK V ≫ ξ ≫ π → ∃ b : Fin Cm.m → ℕ, (∀ k, (b k : ℝ) = d * φ.evalZ ((l.M' : ℤ) • Cm.δ k)) ∧ idlAlong J (ξ ≫ π ≫ pullback.fst C.z (spMap C.b)) = Ideal.span {∏ k, Cm.s k ^ b k} := by
  intro E _ _ _ H Dw hpq l Xo c C φ hpf d J hJ hval S π hbl V _ _ _ Cm hV ξ hξ
  haveI : Module.Projective (𝓞 E) Cm.P.D.toPre.X := GlobalTheory.Forms.projective_of_int _ _
  have hP := hpf Cm.P.D.toPre.X Cm.rank
  have key0 : ∀ k, ∃ n : ℕ, φ.evalZ ((l.M' : ℤ) • Cm.δ k) = n := fun k =>
    hP.exists_nat (Submodule.smul_mem _ _ (Cm.cone.mem k)) (fun y => by
      simp only [LinearMap.smul_apply, smul_eq_mul]
      exact mul_nonneg (by positivity) (Cm.cone.nonneg k y))
  choose n hn using key0
  refine ⟨fun k => d * n k, fun k => by rw [hn]; push_cast; ring, ?_⟩
  set f := ∏ k, Cm.s k ^ (d * n k) with hf
  obtain ⟨g₀, hg₀⟩ := GlobalTheory.NormBlPrincipal.idlAlong_comap_principal π _ hbl V ξ
  rw [GlobalTheory.PullAlong.idlAlong_comap_eq, GlobalTheory.PullAlong.idlAlong_comap_eq, Category.assoc] at hg₀
  rw [hg₀]
  have hV' := hV
  obtain ⟨⟨hNoeth, -, hIC, -⟩, hchar⟩ := hV'
  have key : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ ψ : V →+* W,
      Function.Injective ψ → IsLocalHom ψ → Ideal.span {ψ g₀} = Ideal.span {ψ f} := by
    intro W _ _ _ hW ψ hψi hψl
    haveI : IsDiscreteValuationRing W := ((GlobalTheory.LN.cDvr_iff W).1 hW).1
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
    have hw : ∀ k, ∃ w : ℕ, Associated (ψ (Cm.s k)) (ϖ ^ w) := fun k => by
      have h0 : ψ (Cm.s k) ≠ 0 := fun h => s_ne_zero Cm k (hψi (h.trans (map_zero ψ).symm))
      obtain ⟨w, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
      exact ⟨w, ⟨u⁻¹, by rw [hu, mul_comm (u : W), _root_.mul_assoc, Units.mul_inv, _root_.mul_one]⟩⟩
    choose w hw using hw
    have hinj : Function.Injective ((algebraMap W (FractionRing W)).comp ψ) :=
      (IsFractionRing.injective W (FractionRing W)).comp hψi
    obtain ⟨gam, e⟩ : ∃ gam : FractionRing V →+* FractionRing W,
        gam.comp (algebraMap V (FractionRing V)) = (algebraMap W (FractionRing W)).comp ψ :=
      ⟨IsFractionRing.lift hinj, RingHom.ext fun r => by
        rw [RingHom.comp_apply, RingHom.comp_apply]; exact IsFractionRing.lift_algebraMap hinj r⟩
    have hκ : spMap gam ≫ jK V = jK W ≫ spMap ψ := by
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e]
    obtain ⟨t, tK, P, ⟨a1⟩, ⟨a2⟩, be, hbe, hmono, hφbe⟩ :=
      GlobalTheory.UChart.pull_trait Xo c φ V hV Cm W hW ψ hψi hψl ϖ hϖ w hw (spMap gam) hκ
    have hy : (spMap gam ≫ Cm.y) ≫ C.i = jK W ≫ (spMap ψ ≫ ξ ≫ π ≫ pullback.fst C.z (spMap C.b)) := by
      simp only [UCompact.i, Category.assoc]
      rw [reassoc_of% hξ, reassoc_of% hκ]
    obtain ⟨N, hN, hid⟩ := hval W hW ϖ hϖ _ (spMap gam ≫ Cm.y) hy t tK ⟨a1⟩ ⟨a2⟩ P be hbe hmono
    rw [GlobalTheory.TraitOrder.idlAlong_comp, hg₀, Ideal.map_span, Set.image_singleton] at hid
    rw [hid]
    have hNe : N = ∑ k, w k * (d * n k) := by
      have : (N : ℝ) = ((∑ k, w k * (d * n k) : ℕ) : ℝ) := by
        rw [hN, hφbe]
        push_cast
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hn]; ring
      exact_mod_cast this
    refine Ideal.span_singleton_eq_span_singleton.2 ?_
    rw [hf, map_prod, hNe, ← Finset.prod_pow_eq_pow_sum]
    refine (Associated.prod Finset.univ (fun k => ψ (Cm.s k ^ (d * n k))) (fun k => ϖ ^ (w k * (d * n k)))
      fun k _ => ?_).symm
    rw [map_pow, pow_mul ϖ (w k)]
    exact (hw k).pow_pow
  haveI := hNoeth
  haveI := hIC
  haveI := hchar
  have hf0 : f ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (s_ne_zero Cm k)
  have hg0 : g₀ ≠ 0 := by
    rintro rfl
    obtain ⟨W, _, _, _, ψ, hW, hψi, hψl⟩ := GlobalTheory.DvrDom.exists_cdvr_dominating V
    have := key W hW ψ hψi hψl
    rw [map_zero, Ideal.span_singleton_eq_bot.2 rfl, eq_comm, Ideal.span_singleton_eq_bot] at this
    exact hf0 (hψi (this.trans (map_zero ψ).symm))
  have hkey' : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W], IsAdicComplete (maximalIdeal W) W →
      ∀ ψ : V →+* W, Function.Injective ψ → IsLocalHom ψ → Associated (ψ g₀) (ψ f) := by
    intro W _ _ _ hc ψ hψi hψl
    have : CharZero W := charZero_of_injective_ringHom hψi
    exact Ideal.span_singleton_eq_span_singleton.1 (key W ((GlobalTheory.LN.cDvr_iff W).2 ⟨inferInstance, hc, this⟩) ψ hψi hψl)
  have d1 := GlobalTheory.Poinc.dvd_of_forall_complete_dvr V g₀ f hf0 fun W _ _ _ hc ψ hψi hψl => (hkey' W hc ψ hψi hψl).symm.dvd
  have d2 := GlobalTheory.Poinc.dvd_of_forall_complete_dvr V f g₀ hg0 fun W _ _ _ hc ψ hψi hψl => (hkey' W hc ψ hψi hψl).dvd
  exact Ideal.span_singleton_eq_span_singleton.2 (associated_of_dvd_dvd d2 d1)

end GlobalTheory.UGZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageIsoUniformisedFactorOfAdjointPair
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam

namespace GlobalTheory.MumIsoAdj

section

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
  {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem linHom_unique (hR : Base R) (hG : IsSemiAbelian G) {U : Unif (maximalIdeal R) D A G} {a a' k k' g g'}
    (h : LinHom U.toUnifPre U.toUnifPre a k g) (h' : LinHom U.toUnifPre U.toUnifPre a' k' g') (ha : a = a')
    (hk : ∀ y, k y = k' y) : g = g' := by
  obtain rfl := ha
  obtain rfl : k = k' := AddMonoidHom.ext hk
  obtain ⟨u₁, u₂⟩ := GlobalTheory.MumUniq.main R hR.1 D A G hG U a k
  exact u₂ g g' (congrFun (u₁ _ _ (linHom_iff_linEnd.1 h).2 (linHom_iff_linEnd.1 h').2))

end

theorem iso_of_factor_adj : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre), F.Alg → ∀ (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ U₀ : Unif (maximalIdeal R) D A₀ G₀, ∃ (ε : G ≅ G₀) (u : G' ⟶ G₀) (u' : G₀ ⟶ G'), IsMonHom ε.hom ∧ IsMonHom u ∧ IsMonHom u' ∧ ε.hom = inc ≫ u ∧ u ≫ u' = oG.act (Star.star F.e * F.f * F.e) ∧ GAdj U'.LG.L U₀.LG.L u u' := by
  intro R _ _ _ hR D D' F hF A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hinc hpr hip hpi A₀ G₀ _ _ hG₀ U₀
  obtain ⟨-, hsym, g, hg⟩ := hF
  obtain ⟨u, u', hu, hu', hadj⟩ :=
    _root_.GlobalTheory.MumAdj.adj_groups R hR D' A' G' hG' U' D A₀ G₀ hG₀ U₀ _ _ _ _ (_root_.GlobalTheory.MumFam.FactorAdj.factor_adj R _ D D' F)
  have hO : ∀ a : F.O, LinHom U'.toUnifPre U'.toUnifPre (F.o.onB.act a)
      (DistribSMul.toAddMonoidHom D'.toPre.X (Star.star a)) (oG.act a) := fun a =>
    ⟨oG.hom a, fun e => hlin.q_lin e a, fun e => by
      obtain ⟨t, ht, hi⟩ := hlin.i_lin e a
      exact ⟨t, ht, hi⟩⟩
  have hu1 := hu.1
  have hu1' := hu'.1
  have hee : Star.star F.e * Star.star F.e = Star.star F.e := by rw [← star_mul, F.idem]
  have hsS : Star.star (Star.star F.e * F.f * F.e) = Star.star F.e * F.f * F.e := by
    rw [star_mul, star_mul, star_star, ← _root_.mul_assoc, ← hsym]
  have hsg : (Star.star F.e * F.f * F.e) * Star.star g = Star.star F.e := by
    have := congrArg Star.star hg
    rwa [star_mul, hsS] at this
  have hkey : F.e * Star.star g * (Star.star F.e * F.f * F.e) = F.e := by
    calc F.e * Star.star g * (Star.star F.e * F.f * F.e)
        = g * ((Star.star F.e * F.f * F.e) * Star.star g) * (Star.star F.e * F.f * F.e) := by
          nth_rewrite 1 [← hg]; simp only [_root_.mul_assoc]
      _ = g * (Star.star F.e * (Star.star F.e * F.f * F.e)) := by rw [hsg, _root_.mul_assoc]
      _ = F.e := by
          rw [← _root_.mul_assoc (Star.star F.e) (Star.star F.e * F.f) F.e,
            ← _root_.mul_assoc (Star.star F.e) (Star.star F.e) F.f, hee, hg]
  have hxi : ∀ y, F.xi y = F.e • F.xi y := fun y => by rw [← F.xi_xp, F.xp_xi]
  have hincE : F.inc ≫ F.o.onB.act F.e = F.inc := by
    rw [← F.pr_inc, ← Category.assoc, F.inc_pr, Category.id_comp]
  have h1 : u ≫ u' = oG.act (Star.star F.e * F.f * F.e) :=
    GlobalTheory.MumIsoAdj.linHom_unique hR hG' (hu.comp hu') (hO _)
      (by rw [F.o.onB.map_mul (Star.star F.e * F.f) F.e, ← F.pr_inc]; exact (Category.assoc _ _ _).symm)
      (fun y => by
        change (Star.star F.e * F.f) • F.xi (F.xp y) = Star.star (Star.star F.e * F.f * F.e) • y
        rw [hsS, F.xi_xp, smul_smul])
  have h2 : u' ≫ oG.act (F.e * g) ≫ u = 𝟙 G₀ :=
    GlobalTheory.MumIsoAdj.linHom_unique hR hG₀ ((hu'.comp (hO _)).comp hu) (LinHom.id _)
      (by
        calc ((F.inc ≫ F.o.onB.act (Star.star F.e * F.f)) ≫ F.o.onB.act (F.e * g)) ≫ F.pr
            = F.inc ≫ F.o.onB.act ((F.e * g) * (Star.star F.e * F.f * F.e)) ≫ F.pr := by
              rw [F.o.onB.map_mul (F.e * g) (Star.star F.e * F.f * F.e),
                F.o.onB.map_mul (Star.star F.e * F.f) F.e]
              conv_lhs => rw [← hincE]
              simp only [Category.assoc]
          _ = 𝟙 _ := by
              rw [_root_.mul_assoc F.e g, hg, F.idem, ← F.pr_inc]
              simp only [← Category.assoc, F.inc_pr, Category.id_comp])
      (fun y => by
        change F.xp (Star.star (F.e * g) • ((Star.star F.e * F.f) • F.xi y)) = y
        have hw : Star.star (F.e * g) • ((Star.star F.e * F.f) • F.xi y) =
            (Star.star g * (Star.star F.e * F.f * F.e)) • F.xi y := by
          conv_lhs => rw [hxi y]
          rw [smul_smul, smul_smul, star_mul]
          congr 1
          simp only [_root_.mul_assoc]
          rw [← _root_.mul_assoc (Star.star F.e) (Star.star F.e), hee]
        have h3 : F.xi (F.xp (Star.star (F.e * g) • ((Star.star F.e * F.f) • F.xi y))) = F.xi y := by
          rw [F.xi_xp, hw, smul_smul, ← _root_.mul_assoc, hkey, ← hxi]
        have := congrArg F.xp h3
        rwa [F.xp_xi, F.xp_xi] at this)
  refine ⟨⟨inc ≫ u, u' ≫ oG.act g ≫ pr, ?_, ?_⟩, u, u', inferInstance, hu.1, hu'.1, rfl, h1, hadj⟩
  · calc (inc ≫ u) ≫ u' ≫ oG.act g ≫ pr = inc ≫ ((u ≫ u') ≫ oG.act g) ≫ pr := by simp only [Category.assoc]
      _ = 𝟙 G := by
          rw [h1, ← oG.map_mul, hg, ← hpi]
          simp only [← Category.assoc, hip, Category.id_comp]
  · calc (u' ≫ oG.act g ≫ pr) ≫ inc ≫ u = u' ≫ (oG.act g ≫ pr ≫ inc) ≫ u := by simp only [Category.assoc]
      _ = 𝟙 G₀ := by rw [hpi, ← oG.map_mul, h2]

end GlobalTheory.MumIsoAdj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFrameIdentityOfGenericPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

namespace GlobalTheory.Poinc.Sep.FrameInt

theorem kap_of_generic : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (N : ℕ) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A), b ^ N = 1 → ∀ (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))), t.IsGen → ∀ (κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1)), Normd κ → (∀ z J, Good D.P.L z J → val t (toUnit (TF (R := V) (FractionRing V))).left z J ^ (N ^ 2) * val κ ((toUnit (TF (R := V) (FractionRing V))).left ≫ b.left) z J = 1) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V) (z : Z) J, Good D.P.L z J → val t r z J ^ (N ^ 2) * val κ (r ≫ b.left) z J = 1 := by
  intro V _ _ D N b hbN t ht κ hκn hgen Z r z J hJ
  have G := ((SymFrame.grep_gen t ht (𝟙 _)).pow (N ^ 2)).mul (SymFrame.grep_kap κ hκn.1 b)
  obtain ⟨s, hs, vs⟩ := G.out D.P.isLB (K := PEmpty) PEmpty.elim PEmpty.elim
    (fun U _ h => Eq.trans (by
      rw [Fin.prod_univ_two, hbN, ← SymFrame.eta_eq]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, DegPre.lineε, Category.comp_id,
        Category.id_comp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      rw [← natCast_zsmul]
      push_cast
      module) (Fintype.prod_empty _).symm)
  obtain ⟨ρ, hρ⟩ := exists_ratio D.P.isLB rfl s (LB.oneGen D.P.L) hs (oneGen_gen _)
  have hρ1 : ρ = 1 := by
    obtain ⟨z₀⟩ := exists_pt (R := V) (F := FractionRing V)
    obtain ⟨J₀, hJ₀⟩ := exists_good' D.P.isLB z₀
    have a := vs _ (toUnit (TF (R := V) (FractionRing V))) z₀ J₀ hJ₀
    rw [hρ _ _ z₀ J₀ hJ₀, val_one, _root_.mul_one] at a
    simp only [Category.comp_id] at a
    have a1 : gm (toUnit (TF (R := V) (FractionRing V))).left z₀ ⊤ ρ = 1 := a.trans (hgen z₀ J₀ hJ₀)
    have c := gm_top_eq ρ z₀
    rw [a1, Units.val_one, cst_eq, ← map_one (cstH z₀)] at c
    have d := cstH_inj z₀ c
    rw [← map_one (algebraMap V (FractionRing V))] at d
    have e := IsFractionRing.injective V (FractionRing V) d
    apply Units.ext
    have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom :=
      (Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv.injective
    apply hinj
    rw [Units.val_one, map_one]
    exact e.symm
  have a := vs (Over.mk r) (toUnit _) z J hJ
  rw [hρ _ _ z J hJ, val_one, _root_.mul_one, hρ1, map_one] at a
  simp only [Category.comp_id] at a
  exact a.symm

end GlobalTheory.Poinc.Sep.FrameInt
end

