module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2064
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1293
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2068
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0194
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1488
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
public import Formalism.SharpRestriction.Divisibility.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsWeilChar
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0186
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
public import ReciprocityTheory.DualLattices.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0242
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1212
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2075
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingDualNumber

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroClassicalPointOfLocalHomAvoiding
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Izumi

theorem exists_point_of_isLocalHom {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (x : M.Z)
    {p : ℕ} [Fact p.Prime] (χ : M.O x →+* OO p) [IsLocalHom χ] :
    ∃ y : Sp (OO p) ⟶ M.Z, y (cPt p) = x ∧ ∀ a : M.O x,
      RatModel.val M (gPt p ≫ y) (a : Ω) = ((χ a : OO p) : PadicAlgCl p) := by
  let χ' : M.Z.presheaf.stalk x ⟶ CommRingCat.of (OO p) :=
    CommRingCat.ofHom (χ.comp (M.stalkEquiv x).toRingHom)
  haveI : IsLocalHom χ'.hom := by
    refine ⟨fun a ha => ?_⟩
    have h1 : IsUnit (M.stalkEquiv x a) := isUnit_of_map_unit χ _ ha
    exact (MulEquiv.isUnit_map (M.stalkEquiv x).toMulEquiv).1 h1
  set y : Sp (OO p) ⟶ M.Z := Spec.map χ' ≫ M.Z.fromSpecStalk x with hy
  have hc : y (cPt p) = x := by
    rw [hy, Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  have key : ∀ h : y (cPt p) ⤳ x, M.Z.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo y = χ' := by
    intro h
    refine TopCat.Presheaf.stalk_hom_ext _ fun W hxW => ?_
    rw [← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes]
    exact Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk χ' W _
  refine ⟨y, hc, fun a => ?_⟩
  rw [RatModel.val_gPt hc a]
  change (((M.Z.presheaf.stalkSpecializes _ ≫ Scheme.stalkClosedPointTo y).hom
    ((M.stalkEquiv x).symm a) : OO p) : PadicAlgCl p) = _
  rw [key]
  exact congrArg (fun b => ((χ b : OO p) : PadicAlgCl p)) ((M.stalkEquiv x).apply_symm_apply a)

theorem exists_ne_zero_forall_exists_cen (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (U : M.Z.Opens) (hU : (U : Set M.Z).Nonempty) (x : M.Z) :
    ∃ s : M.O x, s ≠ 0 ∧ ∀ (p : ℕ) [Fact p.Prime] (χ : M.O x →+* OO p), IsLocalHom χ → χ s ≠ 0 →
      ∃ y : Sp (OO p) ⟶ M.Z, M.Cen U x y ∧ ∀ a : M.O x,
        RatModel.val M (gPt p ≫ y) (a : Ω) = ((χ a : OO p) : PadicAlgCl p) := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  obtain ⟨w, hwU, hwV⟩ := M.nonempty_inf hU ⟨x, hxV⟩
  obtain ⟨t, htU, hwt⟩ := hV.exists_basicOpen_le (V := U) ⟨w, hwU⟩ hwV
  have ht0 : valF M.pt V t ≠ 0 :=
    ((RatModel.isUnit_O_iff _).1 ((RatModel.isUnit_valF_iff hwV t).2 hwt)).1
  refine ⟨⟨valF M.pt V t, RatModel.valF_mem_O hxV t⟩, fun h => ht0 (congrArg Subtype.val h), ?_⟩
  intro p _ χ hχ hs
  obtain ⟨y, hc, hval⟩ := exists_point_of_isLocalHom M x χ
  refine ⟨y, ⟨hc, ?_⟩, hval⟩
  rintro _ ⟨w', rfl⟩
  have hz : (gPt p ≫ y) w' ∈ V := (RatModel.gPt_specializes hc w').mem_open V.isOpen hxV
  have hne : M.val (gPt p ≫ y) (valF M.pt V t) ≠ 0 := by
    have e := hval ⟨valF M.pt V t, RatModel.valF_mem_O hxV t⟩
    rw [e]
    intro h0
    exact hs (Subtype.ext h0)
  have hu := (RatModel.val_ne_zero_iff (RatModel.range_eq_singleton _ w')
    ⟨valF M.pt V t, RatModel.valF_mem_O hz t⟩).1 hne
  exact htU ((RatModel.isUnit_valF_iff hz t).1 hu)

end GlobalTheory.Izumi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroCuspFormParallelWeightEachComponent
section
set_option autoImplicit false

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.FlatCore.NonzeroCusp

theorem laU_const {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (V : Unf Xo c σ r) (m n : ℕ) (k : V.Comp) :
    laU V (fun _ => m) n k = laU V 0 (n + 2 * m) k := by
  funext τ j
  have e : (n + 2 * m) / 2 = n / 2 + m := by omega
  simp only [laU, Pi.zero_apply, e]
  split_ifs <;> push_cast <;> ring

theorem exists_cuspOn_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c), ∃ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n ∧ (∀ τ i, i < Dw.mult τ → 2 ≤ a (τ, i)) ∧ 4 * (finrank ℚ E * r) + 4 ≤ n ∧ ∃ f ∈ cuspOn U Z (wtZ a n), f ≠ 0 := by
  intro E _ _ _ H Dw l Xo c r U x hL Z
  have hσ : GoodEmb c c.F.val.toRingHom := rfl
  obtain ⟨n₀, hn₀, hev, f₀, hf₀, ⟨k, y⟩, hz, hne⟩ := _root_.GlobalTheory.ScalarCusp.exists_scalar_cusp_ne_zero E H Dw l Xo c r U x hL _ hσ Z
  obtain ⟨hy, hlies⟩ := hz
  have hM : CuspMul Xo c U := cusp_mul_of_M5 siegelSpaceAlgebra_holds U
  have hD0 : ∀ m, Even m → Dom (0 : (E →+* ℂ) × ℕ → ℕ) m := fun m hm => ⟨fun _ => antitone_const, hm⟩
  have hpow : ∀ j : ℕ, f₀ ^ (j + 1) ∈ cusp Xo c U 0 ((j + 1) * n₀) := by
    intro j
    induction j with
    | zero => simpa using hf₀
    | succ j ih =>
      have h := hM 0 0 ((j + 1) * n₀) n₀ (f₀ ^ (j + 1)) f₀ (hD0 _ (hev.mul_left _)) (hD0 _ hev) ih hf₀
      have e1 : ((j + 1) * n₀ + n₀) = (j + 1 + 1) * n₀ := by ring
      rw [add_zero, e1] at h
      rw [pow_succ]
      exact h
  have hrd : ∀ j : ℕ, rdU (U c.F.val.toRingHom) (f₀ ^ (j + 1)) k y = (rdU (U c.F.val.toRingHom) f₀ k y) ^ (j + 1) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, Formalism.L2.Pj.rdU_mul, Pi.mul_apply, Pi.mul_apply, ih]
      ring
  set M : ℕ := 4 * (finrank ℚ E * r) + 7 with hMdef
  obtain ⟨t, ht⟩ := hev
  have hMt : (M + 1) * n₀ = (M + 1) * t + (M + 1) * t := by rw [ht]; ring
  have ht1 : 1 ≤ t := by omega
  have hMt1 : M + 1 ≤ (M + 1) * t := Nat.le_mul_of_pos_right _ ht1
  set n : ℕ := (M + 1) * n₀ - 4 with hndef
  have hnev : Even n := ⟨(M + 1) * t - 2, by omega⟩
  have hnb : 4 * (finrank ℚ E * r) + 4 ≤ n := by omega
  have hn4 : n + 2 * 2 = (M + 1) * n₀ := by omega
  have hP : rdU (U c.F.val.toRingHom) (f₀ ^ (M + 1)) ∈
      holSub0 (U c.F.val.toRingHom).X (laU (U c.F.val.toRingHom) (fun _ => 2) n) := by
    have e : laU (U c.F.val.toRingHom) (fun _ => 2) n = laU (U c.F.val.toRingHom) 0 ((M + 1) * n₀) :=
      funext fun k' => by rw [laU_const, hn4]
    rw [e]
    exact ⟨((mem_cusp Xo c U 0 _ _).1 (hpow M)).2 _ hσ, rdU_mem_offZero _ _⟩
  have hspan := hL.onto _ hσ (fun _ => 2) n ⟨fun _ => antitone_const, hnev⟩ (fun _ _ _ => by norm_num) hnb hP
  obtain ⟨f, hf, hfy⟩ : ∃ f ∈ cusp Xo c U (fun _ => 2) n, rdU (U c.F.val.toRingHom) f k y ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    let ev : FDSec (U c.F.val.toRingHom).X →ₗ[ℂ] ℂ :=
      { toFun := fun P => P k y, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hle : Submodule.span ℂ (rdU (U c.F.val.toRingHom) '' (cusp Xo c U (fun _ => 2) n : Set (Rul Xo c))) ≤
        LinearMap.ker ev := by
      rw [Submodule.span_le]
      rintro _ ⟨f, hf, rfl⟩
      exact hcon f hf
    have h0 : ev (rdU (U c.F.val.toRingHom) (f₀ ^ (M + 1))) = 0 := hle hspan
    have h1 : ev (rdU (U c.F.val.toRingHom) (f₀ ^ (M + 1))) = (rdU (U c.F.val.toRingHom) f₀ k y) ^ (M + 1) := hrd M
    exact pow_ne_zero _ hne (h1.symm.trans h0)
  obtain ⟨g, hg, -⟩ := GlobalTheory.CompRestr.exists_cuspOn_restrict E H Dw l Xo c r U hL.unf Z (wtZ (fun _ => 2) n)
    ⟨f, by rw [cuspW_wtZ]; exact hf⟩
  refine ⟨fun _ => 2, n, ⟨fun _ => antitone_const, hnev⟩, fun _ _ _ => le_rfl, hnb, g, g.2, ?_⟩
  intro h0
  have e : rdU (U c.F.val.toRingHom) (g : Rul Xo c) k y = rdU (U c.F.val.toRingHom) f k y := by
    simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hy]
    rw [hg _ _ hlies]
  rw [h0, map_zero] at e
  exact hfy e.symm

end GlobalTheory.FlatCore.NonzeroCusp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroExpansionTermCompleteDVR
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ExpansionNonzero

theorem exists_term_ne_zero : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (U' : GlobalTheory.UU.PreU (maximalIdeal V) D'.toPre A' G') (U₀ : Unif (maximalIdeal V) D' A' G'), GlobalTheory.LN.Under U' U₀.toUnifPre → ∀ (σ' : U'.SecGT (𝟙_ _) 1) (f' : ∀ α, GlobalTheory.UU.SecBT D'.toPre (𝟙_ _) 1 α), U'.ExpT (𝟙_ _) 1 σ' f' → (∃ j, σ'.f j ≠ 0) → ∃ α j, (f' α).f j ≠ 0 := by
  intro V _ _ _ hV D' A' G' _ _ U' U₀ _ σ' f' hf ⟨j, hj⟩
  have := hV.1
  have := U'.semi.smooth
  have : IsReduced G'.left := isReduced_of_smooth_of_isReduced G'.hom
  have := FibreNonzero.isIso_snd_left G'
  have : IsReduced (𝟙_ _ ⊗ G').left := isReduced_of_isOpenImmersion (snd (𝟙_ _) G').left
  have h : (𝟙_ _ ⊗ G').left.basicOpen (σ'.f j) ≠ ⊥ := fun h => hj ((basicOpen_eq_bot_iff _).1 h)
  obtain ⟨y, hy⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 h
  refine GlobalTheory.SectionUnif.exists_term_ne_zero (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge U' 1 σ' f' hf y ?_
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hy⟩

end GlobalTheory.ExpansionNonzero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroSectionPreUniformisedCompleteNormal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.ModelSection
open GlobalTheory.UU GlobalTheory.TwistLoc

theorem isUnit_gc {K : Type} [Field K] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of K)) (z : Z) {c : K} (hc : c ≠ 0) :
    IsUnit (gc q z c) := by
  have h1 : gc q z (1 : K) = 1 := by
    unfold gc gs
    exact (dif_pos trivial).trans ((congrArg _ ((congrArg _ (map_one _)).trans (map_one _))).trans (map_one _))
  exact IsUnit.of_mul_eq_one (gc q z c⁻¹) (by rw [← gc_mul, mul_inv_cancel₀ hc, h1])

theorem exists_ne_zero {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) :
    ∃ σ : U.SecGT (𝟙_ _) 1, ∃ j, σ.f j ≠ 0 := by
  have h1 := GlobalTheory.abelianSchemeLaws_all.1
  have h2 := GlobalTheory.abelianSchemeLaws_all.2
  obtain ⟨v, hv⟩ := ThetaIntegral.exists_sec_ne_zero h1 h2 _ A (Kbar R) (jFK (R := R) (Kbar R))
  obtain ⟨n, c, a, ha⟩ := ExpTotal.exists_span h1.secBaseChange A 1 le_rfl (Kbar R) (jFK (R := R) (Kbar R))
    (SecM.toSec A.A v)
  choose d hd σ hσ using fun i => ExpTotal.exists_integral U 1 (a i)
  by_contra hn
  have hz : ∀ i j, (σ i).f j = 0 := fun i j => by
    by_contra h
    exact hn ⟨σ i, j, h⟩
  refine hv (Subtype.ext (funext fun j => ?_))
  refine sec_ext_val (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) (Kbar R)) A.A).left)
    (ε := fun _ => ((1 : ℕ) : ℤ)) A.isLB (s := SecM.toSec A.A v) (s' := SecM.toSec A.A 0) (fun z JA hJA => ?_) j
  obtain ⟨JG, hJG⟩ := exists_good_pt U.P.L.isLB z
  let y := (snd (TFK (R := R) (Kbar R)) A.A).left ≫ U.gen.inv.left
  let T : Over (Spec (CommRingCat.of R)) := Over.mk ((y ≫ pullback.fst G.hom (jK R)) ≫ G.hom)
  let x : T ⟶ G := Over.homMk (y ≫ pullback.fst G.hom (jK R)) rfl
  have hy : y ≫ U.gen.hom.left = 𝟙 _ ≫ (snd (TFK (R := R) (Kbar R)) A.A).left := by
    rw [Category.id_comp, Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.comp_id]
  refine (ha _ (𝟙 _) z JA hJA).trans (Eq.trans (Finset.sum_eq_zero fun i _ => ?_)
    (ThetaIntegral.sval_eq_zero _ (fun _ => rfl) _ _ _).symm)
  have e := hσ i _ y (lift (toUnit T) x).left (congrArg (fun q => q.left) (lift_snd (toUnit T) x)) z JA JG hJA hJG
  rw [ThetaIntegral.sval_eq_zero (σ i) (hz i)] at e
  have e₃ : y ≫ pullback.fst G.hom (jK R) ≫ G.hom = (y ≫ pullback.snd G.hom (jK R)) ≫ jK R :=
    (congrArg (y ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm
  have hu : IsUnit (gc (y ≫ pullback.fst G.hom (jK R) ≫ G.hom) z (d i)) := by
    have e₄ := (congrArg (gc · z (d i)) e₃).trans (ExpTotal.gc_map _ _ z _)
    exact e₄ ▸ isUnit_gc _ z ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 (hd i))
  have e₅ := hu.mul_right_eq_zero.1 e.symm
  rw [← Units.val_pow_eq_pow_val, Units.mul_right_eq_zero] at e₅
  have e₆ := (congrArg (fun q => sval (a i) q z JA) hy).symm.trans e₅
  exact (congrArg (_ * ·) e₆).trans (mul_zero _)

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), ∃ σ : U.SecGT (𝟙_ _) 1, ∃ j, σ.f j ≠ 0 :=
  fun _ _ _ _ _ _ _ _ _ _ U => exists_ne_zero U

end GlobalTheory.Mum.ModelSection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalFiniteModelOfExtension
section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.PerfdLat GlobalTheory.Published

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BplusDescent

section Field

variable {X : Scheme.{0}} [IsIntegral X] {L : Type} [Field L] (φ : X.presheaf.stalk (genericPoint X) ⟶ .of L)

abbrev fieldPt : Spec (.of L) ⟶ X := Spec.map φ ≫ X.fromSpecStalk (genericPoint X)

theorem fieldPt_apply (x : Spec (.of L)) : fieldPt φ x = genericPoint X := by
  letI : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
  have : Spec.map φ x = closedPoint (X.presheaf.stalk (genericPoint X)) :=
    Subsingleton.elim (α := PrimeSpectrum (X.presheaf.stalk (genericPoint X))) _ _
  change X.fromSpecStalk _ (Spec.map φ x) = _
  rw [this]
  exact Scheme.fromSpecStalk_closedPoint

theorem top_le_fieldPt {U : X.Opens} (hU : genericPoint X ∈ U) : ⊤ ≤ fieldPt φ ⁻¹ᵁ U := fun x _ => by
  change fieldPt φ x ∈ U
  rwa [fieldPt_apply]

theorem fieldPt_appLE {U : X.Opens} (hU : genericPoint X ∈ U) :
    (fieldPt φ).appLE U ⊤ (top_le_fieldPt φ hU) ≫ (Scheme.ΓSpecIso (.of L)).hom = X.presheaf.germ U _ hU ≫ φ := by
  have h1 : ⊤ ≤ X.fromSpecStalk (genericPoint X) ⁻¹ᵁ U := fun x _ => by
    letI : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
    have : x = closedPoint (X.presheaf.stalk (genericPoint X)) :=
      Subsingleton.elim (α := PrimeSpectrum (X.presheaf.stalk (genericPoint X))) _ _
    change X.fromSpecStalk _ x ∈ U
    rw [this, Scheme.fromSpecStalk_closedPoint]
    exact hU
  rw [← Scheme.Hom.appLE_comp_appLE (Spec.map φ) (X.fromSpecStalk (genericPoint X)) U ⊤ ⊤ h1 le_rfl]
  have h2 : (Spec.map φ).appLE ⊤ ⊤ le_rfl = (Spec.map φ).appTop := (Scheme.Hom.app_eq_appLE _).symm
  rw [h2, Category.assoc, Scheme.ΓSpecIso_naturality, Scheme.Hom.appLE, Scheme.fromSpecStalk_app hU]
  simp only [Category.assoc, ← Functor.map_comp_assoc]
  have h3 : ∀ i : (Opposite.op ⊤ : (Spec (X.presheaf.stalk (genericPoint X))).Opensᵒᵖ) ⟶ Opposite.op ⊤,
      (Spec (X.presheaf.stalk (genericPoint X))).presheaf.map i = 𝟙 _ := fun i => by
    rw [Subsingleton.elim i (𝟙 _)]; exact CategoryTheory.Functor.map_id _ _
  rw [h3]
  simp

def normFun {U : X.Opens} (hU : genericPoint X ∈ U) :
    Γ((fieldPt φ).normalization, (fieldPt φ).fromNormalization ⁻¹ᵁ U) ⟶ .of L :=
  (fieldPt φ).toNormalization.appLE _ ⊤ (by
    rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toNormalization_fromNormalization]; exact top_le_fieldPt φ hU) ≫
    (Scheme.ΓSpecIso (.of L)).hom

theorem app_normFun {U : X.Opens} (hU : genericPoint X ∈ U) :
    (fieldPt φ).fromNormalization.app U ≫ normFun φ hU = X.presheaf.germ U _ hU ≫ φ := by
  have key : ∀ (g : Spec (.of L) ⟶ X) (_ : g = fieldPt φ) (e : ⊤ ≤ g ⁻¹ᵁ U),
      g.appLE U ⊤ e = (fieldPt φ).appLE U ⊤ (top_le_fieldPt φ hU) := by
    rintro _ rfl _
    rfl
  rw [normFun, ← fieldPt_appLE, ← Category.assoc]
  congr 1
  exact (Scheme.Hom.comp_appLE _ _ _ _ _).symm.trans (key _ (fieldPt φ).toNormalization_fromNormalization (by
    rw [Scheme.Hom.toNormalization_fromNormalization]; exact top_le_fieldPt φ hU))

theorem normFun_spec {U : X.Opens} (hU : genericPoint X ∈ U) (hA : IsAffineOpen U) :
    Function.Injective (normFun φ hU).hom ∧
      ∀ x : L, x ∈ (normFun φ hU).hom.range ↔ (X.presheaf.germ U _ hU ≫ φ).hom.IsIntegralElem x := by
  let u := fieldPt φ
  letI := (u.app U).hom.toAlgebra
  let ε : Γ(Spec (.of L), u ⁻¹ᵁ U) ⟶ .of L :=
    (Spec (.of L)).presheaf.map (homOfLE (top_le_fieldPt φ hU)).op ≫ (Scheme.ΓSpecIso (.of L)).hom
  have hε : Function.Bijective ε.hom := by
    have : homOfLE (top_le_fieldPt φ hU) = eqToHom (top_le_iff.1 (top_le_fieldPt φ hU)).symm := Subsingleton.elim _ _
    haveI : IsIso ε := by
      simp only [ε, this]
      infer_instance
    exact ConcreteCategory.bijective_of_isIso ε
  have h1 : normFun φ hU = (u.normalizationObjIso hA).hom ≫
      CommRingCat.ofHom (integralClosure Γ(X, U) Γ(Spec (.of L), u ⁻¹ᵁ U)).val.toRingHom ≫ ε := by
    rw [← Category.assoc, u.normalizationObjIso_hom_val hA, normFun]
    simp only [ε]
    rw [Scheme.Hom.appLE_map_assoc]
  have h2 : X.presheaf.germ U _ hU ≫ φ = u.app U ≫ ε := by
    rw [← fieldPt_appLE, Scheme.Hom.appLE, Category.assoc]
  have hb := ConcreteCategory.bijective_of_isIso (u.normalizationObjIso hA).hom
  rw [h1, h2]
  refine ⟨hε.1.comp (Subtype.val_injective.comp hb.1), fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨p, hp, hp0⟩ := ((u.normalizationObjIso hA).hom y).2
    refine ⟨p, hp, ?_⟩
    have := congrArg ε.hom hp0
    rw [Polynomial.hom_eval₂, map_zero] at this
    exact this
  · rintro ⟨p, hp, hp0⟩
    obtain ⟨y, rfl⟩ := hε.2 x
    have hy : IsIntegral Γ(X, U) y := ⟨p, hp, hε.1 (by rw [Polynomial.hom_eval₂, map_zero]; exact hp0)⟩
    obtain ⟨z, hz⟩ := hb.2 ⟨y, hy⟩
    exact ⟨z, congrArg (fun w : integralClosure Γ(X, U) Γ(Spec (.of L), u ⁻¹ᵁ U) => ε.hom w.1) hz⟩

end Field

end GlobalTheory.BplusDescent

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisationModelFiniteExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem RatModel.stalkMap_pt_surjective {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (y : Sp Ω) : Function.Surjective (M.pt.stalkMap y).hom := by
  obtain rfl : y = closedPoint Ω := Subsingleton.elim _ _
  intro t
  obtain ⟨U, f, hU, hf⟩ := M.onto ((stalkClosedPointIso (CommRingCat.of Ω)).hom.hom t)
  have h : ⊤ ≤ M.pt ⁻¹ᵁ U := M.top_le_preimage_pt hU
  have e := GlobalTheory.Points.germ_stalkClosedPointTo_eq_valMap M.pt U h
  refine ⟨(M.Z.presheaf.germ U _ ((GlobalTheory.Points.le_preimage_iff M.pt U).1 h)).hom f, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (CommRingCat.of Ω)).hom).1
  have e2 := congrArg (fun φ => φ.hom f) e
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
  rw [GlobalTheory.Points.valF_eq_valR, GlobalTheory.Points.valR_eq _ _ h] at hf
  rw [← hf, ← e2]
  rfl

theorem stalkMap_spMap_finite {K L : Type} [Field K] [Field L] (φ : K →+* L) (hφ : φ.Finite) (y : Sp L) :
    ((spMap φ).stalkMap y).hom.Finite := by
  obtain rfl : y = closedPoint L := Subsingleton.elim _ _
  have e := Scheme.germ_stalkClosedPointTo_Spec (CommRingCat.ofHom φ)
  have hc : (Scheme.stalkClosedPointTo (spMap φ)).hom.Finite := by
    apply RingHom.Finite.of_comp_finite (f := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      (Spec (CommRingCat.of K)).presheaf.germ ⊤ _ trivial).hom)
    have : ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      (Spec (CommRingCat.of K)).presheaf.germ ⊤ _ trivial ≫ Scheme.stalkClosedPointTo (spMap φ)) =
        CommRingCat.ofHom φ := by
      rw [e, Iso.inv_hom_id_assoc]
    rw [← CommRingCat.hom_comp, Category.assoc, this]
    exact hφ
  have : (spMap φ).stalkMap (closedPoint L) =
      Scheme.stalkClosedPointTo (spMap φ) ≫ (stalkClosedPointIso (CommRingCat.of L)).inv := by
    rw [Scheme.stalkClosedPointTo, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [this, CommRingCat.hom_comp]
  exact RingHom.Finite.comp (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (CommRingCat.of L)).inv).2) hc

end GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem Setup.exists_model_of_finiteDimensional : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ}
    {Z : Scheme.{0}} {i : F.X ⟶ Z} (X₁ : Setup F W i) (o₂ Ω₂ : Type) [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂]
    [ArithBase o₂ Ω₂] [Algebra X₁.Ω₁ Ω₂] [FiniteDimensional X₁.Ω₁ Ω₂] (κ : X₁.o₁ →+* o₂), κ.Finite →
    (algebraMap o₂ Ω₂).comp κ = (algebraMap X₁.Ω₁ Ω₂).comp (algebraMap X₁.o₁ X₁.Ω₁) →
    ∃ (M : RatModel o₂ Ω₂) (q : M.Z ⟶ X₁.M.Z), GlobalTheory.IsNormalScheme M.Z ∧ IsFinite q ∧
      M.pt ≫ q = spMap (algebraMap X₁.Ω₁ Ω₂) ≫ X₁.M.pt := by
  intro g n F W Z i X₁ o₂ Ω₂ _ _ _ _ _ _ κ hκ hc
  haveI : IsDedekindDomain X₁.o₁ := ArithBase.ded (o := X₁.o₁) (Ω := X₁.Ω₁)
  have hp : (spMap (algebraMap X₁.Ω₁ Ω₂) ≫ X₁.M.pt) ≫ X₁.M.s = spMap ((algebraMap o₂ Ω₂).comp κ) := by
    rw [Category.assoc, X₁.M.pt_s, hc]
    exact (Spec.map_comp (CommRingCat.ofHom (algebraMap X₁.o₁ X₁.Ω₁))
      (CommRingCat.ofHom (algebraMap X₁.Ω₁ Ω₂))).symm
  have hst : ((spMap (algebraMap X₁.Ω₁ Ω₂) ≫ X₁.M.pt).stalkMap (genericPoint (Sp Ω₂))).hom.Finite := by
    rw [Scheme.Hom.stalkMap_comp]
    exact RingHom.Finite.comp (stalkMap_spMap_finite _ (RingHom.finite_algebraMap.2 inferInstance) _)
      (RingHom.Finite.of_surjective _ (RatModel.stalkMap_pt_surjective X₁.M _))
  obtain ⟨M, q, hn, hq, hpt⟩ := exists_ratModel_normalization X₁.o₁ o₂ Ω₂ κ hκ X₁.M.Z X₁.M.s X₁.M.lft X₁.M.qc
    X₁.M.sep _ hp hst
  exact ⟨M, q, GlobalTheory.IsNormalScheme.of_pred hn, hq, hpt⟩

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorOfOriginDerivationStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tangentVector_of_originDerivation : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (D : G.left.presheaf.stalk (origin G) → R), (∀ x y, D (x + y) = D x + D y) → (∀ x y, D (x * y) = evO G x * D y + evO G y * D x) → (∀ r, D (constO G r) = 0) → ∃ v : TanM (𝟙 (Sp R)) G, ∀ f, tanDer G v f = D f := by
  first | exact @GlobalTheory.CoordsOrigin.exists_tan_of_derivation | exact GlobalTheory.CoordsOrigin.exists_tan_of_derivation | (intros; apply GlobalTheory.CoordsOrigin.exists_tan_of_derivation <;> assumption)
end

