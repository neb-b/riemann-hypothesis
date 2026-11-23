module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0050
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGlobalGenerators
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBigThetaSysWithAction
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsWeilIsRoot
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsPrimitiveRootArcRoot
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0073

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BasisOriginValuesRegularAndUnit
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH

theorem ThetaSys.proj_column_mem_of_stable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)
    (A : Subalgebra o Ω) (E : Submodule A (S.J → Ω)) (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N)
    (h1 : ∀ i, Pi.single i (1 : Ω) ∈ E)
    (h2 : ∀ h ∈ T, ∀ v ∈ E, ((S.ρ h).map (algebraMap o Ω)).mulVec v ∈ E) (i : S.J) :
    (fun j => algebraMap o Ω (S.proj T c j i)) ∈ E := by
  haveI : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  haveI : Fintype T := Fintype.ofFinite _
  have e : (fun j => algebraMap o Ω (S.proj T c j i)) =
      ∑ t : T, (algebraMap o A (Ring.inverse (Nat.card T : o) * S.ζN ^ (-(c t)).val)) •
        ((S.ρ t).map (algebraMap o Ω)).mulVec (Pi.single i 1) := by
    funext j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ThetaSys.proj, finsum_eq_sum_of_fintype, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
      Finset.mul_sum, map_sum, Finset.sum_apply, Pi.smul_apply, Matrix.mulVec_single_one, Matrix.col_apply,
      Matrix.map_apply, algebraMap_smul, map_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Algebra.smul_def, map_mul, _root_.mul_assoc]
    rfl
  rw [e]
  exact E.sum_mem fun t _ => E.smul_mem _ (h2 t t.2 _ (h1 i))

theorem basis_origin_values_regular_and_unit :
    GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → S.IsEE M U₀ EE → ∀ (z : M.Z) (x₀ : S.Gam) (b : Matrix S.J S.J Ω), x₀ ∈ S.supI M z → EE.E z = Submodule.span (M.O z) (Set.range b) → (∀ i, (b i ⬝ᵥ S.ev 0) / S.th x₀ ∈ M.O z) ∧ ∃ i, (b i ⬝ᵥ S.ev 0) / S.th x₀ ≠ 0 ∧ ((b i ⬝ᵥ S.ev 0) / S.th x₀)⁻¹ ∈ M.O z := by
  intro h₁ h₂ h₃ h₄ h₅ o Ω _ _ _ _ S ρ M U₀ EE hO hEE z x₀ b hx₀ hb
  haveI : Algebra.FiniteType ℤ o := ArithBase.ft Ω
  haveI : CharZero Ω := ArithBase.char o
  have hL := classical_points_and_local_regularity o Ω M U₀ hO.normal
  have hT := exists_at_test_of_cen o Ω S M U₀ (_root_.GlobalTheory.ZH.hasTests_of_real h₁ h₂ h₃ h₄ h₅ o Ω S ρ).1 hO
  have hS := ThetaSys.mem_supI_iff_and_HH_eq_ker o Ω S M U₀ hO
  have hI := isoFree_TT_and_supI_specializes o Ω S M U₀ hO hL hT hS
  obtain ⟨hreg, i, hne, hinv⟩ :=
    coord_regular_and_unit o Ω S M U₀ EE hO hL hT hS hI hEE z x₀ hx₀ 0 (zero_mem _)
  obtain ⟨e1, e2, -⟩ := EE_contains_stable_weightZero o Ω S M U₀ EE hO hL hT hS hI hEE z
  have hA : ∀ i, (b i ⬝ᵥ S.ev 0) / S.th x₀ ∈ M.O z := fun i =>
    hreg _ (hb ▸ Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨hA, ?_⟩
  have hv := S.proj_column_mem_of_stable (M.O z) (EE.E z) (S.TT M z) 0 e1
    (fun h hh => e2 h ((hI.1 z).2 ▸ (hI.1 z).1.1 hh)) i
  have hu : IsUnit (⟨_, hreg _ hv⟩ : M.O z) :=
    (RatModel.isUnit_O_iff _).2 ⟨div_ne_zero hne hx₀.1, by simpa only [inv_div] using hinv⟩
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hb ▸ hv)
  have e : (⟨_, hreg _ hv⟩ : M.O z) = ∑ k, a k * ⟨_, hA k⟩ := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only [← ha, sum_dotProduct, Finset.sum_div, MulMemClass.coe_mul, Subalgebra.smul_def, smul_dotProduct,
      smul_eq_mul, mul_div_assoc]
  obtain ⟨k, -, hk⟩ := IsLocalRing.exists_of_isUnit_sum (e ▸ hu)
  exact ⟨k, (RatModel.isUnit_O_iff _).1 (isUnit_of_mul_isUnit_right hk)⟩

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianModelOfGeometricHalf
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH

theorem exists_model_semiAbelian_of_geo :
    GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → UTorsSt → ZHGeoSt → ZHSt := by
  intro hN hU hL hL2 hTors hGeo o Ω _ _ _ hb S ρ hBig J₀ _ t₀ ht hfin
  have hT : S.HasTests := (_root_.GlobalTheory.ZH.hasTests_of_real hN hU hL hL2 hTors o Ω S ρ).1
  obtain ⟨M, U₀, hA, -, hD⟩ := @GlobalTheory.ZH.exists_admissible_affine_model_dividing_tuple o Ω _ _ _ _ S J₀ _ t₀ ht hfin
  obtain ⟨EE, hEE, hE⟩ := @GlobalTheory.ZH.exists_isEE_of_adm o Ω _ _ _ _ S M U₀ hT hA
  have hO : S.Over₀ M U₀ := hA.1
  haveI := hb.ft
  haveI := hb.char
  have hll := @GlobalTheory.ZH.classical_points_and_local_regularity o Ω _ _ _ _ _ M U₀ hO.normal
  have hte := @GlobalTheory.ZH.exists_at_test_of_cen o Ω _ _ _ _ S M U₀ hT hO
  have hwt := @GlobalTheory.ZH.test_weights o Ω _ _ _ _ S
  have h0a := @GlobalTheory.ZH.ThetaSys.mem_supI_iff_and_HH_eq_ker o Ω _ _ _ _ S M U₀ hO
  have h0b := @GlobalTheory.ZH.isoFree_TT_and_supI_specializes o Ω _ _ _ _ S M U₀ hO hll hte h0a
  have h11 := @GlobalTheory.thetaSys_norm_FF_le_exp o Ω _ _ _ _ S hwt
  have h12 := @GlobalTheory.norm_val_FF_eq_of_div o Ω _ _ _ _ S M U₀ hO h0a h11 hte
  have hne := @GlobalTheory.ZH.FF_TT_ne_zero o Ω _ _ _ _ S M U₀ hO hll hte h0a h0b hwt
  have hsec := @GlobalTheory.ZH.DualSection.ff_div_th_mul_dotProduct_mem o Ω _ _ _ _ S M U₀ EE hA hll hte h0a h0b hwt h11 h12 hne hE
  obtain ⟨n, a, GG, hGG⟩ := @GlobalTheory.ZH.GlobalGen.exists_global_generators o Ω _ _ _ _ S M U₀ EE hA hll.2 h0b hne hE hsec
  exact ⟨M, U₀, EE, hO, hD, hEE, hGeo o Ω S ρ hBig M U₀ EE hO hEE ⟨n, a, fun k j => (GG k j : Ω), hGG⟩⟩

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUTestNontrivial
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DegenerateTest

section Pull

variable {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [GrpObj G'] [GrpObj G'']
  {L : LB G.left} {L' : LB G'.left} {L'' : LB G''.left}

end Pull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}


open IsLocalRing in
theorem exists_padic_embedding (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V]
    [IsAdicComplete (maximalIdeal V) V] (h : Finite (ResidueField V)) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (c : FractionRing V →+* PadicAlgCl p),
      ∀ x, ‖c x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V)) := by
  obtain ⟨p, _, K₀, e, e₀, -, he⟩ := completeDVR_eq_integralClosure_padicInt.1 V (FractionRing V) h
  refine ⟨p, inferInstance, (algebraMap K₀ (PadicAlgCl p)).comp e.toRingHom, fun x => ?_⟩
  refine (mem_integralClosure_padicInt_iff K₀ (e x)).symm.trans ⟨fun hx => ⟨e₀.symm ⟨e x, hx⟩, ?_⟩, ?_⟩
  · apply e.injective
    rw [he, e₀.apply_symm_apply]
  · rintro ⟨v, rfl⟩
    rw [he]
    exact (e₀ v).2

end GlobalTheory.DegenerateTest

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaDividedByConstantNonvanishingFibres
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.ZHPre
open GlobalTheory.Points
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
variable {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} (Q : ZHPre ρ M U₀)

theorem exists_thMul (h1 : Laws) (h2 : Laws2) (ov : S.Over₀ M U₀) (N : M.Z.Opens) (σ : Q.SecFam N)
    (hσ : σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N)) (hN : (N : Set M.Z).Nonempty) : ∃ c, Q.ThMul c N σ := by
  have hpt : Set.range M.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact (top_le_preimage_iff M.pt U₀).1 (M.top_le_preimage_pt ov.ne) ⟨w, rfl⟩
  have heta : IsOpenImmersion.lift U₀.ι M.pt hpt ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨s, hs⟩ := _root_.GlobalTheory.ZH.GenSec.exists_generic_section o Ω S ρ M U₀ Q N σ _ hσ hN heta
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.ZH.sec_generic_eq_mul_theta h1 h2 o Ω S ρ s
  refine ⟨c, ?_⟩
  intro K _ β g r jP jL hg hr hP hL _
  have hg' : g ≫ pullback.snd _ _ = spMap β ≫ IsOpenImmersion.lift U₀.ι M.pt hpt := by
    rw [← cancel_mono U₀.ι, Category.assoc, Category.assoc, heta]
    exact hg
  have hcomm : spMap β ≫ spMap S.R.val.toRingHom = (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ≫ ρ.P.A.hom := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hg', Category.assoc, Q.u₀_gen _ heta]
  let q : Sp K ⟶ ((Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ⊗ ρ.P.A).left :=
    pullback.lift (spMap β) (g ≫ pullback.fst _ _) hcomm
  have hq1 : q ≫ (fst (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left = spMap β :=
    pullback.lift_fst _ _ _
  have hq2 : q ≫ (snd (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left =
      g ≫ pullback.fst _ _ :=
    pullback.lift_snd _ _ _
  have e1 := hs K β q g jP jL hq1 hq2.symm hg' hP hL
  have e2 := hc K β q r jP hq1 (hr.trans hq2.symm) (by rw [hq2]; exact hP)
  simp only [Finset.univ_unique, Finset.sum_singleton, zpow_one]
  rw [← e2, e1]

theorem exists_good_label (h0 : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f)) (hs : GlobalTheory.Published.SemistableReductionSt) (hU : ThmUSt) (h1 : Laws) (h2 : Laws2)
    (hT : UTorsSt) (big : S.Big) (ov : S.Over₀ M U₀) (N : M.Z.Opens) (σ : Q.SecFam N)
    (hσ : σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N)) (hne : Q.FibNe N σ) (z : M.Z) (hz : IsClosed ({z} : Set M.Z))
    (hzN : z ∈ N) : ∃ a ∈ S.HH M z, ∀ (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.left) (w : W.toScheme),
      Q.ExtPt a W h → W.ι w = z → ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ W.toScheme) (j : Q.LOne.ι),
        Set.range x = {w} ∧ valF (x ≫ h) _ (σ j) ≠ 0 := by
  haveI : Algebra.FiniteType ℤ o := ArithBase.ft (Ω := Ω)
  haveI : CharZero Ω := ArithBase.char (o := o)
  obtain ⟨⟨p, hp, y, hy⟩, -⟩ := (classical_points_and_local_regularity o Ω M U₀ ov.normal).1 U₀ le_rfl ov.ne z hz
  obtain ⟨y₀, Fs, hAt, hint, hfac⟩ := _root_.GlobalTheory.ZH.ZHPre.exists_testFac_of_large o Ω S ρ M U₀ Q ov z p y hy
  obtain ⟨u, l, τ, hmatch, hFs⟩ := (_root_.GlobalTheory.ZH.hasTests_of_real hs hU h1 h2 hT o Ω S ρ).2 p y₀ Fs hint
  obtain ⟨jV, yV, yK, hTF⟩ := hfac u hFs
  obtain ⟨F, ψ, hTM⟩ := _root_.GlobalTheory.ZH.ZHPre.exists_testMap h0 o Ω S ρ M U₀ Q p y y₀ u jV yV yK hTF
  have hLB := _root_.GlobalTheory.ZH.TestBundle.lbIso_pull_unif o Ω S ρ M U₀ Q p y y₀ u jV yV yK hTF F ψ hTM
  have hyN : y (cPt p) ∈ N := by rw [hy.1]; exact hzN
  obtain ⟨t, ht, j, hj⟩ := GlobalTheory.T.exists_torsionPoint_specialFibre_section_ne_zero h1 h2 o Ω S ρ M U₀ Q big p y y₀ u jV yV yK hTF F ψ hTM hLB N σ hσ hne hyN
  have hn : IsUnit ((S.r * S.N : ℕ) : Γ(Sp u.V, ⊤)) := by
    have hv : IsUnit ((S.r * S.N : ℕ) : u.V) := by
      have he : ((S.r * S.N : ℕ) : o) * ↑(S.unit.unit⁻¹) = 1 := S.unit.mul_val_inv
      have hnorm : ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (u.yK (algebraMap o S.R ↑(S.unit.unit⁻¹)))‖ ≤ 1 := by
        have hf := RingHom.congr_fun u.fac (algebraMap o S.R ↑(S.unit.unit⁻¹))
        rw [RingHom.comp_apply] at hf
        rw [hf]
        exact hint _
      obtain ⟨v, hvE⟩ := (u.norm_le _).1 hnorm
      have hmul : ((S.r * S.N : ℕ) : u.V) * v = 1 := by
        apply IsFractionRing.injective u.V (FractionRing u.V)
        rw [map_mul, map_one, hvE, map_natCast, ← map_natCast u.yK, ← map_natCast (algebraMap o S.R),
          ← map_mul, ← map_mul, he, map_one, map_one]
      exact ⟨⟨_, v, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩
    simpa using hv.map (Scheme.ΓSpecIso (CommRingCat.of u.V)).inv.hom
  obtain ⟨b, hb, hbt⟩ := _root_.GlobalTheory.ZJ.exists_torsion_lift_of_residue p (Sp u.V) u.G u.semi (spMap jV) (S.r * S.N) hn t ht
  obtain ⟨a, hV, x, ⟨hV1, hx1, hx2, hx3⟩, hbV⟩ := _root_.GlobalTheory.ZH.torsion_integral_descends o Ω S ρ p y₀ u jV hTF.1 b hb
  have hker : a ∈ τ.yy.ker := by
    obtain ⟨e, -, he⟩ := hmatch
    have hl : l.yy a = 0 := (AddMonoidHom.mem_ker).1 ((l.ker_iff a).2 ⟨hV, x, hV1, hx1, hx2, hx3⟩)
    have h0' : τ.yy a = QuotientAddGroup.mk 0 := (he a 0).2 (by rw [hl, map_zero]; rfl)
    rw [AddMonoidHom.mem_ker, h0']
    rfl
  have hHH := (ThetaSys.mem_supI_iff_and_HH_eq_ker o Ω S M U₀ ov z p y y₀ τ hy hAt).2
  refine ⟨a, by rw [hHH]; exact hker, ?_⟩
  intro W h w hExt hwz
  haveI := isLocalHom_of_test u jV hTF.1
  have hzW : z ∈ W := by
    have hr : z ∈ Set.range W.ι := ⟨w, hwz⟩
    rwa [Scheme.Opens.range_ι] at hr
  have hVz : yV (IsLocalRing.closedPoint u.V) = z := by
    rw [← hy.1, ← hTF.2.1, Scheme.Hom.comp_apply]
    congr 1
    exact (IsLocalRing.comap_closedPoint jV).symm
  have hsp : ∀ v, yV v ⤳ z := fun v => hVz ▸ (IsLocalRing.specializes_closedPoint v).map yV.continuous
  have hrange : Set.range yV ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    exact (top_le_preimage_iff yV W).1 (top_le_preimage_of_specializes hsp hzW)
  have hyW : IsOpenImmersion.lift W.ι yV hrange ≫ W.ι = yV := IsOpenImmersion.lift_fac _ _ _
  have hcomp := _root_.GlobalTheory.ZH.extPt_comp_eq_integral_point o Ω S ρ M U₀ Q p y y₀ u jV yV yK hTF F ψ hTM a W h hExt hV x
    ⟨hV1, hx1, hx2, hx3⟩ _ hyW
  refine ⟨IsLocalRing.ResidueField (OO p), inferInstance,
    spMap (IsLocalRing.residue (OO p)) ≫ spMap jV ≫ IsOpenImmersion.lift W.ι yV hrange, j, ?_, ?_⟩
  · rw [Set.range_unique]
    congr 1
    apply W.ι.isOpenEmbedding.injective
    rw [hwz, ← Scheme.Hom.comp_apply]
    simp only [Category.assoc, hyW, hTF.2.1]
    rw [Scheme.Hom.comp_apply, ← hy.1]
    congr 1
    rw [show (default : Sp (IsLocalRing.ResidueField (OO p))) = IsLocalRing.closedPoint _ from
      Subsingleton.elim _ _]
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p))
  · have hx : (spMap (IsLocalRing.residue (OO p)) ≫ spMap jV ≫ IsOpenImmersion.lift W.ι yV hrange) ≫ h =
        t.left ≫ F := by
      rw [Category.assoc, Category.assoc, hcomp, ← Category.assoc (spMap jV), hbV, ← Category.assoc, hbt]
    rw [hx]
    exact hj

theorem exists_theta_div : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Big → S.Over₀ M U₀ → Q.Sec → Q.LocTheta → ∀ (W : M.Z.Opens) (x₀ : S.Gam), (∀ z ∈ W, x₀ ∈ S.supI M z) → ∃ σ ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => 1)) (Q.G.hom ⁻¹ᵁ W), GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w 1 (fun _ : Unit => ρ.th₁) (fun _ => (S.th x₀)⁻¹) _ σ ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ M.Z), Set.range x ⊆ W → ∃ (g : Sp K ⟶ Q.G.left) (j : _), g ≫ Q.G.hom = x ∧ valF g _ (σ j) ≠ 0 := by
  intro h0 hs hU h1 h2 hT o Ω _ _ _ _ S ρ M U₀ Q big ov hSec hLoc W x₀ hx₀
  refine _root_.GlobalTheory.ZH.GlueTheta.exists_glue o Ω S ρ M U₀ Q (S.th x₀)⁻¹
    (fun N N' σ σ' hσ hσ' j O h h' => _root_.GlobalTheory.ZH.ZHPre.resG_eq_of_thMul o Ω S ρ M U₀ Q ov N N' σ σ' _ hσ hσ' j O h h') W ?_
  intro z hzW
  haveI : Algebra.FiniteType ℤ o := ArithBase.ft (Ω := Ω)
  haveI : CharZero Ω := ArithBase.char (o := o)
  haveI : JacobsonSpace M.Z := (classical_points_and_local_regularity o Ω M U₀ ov.normal).2
  obtain ⟨N₀, σ₀, hzN₀, hσ₀, hne₀⟩ := _root_.GlobalTheory.ZH.LocThetaConv.exists_secFam_fibNe o Ω S ρ M U₀ Q hLoc z
  obtain ⟨c₀, hc₀⟩ := Q.exists_thMul h1 h2 ov N₀ σ₀ hσ₀ ⟨z, hzN₀⟩
  have hext : ∀ (z' : M.Z), ∀ b ∈ S.HH M z', ∃ (Wb : M.Z.Opens) (hb : Wb.toScheme ⟶ Q.G.left) (wb : Wb.toScheme),
      Q.ExtPt b Wb hb ∧ Wb.ι wb = z' ∧ Q.FrameUnit b Wb hb wb := by
    intro z' b hb
    obtain ⟨Wb, hb', hz'Wb, hb1, hb2⟩ := hSec z' b hb
    obtain ⟨wb, hwb⟩ : z' ∈ Set.range Wb.ι := by rw [Scheme.Opens.range_ι]; exact hz'Wb
    have hE : Q.ExtPt b Wb hb' := ⟨hb1, hb2⟩
    exact ⟨Wb, hb', wb, hE, hwb, GlobalTheory.T.torsionFrame_isUnit_along_section o Ω S ρ M U₀ Q ov
      (fun α hα hn => GlobalTheory.T.exists_generator_normalised_mulByN_iso o Ω S ρ M U₀ Q ov (S.r * S.N) α hα hn) b Wb hb' wb hE⟩
  have hcl : ∀ z' : M.Z, IsClosed ({z'} : Set M.Z) → z' ∈ N₀ → z' ∈ W →
      c₀ * S.th x₀ ≠ 0 ∧ c₀ * S.th x₀ ∈ M.O z' ∧ (c₀ * S.th x₀)⁻¹ ∈ M.O z' := by
    intro z' hz' hz'N hz'W
    obtain ⟨a, ha, hgood⟩ := Q.exists_good_label h0 hs hU h1 h2 hT big ov N₀ σ₀ hσ₀ hne₀ z' hz' hz'N
    obtain ⟨Wa, ha', wa, hEa, hwa, hFa⟩ := hext z' a ha
    have hwaN : Wa.ι wa ∈ N₀ := by rw [hwa]; exact hz'N
    have hxa := _root_.GlobalTheory.ZH.mul_theta_regular_and_unit o Ω S ρ M U₀ Q ov N₀ σ₀ c₀ hσ₀ hc₀ a Wa ha' wa hEa hFa hwaN
    obtain ⟨K, _, x, j, hx, hv⟩ := hgood Wa ha' wa hEa hwa
    obtain ⟨hne, hinv⟩ := hxa.2 K x j hx hv
    have hx₀' : x₀ ∈ S.supI M z' := hx₀ z' hz'W
    obtain ⟨Wb, hb', wb, hEb, hwb, hFb⟩ := hext z' x₀ (AddSubgroup.subset_closure hx₀')
    have hwbN : Wb.ι wb ∈ N₀ := by rw [hwb]; exact hz'N
    have hxb := (_root_.GlobalTheory.ZH.mul_theta_regular_and_unit o Ω S ρ M U₀ Q ov N₀ σ₀ c₀ hσ₀ hc₀ x₀ Wb hb' wb hEb hFb hwbN).1
    rw [hwa] at hinv
    rw [hwb] at hxb
    have hdiv : M.Div S.th x₀ z' := hx₀'
    obtain ⟨hth, hdivs⟩ := hdiv
    have hc : c₀ ≠ 0 := left_ne_zero_of_mul hne
    have hta : S.th a ≠ 0 := right_ne_zero_of_mul hne
    refine ⟨mul_ne_zero hc hth, hxb, ?_⟩
    have heq : (c₀ * S.th x₀)⁻¹ = S.th a / S.th x₀ * (c₀ * S.th a)⁻¹ := by
      field_simp
    rw [heq]
    exact Subalgebra.mul_mem _ (hdivs a) hinv
  have hopen : IsOpen {z' : M.Z | c₀ * S.th x₀ ∈ M.O z' ∧ (c₀ * S.th x₀)⁻¹ ∈ M.O z'} :=
    (M.isOpen_setOf_mem_O _).inter (M.isOpen_setOf_mem_O _)
  have hall : ∀ z' : M.Z, z' ∈ N₀ → z' ∈ W → c₀ * S.th x₀ ∈ M.O z' ∧ (c₀ * S.th x₀)⁻¹ ∈ M.O z' := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨z₂, hz₂N, hz₂W, hbad⟩ := hcon
    have hZ : (((N₀ : Set M.Z) ∩ (W : Set M.Z)) ∩
        {z' : M.Z | c₀ * S.th x₀ ∈ M.O z' ∧ (c₀ * S.th x₀)⁻¹ ∈ M.O z'}ᶜ).Nonempty :=
      ⟨z₂, ⟨hz₂N, hz₂W⟩, fun h => hbad h.1 h.2⟩
    obtain ⟨z', ⟨⟨hz'N, hz'W⟩, hz'bad⟩, hz'c⟩ := nonempty_inter_closedPoints hZ
      ⟨_, _, N₀.isOpen.inter W.isOpen, hopen.isClosed_compl, rfl⟩
    obtain ⟨-, h1', h2'⟩ := hcl z' hz'c hz'N hz'W
    exact hz'bad ⟨h1', h2'⟩
  obtain ⟨z₁, ⟨hz₁N, hz₁W⟩, hz₁c⟩ := nonempty_inter_closedPoints
    (⟨z, hzN₀, hzW⟩ : ((N₀ : Set M.Z) ∩ (W : Set M.Z)).Nonempty) (N₀.isOpen.inter W.isOpen).isLocallyClosed
  have hf0 : c₀ * S.th x₀ ≠ 0 := (hcl z₁ hz₁c hz₁N hz₁W).1
  obtain ⟨σ', hσ', hth', hne'⟩ := _root_.GlobalTheory.ZH.ZHPre.exists_scale_section o Ω S ρ M U₀ Q N₀ (N₀ ⊓ W) σ₀ c₀ (c₀ * S.th x₀)⁻¹ inf_le_left
    (fun z' hz' => by
      obtain ⟨hz'N, hz'W⟩ := hz'
      obtain ⟨h1', h2'⟩ := hall z' hz'N hz'W
      exact ⟨inv_ne_zero hf0, h2', by rw [inv_inv]; exact h1'⟩) hσ₀ hc₀ hne₀
  have hc₀0 : c₀ ≠ 0 := left_ne_zero_of_mul hf0
  have hth0 : S.th x₀ ≠ 0 := right_ne_zero_of_mul hf0
  have hfc : (c₀ * S.th x₀)⁻¹ * c₀ = (S.th x₀)⁻¹ := by
    field_simp
  rw [hfc] at hth'
  exact ⟨N₀ ⊓ W, σ', ⟨hzN₀, hzW⟩, inf_le_right, hσ', hth', hne'⟩

end GlobalTheory.ZH.ZHPre
end
end

