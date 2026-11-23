module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0118
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2405
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2371
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2224
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2383
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0659
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2083
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1036
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1894
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicSumSectionsPullbacksValueAbelianPart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange

noncomputable section
namespace GlobalTheory.SecAdicSumAny

open GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw GlobalTheory.SecAdicSum

theorem sumF_of_sum_on_thickenings_any : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (X : Scheme.{0}) (N : LB X), N.IsLB → ∀ (K : Type) [Fintype K] (φ : K → (D.toPre.P.A.left ⟶ X)) (ε : K → ℤ) (Ix : Type) (n : Ix → LB.Sec (LB.LinComb N φ ε)) (n₀ : LB.Sec (LB.LinComb N φ ε)), (∀ e : ℕ, ∃ S : Finset Ix, ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e D.toPre.P.A).left) (z : Z) (J), Good N z J → (∀ i ∉ S, sval (n i) (r ≫ (D.toPre.prBe I e).left) z J = 0) ∧ sval n₀ (r ≫ (D.toPre.prBe I e).left) z J = ∑ i ∈ S, sval (n i) (r ≫ (D.toPre.prBe I e).left) z J) → ∀ (b : TF (R := R) F ⟶ D.toPre.P.A) (τ : LB.Gen (LB.LinComb N (fun i => b.left ≫ φ i) ε)), τ.IsGen → ∀ (x : Ix → F) (x₀ : F), (∀ z J, Good N z J → (∀ i, sval (n i) b.left z J = cst F z (x i) * (val τ (𝟙 _) z J).val) ∧ sval n₀ b.left z J = cst F z x₀ * (val τ (𝟙 _) z J).val) → SumF I F x x₀ := by
  intro R _ _ _ I hR D F _ _ _ X N hL K _ φ ε Ix n n₀ hS b τ _ x x₀ hx
  have := hR.1
  have := D.toPre.P.isAb.smooth
  obtain ⟨P⟩ := _root_.GlobalTheory.AbLaw.nonempty_perf_of_noetherian R _ D.toPre.P.A.hom inferInstance
    (GlobalTheory.AbProj.isProjBy_of_isPullback D.toPre.P (IsPullback.id_horiz _)) _ (LB.isLB_linComb hL φ ε)
  choose v hv hv' using fun i => exists_vec P (n i)
  obtain ⟨v₀, hv₀, hv₀'⟩ := exists_vec P n₀
  obtain ⟨z⟩ := CoefBasic.exists_pt (R := R) (F := F)
  obtain ⟨J, hJ⟩ := CoefBasic.exists_good' hL z
  obtain ⟨i₀, hi₀⟩ := exists_mem P (b.left z)
  let t := trF φ ε b.left z (P.ch i₀) (fun k => J (b.left ≫ φ k)) * val τ (𝟙 _) z J
  choose y hy using fun k => CoefBasic.cstH_surj z (gs b.left z _ (P.u k i₀) * (t⁻¹).val)
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  let ev : (Fin P.a → R) →ₗ[R] F := Fintype.linearCombination R y
  have key : ∀ (s : LB.Sec (LB.LinComb N φ ε)) (w : Fin P.a → R) (c : F),
      (∀ i, AbLaw.rs _ (P.le i) (s.f (P.ch i)) = loc₀ P w i) →
      sval s b.left z J = UT.cst F z c * (val τ (𝟙 _) z J).val → c = ev w := fun s w c h₁ h₂ => by
    have e := gs_loc₀ P h₁ b.left z hi₀ hJ
    rw [h₂, mul_left_comm, ← Units.val_mul, CoefBasic.cst_eq] at e
    refine CoefBasic.cstH_inj (R := R) z ?_
    have e' : CoefBasic.cstH z c = gs b.left z _ (loc₀ P w i₀) * (t⁻¹).val :=
      (Units.eq_mul_inv_iff_mul_eq t).2 e.symm
    have hs : ∀ a : Fin P.a → Γ(D.toPre.P.A.left, P.W i₀), gs b.left z _ (∑ k, a k) = ∑ k, gs b.left z _ (a k) :=
      fun a => by simp only [gs_eq b.left z _ hi₀, map_sum]
    rw [e', loc₀, hs, Finset.sum_mul]
    refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (map_sum _ (fun k => w k • y k) _).symm
    rw [gs_mul b.left z _ hi₀, gs_cst_point b z _ hi₀, _root_.mul_assoc, ← hy, ← map_mul, ← Algebra.smul_def]
    rfl
  obtain rfl : x = fun i => ev (v i) := funext fun i => key _ _ _ (hv' i) ((hx z J hJ).1 i)
  obtain rfl : x₀ = ev v₀ := key _ _ _ hv₀' (hx z J hJ).2
  refine sumI_of_ker I P.D₀ ev v v₀ hv hv₀ fun e => ?_
  obtain ⟨S, hS⟩ := hS e
  refine ⟨S, fun T hT k => Ideal.Quotient.eq_zero_iff_mem.1 (congrFun (comp_eq_zero P
    (IsPullback.of_hasPullback D.toPre.P.A.hom (thick R I e)) (v₀ - ∑ i ∈ T, v i) ?_ fun i p hp => ?_) k)⟩
  · simp only [Matrix.mulVec_sub, Matrix.mulVec_sum, hv, hv₀, Finset.sum_const_zero, sub_zero]
  · obtain ⟨J', hJ'⟩ := CoefBasic.exists_good' hL p
    obtain ⟨h₁, h₂⟩ := hS _ (𝟙 _) p J' hJ'
    rw [Category.id_comp] at h₁ h₂
    have h₃ := h₂.trans (Finset.sum_subset hT fun j _ hj => h₁ j hj)
    have e₀ := gs_loc₀ P hv₀' _ p hp hJ'
    have e₁ := fun j => gs_loc₀ P (hv' j) _ p hp hJ'
    rw [gs_eq _ p _ hp] at e₀
    simp only [gs_eq _ p _ hp] at e₁
    set_option synthInstance.maxHeartbeats 100000 in
      rw [loc₀_sub_sum, gs_eq _ p _ hp, map_sub, map_sub, map_sum, map_sum, e₀, Finset.sum_congr rfl fun j _ => e₁ j,
      ← Finset.mul_sum]
    exact sub_eq_zero.2 (congrArg _ h₃)

end GlobalTheory.SecAdicSumAny
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointUniformisationEndomorphismLiesOverAdjoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Mum.AdjEnd

theorem rosati_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (f g g' : D.toPre.P.A ⟶ D.toPre.P.A), IsMonHom f → IsMonHom g → IsMonHom g' → RosatiAdj D.toPre.P.A D.toPre.P.L f g → RosatiAdj D.toPre.P.A D.toPre.P.L f g' → g = g' := _root_.GlobalTheory.Mum.rosatiAdj_unique

theorem keepsIota : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ E : EndU U.toUnifPre, E.aB = a → E.h = h' → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (y : D.toPre.X) (g g' : GtPtF D.toPre F), GtPtF.IsIota y g → E.Act g g' → GtPtF.IsIota (h y) g' := _root_.GlobalTheory.Mum.KeepsIota.main

theorem aB_h_eq (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : AdmBase R (maximalIdeal R))
    (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (U : UnifPre (maximalIdeal R) D A G) (E : EndU U) (a : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X)
    (ha : IsMonHom a) (hE : FormalEnd U a h' fun e => (Over.pullback (thick R (maximalIdeal R) e)).map E.aG) :
    E.aB = a ∧ E.h = h' := by
  have := E.homG
  have := E.homB
  have hu := fun e => gtCoord_end_torus_abelian GlobalTheory.firstFiveLaws R (maximalIdeal R) hR D.toPre e G (U.gt e)
    ((Over.pullback (thick R (maximalIdeal R) e)).map E.aG) inferInstance
  have hm : ∀ e, (Over.pullback (thick R (maximalIdeal R) e)).map E.aB =
      (Over.pullback (thick R (maximalIdeal R) e)).map a := fun e =>
    (hu e).2.unique ⟨inferInstance, (E.q_lin e)⟩ ⟨inferInstance, hE.2.2.1 e⟩
  have := D.toPre.P.isAb.proper
  haveI : IsNoetherianRing R := hR.1
  refine ⟨GlobalTheory.hom_eq_of_thickenings_of_isProper R (maximalIdeal R) (IsLocalRing.maximalIdeal_le_jacobson _)
    D.toPre.P.A D.toPre.P.A _ _ fun e => ?_, ?_⟩
  · have k := congrArg (fun m => m.left ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) (hm e)
    simp only [GlobalTheory.EndData.map_fst] at k
    exact k
  · obtain ⟨t, ht, hi⟩ := hE.2.2.2 0
    obtain ⟨t', ht', hi'⟩ := E.i_lin 0
    exact (hu 0).1.unique ⟨t', ht', hi'⟩ ⟨t, ht, hi⟩

theorem linEnd_of_adjoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ g g' : G ⟶ G, LinEnd U.toUnifPre a h' g → IsMonHom g' → LBIso (cubeLB G ![fst G G ≫ g, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ g'] U.LG.L) → LinEnd U.toUnifPre a' h g' := by
  intro R _ _ _ hB D A G _ _ hG U a a' h h' hD g g' hg hg' hL
  obtain ⟨hadm, hc⟩ := hB
  have hF := GlobalTheory.UT.functorial_of_unif R (maximalIdeal R) hadm D A G hG U
  have := U.gen_hom
  have := hg.1
  have ex : ∀ b : G ⟶ G, IsMonHom b → ∃ E : EndU U.toUnifPre, E.aG = b := fun b hb => by
    obtain ⟨E, e1, -⟩ := hF.1 b (U.gen.inv ≫ (Over.pullback (jK R)).map b ≫ U.gen.hom) hb inferInstance (by simp)
    exact ⟨E, e1⟩
  obtain ⟨E, rfl⟩ := ex g hg.1
  obtain ⟨E', rfl⟩ := ex g' hg'
  obtain ⟨⟨-, hRB, -, -⟩, hFp⟩ := hF.2 E E' hL
  obtain ⟨haB, hh⟩ := aB_h_eq R hadm D A G U.toUnifPre E a h' hD.1 hg.2
  have ha' : E'.aB = a' := rosati_unique R ⟨hadm, hc⟩ D a E'.aB a' hD.1 E'.homB hD.2.1 (haB ▸ hRB) hD.2.2.1
  have hh2 : E'.h = h := by
    ext y
    let F := AlgebraicClosure (FractionRing R)
    obtain ⟨g₀, hg₀⟩ := GlobalTheory.TorusExt.exists_iota (F := F) D.tau_bimult y
    obtain ⟨g₁, hg₁, -⟩ := ((hFp F).1 g₀)
    exact GlobalTheory.IotaInj.main GlobalTheory.firstFiveLaws R (maximalIdeal R) hadm D F _ _ g₁ ((hFp F).2.1 y g₀ g₁ hg₀ hg₁)
      (keepsIota R ⟨hadm, hc⟩ D A G hG U a a' h h' hD E haB hh F y g₀ g₁ hg₀ hg₁)
  have := E'.homG
  exact ⟨inferInstance, fun e => inferInstance, fun e => GlobalTheory.Mum.EndModel.thickMap_map _ e,
    fun e => ha' ▸ E'.q_lin e, fun e => hh2 ▸ E'.i_lin e⟩

end GlobalTheory.Mum.AdjEnd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjunctionKltOfKltAlongResidueSubring
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

theorem adjKlt_of_klt_restrict : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (n : ℕ) (T : Subring L) (S : Place cL) (hS : S.Contains T) (ψ : S.ring →+* K) (f : S.ring) (w : Fin n → S.ring) (θ : S.ring →₀ ℚ) (R : Subring K), Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) → Irreducible f → TrBasis cK (fun i => ψ (w i)) → (∀ g ∈ θ.support, ψ g ≠ 0) → (∀ a ∈ R, ∃ t : T, ψ ⟨t, hS t t.2⟩ = a) → Klt cK n R (dForm cK (fun i => ψ (w i))) (Finsupp.mapDomain ψ θ) → AdjKlt cL (n + 1) T S (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L)) (Finsupp.mapDomain (fun g : S.ring => (g : L)) θ + Finsupp.single (f : L) 1) := by
  intro L K _ _ cL cK n T S hS ψ f w θ R hψ hc hf hw hθ hR hK
  refine ⟨?_, ?_, ?_⟩
  · have htr := (trBasis_uniformiser_cons cL cK n S ψ f w hψ hc hf hw).1
    have hfree := (formOrd_api cL (n + 1) _ htr).1
    exact fun h0 => one_ne_zero (hfree.1 (a₁ := 1) (a₂ := 0) (by simp [h0]))
  · have hf0 : (0 : L) ≠ (f : L) := fun h => hf.ne_zero (Subtype.ext h.symm)
    have hθ0 : θ 0 = 0 := by
      by_contra h
      exact hθ 0 (Finsupp.mem_support_iff.2 h) (map_zero ψ)
    have h1 : Finsupp.mapDomain (fun g : S.ring => (g : L)) θ ((0 : S.ring) : L) = θ 0 :=
      Finsupp.mapDomain_apply_of_injective Subtype.val_injective θ 0
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hf0, add_zero]
    exact h1.trans hθ0
  intro Q hQ t u E hTQ hspan hdim hSQ hEQ hSt hEu hP
  obtain ⟨F, hF, hdisc⟩ := GlobalTheory.AdjCodimTwo.disc_residue_eq cL cK n Q hQ t u S E ψ f w θ hspan hdim
    hSQ hEQ hSt hEu hψ hc hf hw hθ hP
  rw [← hdisc]
  apply hK.lt_disc
  intro a ha
  obtain ⟨x, hx⟩ := hR a ha
  exact (hF a).2 ⟨⟨x, hS x x.2⟩, hTQ x.2, hx⟩

end GlobalTheory.FieldPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomEvalCompEqEvAMap
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem algHom_eval_comp_eq_evA_map :
    ∀ (p m : ℕ) (O A k A' σ : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing k]
      [CommRing A'] [Algebra k A'] [Fintype σ] (x : σ → A) (E : MvPowerSeries σ O →ₐ[O] A),
      IsEval p x E → ∀ (r : O →+* k) (g : A →+* A'),
      (∀ c, g (algebraMap O A c) = algebraMap k A' (r c)) → (p : A') ^ m = 0 →
      ∀ hx : ∀ i, IsNilpotent (g (x i)), ∀ f,
        g (E f) = evA k (fun i => g (x i)) hx (map r f) := by
  intro p m O A k A' σ _ _ _ _ _ _ _ x E hE r g hg _ hx f
  letI : Algebra O A' := ((algebraMap k A').comp r).toAlgebra
  have hs : HasSubst (fun i => (C (g (x i)) : MvPowerSeries Empty A')) :=
    hasSubst_of_constantCoeff_nilpotent fun i => by simpa using hx i
  have hevX : ∀ i, evA k (fun i => g (x i)) hx (X i) = g (x i) := by
    intro i
    simp [evA, coe_substAlgHom, subst_X hs]
  let φ : MvPowerSeries σ O →ₐ[O] A' :=
    { g.comp E.toRingHom with
      commutes' := fun c => by
        show g (E (algebraMap O _ c)) = (algebraMap k A').comp r c
        rw [AlgHom.commutes, hg]; rfl }
  let ψ : MvPowerSeries σ O →ₐ[O] A' :=
    { (evA k (fun i => g (x i)) hx).toRingHom.comp (map r) with
      commutes' := fun c => by
        show evA k (fun i => g (x i)) hx (map r (algebraMap O _ c)) = (algebraMap k A').comp r c
        have hm : map r (algebraMap O (MvPowerSeries σ O) c) =
            algebraMap k (MvPowerSeries σ k) (r c) := by
          simp [MvPowerSeries.algebraMap_apply, map_C]
        rw [hm, AlgHom.commutes]; rfl }
  have hφX : ∀ i, φ (X i) = g (x i) := fun i => by
    show g (E (X i)) = _
    rw [hE.1 i]
  have hψX : ∀ i, ψ (X i) = g (x i) := fun i => by
    show evA k (fun i => g (x i)) hx (map r (X i)) = _
    rw [map_X, hevX]
  have key := GlobalTheory.mvPowerSeries_algHom_ext_of_isNilpotent O σ A' φ ψ
    (fun i => by rw [hφX]; exact hx i) (fun i => by rw [hφX, hψX])
  exact DFunLike.congr_fun key f

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertFrameLogDerivativeQuasiPeriodic
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.CechPer.LogDer

open Filter Topology

theorem logDer_mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f c d : E → ℂ} {z : E}
    (h : f =ᶠ[𝓝 z] fun w => c w * d w) (hc : DifferentiableAt ℂ c z) (hd : DifferentiableAt ℂ d z)
    (hc0 : c z ≠ 0) (hd0 : d z ≠ 0) (v : E) :
    fderiv ℂ f z v / f z = fderiv ℂ c z v / c z + fderiv ℂ d z v / d z := by
  have hm : HasFDerivAt (fun w => c w * d w) (c z • fderiv ℂ d z + d z • fderiv ℂ c z) z :=
    hc.hasFDerivAt.mul hd.hasFDerivAt
  rw [h.fderiv_eq, hm.fderiv, h.eq_of_nhds]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem hasFDerivAt_factor {g : ℕ} (a b c : ℂ) (m z : Fin g → ℂ) :
    ∃ D : (Fin g → ℂ) →L[ℂ] ℂ, HasFDerivAt (fun w : Fin g → ℂ => a * Complex.exp (b * (w ⬝ᵥ m) + c)) D z ∧
      ∀ v, D v = a * Complex.exp (b * (z ⬝ᵥ m) + c) * (b * (v ⬝ᵥ m)) := by

  let ℓ : (Fin g → ℂ) →L[ℂ] ℂ := ∑ i, m i • ContinuousLinearMap.proj i
  have hℓ : ∀ w, ℓ w = w ⬝ᵥ m := by
    intro w
    simp [ℓ, dotProduct, mul_comm]
  have H := (((ℓ.hasFDerivAt (x := z)).const_mul b).add_const c).cexp.const_mul a
  have hfun : (fun w : Fin g → ℂ => a * Complex.exp (b * (w ⬝ᵥ m) + c)) = fun w => a * Complex.exp (b * ℓ w + c) := by
    funext w
    rw [hℓ]
  refine ⟨a • (Complex.exp (b * ℓ z + c) • (b • ℓ)), ?_, ?_⟩
  · rw [hfun]
    exact H
  · intro v
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, hℓ]
    ring

theorem main : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → L.IsLB → ∀ (H : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), u.IsAH H χ → ∀ v : Fin g → ℂ, (∀ i, DifferentiableOn ℂ (fun z => fderiv ℂ (u.fr i) z v / u.fr i z) (pre u.ex (L.U i))) ∧ (∀ i j, IsReg u.ex (L.U i ⊓ L.U j) ((fun z => fderiv ℂ (u.fr i) z v / u.fr i z) - fun z => fderiv ℂ (u.fr j) z v / u.fr j z)) ∧ ∀ i (l : u.Λ), ∀ z ∈ pre u.ex (L.U i), fderiv ℂ (u.fr i) (z + l) v / u.fr i (z + l) = fderiv ℂ (u.fr i) z v / u.fr i z - Real.pi * (v ⬝ᵥ H.mulVec (star (l : Fin g → ℂ))) := by
  intro A _ g L u hA _ H χ hAH v
  obtain ⟨hopen, hdval, hshift, -, hinf, -, -, -, -, hev, -, -⟩ := _root_.GlobalTheory.CechPer.pre_val_rules A g L u

  have hfrd : ∀ i, DifferentiableOn ℂ (u.fr i) (pre u.ex (L.U i)) := u.10
  have hfr0 : ∀ i, ∀ z ∈ pre u.ex (L.U i), u.fr i z ≠ 0 := fun i z hz => u.11 i z hz
  have hfrg : ∀ i j, ∀ z ∈ pre u.ex (L.U i ⊓ L.U j),
      u.fr i z = val u.ex (L.U i ⊓ L.U j) (L.g i j : Γ(A.left, L.U i ⊓ L.U j)) z * u.fr j z :=
    fun i j z hz => u.12 i j z hz
  have hfra : ∀ i, ∀ z ∈ pre u.ex (L.U i), DifferentiableAt ℂ (u.fr i) z :=
    fun i z hz => (hfrd i).differentiableAt ((hopen _).mem_nhds hz)
  refine ⟨?_, ?_, ?_⟩
  ·
    intro i z hz

    let e : ReciprocityTheory.L2DbarEstimates.V g ≃L[ℂ] (Fin g → ℂ) := EuclideanSpace.equiv (Fin g) ℂ
    have hpre : IsOpen (e ⁻¹' pre u.ex (L.U i)) := (hopen _).preimage e.continuous
    have hsm := ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn g (u.fr i ∘ e) _ hpre
      ((hfrd i).comp e.differentiableOn (fun y hy => hy))
    have hsm' : ContDiffOn ℂ (↑(⊤ : ℕ∞)) (u.fr i) (pre u.ex (L.U i)) := by
      have h2 := hsm.comp e.symm.contDiff.contDiffOn (fun y hy => by simpa using hy)
      have h3 : (u.fr i ∘ e) ∘ e.symm = u.fr i := by
        funext y
        simp
      rwa [h3] at h2
    have hca := (hsm'.contDiffAt ((hopen _).mem_nhds hz)).fderiv_right (m := 1)
      (by first | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))
    have h1 : DifferentiableAt ℂ (fun w => fderiv ℂ (u.fr i) w v) z :=
      (hca.differentiableAt one_ne_zero).clm_apply (differentiableAt_const v)
    have h4 := h1.mul ((hfra i z hz).inv (hfr0 i z hz))
    simp only [div_eq_mul_inv]
    exact h4.differentiableWithinAt
  ·
    intro i j
    set U := L.U i ⊓ L.U j with hU
    set G : Γ(A.left, U) := (L.g i j).val with hG
    set G' : Γ(A.left, U) := ((L.g i j)⁻¹ : (Γ(A.left, U))ˣ).val with hG'
    obtain ⟨-, hring, hcongr, -, -, -⟩ := _root_.GlobalTheory.RegAlg.main A g L u U
    have hder : IsReg u.ex U fun z => fderiv ℂ (val u.ex U G) z v := _root_.GlobalTheory.CechPer.isReg_fderiv_val A g L u hA U G v
    have hinv : IsReg u.ex U (val u.ex U G') := ⟨G', fun z _ => rfl⟩
    have hprod := (hring _ _ hder hinv).2.2
    refine hcongr _ _ hprod ?_
    intro z hz
    have hzij : z ∈ pre u.ex (L.U i) ∩ pre u.ex (L.U j) := by rw [← hinf]; exact hz
    have hGG : val u.ex U G z * val u.ex U G' z = 1 := by
      obtain ⟨e, he⟩ := hev U z hz
      have h1 : G * G' = 1 := Units.mul_inv _
      rw [he, he]
      exact (map_mul e G G').symm.trans ((congrArg e h1).trans (map_one e))
    have hG0 : val u.ex U G z ≠ 0 := left_ne_zero_of_mul_eq_one hGG
    have hev' : ∀ᶠ w in 𝓝 z, u.fr i w = val u.ex U G w * u.fr j w :=
      Filter.eventually_of_mem ((hopen U).mem_nhds hz) (fun w hw => hfrg i j w hw)
    have key := logDer_mul hev' ((hdval U G).differentiableAt ((hopen U).mem_nhds hz))
      (hfra j z hzij.2) hG0 (hfr0 j z hzij.2) v
    simp only [Pi.sub_apply, Pi.mul_apply]
    rw [key, eq_inv_of_mul_eq_one_right hGG]
    ring
  ·
    intro i l z hz
    set m := H.mulVec (star (l : Fin g → ℂ)) with hm
    have hzl : z + (l : Fin g → ℂ) ∈ pre u.ex (L.U i) := (hshift (L.U i) l z).2 hz
    have hχ : χ l ≠ 0 := by
      intro h0
      have := hAH.2.2.1 l
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    obtain ⟨D, hD, hDv⟩ := hasFDerivAt_factor (χ l) (Real.pi : ℂ) ((Real.pi : ℂ) / 2 * ((l : Fin g → ℂ) ⬝ᵥ m)) m z
    have hev' : ∀ᶠ w in 𝓝 z, u.fr i w = (χ l * Complex.exp ((Real.pi : ℂ) * (w ⬝ᵥ m) + (Real.pi : ℂ) / 2 * ((l : Fin g → ℂ) ⬝ᵥ m))) * u.fr i (w + l) :=
      Filter.eventually_of_mem ((hopen _).mem_nhds hz) (fun w hw => hAH.2.2.2 l i w hw)
    have hdl : DifferentiableAt ℂ (fun w => u.fr i (w + l)) z :=
      (hfra i _ hzl).comp z (differentiableAt_id.add_const _)
    have key := logDer_mul hev' hD.differentiableAt hdl
      (mul_ne_zero hχ (Complex.exp_ne_zero _)) (hfr0 i _ hzl) v
    rw [hD.fderiv, hDv, fderiv_comp_add_right] at key
    have hE : χ l * Complex.exp ((Real.pi : ℂ) * (z ⬝ᵥ m) + (Real.pi : ℂ) / 2 * ((l : Fin g → ℂ) ⬝ᵥ m)) ≠ 0 :=
      mul_ne_zero hχ (Complex.exp_ne_zero _)
    rw [key, mul_div_cancel_left₀ _ hE]
    ring

end GlobalTheory.CechPer.LogDer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticBundleRankComparison
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCovQF

open CategoryTheory.Limits GlobalTheory.FlagCell

theorem finite_points {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] (K : Type) [Field K] (y : Sp K ⟶ Y) :
    {x : Sp K ⟶ X | x ≫ f = y}.Finite := by
  have hp : IsFinite (pullback.snd f y) := inferInstance
  have : IsAffine (pullback f y) := isAffine_of_isAffineHom (pullback.snd f y)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ((pullback f y).isoSpec.inv ≫ pullback.snd f y)
  have h4 : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]; infer_instance
  letI : Algebra K Γ(pullback f y, ⊤) := φ.hom.toAlgebra
  haveI : Module.Finite K Γ(pullback f y, ⊤) := h4
  refine (Set.finite_range fun σ : Γ(pullback f y, ⊤) →ₐ[K] K =>
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (pullback f y).isoSpec.inv ≫ pullback.fst f y).subset fun x hx => ?_
  let s : Sp K ⟶ pullback f y := pullback.lift x (𝟙 _) (by rw [Category.id_comp]; exact hx)
  obtain ⟨σ, hσ⟩ := Spec.map_surjective (s ≫ (pullback f y).isoSpec.hom)
  have e : φ ≫ σ = 𝟙 _ := Spec.map_injective (by
    rw [Spec.map_comp, hσ, hφ, Spec.map_id, Category.assoc, Iso.hom_inv_id_assoc]
    exact pullback.lift_snd _ _ _)
  refine ⟨⟨σ.hom, fun a => congr($e a)⟩, ?_⟩
  show Spec.map σ ≫ _ = _
  rw [hσ, Category.assoc, Iso.hom_inv_id_assoc]
  exact pullback.lift_fst _ _ _

section Sheaves

open GlobalTheory.Twist (resM resM_resM app_resM)

end Sheaves

section Matrices

variable {L : Type} [Field L] {m : ℕ}

end Matrices

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}
  {R K L : Type} [CommRing R] [Field K] [Field L]

variable {F : Type} [Field F] {e : F ≃+* c.F}

end Frames

section Points

variable {D : D7} {O : Setup D} {c : O.s.Comp} {Bs : Scheme.{0}} {E : D.what₂.Tau × Bool → Bs.Modules}
  (hE : ∀ a, IsVB (E a) (rkB D.what₂.Tau O.N O.j a)) {Bg : Scheme.{0}} {jB : Bg ⟶ Bs} {πB : Bg ⟶ gen O.s.T.Z}
  {u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB} {Y₀ : Scheme.{0}} {π₀ : Y₀ ⟶ Bs}
  {fl₀ : ∀ a, Vert.Flag ((Scheme.Modules.pullback π₀).obj (E a)) (rkB D.what₂.Tau O.N O.j a)}
  {G : Scheme.{0}} [IsIntegral G] {j : G ⟶ Y₀} {πG : G ⟶ (O.var c).X} {φ : (O.var c).Fn →+* G.functionField}
  {jG : G ⟶ Bg}

end Points

end GlobalTheory.FlagCovQF

end
end

