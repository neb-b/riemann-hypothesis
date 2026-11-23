module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2522
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2543
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2529
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2413
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2381
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2350
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFrameIsUnitAlongSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2550
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2531
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2024
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2409
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2533
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitAdicSumOriginValuesIntegralFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem exists_unit_origin_sum : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ), 1 ≤ k → ∀ b₀ : D.toPre.SecB k 0, eSec D.toPre.P.A (closedPoint R) ∈ nonzeroLocus b₀ → ∀ F₀ : IntFam (maximalIdeal R) D.toPre k, F₀.Lead 0 b₀ → ∃ s₀ : R, IsUnit s₀ ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (σ' : H0 T.U.LG.L k) (f' : ∀ x, T.D'.toPre.SecB k x), (∀ x, PullB T.hD x (F₀.f (T.hD.xe x)) (f' x)) → (∀ e, T.U.ExpandsAt e k σ' f') → ∀ J', Good T.U.LG.L (cpt W) J' → sval σ' (unitW T.G) (cpt W) J' = stalkOf (cpt W) (T.φ s₀) * (val T.U.LG.rig (idW W) (cpt W) J').val ^ k := by
  intro R _ _ _ hB D C k hk b₀ hb₀ F₀ hL
  choose v hv using fun α => _root_.GlobalTheory.Mum.exists_origVal R D.toPre k α (F₀.f α)
  have hvm : ∀ α e, VanMod (maximalIdeal R) (F₀.f α) e → v α ∈ maximalIdeal R ^ (e + 1) :=
    fun α e h => _root_.GlobalTheory.Mum.origVal_mem_of_vanMod R _ D.toPre k α (F₀.f α) (v α) e (hv α) h
  have hfin : ∀ e : ℕ, {α | v α ∉ maximalIdeal R ^ (e + 1)}.Finite := fun e =>
    (F₀.small e).subset fun α h h' => h (hvm α e h')
  obtain ⟨s, hs⟩ := _root_.GlobalTheory.Mum.AdicSum.exists_adic_sum R hB D.toPre.X v hfin
  refine ⟨s, ?_, ?_⟩
  · have hv0 : IsUnit (v 0) := by
      have h0 := hv 0
      rw [hL.1] at h0
      exact _root_.GlobalTheory.Mum.isUnit_origVal R D.toPre k 0 b₀ (v 0) h0 hb₀
    have h1 : s - v 0 ∈ maximalIdeal R := by
      have := hs 0 {0} (fun α hα => hvm α 0 (hL.2 α (by simpa using hα)))
      simpa using this
    by_contra hn
    have hs' : s ∈ maximalIdeal R := (mem_maximalIdeal s).2 hn
    have : v 0 ∈ maximalIdeal R := by
      have := (maximalIdeal R).sub_mem hs' h1
      simpa using this
    exact ((mem_maximalIdeal _).1 this) hv0
  · intro W _ _ _ T σ' f' hP hE J' hJ'
    have hw : ∀ x, OrigVal T.D'.toPre (f' x) (T.φ (v (T.hD.xe x))) := fun x =>
      _root_.GlobalTheory.Mum.OrigValPull.origVal_pull R W T.φ D.toPre T.D'.toPre T.hD k x (F₀.f (T.hD.xe x)) (f' x) (v (T.hD.xe x)) (hP x) (hv _)
    haveI : IsLocalHom T.φ := T.loc
    have hmap : ∀ e, (maximalIdeal R ^ (e + 1)).map T.φ ≤ maximalIdeal W ^ (e + 1) := fun e => by
      rw [Ideal.map_pow]
      refine Ideal.pow_right_mono ?_ _
      refine Ideal.map_le_iff_le_comap.2 fun x hx => (mem_maximalIdeal _).2 fun hu =>
        (mem_maximalIdeal x).1 hx (isUnit_of_map_unit T.φ x hu)
    have step : ∀ e : ℕ, ∃ c ∈ maximalIdeal W ^ (e + 1),
        sval σ' (unitW T.G) (cpt W) J' = stalkOf (cpt W) (T.φ s + c) * (val T.U.LG.rig (idW W) (cpt W) J').val ^ k := by
      intro e
      obtain ⟨S, hS, hc⟩ := _root_.GlobalTheory.Mum.expandsAt_origVal W T.D' T.A T.G T.U.toUnifPre k e σ' f' _ hw (hE e)
      obtain ⟨c, hcm, heq⟩ := hc J' hJ'
      classical
      let S1 : Finset D.toPre.X := S.map T.hD.xe.toEquiv.toEmbedding
      let S2 : Finset D.toPre.X := S1 ∪ (hfin e).toFinset
      have h2 := hs e S2 (fun α hα => by
        by_contra h
        exact hα (Finset.mem_union_right _ ((hfin e).mem_toFinset.2 h)))
      have hsum1 : ∑ x ∈ S, T.φ (v (T.hD.xe x)) = T.φ (∑ α ∈ S1, v α) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp [S1, map_sum]
      have hdiff : T.φ (∑ α ∈ S2, v α) - T.φ (∑ α ∈ S1, v α) ∈ maximalIdeal W ^ (e + 1) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← map_sub, ← Finset.sum_sdiff (Finset.subset_union_left : S1 ⊆ S2), add_sub_cancel_right, map_sum]
        refine Ideal.sum_mem _ fun α hα => ?_
        have hα1 : α ∉ S1 := (Finset.mem_sdiff.1 hα).2
        have := hS (T.hD.xe.symm α) (fun hx => hα1 (by
          simp only [S1, Finset.mem_map_equiv]
          simpa using hx))
        simpa using this
      have h2' : T.φ s - T.φ (∑ α ∈ S2, v α) ∈ maximalIdeal W ^ (e + 1) := by
        rw [← map_sub]; exact hmap e (Ideal.mem_map_of_mem _ h2)
      refine ⟨c - (T.φ s - T.φ (∑ α ∈ S2, v α)) - (T.φ (∑ α ∈ S2, v α) - T.φ (∑ α ∈ S1, v α)),
        Ideal.sub_mem _ (Ideal.sub_mem _ hcm h2') hdiff, ?_⟩
      rw [heq, hsum1]
      congr 2
      ring
    haveI : IsDiscreteValuationRing W := ((GlobalTheory.LN.cDvr_iff W).1 T.cdvr).1
    choose c hc heq using step
    have hce : ∀ e, c e = c 0 := fun e => by
      have := (heq e).symm.trans (heq 0)
      have hu := (Units.isUnit ((val T.U.LG.rig (idW W) (cpt W) J') ^ k))
      rw [Units.val_pow_eq_pow_val] at hu
      have := hu.mul_right_cancel this
      apply add_left_cancel (a := T.φ s)
      apply stalkOf_injective (cpt W)
      exact this
    have h0 : c 0 = 0 := by
      have hm : c 0 ∈ ⨅ n : ℕ, maximalIdeal W ^ n := Submodule.mem_iInf _ |>.2 fun n => by
        rcases n with _ | n
        · simp
        · rw [← hce n]; exact hc n
      rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal W) (maximalIdeal.isMaximal W).ne_top, Submodule.mem_bot] at hm
    rw [heq 0, h0, add_zero]

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilComparisonGeneratorNormalisedZeroSectiStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.Mum.Two.WeilCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilComparisonGenerator_normalised_zeroSection : ∀ (S : Scheme.{0}) (P₀ P₁ P₂ : PolAV S) [Nonempty P₁.A.left] [Nonempty P₂.A.left] (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂] [IsMonHom g₂], ∀ (u : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂)), u.IsGen → ∃ u' : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂), u'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) (J), Good (join P₁.L P₂.L) z J → val u' (r ≫ zero2 P₀.A) z J = 1 := by
  first | exact @GlobalTheory.Mum.Two.WeilCmp.exists_gen_nrm | exact GlobalTheory.Mum.Two.WeilCmp.exists_gen_nrm | (intros; apply GlobalTheory.Mum.Two.WeilCmp.exists_gen_nrm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilComparisonGeneratorOfLambdaBundleIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.Mum.Two.WeilCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilComparisonGenerator_of_lambdaBundleIso : ∀ (S : Scheme.{0}) (P₀ P₁ P₂ : PolAV S) (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A), LBIso (cubeLB P₁.A ![fst P₀.A P₀.A ≫ f₁, snd P₀.A P₀.A ≫ g₁] P₁.L) (cubeLB P₂.A ![fst P₀.A P₀.A ≫ f₂, snd P₀.A P₀.A ≫ g₂] P₂.L) → ∃ u : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂), u.IsGen := by
  first | exact @GlobalTheory.Mum.Two.WeilCmp.exists_cmpGen_of_lbIso | exact GlobalTheory.Mum.Two.WeilCmp.exists_cmpGen_of_lbIso | (intros; apply GlobalTheory.Mum.Two.WeilCmp.exists_cmpGen_of_lbIso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionOddMultiplicationPullbackAtTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exp_mulPull_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ (F₁ : IntFam (maximalIdeal R) D.toPre 1) (G : IntFam (maximalIdeal R) D.toPre (m ^ 2)) (θ₀ : SecK C.P.L.L C.α 1) (S : SecK C.P.L.L C.α (m ^ 2)), MulFam m F₁ G → MulSecK C m θ₀ S → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a b : W), a ≠ 0 → T.Exp a b θ₀ F₁ → ∃ v : Wˣ, T.Exp a (b * v) S G := by
  intro R _ _ _ hR D C m hm F₁ G θ₀ S hMF hMS W _ _ _ T a b ha hE
  obtain ⟨σ, ⟨σ', f', hcar, hpull, hexp⟩, hgen⟩ := hE
  obtain ⟨u, hu, hS⟩ := hMS
  obtain ⟨σ₂, hσ₂⟩ := GlobalTheory.T.exists_section_pullback_commuting_endomorphism_generator C.P.L.L C.P.L.isLB T.β (mulA T.G m).left (mulA C.G m).left
    (GlobalTheory.ZH.TorsFrame.mulA_comm T.cart m) 1 (m ^ 2) u hu σ
  have hgen₂ := GlobalTheory.T.multiplicationPullback_trait_genericCondition R D C W T m a u θ₀ S hS σ σ₂ hgen hσ₂
  obtain ⟨G', hG'⟩ := GlobalTheory.Mum.exists_intFam_pull R hR D W T.φ T.D' T.hD T.inj T.loc (m ^ 2) G
  obtain ⟨uG, σ'', huG, hσ'', hexp''⟩ := GlobalTheory.T.expansion_multiplicationPullback_trait_degreeOne R hR D C W T m hm F₁ G hMF σ' f' hpull hexp G'.f hG'
  obtain ⟨v, hv⟩ := GlobalTheory.T.multiplicationPullbacks_differ_by_unit R hR D C W T m u hu uG huG b σ' σ hcar σ₂ σ'' hσ₂ hσ''
  exact ⟨v, σ₂, ⟨σ'', G'.f, hv, hG', hexp''⟩, hgen₂⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionPullbackFormalEndomorphismTermwise
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFam

theorem texp_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (k e : ℕ) (σ : H0 U.LG.L k) (f : ∀ α, D.toPre.SecB k α) (u : ∀ α, LB.Gen (IotaLB D.toPre a α (h' α))) (s : ∀ α, SecT D.toPre a 0 k (h' α)) (τ : SecE U.toUnifPre (b e) 0 k), U.ExpandsAt e k σ f → (∀ α, IsIota (u α)) → (∀ α, IsPullT (u α) (f α) (s α)) → (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ x z J' = sval σ (x ≫ (b e).left ≫ (fstG (maximalIdeal R) e G).left) z J') → TExp U.toUnifPre τ s := by
  intro R _ _ _ hR D a a' h h' hE A G _ _ hG U b hb k e σ f u s τ hσ hu hs hτ S hS Z x z J J' hJ hJ'
  classical
  obtain ⟨S₀, hS₀⟩ := DVR.expandsAt_val U.toUnifPre e k σ f hσ
  have hp : (U.gt e).pG.left = (U.gt e).q.left ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e) := rfl
  have hc : (b e).left ≫ (U.gt e).pG.left = (U.gt e).pG.left ≫ a.left := by
    have h₁ := congrArg (fun m => m.left) (hb.2.2.1 e)
    have h₂ : ((Over.pullback (thick R (maximalIdeal R) e)).map a).left ≫
        pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e) =
        pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e) ≫ a.left := pullback.lift_fst _ _ _
    rw [hp]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₁).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) h₂).trans (Category.assoc _ _ _).symm)))
  have hx : (x ≫ (b e).left) ≫ (U.gt e).pG.left = (x ≫ (U.gt e).pG.left) ≫ a.left := by
    rw [Category.assoc, hc, Category.assoc]
  obtain ⟨z₀, e₀⟩ := hS₀ Z (x ≫ (b e).left) z J hJ
  have e₁ := e₀ (J' (x ≫ (b e).left ≫ (fstG (maximalIdeal R) e G).left)) (hJ' (x ≫ (b e).left ≫ (fstG (maximalIdeal R) e G).left))
  have term : ∀ α, sval (f α) ((x ≫ (b e).left) ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t α) (x ≫ (b e).left) z J).val =
      sval (s α) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (h' α)) x z J).val := fun α => by
    rw [hs α Z _ z J hJ, _root_.GlobalTheory.TwFam.coord_of_formalEnd R hR D a a' h h' hE A G hG U b hb α (u α) (hu α) e Z x z J hJ, hx, Units.val_mul]
    ring
  have l : evalE U.toUnifPre τ x z J J' = ∑ α ∈ S₀, sval (s α) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (h' α)) x z J).val := by
    refine Eq.trans ?_ (e₁.trans (Finset.sum_congr rfl fun α _ => term α))
    rw [evalE, hτ Z x z J' hJ', zpow_zero, _root_.one_mul, zpow_natCast, Category.assoc, Category.assoc,
      sval_of σ _ z J' (fun _ => J' (x ≫ (b e).left ≫ (fstG (maximalIdeal R) e G).left))
        (fun _ => congrArg J' (Category.comp_id _))]
    rfl
  rw [l]
  refine (Finset.sum_subset (Finset.subset_union_left (s₂ := S)) fun α _ hα => ?_).trans
    (Finset.sum_subset (Finset.subset_union_right (s₁ := S₀)) fun α _ hα => ?_).symm
  · rw [← term α, z₀ α hα, zero_mul]
  · have := hS α hα Z (x ≫ (U.gt e).q.left) z J hJ
    rw [hp, ← Category.assoc, this, zero_mul]

end GlobalTheory.TwFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionTransportTranslationTwistStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansion_transport_translation_twist : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₂ : DegData R I) (A A₂ : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (U₂ : UnifPre I D₂ A₂ G) (a : 𝟙_ (Over (Sp R)) ⟶ G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))) (β : D₂.toPre.P.A ⟶ D.toPre.P.A) (xe : D₂.toPre.X ≃+ D.toPre.X) (w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b) GlobalTheory.MumCmp.twε)) (wL : LB.Iso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left)) (ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![g.b.left, η[D.toPre.P.A].left] ![-1, 1])) (e : ℕ) (h : (thickObj R I e G).left ⟶ (thickObj R I e G).left), h ≫ (fstG I e G).left = (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → h ≫ (U.gt e).pG.left = (U₂.gt e).pG.left ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b 0 → (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι) (N : (Z ⟶ G.left) → U.LG.L.ι) (N' : (Z ⟶ G.left) → U₂.LG.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.Good U.LG.L z N → Geo.Tor.Good U₂.LG.L z N' → Geo.Tor.gv w (r ≫ (U₂.gt e).pG.left) z (fun i => J ((r ≫ (U₂.gt e).pG.left) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i)) (J' (r ≫ (U₂.gt e).pG.left)) * Geo.Tor.gw (U₂.w e) r z (J' (r ≫ (U₂.gt e).pG.left)) (fun _ => N' (r ≫ (fstG I e G).left)) = Geo.Tor.gw (U.w e) (r ≫ h) z (J (r ≫ h ≫ (U.gt e).pG.left)) (fun _ => N (r ≫ h ≫ (fstG I e G).left)) * Geo.Tor.gw wL (r ≫ (fstG I e G).left) z (N (r ≫ (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (N' (r ≫ (fstG I e G).left)) * Geo.Tor.val ν (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J) → (∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.val ((U.gt e).t (xe χ)) (r ≫ h) z J = (∏ k, Geo.Tor.gv w (r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k) z (fun i => J ((r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i)) (J' (r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k)) ^ Oinvε k) * Geo.Tor.val ((U₂.gt e).t χ) r z J' * Geo.Tor.val (g.s (xe χ)) (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J) → ∀ (σ : H0 U.LG.L 1) (σ₂ : H0 U₂.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α) (f₂ : ∀ α : D₂.toPre.X, D₂.toPre.SecB 1 α), (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι) (N' : (Z ⟶ G.left) → U₂.LG.L.ι), Geo.Tor.Good U.LG.L z N → Geo.Tor.Good U₂.LG.L z N' → Geo.Tor.sval σ (r ≫ ((toUnit G ≫ a) * 𝟙 G).left) z N = (Geo.Tor.gw wL r z (N (r ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (N' r)).val * Geo.Tor.sval σ₂ r z N') → (∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b 0) z J * (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.toPre.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.toPre.P.A).left) z J).val = (∏ κ, Geo.Tor.gv w (r ≫ D₂.toPre.famφB χ κ) z (fun i => J ((r ≫ D₂.toPre.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i)) (J' (r ≫ D₂.toPre.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval (f₂ χ) r z J') → U.ExpandsAt e 1 σ f → U₂.ExpandsAt e 1 σ₂ f₂ := by
  first | exact @GlobalTheory.TwistedExpTransport.expandsAt_twist | exact GlobalTheory.TwistedExpTransport.expandsAt_twist | (intros; apply GlobalTheory.TwistedExpTransport.expandsAt_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFreeOfPositiveDefiniteFormBoundedRank
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem finite_free_of_definite_form_of_rank_le :
    ∀ (H : Type) [AddCommGroup H] (Q : H → ℤ), (∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) → (∀ f, 0 ≤ Q f) → (∀ f, Q f = 0 → f = 0) → ∀ r : ℕ, (∀ (n : ℕ) (u : Fin n → H), LinearIndependent ℤ u → n ≤ r) → Module.Finite ℤ H ∧ Module.Free ℤ H ∧ Module.finrank ℤ H ≤ r := by
  intro H _ Q hQ hpos hdef r hr
  classical
  have h0 : Q 0 = 0 := by
    have := hQ 0 0
    simp only [add_zero, sub_zero] at this
    omega
  have htf : ∀ (k : ℤ) (f : H), k ≠ 0 → k • f = 0 → f = 0 := by
    intro k f hk hkf
    apply hdef
    have h1 := parallelogram_zsmul Q hQ k f
    rw [hkf, h0] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left (pow_ne_zero 2 hk)
  let P : ℕ → Prop := fun n => ∃ u : Fin n → H, LinearIndependent ℤ u
  obtain ⟨n, hn⟩ : ∃ n, n = Nat.findGreatest P r := ⟨_, rfl⟩
  have hPn : P n := hn ▸
    Nat.findGreatest_spec (P := P) (m := 0) (Nat.zero_le r) ⟨Fin.elim0, linearIndependent_empty_type⟩
  obtain ⟨u, hu⟩ := hPn
  have hmax : ¬ P (n + 1) := by
    rintro ⟨v, hv⟩
    have hlt : Nat.findGreatest P r < n + 1 := by omega
    exact Nat.findGreatest_is_greatest (P := P) (n := r) hlt (hr _ v hv) ⟨v, hv⟩
  have hspan : ∀ h : H, ∃ k : ℕ, 0 < k ∧ ∃ m : Fin n → ℤ, k • h = ∑ i, m i • u i := by
    intro h
    by_contra hne
    push_neg at hne
    apply hmax
    refine ⟨Fin.cons h u, LinearIndependent.finCons' h u hu fun c y hy hcy => ?_⟩
    by_contra hc
    obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hy
    have hpos' : 0 < c.natAbs := Int.natAbs_pos.2 hc
    rcases Int.natAbs_eq c with hc' | hc'
    · apply hne c.natAbs hpos' (fun i => - m i)
      rw [← natCast_zsmul, ← hc']
      simp only [neg_smul, Finset.sum_neg_distrib, hm]
      exact eq_neg_of_add_eq_zero_left hcy
    · apply hne c.natAbs hpos' m
      rw [← natCast_zsmul, hm]
      have : c • h = - ((c.natAbs : ℤ) • h) := by
        conv_lhs => rw [hc']
        rw [neg_smul]
      rw [this] at hcy
      exact (neg_add_eq_zero.mp hcy)
  obtain ⟨e, he, hdiv⟩ := exists_dvd_coords_of_definite_form H ⊤ Q hQ hpos
    (fun f _ => hdef f) n u (fun _ => trivial) hu
  have hmem : ∀ h : H, (e : ℤ) • h ∈ Submodule.span ℤ (Set.range u) := by
    intro h
    obtain ⟨k, hk, m, hkm⟩ := hspan h
    have hd := hdiv k m h trivial hkm
    choose m' hm' using hd
    have hz : (k : ℤ) • ((e : ℤ) • h - ∑ i, m' i • u i) = 0 := by
      rw [smul_sub, smul_comm (k : ℤ) (e : ℤ) h, natCast_zsmul h k, hkm, Finset.smul_sum, Finset.smul_sum,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [smul_smul, smul_smul, ← hm' i, sub_self]
    have := htf k _ (by exact_mod_cast hk.ne') hz
    rw [sub_eq_zero.mp this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let f : H →ₗ[ℤ] Submodule.span ℤ (Set.range u) :=
    LinearMap.codRestrict _ ((e : ℤ) • LinearMap.id) hmem
  have hinj : Function.Injective f := by
    intro a b hab
    have h' : (e : ℤ) • a = (e : ℤ) • b := congrArg Subtype.val hab
    have : (e : ℤ) • (a - b) = 0 := by rw [smul_sub, h', sub_self]
    exact sub_eq_zero.mp (htf e _ (by exact_mod_cast he.ne') this)
  have : Module.Finite ℤ (Submodule.span ℤ (Set.range u)) :=
    Module.Finite.span_of_finite ℤ (Set.finite_range u)
  have hfin : Module.Finite ℤ H := Module.Finite.of_injective f hinj
  have : Module.IsTorsionFree ℤ H := Module.IsTorsionFree.of_smul_eq_zero fun k x hkx => by
    by_cases hk : k = 0
    · exact Or.inl hk
    · exact Or.inr (htf k x hk hkx)
  have hfree : Module.Free ℤ H := Module.free_of_finite_type_torsion_free'
  refine ⟨hfin, hfree, ?_⟩
  exact hr _ _ (Module.finBasis ℤ H).linearIndependent

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMorphismValuativeLiftingNormalDomainStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_morphism_valuative_lifting_normal_domain : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (Z P : Scheme.{0}) (p : Z ⟶ P) (ξ₀ : Sp R ⟶ P) (y : Sp (FractionRing R) ⟶ Z), IsFinite p → y ≫ p = jK R ≫ ξ₀ → ∃ ξ : Sp R ⟶ Z, jK R ≫ ξ = y ∧ ξ ≫ p = ξ₀ := by
  first | exact @GlobalTheory.finite_lift_fractionField | exact GlobalTheory.finite_lift_fractionField | (intros; apply GlobalTheory.finite_lift_fractionField <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMumfordClassEqZeroAmple
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AV.AbVar

theorem memKL_of_lam_geom_eq_zero {K : Type} [Field K] (A : AbVar K) {L : LB A.X.left} (hL : L.IsLB)
    (x : A.Pt) (h : AbVar.lam (cls L hL) (fst A.X (ptOver K (AlgebraicClosure K))) (snd A.X _ ≫ x) = 0) :
    MemKL A.X L x := by
  set P := ptOver K (AlgebraicClosure K)
  have h1 := congrArg (CechPic.pull (lift (snd P A.X) (fst P A.X)).left) h
  rw [lam_eq, pull_lam, map_zero, lift_fst, lift_snd_assoc, lam_comm, ← lam_eq] at h1
  have h0 : CechPic.pull (fst P A.X ≫ x).left (cls L hL) = 0 := by
    rw [Over.comp_left, pull_comp, GlobalTheory.PrimitiveOverField.pic_field (K := AlgebraicClosure K) (CechPic.pull x.left (cls L hL)), map_zero]
  rw [AbVar.lam, h0, sub_zero] at h1
  intro p
  refine ⟨⊤, trivial, ?_⟩
  have hD : (Out.translDiff A.X L x).IsLB := LB.isLB_linComb hL _ _
  refine (cls_eq_zero_iff (pull_isLB hD _)).1 ?_
  rw [cls_pull hD]
  refine (congrArg _ ?_).trans (map_zero _)
  refine (cls_linComb hL _ _ hD).trans (Eq.trans ?_ h1)
  rw [Fin.sum_univ_two, sub_eq_add_neg]
  exact congrArg₂ (· + ·) (one_zsmul _) (neg_one_zsmul _)

end GlobalTheory.AV.AbVar

theorem GlobalTheory.AV.AbVar.finite_lam_eq_zero : ∀ (K : Type) [Field K] (A : AbVar K) (c : Pic A.X.left), IsAmpleCls c → Finite {x : A.Pt // AbVar.lam c (fst A.X (ptOver K (AlgebraicClosure K))) (snd A.X _ ≫ x) = 0} := by
  intro K _ A c ⟨L, hL, ha, hc⟩
  subst hc
  obtain ⟨H, _, i, -, hmono, hfin, -, hH⟩ := GlobalTheory.kernel_finiteFlat_subgroup K A.X A.ab L hL ha
  have hF := GlobalTheory.FlagCovQF.finite_points H.hom (AlgebraicClosure K) (spMap (algebraMap K (AlgebraicClosure K)))
  haveI := hF.to_subtype
  have hz : ∀ x : {x : A.Pt // AbVar.lam (cls L hL) (fst A.X (ptOver K (AlgebraicClosure K))) (snd A.X _ ≫ x) = 0},
      ∃ z : ptOver K (AlgebraicClosure K) ⟶ H, z ≫ i = x.1 := fun x =>
    (hH _ x.1).1 (memKL_of_lam_geom_eq_zero A hL x.1 x.2)
  choose z hz using hz
  refine Finite.of_injective (fun x => (⟨(z x).left, Over.w (z x)⟩ :
    {y : Sp (AlgebraicClosure K) ⟶ H.left | y ≫ H.hom = spMap (algebraMap K (AlgebraicClosure K))})) ?_
  intro a b hab
  have e : z a = z b := Over.OverMorphism.ext (congrArg Subtype.val hab)
  exact Subtype.ext ((hz a).symm.trans (e ▸ hz b))
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEigenspacesOfSeparableMinpoly
section
open CategoryTheory Polynomial NumberField IsDedekindDomain AlgebraicGeometry
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

namespace GlobalTheory.EigSum

theorem finrank_eigenspaces_of_separable_minpoly
    (Ω V : Type) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [AddCommGroup V] [Module Ω V]
    [FiniteDimensional Ω V] (T : Module.End Ω V) (f : Polynomial Ω) (hm : f.Monic)
    (hs : f.Separable) (h0 : Polynomial.aeval T f = 0)
    (hmin : ∀ g : Polynomial Ω, Polynomial.aeval T g = 0 → f ∣ g) :
    ∑ z ∈ f.roots.toFinset, Module.finrank Ω (T.eigenspace z) = Module.finrank Ω V ∧
      ∀ z ∈ f.roots, T.eigenspace z ≠ ⊥ := by
  have hf : f = minpoly Ω T := by
    apply Polynomial.eq_of_monic_of_associated hm (minpoly.monic (Algebra.IsIntegral.isIntegral T))
    exact associated_of_dvd_dvd (hmin _ (minpoly.aeval Ω T)) (minpoly.dvd Ω T h0)
  have hroot : ∀ z, T.HasEigenvalue z ↔ z ∈ f.roots := by
    intro z
    rw [Module.End.hasEigenvalue_iff_isRoot, ← hf, Polynomial.mem_roots hm.ne_zero]
  have hss : T.IsSemisimple := Module.End.isSemisimple_of_squarefree_aeval_eq_zero hs.squarefree h0
  refine ⟨?_, fun z hz => (hroot z).2 hz⟩
  set s := f.roots.toFinset
  let N : s → Submodule Ω V := fun z => T.eigenspace z
  have hind : iSupIndep N :=
    iSupIndep.comp (Module.End.eigenspaces_iSupIndep T) Subtype.val_injective
  have htop : ⨆ z, N z = ⊤ := by
    have h1 := Module.End.iSup_maxGenEigenspace_eq_top T
    simp only [hss.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] at h1
    rw [eq_top_iff, ← h1]
    refine iSup_le fun μ => ?_
    by_cases hμ : μ ∈ s
    · exact le_iSup N ⟨μ, hμ⟩
    · have : ¬ T.HasEigenvalue μ := by
        rw [hroot]; simpa [s] using hμ
      rw [Module.End.hasEigenvalue_iff, not_not] at this
      simp [this]
  have hint := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  rw [← (LinearEquiv.ofBijective (DirectSum.coeLinearMap N) hint).finrank_eq,
    Module.finrank_directSum]
  exact (Finset.sum_coe_sort s (fun z => Module.finrank Ω (T.eigenspace z))).symm

end GlobalTheory.EigSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointMapOverRingHomUniqueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericPointMap_over_ringHom_unique : ∀ {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (κ κ' : Sp (FractionRing V) ⟶ Sp (FractionRing R)), κ ≫ jK R = jK V ≫ spMap θ → κ' ≫ jK R = jK V ≫ spMap θ → κ = κ' := by
  first | exact @GlobalTheory.TInj.genPt_map_unique | exact GlobalTheory.TInj.genPt_map_unique | (intros; apply GlobalTheory.TInj.genPt_map_unique <;> assumption)
end

