module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueRealLinearOfEventuallyAddModDiscrete
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemicharacterSqEqOneOfSymmetric
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0106
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLinComb
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PairingComb

open CommutatorPairing

theorem exists_gen_linComb {X X' Y' : Scheme.{0}} {D : LB X} {I K : Type} [Fintype I] [Fintype K]
    (F : I → (X' ⟶ X)) (e : I → ℤ) (ψ : K → (Y' ⟶ X')) (ε : K → ℤ) {Y : I → Scheme.{0}} (h : ∀ i, Y' ⟶ Y i)
    (φ : ∀ i, K → (Y i ⟶ X)) (hc : ∀ i k, ψ k ≫ F i = h i ≫ φ i k)
    (t : ∀ i, LB.Gen (LB.LinComb D (φ i) ε)) (ht : ∀ i, (t i).IsGen) :
    ∃ u : LB.Gen (LB.LinComb (LB.LinComb D F e) ψ ε), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J₀ : (Z ⟶ X) → D.ι), Good D z J₀ →
        val u r z (fun χ i => J₀ (χ ≫ F i)) = ∏ i, val (t i) (r ≫ h i) z J₀ ^ e i := by
  have le : ∀ (jj : K → I → D.ι) (i : I), LB.wchart (LB.LinComb D F e) ψ jj ≤
      h i ⁻¹ᵁ LB.wchart D (φ i) (fun k => jj k i) := fun jj i y hy => Set.mem_iInter.2 fun k => by
    have h₁ : (ψ k ≫ F i) y ∈ D.U (jj k i) := Set.mem_iInter.1 (Set.mem_iInter.1 hy k) i
    rw [hc] at h₁
    exact h₁
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (jj : K → I → D.ι), r z ∈ LB.wchart (LB.LinComb D F e) ψ jj →
      gm r z (LB.wchart (LB.LinComb D F e) ψ jj) (∏ i, res (le jj i) (pullU (h i) _ ((t i).s fun k => jj k i)) ^ e i) =
        ∏ i, gm (r ≫ h i) z (LB.wchart D (φ i) fun k => jj k i) ((t i).s fun k => jj k i) ^ e i := by
    intro Z r z jj hz
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow, gm_res r z _ hz]
    exact congrArg (· ^ e i) (gm_pull r (h i) z _ (le jj i hz) _)
  refine ⟨⟨fun jj => ∏ i, res (le jj i) (pullU (h i) _ ((t i).s fun k => jj k i)) ^ e i⟩,
    (CechPic.isGen_iff_germ _).2 fun y j j' hj hj' => ?_, fun Z r z J₀ hJ => ?_⟩
  · refine (v _ (𝟙 Y') y j hj).trans (Eq.trans ?_ (congrArg₂ (· * ·)
      (gm_linComb (LB.LinComb D F e) ψ ε (𝟙 Y') y j j' hj hj') (v _ (𝟙 Y') y j' hj')).symm)
    have a : ∀ i, gm (𝟙 Y' ≫ h i) y (LB.wchart D (φ i) fun k => j k i) ((t i).s fun k => j k i) = _ := fun i =>
      gen_trans (ht i) (𝟙 Y' ≫ h i) y (le j i hj) (le j' i hj')
    have b : ∀ k, _ := fun k => gm_linComb D F e (𝟙 Y' ≫ ψ k) y (j k) (j' k) (Set.mem_iInter.1 hj k)
      (Set.mem_iInter.1 hj' k)
    simp only [a, mul_zpow, Finset.prod_mul_distrib]
    congr 1
    refine Eq.trans ?_ (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) (b k)).symm
    simp only [trF, ← Finset.prod_zpow, ← zpow_mul, Category.assoc, hc]
    rw [Finset.prod_comm]
    simp only [mul_comm]
  · have hz : r z ∈ LB.wchart (LB.LinComb D F e) ψ (fun k i => J₀ ((r ≫ ψ k) ≫ F i)) :=
      Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun i => hJ ((r ≫ ψ k) ≫ F i)
    refine (v Z r z _ hz).trans (Finset.prod_congr rfl fun i _ => congrArg (· ^ e i) ?_)
    exact (val_of (t i) (r ≫ h i) z J₀ _ fun k => by rw [Category.assoc, Category.assoc, hc]).symm

variable {S : Scheme.{0}} {G A : Over S} [GrpObj G] [GrpObj A] {D : LB A.left} {I : Type} [Fintype I]

theorem exists_theta_linComb (φ : I → (G ⟶ A)) (hφ : ∀ i, IsMonHom (φ i)) (e : I → ℤ) {n : ℤ} {T : Over S}
    {T' : I → Over S} (m : ∀ i, T ⟶ T' i) (x : T ⟶ G) (θ₀ : ∀ i, ThetaGrp A D n (T' i))
    (hx : ∀ i, m i ≫ (θ₀ i).pt = x ≫ φ i) :
    ∃ θ : ThetaGrp G (LB.LinComb D (fun i => (φ i).left) e) n T, θ.pt = x ∧
      ∀ (Z : Over S) (t : Z ⟶ T) (a : Z ⟶ G) (z : Z.left) (J₀), Good D z J₀ →
        thetaVal θ t a z (fun χ i => J₀ (χ ≫ (φ i).left)) = ∏ i, thetaVal (θ₀ i) (t ≫ m i) (a ≫ φ i) z J₀ ^ e i := by
  have hc : ∀ i (k : Fin 2), ![(snd T G).left, (translPt G x).left] k ≫ (φ i).left =
      (lift (fst T G ≫ m i) (snd T G ≫ φ i)).left ≫ ![(snd (T' i) A).left, (translPt A (θ₀ i).pt).left] k := by
    intro i k
    have := hφ i
    fin_cases k
    · exact congrArg CommaMorphism.left (lift_snd (fst T G ≫ m i) (snd T G ≫ φ i)).symm
    · refine congrArg CommaMorphism.left (?_ : translPt G x ≫ φ i = _ ≫ translPt A (θ₀ i).pt)
      rw [lift_translPt, Category.assoc, hx]
      show ((fst T G ≫ x) * snd T G) ≫ φ i = _
      rw [MonObj.mul_comp, Category.assoc]
  obtain ⟨u, hu, hv⟩ := exists_gen_linComb (fun i => (φ i).left) e _ ![n, -n] _ _ hc (fun i => (θ₀ i).φ)
    (fun i => (θ₀ i).isGen)
  refine ⟨⟨x, u, hu⟩, rfl, fun Z t a z J₀ hJ => (hv _ (lift t a).left z J₀ hJ).trans ?_⟩
  refine Finset.prod_congr rfl fun i _ => congrArg (· ^ e i) ?_
  rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc]
  rfl

theorem weilIs_linComb (hG : GlobalFnsSt) (hA : IsAbelianScheme G) (hD : D.IsLB) (φ : I → (G ⟶ A))
    (hφ : ∀ i, IsMonHom (φ i)) (e : I → ℤ) {n : ℤ} {T : Over S} {x y : T ⟶ G} (c : I → Γ(T.left, ⊤)ˣ)
    (h : ∀ i, WeilIs A D n (x ≫ φ i) (y ≫ φ i) (c i)) :
    WeilIs G (LB.LinComb D (fun i => (φ i).left) e) n x y (∏ i, c i ^ e i) := by
  have hL := LB.isLB_linComb hD (fun i => (φ i).left) e
  refine WeilIsogeny.weilIs_of_local hG hA hL fun p => ?_
  choose V hV H using fun i => h i p
  choose θx₀ θy₀ ex ey using fun i => (H i).1
  let V₀ : T.left.Opens := ⟨⋂ i, (V i : Set T.left), isOpen_iInter_of_finite fun i => (V i).isOpen⟩
  have le : ∀ i, V₀ ≤ V i := fun i _ hz => Set.mem_iInter.1 hz i
  obtain ⟨θx, fx, vx⟩ := exists_theta_linComb φ hφ e (fun i => overLE (le i)) (overResι V₀ ≫ x) θx₀
    (fun i => by rw [ex, ← Category.assoc, overLE_ι, Category.assoc])
  obtain ⟨θy, fy, vy⟩ := exists_theta_linComb φ hφ e (fun i => overLE (le i)) (overResι V₀ ≫ y) θy₀
    (fun i => by rw [ey, ← Category.assoc, overLE_ι, Category.assoc])
  obtain ⟨c', hc'⟩ := exists_commIsOf hG hA hL θx θy
  refine ⟨V₀, Set.mem_iInter.2 hV, θx, θy, fx, fy, ?_⟩
  obtain rfl : c' = unitRes V₀ (∏ i, c i ^ e i) := by
    refine unit_ext fun z _ => ?_
    choose J₀ hJ₀ using fun χ : (overRes V₀).left ⟶ A.left => exists_chart hD (χ z)
    have e₁ := (commIsOf_iff hL _ _ _).1 hc' _ (𝟙 _) 1 z (fun χ i => J₀ (χ ≫ (φ i).left))
      (fun χ => Set.mem_iInter.2 fun i => hJ₀ (χ ≫ (φ i).left))
    have e₂ : ∀ i, _ := fun i => (commIsOf_iff hD _ _ _).1 ((H i).2 (θx₀ i) (θy₀ i) (ex i) (ey i)) _
      (𝟙 _ ≫ overLE (le i)) (1 ≫ φ i) z J₀ hJ₀
    have gx : ∀ i, ((𝟙 _ ≫ overLE (le i)) ≫ (θx₀ i).pt) * (1 ≫ φ i) = ((𝟙 _ ≫ θx.pt) * 1) ≫ φ i := fun i => by
      have := hφ i
      rw [MonObj.mul_comp, ex, fx, Category.assoc, ← Category.assoc (overLE _), overLE_ι]
      simp only [Category.assoc]
    have gy : ∀ i, ((𝟙 _ ≫ overLE (le i)) ≫ (θy₀ i).pt) * (1 ≫ φ i) = ((𝟙 _ ≫ θy.pt) * 1) ≫ φ i := fun i => by
      have := hφ i
      rw [MonObj.mul_comp, ey, fy, Category.assoc, ← Category.assoc (overLE _), overLE_ι]
      simp only [Category.assoc]
    have e₃ : ∀ i, gm (𝟙 _ ≫ overLE (le i)).left z ⊤ (unitRes (V i) (c i)) = gm (𝟙 _ ≫ V₀.ι) z ⊤ (c i) := fun i => by
      refine (gm_unitRes (V i) (c i) _ z).trans ?_
      exact congrArg (fun q => gm q z ⊤ (c i)) (congrArg CommaMorphism.left
        ((Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·) (overLE_ι (le i)))))
    refine e₁.symm.trans (Eq.trans ?_ (gm_unitRes V₀ _ (𝟙 _) z).symm)
    unfold commVal
    rw [vx _ _ _ _ _ hJ₀, vx _ _ _ _ _ hJ₀, vy _ _ _ _ _ hJ₀, vy _ _ _ _ _ hJ₀, map_prod,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow, ← e₃, ← e₂, commVal, gx, gy]
    simp only [mul_zpow, inv_zpow]
  exact hc'

end GlobalTheory.PairingComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHalfChar
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.PTheta
open scoped BigOperators Real

namespace GlobalTheory.ThetaPoint

open CanTh

theorem exists_linearEquiv_lift (hmul : Out.MulNSt) (P : Out.PolAV (Sp ℂ)) {L : LB P.A.left} {d g : ℕ}
    (u : HolUnif P.A L d) (a : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)) (hadd : ∀ z w, a (z + w) = a z * a w)
    (hon : Function.Surjective a) (hol : IsHolTo Set.univ fun z => (a z).left) (hker : {z | a z = 1}.Countable) :
    ∃ F : (Fin g → ℂ) ≃ₗ[ℂ] (Fin d → ℂ), ∀ z, u.ex (F z) = a z := by
  have hval := @valAt'_rules
  have hvalaff := @existsUnique_point_of_ringHom
  obtain ⟨u₀, -, hlift⟩ := AbelianExp.exists_holUnif hmul hval (holFamily_lift hval)
    (isTopologicalGroup_complexPoints hval) (PointsCompact.compactSpace_points_polAV hval hvalaff)
    (HolChart.exists_holomorphic_chart hval hvalaff exists_holomorphic_section_of_etale) P
  have cnt : ∀ {L : LB P.A.left} {d : ℕ} (u : HolUnif P.A L d), (u.Λ : Set (Fin d → ℂ)).Countable := fun u =>
    countable_of_isDiscrete_finiteDimensional (isDiscrete_iff_discreteTopology.2 u.discrete)
  have key : ∀ (n : ℕ) (a : (Fin n → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), (∀ z w, a (z + w) = a z * a w) →
      Function.Surjective a → (IsHolTo Set.univ fun z => (a z).left) → {z | a z = 1}.Countable →
      ∃ F : (Fin n → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ), ∀ z, u₀.ex (F z) = a z := by
    intro n a hadd hon hol hker
    have h0 : a 0 = 1 := by
      have := hadd 0 0
      rw [add_zero] at this
      exact mul_eq_left.1 this.symm
    obtain ⟨G, hG0, hGa, hGe⟩ := hlift n a hol h0
    have hF := EndoLinear.fderiv_lifts u₀.ex u₀.ex_add u₀.Λ u₀.ker u₀.discrete a hadd G hG0
      hGa.differentiableAt hGe
    have hi : Function.Injective (fderiv ℂ G 0) :=
      realLinear_injective_of_countable_ker ((fderiv ℂ G 0).restrictScalars ℝ).toLinearMap
        (hker.mono fun x (hx : fderiv ℂ G 0 x = 0) => by
          change a x = 1
          rw [← hF, hx, CubeValues.ex_zero])
    have hs : Function.Surjective (fderiv ℂ G 0) :=
      realLinear_surjective_of_mod_countable ((fderiv ℂ G 0).restrictScalars ℝ).toLinearMap (cnt u₀) fun y => by
        obtain ⟨x, hx⟩ := hon (u₀.ex y)
        refine ⟨x, (u₀.ker _).1 ?_⟩
        have := u₀.ex_add (y - fderiv ℂ G 0 x) (fderiv ℂ G 0 x)
        rw [sub_add_cancel, hF, hx] at this
        exact mul_eq_right.1 this.symm
    exact ⟨LinearEquiv.ofBijective (fderiv ℂ G 0).toLinearMap ⟨hi, hs⟩, hF⟩
  obtain ⟨F₁, h₁⟩ := key g a hadd hon hol hker
  obtain ⟨F₀, h₀⟩ := key d u.ex u.ex_add u.ex_onto (fun U f => by simpa using u.hol U f)
    ((cnt u).mono fun z hz => (u.ker z).1 hz)
  exact ⟨F₁.trans F₀.symm, fun z => by rw [← h₀, ← h₁]; simp⟩

theorem isHolTo_fibre {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {S X Z : Scheme.{0}} {p : Z ⟶ X}
    {q : Z ⟶ Sp ℂ} {s : X ⟶ S} {y : Sp ℂ ⟶ S} (H : IsPullback p q s y) (c : V → (Sp ℂ ⟶ Z))
    (hq : ∀ w, c w ≫ q = 𝟙 _) (ha : IsHolTo Set.univ fun w => c w ≫ p) : IsHolTo Set.univ c := by
  intro U f
  refine holFamily_of_affine valAt'_rules Set.univ Z c (fun w₀ _ => ?_) U f
  obtain ⟨US, hUS, hy, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤)
    (x := y (default : PrimeSpectrum ℂ)) trivial
  have hyU : ⊤ ≤ y ⁻¹ᵁ US := (top_le_preimage_iff_mem y US).2 hy
  have hs : (c w₀ ≫ p) (default : PrimeSpectrum ℂ) ∈ s ⁻¹ᵁ US := by
    rw [← top_le_preimage_iff_mem, ← top_le_preimage_comp, Category.assoc, H.w, ← Category.assoc, hq,
      Category.id_comp]
    exact hyU
  obtain ⟨U₁, hU₁, hx₁, hle⟩ := exists_isAffineOpen_mem_and_subset hs
  have hle : U₁ ≤ s ⁻¹ᵁ US := hle
  set W : Z.Opens := p ⁻¹ᵁ U₁ ⊓ q ⁻¹ᵁ ⊤ with hW
  have hiff : ∀ w, ⊤ ≤ c w ⁻¹ᵁ W ↔ ⊤ ≤ (c w ≫ p) ⁻¹ᵁ U₁ := fun w => by
    rw [hW, top_le_preimage_inf, top_le_preimage_comp]
    exact ⟨fun h => h.1, fun h => ⟨h, fun _ _ => trivial⟩⟩
  have hV : IsAffineOpen W := by
    have : IsAffine _ := isAffineOpen_top (Sp ℂ)
    have : IsAffine _ := hU₁
    have : IsAffine _ := hUS
    exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := US) (UT := ⊤) (UX := U₁) hyU hle hW).isoPullback.hom
  have po := (isIso_pushoutSection_iff H (US := US) (UT := ⊤) (UX := U₁) hyU hle hW).mp
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ hUS (isAffineOpen_top _) hU₁)
  have hgen := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
  refine ⟨W, hV, (hiff w₀).2 ((top_le_preimage_iff_mem _ _).2 hx₁), ?_, fun g => ?_⟩
  · simpa only [hiff] using (ha U₁ 0).1
  · have hg : g ∈ Subring.closure _ := hgen.ge (Subring.mem_top g)
    induction hg using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · refine ((ha U₁ t).2.mono fun w (hw : w ∈ Set.univ ∩ {w | ⊤ ≤ c w ⁻¹ᵁ W}) =>
          ⟨hw.1, (hiff w).1 hw.2⟩).congr fun w hw => ?_
        exact valAt'_appLE (c w) p U₁ W _ t hw.2
      · refine (differentiableOn_const (valAt' (𝟙 (Sp ℂ)) ⊤ t)).congr fun w hw => ?_
        exact (valAt'_appLE (c w) q ⊤ W _ t hw.2).trans (by rw [hq])
    | zero => simpa only [valAt'_zero] using differentiableOn_const (0 : ℂ)
    | one => exact (differentiableOn_const (1 : ℂ)).congr fun w hw => valAt'_one _ hw.2
    | add x y _ _ hx hy => simpa only [valAt'_add] using hx.fun_add hy
    | neg x _ hx => simpa only [valAt'_neg] using hx.fun_neg
    | mul x y _ _ hx hy => simpa only [valAt'_mul] using hx.fun_mul hy

section Frame

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}

def IsHolFrame (L : LB X) (x : V → (Sp ℂ ⟶ X)) (fr : L.ι → V → ℂ) : Prop :=
  (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ x z ⁻¹ᵁ L.U j}) ∧ (∀ j z, ⊤ ≤ x z ⁻¹ᵁ L.U j → fr j z ≠ 0) ∧
    ∀ j j' z, ⊤ ≤ x z ⁻¹ᵁ (L.U j ⊓ L.U j') → fr j z = valAt' (x z) (L.U j ⊓ L.U j') (L.g j j').val * fr j' z

def IsSecFn (L : LB X) (x : V → (Sp ℂ ⟶ X)) (fr : L.ι → V → ℂ) (θ : V → ℂ) : Prop :=
  ∃ s : L.Sec, ∀ j z, ⊤ ≤ x z ⁻¹ᵁ L.U j → valAt' (x z) (L.U j) (s.f j) = θ z * fr j z

theorem exists_frame_ratio {L : LB X} (hL : L.IsLB) {x : V → (Sp ℂ ⟶ X)}
    (ho : ∀ j, IsOpen {z | ⊤ ≤ x z ⁻¹ᵁ L.U j}) {fr fr' : L.ι → V → ℂ} (h : IsHolFrame L x fr)
    (h' : IsHolFrame L x fr') : ∃ r : V → ℂ, Differentiable ℂ r ∧ (∀ z, r z ≠ 0) ∧
      ∀ j z, ⊤ ≤ x z ⁻¹ᵁ L.U j → fr' j z = r z * fr j z := by
  have hc : ∀ z, ∃ j, ⊤ ≤ x z ⁻¹ᵁ L.U j := fun z => by
    have h : x z (default : PrimeSpectrum ℂ) ∈ ⨆ i, L.U i := by rw [hL.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h
    exact ⟨i, (top_le_preimage_iff_mem _ _).2 hi⟩
  choose ch hch using hc
  have key : ∀ j z, ⊤ ≤ x z ⁻¹ᵁ L.U j → fr' (ch z) z * (fr (ch z) z)⁻¹ = fr' j z * (fr j z)⁻¹ := fun j z hj => by
    have k := (top_le_preimage_inf _ _ _).2 ⟨hch z, hj⟩
    have n := valAt'_unit_ne_zero _ k (L.g _ _)
    have n' := h.2.1 j z hj
    rw [h.2.2 _ _ _ k, h'.2.2 _ _ _ k]
    field_simp
  refine ⟨fun z => fr' (ch z) z * (fr (ch z) z)⁻¹, fun z => ?_,
    fun z => mul_ne_zero (h'.2.1 _ _ (hch z)) (inv_ne_zero (h.2.1 _ _ (hch z))), fun j z hj => ?_⟩
  · exact ((((h'.1 (ch z)).mul ((h.1 (ch z)).inv (h.2.1 _))).congr fun w hw => key _ w hw).differentiableAt
      ((ho _).mem_nhds (hch z)))
  · simp only [key j z hj]
    rw [inv_mul_cancel_right₀ (h.2.1 j z hj)]

end Frame

theorem exists_unique_half_char (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g)
    {Hm : Matrix (Fin P.g) (Fin P.g) ℂ} {χ : u.Λ → ℂ} {Ef : LinearMap.BilinForm ℤ u.Λ} (hAH : u.IsAH Hm χ)
    (hsec : ∀ θ, u.IsThetaFn Hm χ 1 θ → ∃ s, u.IsFnPow 1 s θ)
    (hE : ∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) (hbij : Function.Bijective Ef) {g : ℕ}
    (F : (Fin g → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ)) (k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef)
    (hform : ∀ z w, hermForm Hm (F z) (F w) = hermForm (imInv τ) (k z) (k w))
    (hΛ : ∀ z, F z ∈ u.Λ ↔ ∃ m n : Fin g → ℤ, k z = (fun i => (m i : ℂ)) + τ *ᵥ fun i => (n i : ℂ)) :
    ∃ a b : Fin g → ℝ, (∀ i, a i = 0 ∨ a i = 1 / 2) ∧ (∀ i, b i = 0 ∨ b i = 1 / 2) ∧
      (∃ fr, IsHolFrame P.L (fun z => (u.ex (F z)).left) fr ∧ (∀ j, fr j 0 = u.fr j 0) ∧
        IsSecFn P.L (fun z => (u.ex (F z)).left) fr fun z => theta a b (k z) τ) ∧
      ∀ a' b' : Fin g → ℝ, (∀ i, a' i = 0 ∨ a' i = 1 / 2) → (∀ i, b' i = 0 ∨ b' i = 1 / 2) →
        ∀ fr, IsHolFrame P.L (fun z => (u.ex (F z)).left) fr →
          (IsSecFn P.L (fun z => (u.ex (F z)).left) fr fun z => theta a' b' (k z) τ) → a' = a ∧ b' = b := by
  have dl : ∀ {m n : ℕ} (T : (Fin m → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)), Differentiable ℂ fun z => T z := fun T =>
    (LinearMap.toContinuousLinearMap T.toLinearMap).differentiable
  have ch := SymmetricSemicharacter.exists_chart u valAt'_rules P.isLB
  have per : ∀ (l : u.Λ) z, u.ex (z + l) = u.ex z := fun l z => CubeValues.ex_add_period u z l l.2
  obtain ⟨a, b, ha, hb, hlaw⟩ := exists_half_char u.Λ Hm χ (k.symm.trans F) hs hp
    (fun z w => by simp [hform]) (fun z => by simp [hΛ])
    (semicharacter_sq_eq_one_of_symmetric P u Hm χ hAH) (fun l m z => by
      obtain ⟨i, hi⟩ := ch z
      have h1 := hAH.2.2.2 (l + m) i z hi
      have h2 := hAH.2.2.2 m i z hi
      have h3 := hAH.2.2.2 l i (z + m) (by rwa [per])
      have e : z + m + l = z + (l + m : u.Λ) := by rw [Submodule.coe_add]; abel
      rw [h3, h1, e] at h2
      refine mul_right_cancel₀ (u.fr_ne i (z + (l + m : u.Λ)) (by rwa [per])) (h2.trans ?_)
      simp only [hermForm]
      ring)
  have hth : u.IsThetaFn Hm χ 1 fun v => canTh τ a b ((k.symm.trans F).symm v) :=
    ⟨(differentiable_canTh hp a b).comp (dl _), fun l z => by rw [pow_one]; exact hlaw l z⟩
  let Q : (Fin g → ℂ) → ℂ := fun ζ => cexp (π / 2 * (ζ ⬝ᵥ imInv τ *ᵥ ζ))
  have hQ : Differentiable ℂ Q := by
    simp only [Q, dotProduct, mulVec]
    fun_prop
  have hfr : IsHolFrame P.L (fun z => (u.ex (F z)).left) fun j z => u.fr j (F z) :=
    ⟨fun j => (u.fr_hol j).comp (dl F).differentiableOn fun _ hz => hz, fun j z hz => u.fr_ne j _ hz,
      fun j j' z hz => u.fr_compat j j' _ hz⟩
  refine ⟨a, b, ha, hb, ⟨fun j z => Q (k z) * u.fr j (F z),
    ⟨fun j => (hQ.comp (dl k)).differentiableOn.mul (hfr.1 j),
      fun j z hz => mul_ne_zero (Complex.exp_ne_zero _) (hfr.2.1 j z hz),
      fun j j' z hz => (congrArg (Q (k z) * ·) (hfr.2.2 j j' z hz)).trans (mul_left_comm _ _ _)⟩,
    fun j => by simp [Q], ?_⟩, fun a' b' ha' hb' fr h ⟨s, hs'⟩ => ?_⟩
  · obtain ⟨s, hs⟩ := hsec _ hth
    refine ⟨secOfPowOne s, fun j z hz => ?_⟩
    refine (valAt'_res _ (powChart_eq (fun _ => j)).ge (powFn s fun _ => j) hz).trans ((hs (fun _ => j) (F z)
      (top_le_preimage_mono _ (powChart_eq (fun _ => j)).ge hz)).trans ?_)
    simp only [LinearEquiv.trans_symm, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply, canTh, thetaChar_eq_theta, pow_one, Q]
    ring
  · obtain ⟨r, hr, hr0, hrf⟩ := exists_frame_ratio P.isLB
      (fun j => (u.hol _ 0).1.preimage (dl F).continuous) hfr h
    let θ : (Fin P.g → ℂ) → ℂ := fun v => theta a' b' (k (F.symm v)) τ * r (F.symm v)
    have hd : Differentiable ℂ fun z => theta a' b' z τ := by
      simpa only [← thetaChar_eq_theta] using differentiable_thetaChar (mem_thetaDomain hp) a' b'
    have hv : ∀ j v, ⊤ ≤ (u.ex v).left ⁻¹ᵁ P.L.U j → valAt' (u.ex v).left (P.L.U j) (s.f j) = θ v * u.fr j v := by
      intro j v hj
      obtain ⟨z, rfl⟩ := F.surjective v
      refine (hs' j z hj).trans ?_
      rw [hrf j z hj]
      simp only [θ, LinearEquiv.symm_apply_apply, _root_.mul_assoc]
    have hθ : u.IsThetaFn Hm χ 1 θ := by
      refine ⟨(hd.comp ((dl k).comp (dl F.symm))).mul (hr.comp (dl F.symm)), fun l z => ?_⟩
      obtain ⟨j, hj⟩ := ch z
      have hj' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ P.L.U j := by rwa [per]
      have e := hv j _ hj'
      rw [per, hv j z hj, hAH.2.2.2 l j z hj] at e
      refine mul_right_cancel₀ (u.fr_ne j _ hj') (e.symm.trans ?_)
      simp only [hermForm]
      ring
    have hne : (fun v => canTh τ a b ((k.symm.trans F).symm v)) ≠ 0 := fun h0 =>
      canTh_ne_zero hs hp a b (funext fun z => by simpa using congrFun h0 ((k.symm.trans F) z))
    have hdep : ¬ LinearIndependent ℂ ![fun v => canTh τ a b ((k.symm.trans F).symm v), θ] := fun hli => by
      have := card_le_pow_of_linearIndependent_theta_principal SiegelNormalForm.exists_normal_form
        (ClassicalTheta.card_le_pow_of_linearIndependent fourierCoeff_unitCube_translate_of_entire_periodic
          (entire_periodic_eq_zero_of_fourierCoeff_eq_zero fourierCoeff_unitCube_translate_of_entire_periodic))
        P.g u.Λ u.discrete u.full Hm χ Ef hAH.1 hAH.2.1 hAH.2.2.1 hE hbij 1 le_rfl 2 _
        (fun i => by fin_cases i; exacts [hth, hθ]) hli
      simp at this
    rw [LinearIndependent.pair_iff' hne] at hdep
    push Not at hdep
    obtain ⟨c, hc⟩ := hdep
    have hcz : ∀ z, theta a' b' z τ = c * Q z * (r (k.symm z))⁻¹ * theta a b z τ := fun z => by
      have e := congrFun hc (F (k.symm z))
      simp only [θ, Pi.smul_apply, smul_eq_mul, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
        LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply, canTh,
        thetaChar_eq_theta] at e
      rw [mul_right_comm, eq_mul_inv_iff_mul_eq₀ (hr0 _), ← e, _root_.mul_assoc]
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact theta_ne_zero (τ := τ) ⟨hs, hp⟩ a' b' (funext fun z => by simp [hcz])
    exact half_char_unique hs hp ha hb ha' hb'
      (((differentiable_const c).mul hQ).mul ((hr.comp (dl k.symm)).inv fun z => hr0 _))
      (fun z => mul_ne_zero (mul_ne_zero hc0 (Complex.exp_ne_zero _)) (inv_ne_zero (hr0 _))) hcz

end GlobalTheory.ThetaPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FixGeometricTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.TUniq

namespace GlobalTheory.TUniq

theorem fix_geometric_torsion {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {S : Scheme.{0}}
    {s : S ⟶ Sp o} (t : TObj g k J b s) (θ : t.A ⟶ t.A) [IsMonHom θ] (hpt : ∀ i, t.pt i ≫ θ = t.pt i)
    (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ t.A) (hy : y ^ k = 1) : y ≫ θ = y := by
  obtain ⟨c, rfl, -⟩ := t.bij K x y hy
  let F : (Over.mk x ⟶ t.A) →* (Over.mk x ⟶ t.A) := IsMonHom.monoidHom θ (Over.mk x)
  refine (map_list_prod F _).trans (congrArg List.prod ?_)
  rw [List.map_ofFn]
  refine congrArg List.ofFn (funext fun i => (map_pow F _ _).trans (congrArg (· ^ (c i).val) ?_))
  show (_ ≫ t.pt i) ≫ θ = _
  rw [Category.assoc, hpt]

theorem tObj_rigid : Out.Laws → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (t : TObj g k J b s) (t' : TObj g k J b s') (f : S ⟶ S'), 3 ≤ k → ∀ φ φ' : t.A.left ⟶ t'.A.left, IsGrpPullback t.A t'.A f φ → IsGrpPullback t.A t'.A f φ' → LBIso t.L (t'.L.pull φ) → LBIso t.L (t'.L.pull φ') → (∀ i, (t.pt i).left ≫ φ = (t.pt i).left ≫ φ') → φ = φ' := by
  intro hL o _ g k J b S S' s s' t t' f hk φ φ' hφ hφ' hl hl' hpt
  obtain ⟨θ, hθ, e⟩ := grpPullback_iso hφ hφ'
  have hη : ∀ i, t.pt i ≫ θ.hom = t.pt i := fun i => by
    apply Over.OverMorphism.ext
    apply hφ'.1.hom_ext
    · rw [Over.comp_left, Category.assoc, e]
      exact hpt i
    · rw [Over.w, Over.w]
  have h₁ : LBIso (t.L.pull θ.hom.left) (t'.L.pull φ) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull t.L _ θ.hom.left rfl) (chartPullSame t'.L _ _ _ θ.hom.left fun _ => e.symm) hl'
  obtain ⟨w, hw⟩ : LBIso t.L (t.L.pull θ.hom.left) :=
    LBIso.trans t.isLB (LB.isLB_pull t'.isLB φ) (LB.isLB_pull t.isLB _) hl h₁.symm
  have hku : IsUnit (k : Γ(S, ⊤)) := by
    simpa using b.unit.map ((Scheme.ΓSpecIso (CommRingCat.of o)).inv ≫ s.appTop).hom
  have := t.ab.comm
  have := t.ab.smooth
  have : Etale (Out.mulA t.A k).left := GrpTangent.etale_id_pow t.A hku
  have h : θ.hom = 𝟙 _ := by
    refine serre_any_base hL t.pol k hk θ hθ (fun _ => ⟨⊤, trivial, ?_⟩)
      (fix_torsion_of_forall_geometric t.A k θ.hom (fix_geometric_torsion t θ.hom hη))
    obtain ⟨u, hu⟩ := gen_of_iso ((isGen_iff w).1 hw) (t.A.hom ⁻¹ᵁ ⊤).ι
    refine gen_chartPull (chartPullOut t.L _ _ _ _ fun n => ?_) u hu
    fin_cases n
    exacts [rfl, (Category.comp_id _).symm]
  rw [← e, h, Over.id_left, Category.id_comp]

end GlobalTheory.TUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.AbLaw

namespace GlobalTheory.AmpleBaseChange

theorem relAmple_of_isPullback {S S' : Scheme.{0}} {B : Over S} [IsProper B.hom] {M : LB B.left}
    (hM : M.IsLB) (hA : Out.RelAmple B M) {t : S' ⟶ S} {X : Scheme.{0}} {π : X ⟶ B.left}
    {f : X ⟶ S'} (h : IsPullback π f B.hom t) : Out.RelAmple (Over.mk f) (M.pull π) := by
  have hp : IsProper (Over.mk f).hom := MorphismProperty.of_isPullback (P := @IsProper) h ‹_›
  refine AmpleLocal.relAmple_of_locally S' (Over.mk f) (M.pull π) (pull_isLB hM π)
    inferInstance inferInstance fun s => ?_
  obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := t s) trivial
  exact ⟨t ⁻¹ᵁ V, hs, PolBaseChange.relAmple_restrict (A' := Over.mk f) h hM hA V hV⟩

theorem isProjBy_smooth_isProper_geometricallyIntegral :
    ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → Out.RelAmple B M → ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S) (X : Scheme.{0}) (π : X ⟶ B.left) (f : X ⟶ Spec (CommRingCat.of R)), IsPullback π f B.hom t → IsProjBy f ∧ Smooth f ∧ IsProper f ∧ GeometricallyIntegral f := by
  intro S B _ M hB hM hA R _ t X π f h
  have := hB.proper
  have hs : Smooth f := MorphismProperty.of_isPullback (P := @Smooth) h hB.smooth
  refine ⟨?_, hs, MorphismProperty.of_isPullback (P := @IsProper) h hB.proper,
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ f hs
      (MorphismProperty.of_isPullback (P := @GeometricallyConnected) h hB.geomConnected)⟩
  obtain ⟨N, -, m, s, hN, hv⟩ := veryAmpleBy_of_relAmple (A := Over.mk f) (pull_isLB hM π)
    (relAmple_of_isPullback hM hA h) (𝟙 X) (Category.id_comp f) (pull_isLB hM π)
    (LBIso.chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (M.pull π) (𝟙 X) (𝟙 X) rfl)
      (PolBaseChange.lbIso_refl (pull_isLB hM π)))
  exact ⟨_, hN, m, s, hv⟩

end GlobalTheory.AmpleBaseChange
end
end

