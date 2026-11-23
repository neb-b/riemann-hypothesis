module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1511
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2912
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0541
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0534
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2834
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1472
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2457
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SamePolarisedDataOfIdempotentFactorUniformisatio
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2343
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2486
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2574
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2577
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2572
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2786
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2804
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMultiplierEqOfPrimitiveAdjointBundle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBiextensionExpansionGeneratorOfTauBimult
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2540
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2616
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2621
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2630
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2925
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2050
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2014
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2933
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupSelfZeroDeRhamAbelian
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

section Helpers

variable {R : Type} [CommRing R]

theorem cup_self_eq_zero_of_wedgeO' {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R} (hW : WedgeO F)
    (x : CatCoh.H1 F) : cup F x x = 0 := by
  obtain ⟨e, he⟩ := hW
  rw [← he]
  have : exteriorPower.ιMulti R 2 ![x, x] = 0 :=
    AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := 1) rfl (by decide)
  rw [this, map_zero]

theorem fn_cupZZ_self_exact {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R} (hW : WedgeO F) (c : cechDeRhamTotalCocyclesOne F) :
    ∃ f, d1 F f = (cupZZ F c c).1.1 := by
  have h := cup_self_eq_zero_of_wedgeO' hW (H1.mk F (cechDeRhamTotalCocyclesOne.fn F c))
  rw [cup_mk, H2.mk_eq_zero] at h
  obtain ⟨f, hf⟩ := h
  exact ⟨f, hf⟩

variable {Y A : Over (Sp R)}

theorem pH2_cupHH_over (f : Y ⟶ A) (a b : HH1 A.hom) :
    deRhamH2Pullback f (cupHH A.hom a b) = cupHH Y.hom (deRhamH1Pullback f a) (deRhamH1Pullback f b) :=
  ((pull_comp_cup_id).2.1 R R _ _ A.hom Y.hom (RingHom.id R) f.left (ovw f)).2.1 a b

theorem toHO1_pH1_over (f : Y ⟶ A) (a : HH1 A.hom) : toHO1 Y.hom (deRhamH1Pullback f a) = pO1 f (toHO1 A.hom a) :=
  ((pull_comp_cup_id).2.1 R R _ _ A.hom Y.hom (RingHom.id R) f.left (ovw f)).2.2 a

theorem pH1_clAll_over (f : Y ⟶ A) (hc : Closed1 (OAff A.hom) = ⊤) (hc' : Closed1 (OAff Y.hom) = ⊤)
    (w : GlobForm A.hom) : deRhamH1Pullback f (clAll (OAff A.hom) hc w) = clAll (OAff Y.hom) hc' (pF f w) :=
  _root_.GlobalTheory.AbCoh.pullHH1_clAll R R _ _ A.hom Y.hom (RingHom.id R) f.left (ovw f) hc hc' w

end Helpers

section Wsum

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem wsum_finAppend {n n' : ℕ} (u v : Fin n → Glob1 F) (u' v' : Fin n' → Glob1 F) :
    wsum F (Fin.append u u') (Fin.append v v') = wsum F u v + wsum F u' v' := by
  funext T
  simp only [wsum, Fin.sum_univ_add, Fin.append_left, Fin.append_right, Pi.add_apply]

theorem wsum_neg_first {n : ℕ} (u v : Fin n → Glob1 F) : wsum F (fun k ↦ -u k) v = -wsum F u v := by
  funext T
  simp only [wsum, Submodule.coe_neg, Pi.neg_apply, map_neg, LinearMap.neg_apply, Finset.sum_neg_distrib]

theorem wsum_eq_add_of_cupSum_eq (hc : Closed1 F = ⊤) (hsur : Function.Surjective (toO F)) {m : ℕ}
    (u₁ v₁ u₂ v₂ u₃ v₃ : Fin m → Glob1 F)
    (h : ∑ k, cupHyp F (clAll F hc (u₁ k)) (clAll F hc (v₁ k)) =
      ∑ k, cupHyp F (clAll F hc (u₂ k)) (clAll F hc (v₂ k)) + ∑ k, cupHyp F (clAll F hc (u₃ k)) (clAll F hc (v₃ k))) :
    wsum F u₁ v₁ = wsum F u₂ v₂ + wsum F u₃ v₃ := by
  have h2 : ∑ k, cupHyp F (clAll F hc (Fin.append (Fin.append u₁ (fun k ↦ -u₂ k)) (fun k ↦ -u₃ k) k))
      (clAll F hc (Fin.append (Fin.append v₁ v₂) v₃ k)) = 0 := by
    rw [Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, map_neg, LinearMap.neg_apply, Finset.sum_neg_distrib]
    rw [h]
    abel
  have h3 := (GlobalTheory.T.cupSum_closedGlobalOneForms_eq_zero_iff_sumWedge R C F hc hsur _ _ _).1 h2
  rw [wsum_finAppend, wsum_finAppend, wsum_neg_first, wsum_neg_first] at h3
  rw [← sub_eq_zero, ← h3]
  abel

end Wsum

theorem cupHH_self_eq_zero : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → ∀ a : HH1 A.hom, cupHH A.hom a a = 0 := by
  intro R _ A _ g hA hs a
  have hb := _root_.GlobalTheory.AbCoh.basic_of_isAbelianScheme R A g hA hs
  have hb2 := _root_.GlobalTheory.AbCoh.basic_of_isAbelianScheme R (A ⊗ A) (g + g) hb.2.2.1 hb.2.2.2
  have hc := _root_.GlobalTheory.AbCoh.closed1_eq_top_of_abelian R A g hA hs
  have hc2 := _root_.GlobalTheory.AbCoh.closed1_eq_top_of_abelian R (A ⊗ A) (g + g) hb.2.2.1 hb.2.2.2
  have hsur := _root_.GlobalTheory.AbCoh.toHO1_surjective R A g hA hs
  have hsur2 := _root_.GlobalTheory.AbCoh.toHO1_surjective R (A ⊗ A) (g + g) hb.2.2.1 hb.2.2.2
  have hW := (_root_.GlobalTheory.AbCoh.oStr R A g hA hs).2.1
  have hP : ∀ x : HH1 A.hom, deRhamH1Pullback μ[A] x = deRhamH1Pullback (fst A A) x + deRhamH1Pullback (snd A A) x := (_root_.GlobalTheory.AbCoh.rank_prim_HH1 R A g hA hs).2
  have hPF : ∀ x : GlobForm A.hom, pF μ[A] x = pF (fst A A) x + pF (snd A A) x := GlobalTheory.T.abelianScheme_globalOneForms_primitive R A g hA hs
  have hax := _root_.GlobalTheory.AbCoh.AxesPull.main R A
  have anti := _root_.GlobalTheory.AbCoh.cupHyp_add_cupHyp_swap R _ (OAff (A ⊗ A).hom)

  have hprim : deRhamH2Pullback μ[A] (cupHH A.hom a a) =
      deRhamH2Pullback (fst A A) (cupHH A.hom a a) + deRhamH2Pullback (snd A A) (cupHH A.hom a a) := by
    rw [pH2_cupHH_over, pH2_cupHH_over, pH2_cupHH_over, hP a]
    have h := anti (deRhamH1Pullback (fst A A) a) (deRhamH1Pullback (snd A A) a)
    simp only [map_add (f := _), LinearMap.add_apply]
    linear_combination (norm := module) h

  obtain ⟨c, rfl⟩ := Hyp1.mk_surjective _ a
  obtain ⟨n, a', w, hz⟩ := _root_.GlobalTheory.AbCoh.hyp2_eq_sum_cup_of_fn_exact R _ (OAff A.hom) hb.1 hb.2.1 hc hsur (cupZZ _ c c) (fn_cupZZ_self_exact hW c)
  rw [← cupHyp_mk] at hz
  change cupHH A.hom _ _ = _ at hz
  set z := cupHH A.hom (Hyp1.mk _ c) (Hyp1.mk _ c)
  clear_value z

  have hcross : ∑ k, (cupHyp (OAff (A ⊗ A).hom) (deRhamH1Pullback (fst A A) (a' k)) (clAll _ hc2 (pF (snd A A) (w k))) +
      cupHyp (OAff (A ⊗ A).hom) (deRhamH1Pullback (snd A A) (a' k)) (clAll _ hc2 (pF (fst A A) (w k)))) = 0 := by
    have h := hprim
    rw [hz] at h
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, pH2_cupHH_over, pH1_clAll_over _ hc hc2, hP, hPF, map_add (f := _), LinearMap.add_apply,
      Finset.sum_add_distrib] at h
    rw [Finset.sum_add_distrib]
    linear_combination (norm := module) h

  have hk : ∀ l : Glob1 (OAff A.hom) →ₗ[R] R, ∑ k, l (w k) • toO (OAff A.hom) (a' k) = 0 := by
    intro l
    have h2 : ∑ k, cupHH (A ⊗ A).hom
        (Fin.append (fun k ↦ deRhamH1Pullback (fst A A) (a' k)) (fun k ↦ deRhamH1Pullback (snd A A) (a' k)) k)
        (clAll _ hc2 (Fin.append (fun k ↦ pF (snd A A) (w k)) (fun k ↦ pF (fst A A) (w k)) k)) = 0 := by
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [← Finset.sum_add_distrib]
      exact hcross
    have h3 := _root_.GlobalTheory.AbCoh.sum_toO_eq_zero_of_sum_cup R _ _ hb2.1 hb2.2.1 hc2 hsur2 (n + n) _ _ h2
      (l ∘ₗ pF (lift (toUnit A ≫ η[A]) (𝟙 A)))
    rw [Fin.sum_univ_add] at h3
    simp only [Fin.append_left, Fin.append_right, LinearMap.comp_apply, (hax.2.1 _).2.2.2.1,
      (hax.2.1 _).2.2.2.2.1, map_zero, zero_smul, Finset.sum_const_zero, add_zero] at h3
    have h4 := congrArg (pO1 (lift (𝟙 A) (toUnit A ≫ η[A]))) h3
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, map_zero] at h4
    simpa only [toHO1_pH1_over, (hax.1 _).1] using h4

  obtain ⟨m, ⟨Φ⟩⟩ := hb.1
  obtain ⟨L, -, hL⟩ := _root_.GlobalTheory.AbCoh.frame_coord R _ (OAff A.hom) hb.2.1 m Φ
  have hu : ∀ i, ∃ u : Glob1 (OAff A.hom), clAll _ hc u = ∑ k, L i (w k) • a' k := by
    intro i
    have hm : ∑ k, L i (w k) • a' k ∈ Fil1 (OAff A.hom) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Fil1, LinearMap.mem_ker, map_sum]
      simpa only [map_smul] using hk (L i)
    rw [Fil1_eq_range] at hm
    obtain ⟨ω, hω⟩ := hm
    refine ⟨ω.1, ?_⟩
    rw [← hω]
    rfl
  choose u hu using hu
  have hz2 : z = ∑ i, cupHyp (OAff A.hom) (clAll _ hc (u i)) (clAll _ hc (Φ.w i)) := by
    rw [hz]
    simp only [hu]
    conv_lhs => enter [2, k]; rw [hL (w k)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    exact Finset.sum_comm

  have hwp : wsum (OAff (A ⊗ A).hom) (fun k ↦ pF μ[A] (u k)) (fun k ↦ pF μ[A] (Φ.w k)) =
      wsum (OAff (A ⊗ A).hom) (fun k ↦ pF (fst A A) (u k)) (fun k ↦ pF (fst A A) (Φ.w k)) +
      wsum (OAff (A ⊗ A).hom) (fun k ↦ pF (snd A A) (u k)) (fun k ↦ pF (snd A A) (Φ.w k)) := by
    have h := hprim
    rw [hz2] at h
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, pH2_cupHH_over, pH1_clAll_over _ hc hc2] at h
    exact wsum_eq_add_of_cupSum_eq _ hc2 hsur2 _ _ _ _ _ _ h
  have hw0 := _root_.GlobalTheory.AbCoh.wsum_eq_zero_of_mul R A g hA hs m u Φ.w hwp
  rw [hz2]
  exact (GlobalTheory.T.cupSum_closedGlobalOneForms_eq_zero_iff_sumWedge R _ _ hc hsur m u Φ.w).2 hw0

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataEighthPowerViaCharacterMaps
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

noncomputable section

namespace GlobalTheory.Mum.PowData

section Power

variable {S : Scheme.{0}} {G G₀ : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀] {r : ℕ}

theorem isMonHom_prod_zpow {K : Type} [Fintype K] (a : K → (G ⟶ G₀)) (ha : ∀ i, IsMonHom (a i)) (n : K → ℤ) :
    IsMonHom (∏ i, a i ^ n i) :=
  isMonHom_of_mul _ fun T x z => by
    rw [comp_prod_zpow, comp_prod_zpow, comp_prod_zpow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have := ha i
    rw [MonObj.mul_comp, mul_zpow]

theorem comp_zpow' {T T' : Over S} (p : T' ⟶ T) (y : T ⟶ G) (n : ℤ) : p ≫ y ^ n = (p ≫ y) ^ n := by
  simpa using comp_prod_zpow (K := Unit) p (fun _ => y) (fun _ => n)

theorem prod_zpow_same {M K : Type} [CommGroup M] [Fintype K] (a : M) (f : K → ℤ) : ∏ i, a ^ f i = a ^ ∑ i, f i := by
  have h := map_prod (zpowersHom M a) (fun i => Multiplicative.ofAdd (f i)) Finset.univ
  rw [← ofAdd_sum] at h
  exact h.symm

theorem exists_vec (q : Fin r → (G ⟶ G₀)) (hq : ∀ u, IsMonHom (q u))
    (huniv : ∀ (T : Over S) (y : Fin r → (T ⟶ G₀)), ∃! x : T ⟶ G, ∀ u, x ≫ q u = y u) (v : Fin r → ℤ) :
    ∃ i : G₀ ⟶ G, IsMonHom i ∧ ∀ b, i ≫ q b = 𝟙 G₀ ^ v b := by
  obtain ⟨i, hi, -⟩ := huniv G₀ fun b => 𝟙 G₀ ^ v b
  refine ⟨i, isMonHom_of_mul _ fun T x z => (huniv T fun b => (x * z) ^ v b).unique (fun b => ?_) (fun b => ?_), hi⟩
  · rw [Category.assoc, hi, comp_zpow', Category.comp_id]
  · have := hq b
    rw [MonObj.mul_comp, Category.assoc, Category.assoc, hi, comp_zpow', comp_zpow', Category.comp_id, Category.comp_id,
      mul_zpow]

theorem lam_of_tens {L₀ : LB G₀.left} (hL : L₀.IsLB) (hΘ : ∃ t : LB.Gen (Theta G₀ L₀), t.IsGen) (q : Fin r → (G ⟶ G₀))
    (hq : ∀ u, IsMonHom (q u)) (W : Matrix (Fin r) (Fin r) ℤ) {c : Pic G.left}
    (hc : c = ∑ a, ∑ b, W a b • lam (cls L₀ hL) (q a) (q b)) {T : Over S} (x y : T ⟶ G) :
    lam c x y = ∑ a, ∑ b, (W + W.transpose) a b • lam (cls L₀ hL) (x ≫ q a) (y ≫ q b) := by
  have hp : ∀ h : T ⟶ G, pull h.left c = ∑ a, ∑ b, W a b • lam (cls L₀ hL) (h ≫ q a) (h ≫ q b) := fun h => by
    rw [hc]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zsmul, pull_lam]
  have hm : ∀ i, (x * y) ≫ q i = x ≫ q i * y ≫ q i := fun i => by
    have := hq i
    exact MonObj.mul_comp _ _ _
  have ho : ∀ i, (1 : T ⟶ G) ≫ q i = 1 := fun i => by
    have := hq i
    exact MonObj.one_comp _
  have e : ∑ i, ∑ j, W i j • lam (cls L₀ hL) (y ≫ q i) (x ≫ q j) =
      ∑ i, ∑ j, W.transpose i j • lam (cls L₀ hL) (x ≫ q i) (y ≫ q j) := by
    rw [Finset.sum_comm]
    simp only [Matrix.transpose_apply, lam_comm _ (y ≫ _)]
  conv_lhs => rw [lam]
  simp only [hp, hm, ho, lam_one_left, lam_mul_left hL hΘ, RosatiTens.lam_mul_right hL hΘ, smul_add,
    Finset.sum_add_distrib, Matrix.add_apply, add_smul, smul_zero, Finset.sum_const_zero]
  rw [e]
  abel

end Power

theorem exists_tens (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) (D D₀ : DegData R (maximalIdeal R))
    (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀]
    (hG : IsSemiAbelian G) (hG₀ : IsSemiAbelian G₀) (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀)
    {r : ℕ} (W N : Matrix (Fin r) (Fin r) ℤ) (hN : (W + W.transpose) * N = 1) (q : Fin r → (G ⟶ G₀)) (hq : ∀ u, IsMonHom (q u))
    (huniv : ∀ (T : Over (Sp R)) (y : Fin r → (T ⟶ G₀)), ∃! x : T ⟶ G, ∀ u, x ≫ q u = y u)
    (hc : cls U.LG.L U.LG.isLB = ∑ a, ∑ b, W a b • lam (cls U₀.LG.L U₀.LG.isLB) (q a) (q b))
    (h : Fin r → (D₀.toPre.X →+ D.toPre.X)) (hh : ∀ u, OnTorus U.toUnifPre U₀.toUnifPre (q u) (h u))
    (xe : D.toPre.X ≃+ (Fin r → D₀.toPre.X))
    (hxe : ∀ mu, xe.symm mu = ∑ u, h u (∑ v, (W + W.transpose) u v • mu v)) :
    ∃ T : Tens D₀.toPre D.toPre W, T.xe = xe := by
  have hA := hR.1
  set Sm := W + W.transpose with hSm
  have hSs : ∀ a b, Sm a b = Sm b a := fun a b => by simp [hSm, add_comm]
  have hN' : N * Sm = 1 := mul_eq_one_comm.1 hN
  have SN : ∀ a c, ∑ b, Sm a b * N b c = if a = c then 1 else 0 := fun a c => by
    rw [← Matrix.mul_apply, hN, Matrix.one_apply]
  have NS : ∀ a c, ∑ b, N a b * Sm b c = if a = c then 1 else 0 := fun a c => by
    rw [← Matrix.mul_apply, hN', Matrix.one_apply]
  have hΘ₀ : ∃ t : LB.Gen (Theta G₀ U₀.LG.L), t.IsGen := ⟨U₀.cubG.t, U₀.cubG.isGen⟩
  have hΘ : ∃ t : LB.Gen (Theta G U.LG.L), t.IsGen := ⟨U.cubG.t, U.cubG.isGen⟩
  have P := fun {T : Over (Sp R)} (x y : T ⟶ G) => lam_of_tens U₀.LG.isLB hΘ₀ q hq W hc x y
  rw [← hSm] at P
  have zr : ∀ {T : Over (Sp R)} (x z : T ⟶ G₀) (n : ℤ), lam (cls U₀.LG.L U₀.LG.isLB) x (z ^ n) =
      n • lam (cls U₀.LG.L U₀.LG.isLB) x z := fun x z n => by
    simpa using RosatiTens.lam_prod_right (κ := Unit) U₀.LG.isLB hΘ₀ x (fun _ => z) (fun _ => n)
  choose j hj jq using fun a => exists_vec q hq huniv fun b => N b a
  choose inc hinc iq using fun a => exists_vec q hq huniv fun b => if a = b then 1 else 0
  let rr' : Fin r → (G ⟶ G₀) := fun a => ∏ b, q b ^ Sm a b
  have hrr : ∀ a, IsMonHom (rr' a) := fun a => isMonHom_prod_zpow q hq _
  have iq₁ : ∀ a, inc a ≫ q a = 𝟙 _ := fun a => by rw [iq, if_pos rfl, zpow_one]
  have jr : ∀ a, j a ≫ rr' a = 𝟙 _ := fun a => by
    simp only [rr', comp_prod_zpow, jq, ← zpow_mul, prod_zpow_same, mul_comm (N _ _), SN]
    simp
  have adjq : ∀ a, AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) (q a) (j a) := fun a T x z => by
    simp only [P, Category.assoc, jq, comp_zpow', Category.comp_id, zr, smul_smul, ← Finset.sum_smul, SN]
    simp
  have adjr : ∀ a, AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) (rr' a) (inc a) := fun a T x z => by
    simp only [P, Category.assoc, iq, comp_zpow', Category.comp_id, zr, smul_smul, ← Finset.sum_smul, rr', comp_prod_zpow,
      RosatiTens.lam_prod_left U₀.LG.isLB hΘ₀]
    simp [hSs a]
  have hNs : ∀ a b, N a b = N b a := fun a b => by
    have e₁ : Sm.transpose = Sm := Matrix.ext fun a b => hSs b a
    have e₂ : N.transpose * Sm = 1 := by rw [← e₁, ← Matrix.transpose_mul, hN, Matrix.transpose_one]
    have e₃ : N.transpose = N := by rw [← Matrix.mul_one N.transpose, ← hN, ← Matrix.mul_assoc, e₂, Matrix.one_mul]
    exact congrFun (congrFun e₃ b) a
  let f : G ⟶ G := ∏ ab : Fin r × Fin r, (q ab.2 ≫ j ab.1) ^ W ab.1 ab.2
  let f' : G ⟶ G := ∏ ab : Fin r × Fin r, (q ab.1 ≫ j ab.2) ^ W ab.1 ab.2
  have hf : IsMonHom f := isMonHom_prod_zpow _ (fun ab => inferInstance) _
  have hf' : IsMonHom f' := isMonHom_prod_zpow _ (fun ab => inferInstance) _
  have ff : f * f' = 𝟙 G := (huniv G q).unique (fun c => by
    simp only [f, f', MonObj.mul_comp, prod_zpow_comp, Category.assoc, jq, comp_zpow', Category.comp_id, ← zpow_mul]
    rw [Fintype.prod_prod_type, Fintype.prod_prod_type, Finset.prod_comm, ← Finset.prod_mul_distrib]
    simp only [prod_zpow_same, ← zpow_add, ← Finset.sum_add_distrib, ← mul_add]
    have : ∀ b, ∑ a, N c a * (W a b + W b a) = if c = b then 1 else 0 := fun b => NS c b
    simp [this]) (fun c => Category.id_comp _)
  have adjf : AdjCls (cls U.LG.L U.LG.isLB) (cls U.LG.L U.LG.isLB) f f' := fun T x z => by
    simp only [f, f', comp_prod_zpow, RosatiTens.lam_prod_left U.LG.isLB hΘ, RosatiTens.lam_prod_right U.LG.isLB hΘ]
    refine Finset.sum_congr rfl fun ab _ => congrArg _ ?_
    rw [← Category.assoc, ← Category.assoc, adjq, lam_comm _ _ z, adjq, lam_comm]
  have primf : cls U.LG.L U.LG.isLB = lam (cls U.LG.L U.LG.isLB) (𝟙 G) f := by
    simp only [f, RosatiTens.lam_prod_right U.LG.isLB hΘ, adjq _ _, Category.id_comp, Fintype.sum_prod_type]
    exact hc
  have idq : ∏ a, (q a ≫ inc a) ^ (1 : ℤ) = 𝟙 G := (huniv G q).unique (fun c => by
    simp only [prod_zpow_comp, Category.assoc, iq, comp_zpow', Category.comp_id]
    simp) (fun c => Category.id_comp _)
  choose qB hqB oq using fun a => exists_abelian_hom R _ hA D D₀ A A₀ G G₀ U.toUnifPre U₀.toUnifPre (q a) (hq a)
  choose jB hjB oj using fun a => exists_abelian_hom R _ hA D₀ D A₀ A G₀ G U₀.toUnifPre U.toUnifPre (j a) (hj a)
  choose iB hiB oi using fun a => exists_abelian_hom R _ hA D₀ D A₀ A G₀ G U₀.toUnifPre U.toUnifPre (inc a) (hinc a)
  choose k tk using fun a => unifPre_hom_character_const R _ hA D₀ D A₀ A G₀ G U₀.toUnifPre U.toUnifPre (j a) (hj a)
  have un := over₀_onTorus_unique R _ hA D D A A G G U.toUnifPre U.toUnifPre
  have un₀ := over₀_onTorus_unique R _ hA D₀ D₀ A₀ A₀ G₀ G₀ U₀.toUnifPre U₀.toUnifPre
  have oz : ∀ m : ℤ, Over₀ U₀.toUnifPre U₀.toUnifPre (𝟙 G₀ ^ m) (𝟙 _ ^ m) := fun m => by
    simpa using _root_.GlobalTheory.Mum.PowData.over₀_prod_zpow R _ D₀ D₀ A₀ A₀ G₀ G₀ U₀.toUnifPre U₀.toUnifPre Unit (fun _ => m) _ _ fun _ => FactorPol.over_id
  have tz : ∀ m : ℤ, OnTorus U₀.toUnifPre U₀.toUnifPre (𝟙 G₀ ^ m) (fun χ => m • χ) := fun m => by
    simpa using _root_.GlobalTheory.Mum.PowData.onTorus_prod_zpow R _ D₀ D₀ A₀ A₀ G₀ G₀ U₀.toUnifPre U₀.toUnifPre Unit (fun _ => m) _ _ fun _ => FactorPol.onTorus_id
  have iqB : ∀ a b, iB a ≫ qB b = 𝟙 _ ^ (if a = b then 1 else 0 : ℤ) := fun a b =>
    (un₀ _).1 _ _ (iq a b ▸ FactorPol.over_comp (oi a) (oq b)) (oz _)
  have jqB : ∀ a b, jB a ≫ qB b = 𝟙 _ ^ N b a := fun a b =>
    (un₀ _).1 _ _ (jq a b ▸ FactorPol.over_comp (oj a) (oq b)) (oz _)
  have idB : ∏ a, (qB a ≫ iB a) ^ (1 : ℤ) = 𝟙 _ := (un _).1 _ _
    (idq ▸ _root_.GlobalTheory.Mum.PowData.over₀_prod_zpow R _ D D A A G G U.toUnifPre U.toUnifPre _ (fun _ => 1) _ _ fun a => FactorPol.over_comp (oq a) (oi a))
    FactorPol.over_id
  have kh : ∀ a b χ, k a (h b χ) = N b a • χ := fun a b =>
    congrFun ((un₀ _).2 _ _ (jq a b ▸ FactorPol.onTorus_comp (tk a) (hh b)) (tz _))
  have xk : ∀ y a, xe y a = k a y := fun y a => by
    obtain ⟨mu, rfl⟩ := xe.symm.surjective y
    rw [AddEquiv.apply_symm_apply, hxe]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, kh, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, hNs _ a, NS]
    simp
  have extB : ∀ {T : Over (Sp R)} (x x' : T ⟶ D.toPre.P.A), (∀ a, x ≫ qB a = x' ≫ qB a) → x = x' := fun x x' e => by
    rw [← Category.comp_id x, ← Category.comp_id x', ← idB, comp_prod_zpow, comp_prod_zpow]
    simp only [← Category.assoc, e]
  have per := fun a => _root_.GlobalTheory.Mum.PowData.periodRel_of_adj R hR D D₀ A A₀ G G₀ hG hG₀ U U₀ (q a) (inc a) (j a) (hinc a) (hj a) (iq₁ a) (adjq a) (qB a) (h a)
    (k a) ⟨hq a, hqB a, oq a, hh a⟩ (tk a)
  have adjB := fun a => _root_.GlobalTheory.Mum.PowData.adjCls_abelianPart R hR D D₀ A A₀ G G₀ hG hG₀ U U₀ (q a) (rr' a) (inc a) (j a) (hq a) (hrr a) (hinc a) (hj a) (iq₁ a)
    (jr a) (adjq a) (adjr a) (qB a) (jB a) (hqB a) (hjB a) (oq a) (oj a)
  have cz : ∀ (m : ℤ) χ, D₀.toPre.c (m • χ) = D₀.toPre.c χ ^ m := fun m χ => by
    let φ : Multiplicative D₀.toPre.X →* (𝟙_ (Over (Sp R)) ⟶ D₀.toPre.P.A) :=
      MonoidHom.mk' (fun y => D₀.toPre.c y.toAdd) fun a b => D₀.toPre.c_add _ _
    exact map_zpow φ (Multiplicative.ofAdd χ) m
  have ch : ∀ a χ, D.toPre.c (h a χ) = D₀.toPre.c χ ≫ jB a := fun a χ => extB _ _ fun b => by
    rw [← (per b).1, kh, cz, Category.assoc, jqB, comp_zpow', Category.comp_id, hNs]
  obtain ⟨w, hw, hψ⟩ := _root_.GlobalTheory.Mum.PowData.tens_iso_psi R D.toPre D₀.toPre r W qB jB (fun a => h a) (fun a => k a) ch (fun a => (per a).1)
    (fun a => (per a).2) (fun a => _root_.GlobalTheory.Mum.PowData.cmpTwo_of_adjCls R _ _ _ _ (hqB a) (hjB a) (adjB a)) (_root_.GlobalTheory.Mum.PowData.expand_of_tauBimult R _ D.tau_bimult _ _ _ _ _)
    (_root_.GlobalTheory.PrimAdj.primVal_of_adj R hR D A G hG U f f' hf hf' ff adjf primf _ _
      (_root_.GlobalTheory.Mum.PowData.over₀_prod_zpow R _ D D A A G G U.toUnifPre U.toUnifPre _ _ _ _ fun ab => FactorPol.over_comp (oq ab.2) (oj ab.1))
      (_root_.GlobalTheory.Mum.PowData.onTorus_prod_zpow R _ D D A A G G U.toUnifPre U.toUnifPre _ _ _ _ fun ab => FactorPol.onTorus_comp (hh ab.1) (tk ab.2)))
  have lf : ∀ {T : Over (Sp R)} (y : Fin r → (T ⟶ D₀.toPre.P.A)) b, (∏ a, (y a ≫ iB a) ^ (1 : ℤ)) ≫ qB b = y b := fun y b => by
    simp only [prod_zpow_comp, Category.assoc, iqB, comp_zpow', Category.comp_id]
    simp
  exact ⟨{ pr := qB, pr_hom := hqB, xe := xe, w := w, w_gen := hw
           lim := Fan.IsLimit.mk _ (fun s => (∏ a, (s.proj a ≫ iB a) ^ (1 : ℤ) : s.pt ⟶ D.toPre.P.A)) (fun s b => lf _ b)
             (fun s m hm => extB _ _ fun b => (hm b).trans (lf _ b).symm)
           c_pr := fun z a => by rw [xk, (per a).1]
           psi := fun y z J J' hJ hJ' => (hψ y z J J' hJ hJ').trans (congrArg _ (Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => by rw [xk, xk])) }, rfl⟩

end GlobalTheory.Mum.PowData


open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
  ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Eq8 in
theorem GlobalTheory.Mum.PowData.sharpRef_of_characters : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁), IsCN V₁ → Function.Injective ρ → ρ.Finite → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X), Refines Q ρ D₀.toPre e₀ → ∀ (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left) (φ₂ : (G2 c.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback c.A F.univ.A y φc → IsSquare φc φ₂ → LBIso c.P (F.univ.P.pull φ₂) → (∀ a, (c.lev a).left ≫ φc = y ≫ (F.univ.lev a).left) → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing V₁))) (y' : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y' a) → LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → (∀ (T' : Over (Sp V₁)) (y' : Fin 8 → (T' ⟶ G₀)), ∃! x : T' ⟶ G, ∀ u, x ≫ q u = y' u) → (∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc) → ∀ c : Fin 8 → (D₀.toPre.X →+ D.toPre.X), (∀ u, TorMatch U₀ U (RingHom.id V₁) (q u).left (c u)) → ∀ e : (Fin 8 → Q.X) ≃+ D.toPre.X, (∀ mu, e mu = ∑ u, c u (e₀.symm (∑ v, (W + W.transpose) u v • mu v))) → SharpRef W Q ρ D.toPre e := by
  intro g n o _ ζ F W hW V _ _ _ Q V₁ _ _ _ ρ hCN _ _ D₀ e₀ hRef G₀ _ _ A₀ U₀ y α α₂ hG₀ hα hsq hlb P c φc φ₂ hφ hφsq hφlb _ pr _ _
    hPL G _ _ hG D U q hq huniv hcomp ch hch e he
  have hR : Base V₁ := ⟨⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩, hCN.2.2.2⟩
  have hc := GlobalTheory.T.uniformisedEighthPower_bundleClass_eq_sum g n o ζ F W V₁ hR D D₀ P A₀ G G₀ hG U U₀ y α α₂ hα hsq hlb c φc φ₂ hφ hφsq hφlb pr hPL q hq hcomp
  have hh : ∀ u, OnTorus U.toUnifPre U₀.toUnifPre (q u) (ch u) := fun u => by
    obtain ⟨h, th⟩ := unifPre_hom_character_const V₁ _ hR.1 D D₀ P A₀ G G₀ U.toUnifPre U₀.toUnifPre (q u) (hq u)
    rwa [torMatch_unique V₁ hR G₀ hG₀ D₀ A₀ U₀ V₁ hR G hG D P U _ _ Function.injective_id _ _ (hch u)
      (_root_.GlobalTheory.Poinc.HomTorChar.torMatch_of_onTorus V₁ hR D D₀ P A₀ G G₀ hG hG₀ U U₀ (q u) (hq u) h th)]
  obtain ⟨T, hT⟩ := GlobalTheory.Mum.PowData.exists_tens V₁ hR D D₀ P A₀ G G₀ hG hG₀ U U₀ W (W + W.transpose)⁻¹
    (Matrix.mul_nonsing_inv _ (by rw [hW.2]; exact isUnit_one)) q hq huniv hc ch hh
    (e.symm.trans (AddEquiv.piCongrRight fun _ => e₀.symm)) (fun mu => by
      show e (fun a => e₀ (mu a)) = _
      simp [he])
  refine _root_.GlobalTheory.Mum.PowData.sharpRef_of_tens W V Q V₁ ρ D₀.toPre D.toPre e₀ hRef T e fun mu a => ?_
  simp [hT]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescSt5
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc GlobalTheory.SiegJoin

namespace GlobalTheory.SiegDescent

theorem descSt5 : GlobalTheory.SiegJoin.DescSt5 := by
  intro g _ φ n hn _ F Z z i d S π j _ BD hB hC
  obtain ⟨J, -, -, -, ⟨hN, -⟩, hP, hD, -⟩ := hB
  have hn0 : n ≠ 0 := by omega
  haveI : IsDedekindDomain (cycAway n) := (arBase_cycAway n hn0).1
  haveI : IsProper (π ≫ z) := GlobalTheory.SchemeWords.isProper_of_isProjOver hP
  haveI : IsNoetherianRing (CommRingCat.of (cycAway n)) := inferInstanceAs (IsNoetherianRing (cycAway n))
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ z)
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (π ≫ z)
  haveI : AlgebraicGeometry.IsNoetherian S := {}
  have hj : IsDominant j := ⟨hD⟩
  have hd : SmoothOfRelativeDimension g F.univ.A.hom :=
    GlobalTheory.SiegSharpCover.smoothDim F.univ (by omega) (cycBase hn0).ζ.isUnit (isUnit_natCast hn0)
  obtain ⟨G, _, e, hG, he, hπ⟩ := _root_.GlobalTheory.Desc.descent_semiAbelian F.X S ((GlobalTheory.isNormalScheme_iff_pred S).1 hN) j hj F.univ.A F.univ.ab F.univ.diag (pull_isLB F.univ.isLB _)
    F.princ.1 fun x => ⟨(exists_chart (hC x)).choose⟩
  obtain ⟨h₁, h₂⟩ := _root_.GlobalTheory.DescAb.abLocus_eq_range_and_relDim F.X S j hj F.univ.A G e g F.univ.ab hd hG he fun x => by
    obtain ⟨C, hab⟩ := exists_chart (hC x)
    obtain ⟨p, hp, -⟩ := hπ x C
    exact ⟨C.R, inferInstance, inferInstance, C.ξ, C.G, inferInstance, p, C.centre, hp, hab⟩
  exact ⟨G, inferInstance, e, hG, h₂, he, h₁⟩

end GlobalTheory.SiegDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeSchemeRepresentingPolarizedHomsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteType_scheme_representing_polarizedHoms : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → Out.RelAmple A L → Out.RelAmple B M → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  first | (exact @GlobalTheory.HomFixAff.exists_homFixRep_finiteType) | (exact GlobalTheory.HomFixAff.exists_homFixRep_finiteType) | (intros; apply GlobalTheory.HomFixAff.exists_homFixRep_finiteType  <;> assumption)
end

