module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0194
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2286
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsStableBasOfPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2263
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianSchemeAway
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2284
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2039

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVRComparisonPreUniformised
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TraitCompare

open GlobalTheory.UU GlobalTheory.LN


set_option maxHeartbeats 1000000 in
theorem exists_cmp_under : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), EvenOn U.P → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (φ : R →+* V) (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (G' : Over (Sp V)) (_ : GrpObj G') (_ : IsCommMonObj G') (U' : GlobalTheory.UU.PreU (maximalIdeal V) D'.toPre A' G') (U₀ : Unif (maximalIdeal V) D' A' G') (F : G'.left ⟶ G.left) (_ : GlobalTheory.LN.Cmp φ U U' F), GlobalTheory.LN.CDvr V ∧ Function.Injective φ ∧ (maximalIdeal V).comap φ = maximalIdeal R ∧ GlobalTheory.LN.Under U' U₀.toUnifPre := by
  intro R _ _ _ hB D A G _ _ U hE
  obtain ⟨⟨hL, hL2, -, -, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  have hEg := GlobalTheory.LN.ega_holds
  have hU := GlobalTheory.uniformisation_dvr_unconditional
  have := hB.1.1
  have := hB.2
  obtain ⟨V, _, _, _, φ, hV, hφ, hc⟩ := GlobalTheory.PrimeUnif.exists_cdvr R (maximalIdeal R)
  have := hV.1
  have hBV : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV.2.1⟩
  have hle : (maximalIdeal R).map φ ≤ maximalIdeal V := Ideal.map_le_iff_le_comap.2 hc.ge
  have := U.gen_hom
  obtain ⟨A', s, w, hw⟩ :=
    GlobalTheory.Mum.TraitSetting.exists_setting_of_evenOn hL U.P U.semi hE A U.gen ⟨U.wA, U.wA_gen⟩ hV φ hφ hc.ge
  obtain ⟨D', U₀, hLG, -, -⟩ := hU V A' _ s
  obtain ⟨U', hU'⟩ := (GlobalTheory.LN.PreForm.under_exists_and_expands hL hL2 V _ D' A' _ s.semi).1 U₀.toUnifPre
  have := s.semi.smooth
  obtain ⟨w', hw'⟩ := GlobalTheory.PrimeUnif.isCPMap_of_eq hL.globalFns s.gen s.P U'.P (hU'.2.1.trans hLG) hw
  obtain ⟨C, -⟩ := _root_.GlobalTheory.LN.PreCompare.exists_cmp hL hL2 hEg R V _ _ hB.1 hBV (maximalIdeal.isMaximal V).ne_top φ hle D D'.toPre A A'
    G _ U U' _ (isGrpPullback_pullback G _) w' hw'
  exact ⟨V, _, _, _, φ, D', A', _, _, _, U', U₀, _, C, hV, hφ, hc, hU'⟩

end GlobalTheory.Mum.TraitCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteTraitOverClosedPointModification
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem exists_cDvr_injective_isLocalHom (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [CharZero A] :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (ψ : A →+* W),
      GlobalTheory.LN.CDvr W ∧ Function.Injective ψ ∧ IsLocalHom ψ := by
  by_cases h : IsField A
  · letI := h.toField
    refine ⟨PowerSeries A, inferInstance, inferInstance, inferInstance, PowerSeries.C, ⟨inferInstance, ?_, ?_⟩,
      RingHom.injective _, inferInstance⟩
    · rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
    · exact charZero_of_injective_ringHom (f := PowerSeries.C (R := A)) (RingHom.injective _)
  · obtain ⟨O, _, _, _, _, φ, h1, h2⟩ := exists_complete_discreteValuationRing_dominating A h
    exact ⟨O, inferInstance, inferInstance, inferInstance, φ,
      ⟨inferInstance, inferInstance, charZero_of_injective_ringHom h1⟩, h1, h2⟩

theorem exists_trait_over_closedPoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (M : Modif R) (x₀ : M.S), M.π x₀ = closedPoint R →
      ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W) (ξ : Sp W ⟶ M.S),
        GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ ξ ≫ M.π = spMap φ ∧ ξ (closedPoint W) = x₀ := by
  intro R _ _ _ hB M x₀ hx
  have : IsNoetherianRing R := hB.1.1
  have : CharZero R := hB.2
  have := M.integral
  have := M.proper
  have := LocallyOfFiniteType.isLocallyNoetherian M.π
  obtain ⟨θ, hθ⟩ := Spec.map_surjective (M.S.fromSpecStalk x₀ ≫ M.π)
  have hpt : ∀ q, (Spec.map θ) q = M.π (M.S.fromSpecStalk x₀ q) := fun q => by
    rw [hθ, Scheme.Hom.comp_apply]
  have hloc : IsLocalHom θ.hom := by
    apply ((local_hom_tfae θ.hom).out 1 5).2
    have e := hpt (closedPoint (M.S.presheaf.stalk x₀) : Spec (M.S.presheaf.stalk x₀))
    rw [Scheme.fromSpecStalk_closedPoint, hx] at e
    exact congrArg PrimeSpectrum.asIdeal e
  have hinj : Function.Injective θ.hom := by
    let pt : Sp (FractionRing R) := closedPoint (FractionRing R)
    obtain ⟨q, hq⟩ : M.gp pt ∈ Set.range (M.S.fromSpecStalk x₀) := by
      rw [Scheme.range_fromSpecStalk]
      show _ ⤳ x₀
      rw [specializes_iff_mem_closure]
      have hd := M.dominant.denseRange
      have hs : Set.range M.gp.base ⊆ {M.gp pt} := by
        rintro _ ⟨y, rfl⟩
        rw [Subsingleton.elim y (closedPoint _)]
        rfl
      exact closure_mono hs (hd.closure_range ▸ Set.mem_univ x₀)
    have h1 : (Spec.map θ) q = jK R pt := by
      rw [hpt, hq]
      exact (Scheme.Hom.comp_apply M.gp M.π pt).symm.trans (by rw [M.gp_π])
    have h2 := congrArg PrimeSpectrum.asIdeal h1
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have h3 : a ∈ Ideal.comap θ.hom q.asIdeal := by
      rw [Ideal.mem_comap, ha]; exact Ideal.zero_mem _
    have h4 : algebraMap R (FractionRing R) a ∈ maximalIdeal (FractionRing R) := by
      have h5 : a ∈ ((jK R) pt).asIdeal := by
        rw [← h2]; exact h3
      exact h5
    have h6 : algebraMap R (FractionRing R) a = 0 := by
      by_contra hne
      exact (maximalIdeal.isMaximal _).ne_top (Ideal.eq_top_of_isUnit_mem _ h4 (isUnit_iff_ne_zero.2 hne))
    exact IsFractionRing.injective R (FractionRing R) (h6.trans (map_zero _).symm)
  have : CharZero (M.S.presheaf.stalk x₀) := charZero_of_injective_ringHom hinj
  obtain ⟨W, _, _, _, ψ, hW, hψi, hψl⟩ := exists_cDvr_injective_isLocalHom (M.S.presheaf.stalk x₀)
  refine ⟨W, inferInstance, inferInstance, inferInstance, ψ.comp θ.hom, spMap ψ ≫ M.S.fromSpecStalk x₀, hW,
    hψi.comp hinj, RingHom.isLocalHom_comp _ _, ?_, ?_⟩
  · rw [Category.assoc, ← hθ, ← Spec.map_comp]
    rfl
  · exact (Scheme.Hom.comp_apply _ _ _).trans
      (Eq.trans (congrArg (M.S.fromSpecStalk x₀) (IsLocalRing.comap_closedPoint ψ))
        (Scheme.fromSpecStalk_closedPoint (x := x₀)))

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubeStepGeneratorTensorPowerPairs
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.CubeStep

section Gens

variable {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]

def zpowGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (n : ℤ) :
    LB.Gen (LB.LinComb L φ (fun k => n * ε k)) where
  s := fun j => t.s j ^ n

theorem zpowGen_isGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (n : ℤ) :
    (zpowGen L φ ε t n).IsGen := fun i j => by
  refine ((map_zpow _ _ _).trans ((congrArg (· ^ n) (ht i j)).trans (mul_zpow _ _ _))).trans
    (congrArg₂ (· * ·) ?_ (map_zpow _ _ _).symm)
  exact (Finset.prod_zpow _ _ _).symm.trans (Finset.prod_congr rfl fun k _ =>
    (zpow_mul _ _ _).symm.trans (congrArg _ (mul_comm _ _)))

theorem val_zpowGen {Z : Scheme.{0}} (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (n : ℤ)
    (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) : val (zpowGen L φ ε t n) r z J = val t r z J ^ n :=
  map_zpow _ _ _

theorem finProdGen_isGen {I : Type} [Fintype I] (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) (ht : ∀ i, (t i).IsGen) : (GeneratorPullback.finProdGen L φ ε t).IsGen := by
  intro (j : I × K → L.ι) (j' : I × K → L.ι)
  refine unit_ext fun y hy => ?_
  have v : ∀ j : I × K → L.ι, y ∈ LB.wchart L (fun p : I × K => φ p.1 p.2) j →
      gm (𝟙 Y) y (LB.wchart L (fun p : I × K => φ p.1 p.2) j) ((GeneratorPullback.finProdGen L φ ε t).s j) =
        ∏ i, gm (𝟙 Y) y (LB.wchart L (φ i) (fun k => j (i, k))) ((t i).s (fun k => j (i, k))) := fun j hj =>
    (map_prod _ _ _).trans (Finset.prod_congr rfl fun _ _ => gm_res (𝟙 Y) y _ hj _)
  refine ((gm_res (𝟙 Y) y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2) ((gm_res (𝟙 Y) y _ hy _).trans (v j' hy.2)))).symm)
  rw [Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => gen_trans (ht i) (𝟙 Y) y
    (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 (i, k)) (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 (i, k))

theorem val_finProdGen {I : Type} [Fintype I] (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    val (GeneratorPullback.finProdGen L φ ε t) r z J = ∏ i, val (t i) r z J :=
  (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ =>
    gm_res r z _ (hJ.mem (fun p : I × K => φ p.1 p.2) r) _)

end Gens

theorem prod_zpow_mul {K U : Type} [Fintype K] [CommGroup U] (f : K → U) (e : K → ℤ) (n : ℤ) :
    ∏ k, f k ^ (n * e k) = (∏ k, f k ^ e k) ^ n := by
  rw [← Finset.prod_zpow]
  exact Finset.prod_congr rfl fun k _ => by rw [← zpow_mul, mul_comm]

theorem prod_finset_fin_two_ulift_expand {U : Type} [CommMonoid U] (f : ULift.{0} (Finset (Fin 2)) → U) :
    ∏ I, f I = f ⟨{0, 1}⟩ * f ⟨{0}⟩ * f ⟨{1}⟩ * f ⟨∅⟩ := by
  refine (Fintype.prod_equiv Equiv.ulift f (fun I => f ⟨I⟩) (fun _ => rfl)).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  ac_rfl

end GlobalTheory.Mum.CubeStep

namespace GlobalTheory.Mum.CubeStep

variable {S : Scheme.{0}} {B B' : Over S} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B']

theorem groupSchemePartialSum_pair_both : psum B' (x2 B') {0, 1} = fst B' B' * snd B' B' := congrArg (fst B' B' * ·) (_root_.mul_one _)
theorem psum0 : psum B' (x2 B') {0} = fst B' B' := _root_.mul_one _
theorem psum1 : psum B' (x2 B') {1} = snd B' B' := _root_.mul_one _
theorem psumE : psum B' (x2 B') ∅ = 1 := rfl

theorem pair_eq {r : ℕ} (pr : Fin r → (B' ⟶ B)) (hpr : ∀ i, IsMonHom (pr i)) (w : ℤ) (i j : Fin r) {U : Type}
    [CommGroup U] (h : ((G2 B').left ⟶ B.left) → U) :
    ∏ k : thK.{0} ⊕ (thK.{0} ⊕ thK.{0}), h (Sum.elim
      (fun k => (lift (fst B' B' ≫ pr i) (lift (snd B' B' ≫ pr i) ((fst B' B' ≫ pr j) * (snd B' B' ≫ pr j)))).left ≫
        thφ B (x3 B) k)
      (Sum.elim (fun k => (lift (fst B' B' ≫ pr j) (lift (snd B' B' ≫ pr j) (fst B' B' ≫ pr i))).left ≫ thφ B (x3 B) k)
        (fun k => (lift (fst B' B' ≫ pr j) (lift (snd B' B' ≫ pr j) (snd B' B' ≫ pr i))).left ≫ thφ B (x3 B) k)) k) ^
      (-w * Sum.elim thε (Sum.elim thε thε) k) =
    (∏ k : Fin 4, h (GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr i) (snd B' B' ≫ pr j) k) ^ Oε k) ^ w *
    (∏ k : Fin 4, h (GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr j) (snd B' B' ≫ pr i) k) ^ Oε k) ^ w *
    (∏ k : Fin 4, ∏ I : ULift.{0} (Finset (Fin 2)),
      h ((psum B' (x2 B') I.down).left ≫ tensφ pr ((i, j), k)) ^ ((-1) ^ (2 - I.down.card) * Oε k)) ^ (-w) := by
  haveI := hpr i
  haveI := hpr j
  refine (prod_zpow_mul (U := U) _ (Sum.elim thε (Sum.elim thε thε)) (-w)).trans ?_
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [prod_cub, prod_cub, prod_cub]
  simp only [prod_finset_fin_two_ulift_expand, Fin.prod_univ_four, GlobalTheory.PolDeg.lamPts, tensφ, Oε, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, groupSchemePartialSum_pair_both, psum0, psum1, psumE]
  have q2 : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  have q0 : (-1 : ℤ) ^ (2 - ({0} : Finset (Fin 2)).card) = -1 := by decide
  have q1 : (-1 : ℤ) ^ (2 - ({1} : Finset (Fin 2)).card) = -1 := by decide
  have qe : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  simp only [q2, q0, q1, qe, ← Over.comp_left, MonObj.comp_mul, MonObj.mul_comp, MonObj.one_comp, MonObj.comp_one,
    _root_.mul_one, _root_.one_mul]
  generalize fst B' B' ≫ pr i = a
  generalize snd B' B' ≫ pr i = b
  generalize fst B' B' ≫ pr j = c
  generalize snd B' B' ≫ pr j = d
  rw [mul_comm (c * d) a, mul_comm c a, mul_comm d a, mul_comm (c * d) b, mul_comm d b]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

end GlobalTheory.Mum.CubeStep

namespace GlobalTheory.Mum.CubeStep

variable {S : Scheme.{0}} {B B' : Over S} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B']

def lamV {T : Over S} {U : Type} [CommGroup U] (h : (T.left ⟶ B.left) → U) (u v : T ⟶ B) : U :=
  ∏ k : Fin 4, h (GlobalTheory.PolDeg.lamPts u v k) ^ Oε k

def pairGen {L : RigLB B} (cb : CubicalStr B L) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (B' ⟶ B))
    (p : Fin r × Fin r) :=
  zpowGen L.L _ _ (LB.mulGen L.L _ _ _ _
    (LB.pullGen L.L (thφ B (x3 B)) thε cb.t
      (lift (fst B' B' ≫ pr p.1) (lift (snd B' B' ≫ pr p.1) ((fst B' B' ≫ pr p.2) * (snd B' B' ≫ pr p.2)))).left)
    (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ B (x3 B)) thε cb.t (lift (fst B' B' ≫ pr p.2) (lift (snd B' B' ≫ pr p.2) (fst B' B' ≫ pr p.1))).left)
      (LB.pullGen L.L (thφ B (x3 B)) thε cb.t (lift (fst B' B' ≫ pr p.2) (lift (snd B' B' ≫ pr p.2) (snd B' B' ≫ pr p.1))).left)))
    (-W p.1 p.2)

theorem pairGen_isGen {L : RigLB B} (cb : CubicalStr B L) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (pr : Fin r → (B' ⟶ B)) (p : Fin r × Fin r) : (pairGen cb W pr p).IsGen :=
  zpowGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ cb.isGen _)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ cb.isGen _) (DVR.pullGen_isGen _ _ _ _ cb.isGen _))) _

end GlobalTheory.Mum.CubeStep

namespace GlobalTheory.Mum


open CubeStep in
theorem cube_step : ∀ {S : Scheme.{0}} {B B' : Over S} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (L : RigLB B) (cb : CubicalStr B L) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (B' ⟶ B)), (∀ i, IsMonHom (pr i)) → ∃ c : LB.Gen (LB.LinComb L.L (Sum.elim (fun k : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr k.1.1) (snd B' B' ≫ pr k.1.2) k.2) (fun p : ULift.{0} (Finset (Fin 2)) × ((Fin r × Fin r) × Fin 4) => (psum B' (x2 B') p.1.down).left ≫ tensφ pr p.2)) (Sum.elim (fun k => (W + W.transpose) k.1.1 k.1.2 * Oε k.2) (fun p => -((-1) ^ (2 - p.1.down.card) * tensε W p.2)))), c.IsGen ∧ ∀ (T : Over S) (ρ : T ⟶ G2 B') (z : T.left) (J : (T.left ⟶ B.left) → L.L.ι), Good L.L z J → val c ρ.left z J = ∏ i, ∏ j, (cubV cb z J (ρ ≫ fst B' B' ≫ pr i) (ρ ≫ snd B' B' ≫ pr i) ((ρ ≫ fst B' B' ≫ pr j) * (ρ ≫ snd B' B' ≫ pr j)) * cubV cb z J (ρ ≫ fst B' B' ≫ pr j) (ρ ≫ snd B' B' ≫ pr j) (ρ ≫ fst B' B' ≫ pr i) * cubV cb z J (ρ ≫ fst B' B' ≫ pr j) (ρ ≫ snd B' B' ≫ pr j) (ρ ≫ snd B' B' ≫ pr i)) ^ (-W i j) := by
  intro S B B' _ _ _ _ L cb r W pr hpr
  have hfe : FormEq (fun q : (Fin r × Fin r) × (thK.{0} ⊕ (thK.{0} ⊕ thK.{0})) => Sum.elim
      (fun k => (lift (fst B' B' ≫ pr q.1.1) (lift (snd B' B' ≫ pr q.1.1)
        ((fst B' B' ≫ pr q.1.2) * (snd B' B' ≫ pr q.1.2)))).left ≫ thφ B (x3 B) k)
      (Sum.elim (fun k => (lift (fst B' B' ≫ pr q.1.2) (lift (snd B' B' ≫ pr q.1.2) (fst B' B' ≫ pr q.1.1))).left ≫
          thφ B (x3 B) k)
        (fun k => (lift (fst B' B' ≫ pr q.1.2) (lift (snd B' B' ≫ pr q.1.2) (snd B' B' ≫ pr q.1.1))).left ≫
          thφ B (x3 B) k)) q.2)
      (fun q => -W q.1.1 q.1.2 * Sum.elim thε (Sum.elim thε thε) q.2)
      (Sum.elim (fun k : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr k.1.1) (snd B' B' ≫ pr k.1.2) k.2)
        (fun p : ULift.{0} (Finset (Fin 2)) × ((Fin r × Fin r) × Fin 4) => (psum B' (x2 B') p.1.down).left ≫ tensφ pr p.2))
      (Sum.elim (fun k => (W + W.transpose) k.1.1 k.1.2 * Oε k.2)
        (fun p => -((-1) ^ (2 - p.1.down.card) * tensε W p.2))) := by
    intro U _ h
    have h1 : ∏ q : (Fin r × Fin r) × Fin 4,
        h (GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr q.1.1) (snd B' B' ≫ pr q.1.2) q.2) ^ ((W + W.transpose) q.1.1 q.1.2 * Oε q.2) =
        (∏ p : Fin r × Fin r, (∏ k : Fin 4, h (GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr p.1) (snd B' B' ≫ pr p.2) k) ^ Oε k) ^
          W p.1 p.2) *
        ∏ p : Fin r × Fin r, (∏ k : Fin 4, h (GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr p.2) (snd B' B' ≫ pr p.1) k) ^ Oε k) ^
          W p.1 p.2 := by
      calc _ = ∏ p : Fin r × Fin r, ∏ k : Fin 4,
            h (GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr p.1) (snd B' B' ≫ pr p.2) k) ^ ((W + W.transpose) p.1 p.2 * Oε k) :=
          Fintype.prod_prod_type _
        _ = ∏ p : Fin r × Fin r, (lamV h (fst B' B' ≫ pr p.1) (snd B' B' ≫ pr p.2) ^ W p.1 p.2 *
            lamV h (fst B' B' ≫ pr p.1) (snd B' B' ≫ pr p.2) ^ W p.2 p.1) :=
          Finset.prod_congr rfl fun p _ => by
            rw [prod_zpow_mul, Matrix.add_apply, Matrix.transpose_apply, zpow_add]; rfl
        _ = _ := by
          rw [Finset.prod_mul_distrib]
          exact congrArg _ (Fintype.prod_equiv (Equiv.prodComm _ _) _ _ fun _ => rfl)
    have h2 : ∏ q : ULift.{0} (Finset (Fin 2)) × ((Fin r × Fin r) × Fin 4),
        h ((psum B' (x2 B') q.1.down).left ≫ tensφ pr q.2) ^ (-((-1) ^ (2 - q.1.down.card) * tensε W q.2)) =
        ∏ p : Fin r × Fin r, (∏ k : Fin 4, ∏ I : ULift.{0} (Finset (Fin 2)),
          h ((psum B' (x2 B') I.down).left ≫ tensφ pr (p, k)) ^ ((-1) ^ (2 - I.down.card) * Oε k)) ^ (-W p.1 p.2) := by
      rw [Fintype.prod_prod_type, Finset.prod_comm, Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [← Finset.prod_zpow]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← Finset.prod_zpow]
      refine Finset.prod_congr rfl fun I _ => ?_
      rw [← zpow_mul]
      congr 1
      simp only [tensε]
      ring
    refine (Fintype.prod_prod_type _).trans (Eq.trans ?_ ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) h1 h2)).symm)
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p _ => pair_eq pr hpr (W p.1 p.2) p.1 p.2 h
  obtain ⟨t, ht, hv⟩ := exists_gen L.isLB hfe (GeneratorPullback.finProdGen L.L _ _ (pairGen cb W pr))
    (finProdGen_isGen _ _ _ _ (pairGen_isGen cb W pr))
  refine ⟨t, ht, fun T ρ z J hJ => ?_⟩
  refine (hv _ _ z J hJ).trans ((val_finProdGen _ _ _ (pairGen cb W pr) _ _ hJ).trans
    ((Fintype.prod_prod_type _).trans ?_))
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  dsimp only [pairGen]
  refine (val_zpowGen _ _ _ _ _ _ _ _).trans (congrArg (· ^ (-W i j)) ?_)
  refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub cb ρ hJ _ _ _) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (val_cub cb ρ hJ _ _ _) (val_cub cb ρ hJ _ _ _))))).trans ?_
  rw [MonObj.comp_mul, ← _root_.mul_assoc]

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalStructureSemiAbelianExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open Classical

namespace GlobalTheory.ZH

theorem exists_cp_zhOut : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → ∀ Z : GlobalTheory.ZH.ZHOut ρS M U₀ EE, ∃ P : GlobalTheory.UU.CP Z.G, P.L = Z.L := by
  intro o Ω _ _ _ _ S ρS M U₀ EE hO Z
  obtain ⟨s, hs, hr⟩ := GlobalTheory.SymmetricBundle.gen_of_isSymmetric Z.L Z.sym

  have hrange : Set.range M.pt ⊆ Set.range U₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hO.ne (Set.mem_univ w)
  let x : Sp Ω ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι M.pt hrange
  have hx : x ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _

  have w' : pullback.fst Z.G.hom M.pt ≫ Z.G.hom = (((Over.pullback M.pt).obj Z.G).hom ≫ x) ≫ U₀.ι := by
    rw [Category.assoc, hx]; exact pullback.condition
  let φ' := Z.cart.1.lift (pullback.fst Z.G.hom M.pt) (((Over.pullback M.pt).obj Z.G).hom ≫ x) w'
  have n : IsGrpPullback ((Over.pullback M.pt).obj Z.G) Z.G (x ≫ U₀.ι) (φ' ≫ Z.φ) :=
    (isGrpPullback_pullback Z.G M.pt).congr hx.symm (Z.cart.1.lift_fst _ _ _).symm
  have h1 := IsGrpPullback.cancel Z.cart n (Z.cart.1.lift_snd _ _ _)
  have h2 := (IsGrpPullback.comp h1 (isGrpPullback_pullback ρS.P.A Z.u₀)).congr (Z.u₀_gen x hx) rfl
  have hA : IsAbelianScheme ((Over.pullback M.pt).obj Z.G) :=
    GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback ρS.P.isAb h2
  have h3 := GlobalTheory.ValueForm.surjective_cube_baseChange GlobalTheory.globalFns_holds M.pt hA (Iso.refl _)

  have := Z.semi.smooth
  have : Flat (G3 Z.G).hom := by
    show Flat (pullback.fst Z.G.hom (pullback.fst Z.G.hom Z.G.hom ≫ Z.G.hom) ≫ Z.G.hom)
    infer_instance
  have := M.sep
  have : QuasiCompact M.pt := by infer_instance
  have : IsSchemeTheoreticallyDominant M.pt := IsSchemeTheoreticallyDominant.of_isDominant M.pt
  have : IsSchemeTheoreticallyDominant (pullback.fst (G3 Z.G).hom M.pt) :=
    .of_isPullback (IsPullback.of_hasPullback (G3 Z.G).hom M.pt).flip
  have hi : ∀ U, Function.Injective ((pullback.fst (G3 Z.G).hom M.pt).app U).hom :=
    fun U => (pullback.fst (G3 Z.G).hom M.pt).app_injective U
  exact ⟨⟨Z.L, Z.cub, s, hs, hr, GlobalTheory.ValueForm.sym_cub_of_baseChange M.pt hi h3 Z.cub s hs hr⟩, rfl⟩

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEndomorphismOfLatticePreservingLinear
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.UnifEndo

theorem exists_isMonHom_of_map_lattice : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (g : ℕ) (u : HolUnif A L g)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ l ∈ u.Λ, F l ∈ u.Λ) → ∃ f : A ⟶ A, IsMonHom f ∧ ∀ z, u.ex (F z) = u.ex z ≫ f := by
  intro A _ hA L g u F hF
  exact GlobalTheory.HolUnifEnd.exists_isMonHom_of_map_lattice A g hA
    (GlobalTheory.TorusAction.smoothOfRelativeDimension_of_holUnif A hA u) L u F hF

end GlobalTheory.UnifEndo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpandsAtOfAdmissibleBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem IntFam.exists_expandsAt_of_admissibleBase : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ k : ℕ, 1 ≤ k → ∀ (F : Fam D.toPre (FractionRing R) k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ α : D.toPre.X, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (F.s α) (D.toPre.famφB α) (DegPre.famε k) (f α) (DegPre.prB D.toPre (FractionRing R)).left (scal (DegPre.BF D.toPre (FractionRing R)).hom (1 : R))) → ∃ σ : H0 U.LG.L k, ∀ e : ℕ, U.ExpandsAt e k σ f := by
  intro R _ _ _ hR D A G _ _ hG U k hk F f hf
  have : IsNoetherianRing R := hR.1
  have := hG.geomConnected
  obtain ⟨s, ⟨r, hr, σ₀, f₀, -, hf₀, hE⟩, -⟩ := (U.expand k hk).2 F
  have h1 : scal (DegPre.BF D.toPre (FractionRing R)).hom (1 : R) = 1 := by
    rw [scal, map_one, map_one]
  have h₁ : ∀ α j, (f₀ α).f j = resTop _ (scal D.toPre.P.A.hom r) * (f α).f j := fun α =>
    GlobalTheory.IntegralExpansion.secIsMul_of_secScal D.toPre.P.isLB _
      (GlobalTheory.IntegralExpansion.prB_app_injective D.toPre) (h1 ▸ hf α)
      (by rw [Over.w (DegPre.prB D.toPre (FractionRing R))]; exact hf₀ α)
  obtain ⟨σ, hσ⟩ := GlobalTheory.sec_div_of_expandsAt R _ hR D A G U.toUnifPre k r hr σ₀ f₀ f h₁ hE
  exact ⟨σ, GlobalTheory.expandsAt_cancel_of_ne_zero R _ D A G U.toUnifPre k r hr σ σ₀ f f₀ hσ h₁ hE⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSiegelObjectPolarisationKernelKilledStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_siegelObject_polarisationKernel_killed : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (h M : ℕ) (t₁ : S ⟶ Sp (cycAway M)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ o.A)) (hl : IsSympLev o.P h M (zetaAway M) t₁ lev) (e : ℕ), e.Coprime p → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) → SiegKerBy (o.toSieg hl) e := by
  first | (exact @GlobalTheory.UPel.HT.KerBy.siegKerBy_toSieg) | (exact GlobalTheory.UPel.HT.KerBy.siegKerBy_toSieg) | (intros; apply GlobalTheory.UPel.HT.KerBy.siegKerBy_toSieg <;> assumption)
end

