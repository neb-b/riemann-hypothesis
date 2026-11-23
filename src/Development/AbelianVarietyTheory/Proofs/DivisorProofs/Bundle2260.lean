module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2149
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0206
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1857
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0515
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2120
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2180
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSymplecticSimilitudeClassifyingMaps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSymplecticLevelFamilyUniversalProper
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGensOfDataFrom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TChart.GensFrom

theorem lam_form {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {T : Over S} (x y : T ⟶ B) (U : Type)
    [CommGroup U] (H : (T.left ⟶ B.left) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), H ((lift x y).left ≫ (psum B (x2 B) I.down).left) ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      (∏ k, H (lamPts x y k) ^ negε k)⁻¹ := by
  have p : ∀ I : Finset (Fin 2), (lift x y).left ≫ (psum B (x2 B) I).left = (psum B ![x, y] I).left := fun I =>
    congrArg (fun q => q.left) ((psum_hom (preHom (lift x y)) (x2 B) I).trans (by
      congr 1; funext i; fin_cases i <;> simp [x2, preHom]))
  simp only [p]
  rw [← Equiv.ulift.symm.prod_comp, show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} from by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton,
    Fin.prod_univ_four]
  have q0 : psum B ![x, y] ∅ = 1 := rfl
  have q1 : psum B ![x, y] {0} = x := _root_.mul_one x
  have q2 : psum B ![x, y] {1} = y := _root_.mul_one y
  have q3 : psum B ![x, y] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  simp [q0, q1, q2, q3, lamPts, negε]
  generalize H (x * y).left = A, H x.left = A₁, H y.left = A₂, H (1 : T ⟶ B).left = A₀
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.TChart.GensFrom

namespace GlobalTheory.TChart.GensFrom

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {F : Y' ⟶ Y}

theorem good_linComb {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    Good (LB.LinComb L φ ε) z (fun ψ k => J (ψ ≫ φ k)) := fun ψ => hJ.mem φ ψ

theorem val_flatGen (u : LB.Gen ((LB.LinComb L φ ε).pull F)) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : val (GlobalTheory.UU.flatGen u) r z J = val u r z (fun ψ k => J (ψ ≫ φ k)) := by
  exact (gm_res r z _ (hJ.mem (fun k => F ≫ φ k) r) _).trans
    (val_of u r z _ (fun _ k => J (r ≫ F ≫ φ k)) (fun _ => funext fun k => by simp only [Category.assoc])).symm

theorem val_unflatGen (v : LB.Gen (LB.LinComb L (fun k => F ≫ φ k) ε)) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : val (GlobalTheory.UU.unflatGen v) r z (fun ψ k => J (ψ ≫ φ k)) = val v r z J := by
  exact (gm_res r z _ ((good_linComb (φ := φ) (ε := ε) hJ).mem (fun _ : PUnit => F) r) _).trans
    (val_of v r z J (fun k => J ((r ≫ F) ≫ φ k)) (fun k => by simp only [Category.assoc])).symm

end GlobalTheory.TChart.GensFrom

namespace GlobalTheory.TChart.GensFrom

theorem om_lam {S S' : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B']
    {M : LB B.left} {M' : LB B'.left} {β₂ : (G2 B').left ⟶ (G2 B).left} (w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂))
    {Z : Scheme.{0}} (p : Z ⟶ (G2 B').left) (z : Z) (J : (Z ⟶ B.left) → M.ι) (J' : (Z ⟶ B'.left) → M'.ι) :
    GlobalTheory.ArcPull.om w z (fun ψ (I : ULift.{0} (Finset (Fin 2))) => J (ψ ≫ (psum B (x2 B) I.down).left))
      (fun ψ (I : ULift.{0} (Finset (Fin 2))) => J' (ψ ≫ (psum B' (x2 B') I.down).left)) p = lamVal w p z J J' := by
  have H : ∀ i i' : (LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).ι, i = i' →
      gm p z ((LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).U i) (w.s i) =
        gm p z ((LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).U i') (w.s i') := by
    rintro _ _ rfl; rfl
  unfold GlobalTheory.ArcPull.om Geo.Tor.gw lamVal
  refine H (fun _ (I : ULift.{0} (Finset (Fin 2))) => J ((p ≫ β₂) ≫ (psum B (x2 B) I.down).left),
      fun (I : ULift.{0} (Finset (Fin 2))) => J' (p ≫ (psum B' (x2 B') I.down).left))
    (fun _ (I : ULift.{0} (Finset (Fin 2))) => J (p ≫ β₂ ≫ (psum B (x2 B) I.down).left),
      fun (I : ULift.{0} (Finset (Fin 2))) => J' (p ≫ (psum B' (x2 B') I.down).left)) (Prod.ext ?_ rfl)
  funext _ I
  exact congrArg J (Category.assoc _ _ _)

end GlobalTheory.TChart.GensFrom

namespace GlobalTheory.TChart.GensFrom

theorem exists_gen_of_base {W V : Type} [CommRing W] [CommRing V] {BT : Over (Sp W)} [GrpObj BT] [IsCommMonObj BT]
    {BQ : Over (Sp V)} [GrpObj BQ] [IsCommMonObj BQ] {MT : LB BT.left} {MQ : LB BQ.left} (hMT : MT.IsLB) (hMQ : MQ.IsLB)
    (iw : W →+* V) {β : BQ.left ⟶ BT.left} {β₂ : (G2 BQ).left ⟶ (G2 BT).left} (hsq : IsSquare β β₂)
    (w : LB.Iso (abelian₂ BQ MQ) ((abelian₂ BT MT).pull β₂)) (hw : w.IsGen) (x y : 𝟙_ (Over (Sp V)) ⟶ BQ)
    (x₀ y₀ : 𝟙_ (Over (Sp W)) ⟶ BT) (hx : x.left ≫ β = spMap iw ≫ x₀.left) (hy : y.left ≫ β = spMap iw ≫ y₀.left)
    (τ₁ : LB.Gen (LB.LinComb MT (lamPts x₀ y₀) negε)) (h₁ : τ₁.IsGen) :
    ∃ τ : LB.Gen (LB.LinComb MQ (lamPts x y) negε), τ.IsGen ∧ ∀ (T' : Over (Sp V)) (z : T'.left) J J',
      Good MT z J → Good MQ z J' →
        val τ (toUnit T').left z J' = lamVal w (lift (toUnit T' ≫ x) (toUnit T' ≫ y)).left z J J' *
          val τ₁ (T'.hom ≫ spMap iw) z J := by
  have hψ : (lift x y).left ≫ β₂ = spMap iw ≫ (lift x₀ y₀).left := by
    apply pullback.hom_ext
    · show ((lift x y).left ≫ β₂) ≫ (fst BT BT).left = (spMap iw ≫ (lift x₀ y₀).left) ≫ (fst BT BT).left
      rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, hx, Category.assoc, ← Over.comp_left,
        lift_fst]
    · show ((lift x y).left ≫ β₂) ≫ (snd BT BT).left = (spMap iw ≫ (lift x₀ y₀).left) ≫ (snd BT BT).left
      rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, hy, Category.assoc, ← Over.comp_left,
        lift_snd]
  obtain ⟨t₂, ht₂, hv₂⟩ := exists_gen hMT
    (φ' := fun I : ULift.{0} (Finset (Fin 2)) => (lift x₀ y₀).left ≫ (psum BT (x2 BT) I.down).left)
    (ε' := fun I => (-1 : ℤ) ^ (2 - I.down.card)) (by
      intro U _ H
      rw [lam_form x₀ y₀ U H, ← Finset.prod_inv_distrib]
      simp only [zpow_neg]) (LB.invGen MT _ _ τ₁) (DVR.invGen_isGen _ _ _ _ h₁)
  let t₃ : LB.Gen ((abelian₂ BT MT).pull (lift x₀ y₀).left) := GlobalTheory.UU.unflatGen t₂
  have ht₃ : t₃.IsGen := GlobalTheory.UU.unflatGen_isGen ht₂
  obtain ⟨a, ha, hva⟩ := GlobalTheory.ArcPull.exists_down_om hw (LB.isLB_linComb hMT _ _) (LB.isLB_linComb hMQ _ _)
    (φ' := fun _ : PUnit => (lift x y).left) (φ := fun _ => (lift x₀ y₀).left) (ε := fun _ => 1) (spMap iw)
    (fun _ => hψ) t₃ ht₃
  obtain ⟨τ, hτ, hvτ⟩ := exists_gen hMQ
    (φ := fun I : ULift.{0} (Finset (Fin 2)) => (lift x y).left ≫ (psum BQ (x2 BQ) I.down).left)
    (ε := fun I => -((-1 : ℤ) ^ (2 - I.down.card))) (φ' := lamPts x y) (ε' := negε) (by
      intro U _ H
      simp only [zpow_neg, Finset.prod_inv_distrib]
      rw [lam_form x y U H, inv_inv]) (LB.invGen MQ _ _ (GlobalTheory.UU.flatGen a))
    (DVR.invGen_isGen _ _ _ _ (GlobalTheory.UU.flatGen_isGen ha))
  refine ⟨τ, hτ, fun T' z J J' hJ hJ' => ?_⟩
  have e1 := hvτ _ (toUnit T').left z J' hJ'
  have e5 := val_flatGen (L := MQ) (φ := fun I : ULift.{0} (Finset (Fin 2)) => (psum BQ (x2 BQ) I.down).left)
    (ε := fun I => (-1 : ℤ) ^ (2 - I.down.card)) (F := (lift x y).left) a (toUnit T').left z hJ'
  rw [val_inv, e5] at e1
  have e6 : val t₃ ((toUnit T').left ≫ spMap iw) z
      (fun ψ (k : ULift.{0} (Finset (Fin 2))) => J (ψ ≫ (psum BT (x2 BT) k.down).left)) =
      val t₂ ((toUnit T').left ≫ spMap iw) z J := val_unflatGen (L := MT) (φ := fun I : ULift.{0} (Finset (Fin 2)) => (psum BT (x2 BT) I.down).left)
    (ε := fun I => (-1 : ℤ) ^ (2 - I.down.card)) (F := (lift x₀ y₀).left) t₂ ((toUnit T').left ≫ spMap iw) z hJ
  have e2 := hva _ (toUnit T').left z _ _
    (good_linComb (L := MT) (φ := fun I : ULift.{0} (Finset (Fin 2)) => (psum BT (x2 BT) I.down).left)
      (ε := fun I => (-1 : ℤ) ^ (2 - I.down.card)) hJ)
    (good_linComb (L := MQ) (φ := fun I : ULift.{0} (Finset (Fin 2)) => (psum BQ (x2 BQ) I.down).left)
      (ε := fun I => (-1 : ℤ) ^ (2 - I.down.card)) hJ')
  rw [e6, hv₂ _ _ z J hJ, val_inv, Fintype.prod_unique, zpow_one, om_lam] at e2
  have e3 : (lift (toUnit T' ≫ x) (toUnit T' ≫ y)).left = (toUnit T').left ≫ (lift x y).left := by
    rw [← comp_lift]; rfl
  have e4 : (toUnit T').left = T'.hom := by simpa using Over.w (toUnit T')
  rw [e1, e3, ← e4, ← inv_inv (val τ₁ ((toUnit T').left ≫ spMap iw) z J), e2, _root_.mul_inv, _root_.mul_inv_cancel_left]
  rfl

end GlobalTheory.TChart.GensFrom

namespace GlobalTheory.TChart


open GensFrom in
theorem exists_gens_of_dataFrom {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V]
    (T : TautBase o W) (iw : W →+* V) {I : Type} [Fintype I] (s : I → V)
    (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (Q : Data V) (e : Q.X ≃+ (Fin T.r → ℤ)) {M : ℕ}
    (eI : I ≃ Fin M) (hD : DataFrom T iw s ε n Q e) :
    ∃ τ : GlobalTheory.Poinc.Sep.Gens Q, GlobalTheory.Poinc.Sep.TauIn Q τ (fun k => s (eI.symm k))
      (fun k => (n : ℤ) • pull e.toIntLinearEquiv.toLinearMap (ε (eI.symm k))) ∧ GlobalTheory.Poinc.Sep.FromBase Q τ iw := by
  obtain ⟨β, β₂, w, hpb, hsq, hw, hc, hτ⟩ := hD
  have key := fun a b => exists_gen_of_base T.M.isLB Q.M.isLB iw hsq w hw (Q.c a) (Q.c b)
    (T.c₀ ((n : ℤ) • e a)) (T.c₀ ((n : ℤ) • e b)) (hc a) (hc b) (T.τ₀ _ _) (T.τ₀_gen _ _)
  choose τ hτg hτv using key
  refine ⟨τ, fun a b => ⟨hτg a b, ?_⟩, T.B, inferInstance, inferInstance, T.M.L, fun a => T.c₀ ((n : ℤ) • e a),
    fun a b => T.τ₀ _ _, β, β₂, w, T.isAb, T.M.isLB, hpb, hsq, hw, hc, fun a b => T.τ₀_gen _ _,
    fun T' a b z J J' hJ hJ' => hτv a b T' z J J' hJ hJ'⟩
  obtain ⟨k, hk, hv⟩ := hτ a b
  refine ⟨k, ?_, fun z J' hJ' => ?_⟩
  · rw [hk]
    refine Fintype.prod_equiv eI _ _ fun i => ?_
    simp [pull]
  · choose J hJ using fun χ : (TK V).left ⟶ T.B.left => exists_chart T.M.isLB (χ z)
    rw [hv z J J' hJ hJ', hτv a b (TK V) z J J' hJ hJ']

end GlobalTheory.TChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHalvingPointAbelianSchemeFiniteExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HalfPt

theorem exists_spec_of_finite_surjective {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} (f : X ⟶ Sp R)
    [IsFinite f] [Surjective f] :
    ∃ (C : Type) (_ : CommRing C) (φ : R →+* C) (g : Sp C ⟶ X),
      Function.Injective φ ∧ φ.Finite ∧ g ≫ f = spMap φ := by
  haveI : IsAffine X := isAffine_of_isAffineHom f
  let ψ : CommRingCat.of R ⟶ Γ(X, ⊤) := Spec.preimage (X.isoSpec.inv ≫ f)
  have hψ : Spec.map ψ = X.isoSpec.inv ≫ f := Spec.map_preimage _
  refine ⟨Γ(X, ⊤), inferInstance, ψ.hom, X.isoSpec.inv, ?_, ?_, ?_⟩
  · have hs : Surjective (Spec.map ψ) := by rw [hψ]; infer_instance
    have hd : DenseRange (PrimeSpectrum.comap ψ.hom) := hs.1.denseRange
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, nilradical_eq_zero] at hd
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    simpa using hd hx
  · have hf : IsFinite (Spec.map ψ) := by rw [hψ]; infer_instance
    exact (IsFinite.SpecMap_iff ψ).1 hf
  · exact hψ.symm

end GlobalTheory.HalfPt

namespace GlobalTheory.HalfPt

theorem exists_half_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B] (a : 𝟙_ (Over (Sp R)) ⟶ B), IsCN R → IsAbelianScheme B → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (b : Over.mk (spMap ρ) ⟶ B), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ b ^ 2 = toUnit _ ≫ a := by
  intro R _ _ _ B _ _ a hCN hAb
  haveI : IsNoetherianRing R := hCN.1
  obtain ⟨hfin, -⟩ := _root_.GlobalTheory.MulFiniteFlat.isFinite_and_flat_mul (Sp R) B hAb 2 (by norm_num)
  have hsurj := _root_.GlobalTheory.SemiAbSurj.surjective_pow (Sp R) B (GlobalTheory.isSemiAbelian_of_isAbelianScheme B hAb) 2 two_ne_zero
  let m : B.left ⟶ B.left := ((𝟙 B) ^ 2 : B ⟶ B).left
  let s : Sp R ⟶ B.left := a.left
  haveI : IsFinite m := hfin
  haveI : Surjective m := hsurj
  haveI : IsFinite (pullback.snd m s) := inferInstance
  haveI : Surjective (pullback.snd m s) := inferInstance
  obtain ⟨C, _, φ, g, hinj, hφf, hg⟩ := exists_spec_of_finite_surjective (pullback.snd m s)
  obtain ⟨R', _, _, _, ρ, σ, hCN', hρi, hρf, hρl, hσ⟩ := _root_.GlobalTheory.LocExt.exists_isCN_cover_of_finite R C φ hCN hinj hφf
  have hsB : s ≫ B.hom = 𝟙 (Sp R) := Over.w a
  have hmB : m ≫ B.hom = B.hom := Over.w ((𝟙 B) ^ 2 : B ⟶ B)
  have hfst : pullback.fst m s ≫ B.hom = pullback.snd m s := by
    rw [← hmB, ← Category.assoc, pullback.condition, Category.assoc, hsB, Category.comp_id]
  have hρ : spMap σ ≫ spMap φ = spMap ρ := by
    rw [← hσ, spMap, spMap, spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  let c : Over.mk (spMap ρ) ⟶ B :=
    Over.homMk (spMap σ ≫ g ≫ pullback.fst m s) (by
      simp only [Over.mk_hom, Category.assoc]
      rw [hfst, hg, hρ])
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, c, hCN', hρi, hρf, hρl, ?_⟩
  have hc : c ^ 2 = c ≫ (𝟙 B) ^ 2 := by rw [comp_pow, Category.comp_id]
  rw [hc]
  ext
  simp only [c, Over.comp_left, Over.homMk_left, Category.assoc]
  show spMap σ ≫ g ≫ pullback.fst m s ≫ m = _
  rw [pullback.condition, ← Category.assoc g, hg, ← Category.assoc, hρ]
  rfl

end GlobalTheory.HalfPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomEvenDefectBimultiplicativePeriods
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.DefectHom

variable {R : Type} [CommRing R] [IsDomain R]

theorem c_zero (D : DegPre R) : D.c 0 = 1 := by
  have h : D.c (0 + 0) = D.c 0 * D.c 0 := D.c_add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem c_neg (D : DegPre R) (a : D.X) : D.c (-a) = (D.c a)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  have h : D.c (-a + a) = D.c (-a) * D.c a := D.c_add _ _
  rw [neg_add_cancel, c_zero] at h
  exact h.symm

theorem pt_neg (D : DegPre R) (a : D.X) : toUnit (TK R) ≫ D.c (-a) = (toUnit (TK R) ≫ D.c a)⁻¹ := by
  rw [c_neg, GrpObj.comp_inv]

theorem pt_add (D : DegPre R) (a b : D.X) :
    toUnit (TK R) ≫ D.c (a + b) = (toUnit (TK R) ≫ D.c a) * (toUnit (TK R) ≫ D.c b) := by
  rw [D.c_add, ← MonObj.comp_mul]; rfl

theorem neg_pt_left (D : DegPre R) (a : D.X) : ptK (D.c (-a)) = D.xK a ≫ (ι[D.P.A]).left := by
  show (toUnit (TK R) ≫ D.c (-a)).left = _
  rw [pt_neg, Hom.inv_def, Over.comp_left]

theorem exists_defect (D : DegPre R) (χ : D.X) : ∃ k : (FractionRing R)ˣ, ∀ (z : (TK R).left) J, Good D.P.L z J →
    val (D.psi (-χ)) (𝟙 _) z J * val D.sym (D.xK χ) z J =
      gm (𝟙 (TK R).left) z ⊤ (unitOn k) * val (D.psi χ) (𝟙 _) z J := by
  let t := LB.mulGen D.P.L _ _ _ _ (D.psi (-χ)) (LB.pullGen D.P.L _ _ D.sym (D.xK χ))
  have ht : t.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (D.psi_gen _) (DVR.pullGen_isGen _ _ _ _ D.sym_gen _)
  have hf : FormEq (Sum.elim (fun _ : PUnit => ptK (D.c (-χ))) (fun k => D.xK χ ≫ ![(ι[D.P.A]).left, 𝟙 D.P.A.left] k))
      (Sum.elim (fun _ => -1) ![1, -1]) (fun _ : PUnit => ptK (D.c χ)) (fun _ => -1) := by
    intro U _ h
    rw [Fintype.prod_sum_type, Fin.prod_univ_two, neg_pt_left]
    simp only [Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id]
    simp only [zpow_neg, zpow_one]
    group
  obtain ⟨c, hc, H⟩ := DVR.TWM.exists_ratio (F := FractionRing R) D.P.isLB t ht (D.psi χ) (D.psi_gen χ) hf
  refine ⟨Units.mk0 c hc, fun z J hJ => ?_⟩
  have e := H _ (𝟙 _) z J hJ
  have e₁ : val t (𝟙 _) z J = val (D.psi (-χ)) (𝟙 _) z J * val D.sym (D.xK χ) z J := by
    refine (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans ?_))
    rw [Category.id_comp]
  rw [← e₁]
  refine Units.ext (e.trans ?_)
  rw [Units.val_mul, ← gs_unit _ z ⊤ trivial]
  rfl

theorem gm_unitOn_inj {u v : (FractionRing R)ˣ} (z : (TK R).left)
    (h : gm (𝟙 (TK R).left) z ⊤ (unitOn u) = gm (𝟙 (TK R).left) z ⊤ (unitOn v)) : u = v := by
  have hs : Subsingleton (TK R).left := (inferInstance : Subsingleton (PrimeSpectrum (FractionRing R)))
  have e : unitOn u = unitOn v := unit_ext fun x _ => by rw [Subsingleton.elim x z]; exact h
  exact Units.map_injective (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv).1 e

theorem val_tau (D : DegPre R) (a b : D.X) {z : (TK R).left} {J} (hJ : Good D.P.L z J) :
    val (D.tau a b) (𝟙 _) z J = val (D.psi (a + b)) (𝟙 _) z J * (val (D.psi a) (𝟙 _) z J)⁻¹ *
      (val (D.psi b) (𝟙 _) z J)⁻¹ * (val D.rigK (𝟙 _) z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem exists_evenDefect_hom : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R),
    D.TauBimult → ∃ h : D.X → (FractionRing R)ˣ, (∀ a b, h (a + b) = h a * h b) ∧ EvenDefect D h := by
  intro R _ _ _ D hB
  choose h hh using exists_defect D
  refine ⟨h, fun a b => ?_, hh⟩
  let z : (TK R).left := (⊥ : PrimeSpectrum (FractionRing R))
  obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt D.P.isLB z
  refine gm_unitOn_inj z ?_
  have g1 := GlobalTheory.T.symmetry_secondDifference_eq_cubical_ratio R D (TK R) (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b) z J hJ
  have g2 := _root_.GlobalTheory.TauNeg.val_tau_neg R D hB a b z J hJ
  rw [← pt_neg, ← pt_neg, ← pt_add] at g1
  rw [val_tau D a b hJ, val_tau D (-a) (-b) hJ, ← neg_add] at g2
  have e₀ := hh (a + b) z J hJ
  have e₁ := hh a z J hJ
  have e₂ := hh b z J hJ
  change val D.sym (D.xK (a + b)) z J * _ = val D.sym (D.xK a) z J * val D.sym (D.xK b) z J * _ at g1
  rw [show unitOn (h a * h b) = unitOn (h a) * unitOn (h b) from map_mul _ _ _, map_mul]
  generalize val D.sym (D.xK (a + b)) z J = s₀ at g1 e₀
  generalize val D.sym (D.xK a) z J = s₁ at g1 e₁
  generalize val D.sym (D.xK b) z J = s₂ at g1 e₂
  generalize gm (𝟙 (TK R).left) z ⊤ (unitOn (h (a + b))) = k₀ at e₀ ⊢
  generalize gm (𝟙 (TK R).left) z ⊤ (unitOn (h a)) = k₁ at e₁ ⊢
  generalize gm (𝟙 (TK R).left) z ⊤ (unitOn (h b)) = k₂ at e₂ ⊢
  apply Additive.ofMul.injective
  have E := fun {p q : ((TK R).left.presheaf.stalk z)ˣ} (e : p = q) => congrArg Additive.ofMul e
  have a₀ := E e₀; have a₁ := E e₁; have a₂ := E e₂; have b₁ := E g1; have b₂ := E g2
  simp only [ofMul_mul, ofMul_inv] at a₀ a₁ a₂ b₁ b₂ ⊢
  linear_combination (norm := abel) -a₀ + a₁ + a₂ + b₁ - b₂
end GlobalTheory.DefectHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogeneousFormOfOverlapIdealPowThickening
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg.JFrac

open MvPolynomial

theorem exists_rs_eq_pow_mul {X : Scheme} {U V : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U))
    (hV : X.basicOpen f = V) (h : V ≤ U) (b : Γ(X, V)) :
    ∃ (M : ℕ) (a : Γ(X, U)), rs X h a = rs X h f ^ M * b := by
  subst hV
  obtain ⟨M, a, ha⟩ :=
    exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated X U hU.isCompact hU.isQuasiSeparated f b
  exact ⟨M, a, ha⟩

theorem exists_form : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (e : ℕ) (i j : Fin (n + 1)) (c : Γ((Y e).left, C.D e i ⊓ C.D e j)), c ∈ towerIdeal Y e (I ^ e) _ → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ k : ℕ, ∃ F : MvPolynomial (Fin (n + 1)) R, F.IsHomogeneous (k + 2 * N) ∧ (∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) ∧ rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ev e i F) = rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ N * c := by
  intro R _ I Y β hP n C e i j c hc
  obtain ⟨hbasic, -, -⟩ := _root_.GlobalTheory.FormalAlg.LiftRatios.lifted_ratios_mod R I Y β hP n C
  obtain ⟨-, hsurj⟩ := _root_.GlobalTheory.FormalAlg.LevSurj.ev_surjective R I Y β hP n C
  have hVU : C.D e i ⊓ C.D e j ≤ C.D e i := inf_le_left
  have hX : ∀ l, C.ev e i (X l) = C.ρ e i l := fun l => by simp [Charts.ev]
  let J : Ideal (MvPolynomial (Fin (n + 1)) R) := Ideal.map MvPolynomial.C (I ^ e)
  let S : Ideal Γ((Y e).left, C.D e i ⊓ C.D e j) :=
    { carrier := {c | ∃ N₁ : ℕ, ∃ G ∈ J,
        rs (Y e).left hVU (C.ev e i G) = rs (Y e).left hVU (C.ρ e i j) ^ N₁ * c}
      add_mem' := by
        rintro a b ⟨N₁, G, hG, h1⟩ ⟨N₂, G', hG', h2⟩
        refine ⟨N₁ + N₂, X j ^ N₂ * G + X j ^ N₁ * G',
          J.add_mem (J.mul_mem_left _ hG) (J.mul_mem_left _ hG'), ?_⟩
        simp only [map_add (f := _), map_mul, map_pow, hX, h1, h2]
        ring
      zero_mem' := ⟨0, 0, J.zero_mem, by simp⟩
      smul_mem' := by
        rintro b a ⟨N₁, G, hG, h1⟩
        obtain ⟨M, a', ha'⟩ := exists_rs_eq_pow_mul (C.aff e i) (C.ρ e i j) (hbasic e i j) hVU b
        obtain ⟨H, rfl⟩ := hsurj e i a'
        refine ⟨M + N₁, H * G, J.mul_mem_left _ hG, ?_⟩
        simp only [map_mul, ha', h1, smul_eq_mul]
        ring }
  have hcS : c ∈ S := by
    refine (Ideal.map_le_iff_le_comap.2 (fun r hr => ?_)) hc
    refine ⟨0, MvPolynomial.C r, Ideal.mem_map_of_mem _ hr, ?_⟩
    simp [Charts.ev, rs_cst]
  obtain ⟨N₁, G, hG, hN₁⟩ := hcS
  have hGc : ∀ d, homogeneousComponent d G ∈ J := fun d => by
    refine MvPolynomial.mem_map_C_iff.2 fun m => ?_
    rw [coeff_homogeneousComponent]
    split_ifs
    · exact MvPolynomial.mem_map_C_iff.1 hG m
    · exact (I ^ e).zero_mem
  have hfix : ∀ d t, C.ρ e i i ^ t * C.ev e i (homogeneousComponent d G) =
      C.ev e i (homogeneousComponent d G) := fun d t => by
    have h1 := (GlobalTheory.T.homogeneousForm_chart_change_coeff_ideal_pow R I Y β hP n C e d (homogeneousComponent d G)
      (homogeneousComponent_isHomogeneous d G) (MvPolynomial.mem_map_C_iff.1 (hGc d)) i i).2.1
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ (C.ρ e i i) t, mul_assoc, h1, ih]
  refine ⟨N₁ + G.totalDegree, fun N hN k => ?_⟩
  refine ⟨X j ^ (N - N₁) * ∑ d ∈ Finset.range (G.totalDegree + 1),
      X i ^ (k + N + N₁ - d) * homogeneousComponent d G, ?_, ?_, ?_⟩
  · have hdeg : k + 2 * N = (N - N₁) + (k + N + N₁) := by omega
    rw [hdeg]
    refine (isHomogeneous_X_pow _ _).mul (IsHomogeneous.sum _ _ _ fun d hd => ?_)
    have hd' : d ≤ k + N + N₁ := by
      have := Finset.mem_range.1 hd
      omega
    have := (isHomogeneous_X_pow i (k + N + N₁ - d)).mul (homogeneousComponent_isHomogeneous d G)
    rwa [Nat.sub_add_cancel hd'] at this
  · exact MvPolynomial.mem_map_C_iff.1
      (J.mul_mem_left _ (J.sum_mem fun d _ => J.mul_mem_left _ (hGc d)))
  · have hsum : C.ev e i (∑ d ∈ Finset.range (G.totalDegree + 1),
        X i ^ (k + N + N₁ - d) * homogeneousComponent d G) = C.ev e i G := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        conv_rhs => rw [← sum_homogeneousComponent G, map_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [map_mul, map_pow, hX, hfix]
    rw [map_mul, hsum, map_mul, hN₁, map_pow, map_pow, hX, ← mul_assoc, ← pow_add,
      Nat.sub_add_cancel (by omega : N₁ ≤ N)]

end GlobalTheory.FormalAlg.JFrac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSymplecticSimilitudeClassifyingMapsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_symplecticSimilitude_classifyingMaps : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ),
  3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p →
  ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)),
    IsSympLev u.P h M (zetaAway M) s₁ lev → HarrisTaylorSymplecticLevelFamilyUniversalProperty b N h M s s₁ u lev →
    ∀ ρ : sympSimGrp h M → (X ⟶ X), SympActs s s₁ u lev ρ →
    ∀ (T : Scheme.{0}) (t : T ⟶ Sp R) (o : Obj b N t) (x x' : T ⟶ X), x ≫ s = t → x' ≫ s = t →
      Nonempty (ObjMap o u x) → Nonempty (ObjMap o u x') →
      ∀ q : T, ∃ (V : T.Opens) (a : sympSimGrp h M), q ∈ V ∧ V.ι ≫ x ≫ ρ a = V.ι ≫ x' := by
  first | (exact @GlobalTheory.HTLocSim.exists_local_similitude) | (exact GlobalTheory.HTLocSim.exists_local_similitude) | (intros; apply GlobalTheory.HTLocSim.exists_local_similitude  <;> assumption)
end

