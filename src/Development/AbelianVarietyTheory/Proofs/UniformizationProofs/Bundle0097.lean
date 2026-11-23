module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0089
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0082

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.AmpleStabFinite
open GlobalTheory.CechPic

theorem eq_pull_of_local {Y S : Scheme.{0}} (p : Y ⟶ S) (e : S ⟶ Y) (he : e ≫ p = 𝟙 S)
    (hp : ∀ V : S.Opens, Function.Surjective (pullback.snd p V.ι).appTop.hom) (c : CechPic.Pic Y)
    (h : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ CechPic.pull (p ⁻¹ᵁ U).ι c = 0) : c = CechPic.pull (p ≫ e) c := by
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  have key := exists_gen_of_local_on_base hM (K := Fin 2) ![𝟙 Y, p ≫ e] ![1, -1] p e he hp
    (fun U _ k => by
      rw [Fin.prod_univ_two]
      show k (e ≫ 𝟙 Y) ^ (1 : ℤ) * k (e ≫ p ≫ e) ^ (-1 : ℤ) = 1
      rw [← Category.assoc e, he, Category.comp_id, Category.id_comp]; simp)
    (fun s => by
      obtain ⟨U, hs, hU⟩ := h s
      refine ⟨U, hs, (cls_eq_zero_iff (LB.isLB_linComb hM _ _)).1 ?_⟩
      obtain ⟨n, n₁⟩ : ∃ n : (p ⁻¹ᵁ U).toScheme ⟶ (p ⁻¹ᵁ U).toScheme,
          n ≫ (p ⁻¹ᵁ U).ι = (p ⁻¹ᵁ U).ι ≫ p ≫ e :=
        ⟨IsOpenImmersion.lift (p ⁻¹ᵁ U).ι ((p ⁻¹ᵁ U).ι ≫ p ≫ e) (by
          rintro _ ⟨y, rfl⟩
          rw [Scheme.Opens.range_ι]
          have e' := congrArg (fun q => q (p y.1)) he
          exact (congrArg (· ∈ U) e').mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
      rw [cls_linComb hM, Fin.sum_univ_two]
      show (1 : ℤ) • CechPic.pull ((p ⁻¹ᵁ U).ι ≫ 𝟙 Y) (cls M hM) +
        (-1 : ℤ) • CechPic.pull ((p ⁻¹ᵁ U).ι ≫ p ≫ e) (cls M hM) = 0
      rw [← n₁, Category.comp_id, pull_comp, hU, map_zero]; simp)
  have k2 := (cls_eq_zero_iff (LB.isLB_linComb hM _ _)).2 key
  rw [cls_linComb hM, Fin.sum_univ_two] at k2
  have k3 : (1 : ℤ) • CechPic.pull (𝟙 Y) (cls M hM) + (-1 : ℤ) • CechPic.pull (p ≫ e) (cls M hM) = 0 := k2
  rw [pull_id, one_zsmul, neg_one_zsmul, ← sub_eq_add_neg, sub_eq_zero] at k3
  exact k3

theorem surj_of_isPullback (hG : GlobalFnsSt) {S : Scheme.{0}} {B : Over S} [GrpObj B] (hB : IsAbelianScheme B)
    {Y T : Scheme.{0}} {a : Y ⟶ B.left} {q : Y ⟶ T} {b : T ⟶ S} (h : IsPullback a q B.hom b) :
    Function.Surjective q.appTop.hom := by
  rw [← h.isoPullback_hom_snd]
  exact surj_comp (ConcreteCategory.bijective_of_isIso (h.isoPullback.hom.app ⊤)).2 (surj_snd hG hB (Over.mk b))

theorem cls_pw {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (d : ℤ) : cls (pw L d) (isLB_pw hL d) = d • cls L hL := by
  have h := LB.isLB_linComb hL (fun _ : PUnit => 𝟙 X) (fun _ => d)
  have e := cls_linComb hL _ _ h
  rw [Fintype.sum_unique, pull_id] at e
  rw [← e]
  refine (cls_eq_iff _ h).2 (iso_of_chart h ⟨fun i _ => i, fun _ _ hy => Set.mem_iInter.2 fun _ => hy, ?_⟩)
  intro y i j hi hj
  refine Eq.trans (map_zpow _ _ _) (Eq.symm ((gm_linComb L (fun _ : PUnit => 𝟙 X) (fun _ => d) (𝟙 X) y (fun _ => i) (fun _ => j)
    (Set.mem_iInter.2 fun _ => hi) (Set.mem_iInter.2 fun _ => hj)).trans ?_))
  rw [Fintype.prod_unique, Category.id_comp]
  rfl

theorem pull_spec_local {K : Type} [CommRing K] [IsLocalRing K] {X : Scheme.{0}} (y : Spec (CommRingCat.of K) ⟶ X)
    (c : CechPic.Pic X) : CechPic.pull y c = 0 := by
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  exact (cls_eq_zero_iff (pull_isLB hM y)).2 (DVR.exists_gen_of_local M hM _ _)

theorem isAffine_of_quasiAffine {X S : Scheme.{0}} [IsAffine S] [X.IsQuasiAffine] (f : X ⟶ S) [UniversallyClosed f] :
    IsAffine X := by
  have : UniversallyClosed (X.toSpecΓ ≫ Spec.map f.appTop) := by
    rw [← Scheme.toSpecΓ_naturality]; infer_instance
  have : UniversallyClosed X.toSpecΓ := .of_comp_of_isSeparated _ (Spec.map f.appTop)
  have : Surjective X.toSpecΓ := inferInstance
  exact ⟨isIso_of_isOpenImmersion_of_opensRange_eq_top _
    (top_unique fun x _ => X.toSpecΓ.surjective x)⟩

theorem quasiAffine_of_pull_add {X Y : Scheme.{0}} [CompactSpace X] (f g : X ⟶ Y) [IsAffineHom f] {M : LB Y}
    (hM : M.IsLB) {I : Type} (s : I → M.Sec) (hc : ⨆ i, nonzeroLocus (s i) = ⊤)
    (ha : ∀ i, IsAffineOpen (nonzeroLocus (s i)))
    (h : CechPic.pull f (cls M hM) + CechPic.pull g (cls M hM) = 0) : X.IsQuasiAffine := by
  refine Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen X fun x => ?_
  obtain ⟨a, hxa⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc.ge (Set.mem_univ (f x)))
  obtain ⟨b, hxb⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc.ge (Set.mem_univ (g x)))
  have hN := LB.isLB_linComb hM (Sum.elim (fun _ : PUnit => g) (fun _ : PUnit => f))
    (Sum.elim (fun _ => 1) (fun _ => 1))
  have h0 : cls _ hN = 0 := by
    rw [cls_linComb hM, Fintype.sum_sum_type]
    simpa [add_comm] using h
  obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_triv X) hN
    ((cls_eq_iff _ _).1 h0.symm)
    (DVR.mulSec M _ _ _ _ (secPull (s b) g) (secPull (s a) f))
  rw [nonzeroLocus_mulSec, nonzeroLocus_secPull (s a)] at ht
  have e : nonzeroLocus t = X.basicOpen (show Γ(X, ⊤) from t.f PUnit.unit) :=
    le_antisymm (iSup_le fun _ => le_rfl) (basicOpen_le_nonzeroLocus t PUnit.unit)
  refine ⟨t.f PUnit.unit, ?_, ?_⟩
  · rw [← e, ht]
    exact isAffineOpen_nonzeroLocus_inf (pull_isLB hM g) _ ((ha a).preimage f)
  · rw [← e, ht, nonzeroLocus_secPull]
    exact ⟨hxb, hxa⟩

section Points

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {L O : LB B.left}

theorem transl_const (hG : GlobalFnsSt) (hB : IsAbelianScheme B) (hL : L.IsLB) (hO : O.IsLB) {T : Over S} (x : T ⟶ B)
    (h : ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L x) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι)) (b : T ⟶ B) :
    CechPic.pull (x * b).left (cls L hL) - CechPic.pull b.left (cls L hL) - CechPic.pull b.left (cls O hO) =
      CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ B).left (cls L hL) -
        CechPic.pull (1 : T ⟶ B).left (cls O hO) := by
  have h₁ : (translDiff B L x).IsLB := LB.isLB_linComb hL _ _
  have h₂ := pull_isLB hO (snd T B).left
  have hM := LB.isLB_div h₁ h₂
  have val : ∀ b : T ⟶ B, CechPic.pull (lift (𝟙 T) b).left (cls _ hM) =
      CechPic.pull (x * b).left (cls L hL) - CechPic.pull b.left (cls L hL) - CechPic.pull b.left (cls O hO) := by
    intro b
    have e₁ : cls _ h₁ = CechPic.pull (lift (fst T B ≫ x) (snd T B) ≫ μ[B]).left (cls L hL) -
        CechPic.pull (snd T B).left (cls L hL) := by
      refine (cls_linComb hL _ _ h₁).trans ?_
      rw [Fin.sum_univ_two, sub_eq_add_neg]
      exact congrArg₂ (· + ·) (one_zsmul _) (neg_one_zsmul _)
    have a₁ : lift (𝟙 T) b ≫ (lift (fst T B ≫ x) (snd T B) ≫ μ[B]) = x * b := by
      rw [comp_lift_assoc, lift_fst_assoc, lift_snd, Category.id_comp]; rfl
    rw [cls_div h₁ h₂, e₁, cls_pull hO, map_sub, map_sub, ← pull_comp, ← pull_comp, ← pull_comp,
      ← Over.comp_left, ← Over.comp_left, a₁, lift_snd]
  have sec : ∀ b : T ⟶ B, (lift (𝟙 T) b).left ≫ (fst T B).left = 𝟙 _ := fun b => by
    rw [← Over.comp_left, lift_fst]; rfl
  have key := eq_pull_of_local (fst T B).left (lift (𝟙 T) (1 : T ⟶ B)).left (sec 1)
    (fun V => surj_of_isPullback hG hB
      ((IsPullback.of_hasPullback (fst T B).left V.ι).paste_horiz
        (IsPullback.of_hasPullback T.hom B.hom).flip)) (cls _ hM)
    (fun p => by
      obtain ⟨U, hU, ht⟩ := h p
      exact ⟨U, hU, (cls_eq_zero_iff (pull_isLB hM _)).2 ht⟩)
  have k := congrArg (CechPic.pull (lift (𝟙 T) b).left) key
  rw [← pull_comp, ← Category.assoc, sec, Category.id_comp, val, val, _root_.mul_one] at k
  exact k

theorem add_inv_eq [IsCommMonObj B] (hG : GlobalFnsSt) (hB : IsAbelianScheme B) (hL : L.IsLB) (hO : O.IsLB)
    {T : Over S} (x y : T ⟶ B)
    (hx : ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L x) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι))
    (hy : ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L y) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι)) :
    CechPic.pull x.left (cls L hL) + CechPic.pull (x⁻¹).left (cls L hL) =
      CechPic.pull y.left (cls L hL) + CechPic.pull (y⁻¹).left (cls L hL) := by
  have a := transl_const hG hB hL hO x hx (x⁻¹ * y⁻¹)
  have b := transl_const hG hB hL hO y hy (x⁻¹ * y⁻¹)
  rw [mul_inv_cancel_left] at a
  rw [mul_comm x⁻¹ y⁻¹, mul_inv_cancel_left, mul_comm y⁻¹ x⁻¹] at b
  linear_combination (norm := abel) b - a

end Points

theorem isFinite_of_relAmple : GlobalFnsSt → ∀ (R : Type) [CommRing R] (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ L O : LB B.left, L.IsLB → O.IsLB → RelAmple B L → ∀ (H : Over (Spec (CommRingCat.of R))) (j : H ⟶ B), IsClosedImmersion j.left → (∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ B), (∀ p : (T).left, ∃ U : (T).left.Opens, p ∈ U ∧ Triv ((LB.div (translDiff B L x) (O.pull (snd (T) B).left)).pull ((fst (T) B).left ⁻¹ᵁ U).ι)) ↔ ∃ y : T ⟶ H, y ≫ j = x) → IsFinite H.hom := by
  intro hG R _ B _ _ hB L O hL hO hA H j hj hH
  obtain ⟨d, -, n, s, hc, ha⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R B L hL).1 hA
  have := hB.proper
  have : IsProper H.hom := by rw [← Over.w j]; infer_instance
  suffices LocallyQuasiFinite H.hom from .of_isProper_of_locallyQuasiFinite _
  refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun z => ?_
  rcases Set.eq_empty_or_nonempty (H.hom ⁻¹' {z}) with h0 | ⟨h, hh⟩
  · rw [h0]; exact Set.finite_empty
  let K : Type := H.left.residueField h
  let y₀ : Spec (CommRingCat.of K) ⟶ H.left := H.left.fromSpecResidueField h
  let P : Over (Spec (CommRingCat.of R)) := Over.mk (y₀ ≫ H.hom)
  let y : P ⟶ H := Over.homMk y₀ rfl
  let π : (H ⊗ P).left ⟶ H.left := (fst H P).left
  let q : (H ⊗ P).left ⟶ Spec (CommRingCat.of K) := (snd H P).left
  have hpb : IsPullback π q H.hom (y₀ ≫ H.hom) := IsPullback.of_hasPullback H.hom P.hom
  have : IsProper q := MorphismProperty.of_isPullback hpb inferInstance
  have : IsAffineHom π := MorphismProperty.of_isPullback hpb.flip inferInstance
  have key := add_inv_eq hG hB hL hO (fst H P ≫ j) (snd H P ≫ y ≫ j) ((hH _ _).2 ⟨_, rfl⟩)
    ((hH _ _).2 ⟨snd H P ≫ y, Category.assoc _ _ _⟩)
  rw [← GrpObj.comp_inv (snd H P), Over.comp_left _ _ _ (snd H P), Over.comp_left _ _ _ (snd H P), pull_comp (snd H P).left,
    pull_comp (snd H P).left, pull_spec_local (K := K) (y ≫ j).left, pull_spec_local (K := K) (y ≫ j)⁻¹.left,
    map_zero, add_zero] at key
  have : CompactSpace (H ⊗ P).left := QuasiCompact.compactSpace_of_compactSpace q
  have : IsAffineHom (fst H P ≫ j).left := inferInstanceAs (IsAffineHom (π ≫ j.left))
  have : (H ⊗ P).left.IsQuasiAffine := quasiAffine_of_pull_add (fst H P ≫ j).left ((fst H P ≫ j)⁻¹).left
    (isLB_pw hL d) s hc (fun i => (ha i).1) (by
      rw [cls_pw hL, map_zsmul, map_zsmul, ← zsmul_add, key, zsmul_zero])
  have : IsAffine (H ⊗ P).left := isAffine_of_quasiAffine q
  have : IsFinite q := IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  have hfin : (Set.univ : Set (H ⊗ P).left).Finite := by
    have := q.finite_preimage_singleton (IsLocalRing.closedPoint K)
    refine this.subset fun t _ => Subsingleton.elim _ _
  refine (hfin.image π).subset fun w hw => ?_
  have e : H.hom w = (y₀ ≫ H.hom) (IsLocalRing.closedPoint K) := by
    have e₀ : y₀ (IsLocalRing.closedPoint K) = h := Scheme.fromSpecResidueField_apply h _
    exact (show H.hom w = z from hw).trans ((show H.hom h = z from hh).symm.trans (congrArg H.hom e₀).symm)
  obtain ⟨t, ht, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := H.hom) (g := y₀ ≫ H.hom) w _ e
  exact ⟨t, trivial, ht⟩

end GlobalTheory.AmpleStabFinite
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsHomogeneousXPowMulAddXPowMul
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ProjQuot

open MvPolynomial GlobalTheory.ProjSpace GlobalTheory.ThickeningDetermines

attribute [local instance] MvPolynomial.gradedAlgebra

section Algebra

variable {R A σ : Type} [CommRing R] [CommRing A] [Algebra R A] {r : σ → A} {i : σ}

theorem aeval_X_pow_mul (hi : r i = 1) (k : ℕ) (F : MvPolynomial σ R) :
    aeval r (X i ^ k * F) = aeval r F := by
  rw [map_mul, map_pow, aeval_X, hi, one_pow, _root_.one_mul]

theorem isHomogeneous_X_pow_mul_add_X_pow_mul (i : σ) {n m : ℕ} {F G : MvPolynomial σ R} (hF : F.IsHomogeneous n)
    (hG : G.IsHomogeneous m) : (X i ^ m * F + X i ^ n * G).IsHomogeneous (m + n) := by
  have h₁ : (X i ^ m * F).IsHomogeneous (m + n) := (isHomogeneous_X_pow i m).mul hF
  have h₂ : (X i ^ n * G).IsHomogeneous (m + n) := by
    simpa only [Nat.add_comm n m] using (isHomogeneous_X_pow i n).mul hG
  exact h₁.add h₂

theorem exists_isHomogeneous_aeval_eq (hi : r i = 1) (p : MvPolynomial σ R) :
    ∃ (n : ℕ) (G : MvPolynomial σ R), G.IsHomogeneous n ∧ aeval r G = aeval r p := by
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨0, C a, isHomogeneous_C _ a, rfl⟩
  | add p q hp hq =>
    obtain ⟨a, F, hF, eF⟩ := hp
    obtain ⟨b, G, hG, eG⟩ := hq
    refine ⟨b + a, X i ^ b * F + X i ^ a * G, isHomogeneous_X_pow_mul_add_X_pow_mul i hF hG, ?_⟩
    rw [map_add (f := _), aeval_X_pow_mul hi, aeval_X_pow_mul hi, eF, eG, map_add (f := _)]
  | mul_X p j hp =>
    obtain ⟨a, F, hF, eF⟩ := hp
    exact ⟨a + 1, F * X j, hF.mul (isHomogeneous_X R j), by rw [map_mul, map_mul, eF]⟩

def valueIdeal (hi : r i = 1) (hr : Function.Surjective (aeval (R := R) r))
    (J : Ideal (MvPolynomial σ R)) : Ideal A where
  carrier := {a | ∃ (n : ℕ) (G : MvPolynomial σ R), G.IsHomogeneous n ∧ G ∈ J ∧ aeval r G = a}
  zero_mem' := ⟨0, 0, isHomogeneous_zero _ R 0, J.zero_mem, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨n, F, hF, jF, rfl⟩ ⟨m, G, hG, jG, rfl⟩
    refine ⟨_, _, isHomogeneous_X_pow_mul_add_X_pow_mul i hF hG,
      J.add_mem (J.mul_mem_left _ jF) (J.mul_mem_left _ jG), ?_⟩
    rw [map_add (f := _), aeval_X_pow_mul hi, aeval_X_pow_mul hi]
  smul_mem' := by
    rintro c _ ⟨m, G, hG, jG, rfl⟩
    obtain ⟨p, rfl⟩ := hr c
    obtain ⟨n, F, hF, eF⟩ := exists_isHomogeneous_aeval_eq hi p
    exact ⟨_, _, hF.mul hG, J.mul_mem_left _ jG, by rw [map_mul, eF, smul_eq_mul]⟩

end Algebra

variable {R : Type} [CommRing R] {n : ℕ}

def formIdeal (J : Ideal (MvPolynomial (Fin (n + 1)) R)) : (PSpace R n).IdealSheafData :=
  ⨆ p : {p : ℕ × MvPolynomial (Fin (n + 1)) R // p.2.IsHomogeneous p.1 ∧ p.2 ∈ J},
    secIdeal (On_isLB R n p.1.1) (formSec p.1.1 p.1.2 p.2.1)

theorem ideal_secIdeal_formSec (i : Fin (n + 1)) (d : ℕ) (G : MvPolynomial (Fin (n + 1)) R)
    (hG : G.IsHomogeneous d) :
    (secIdeal (On_isLB R n d) (formSec d G hG)).ideal ⟨chart R n i, isAffineOpen_chart R n i⟩ =
      Ideal.span {aeval (ratio R n i) G} := by
  have hle : chart R n i ≤ (On R n (d : ℤ)).U (fun _ => i) := (On_U R n d (fun _ => i)).ge
  rw [GlobalTheory.ThickeningDetermines.secIdeal]
  refine (GlobalTheory.EffCartierData.ideal_locIdeal _ _ _ _ _ (fun _ => i) hle).trans ?_
  rw [formSec_f, resG_formOn, formOn_eq_aeval]

private theorem mem_valueIdeal_of_eq_one {S A σ : Type} [CommRing S] [CommRing A] [Algebra S A] {r : σ → A}
    {i : σ} (hi : r i = 1) (hr : Function.Surjective (aeval (R := S) r)) (J : Ideal (MvPolynomial σ S))
    (a : A) : a ∈ valueIdeal hi hr J ↔
      ∃ (m : ℕ) (G : MvPolynomial σ S), G.IsHomogeneous m ∧ G ∈ J ∧ aeval r G = a :=
  Iff.rfl

theorem aeval_mem_formIdeal_iff (J : Ideal (MvPolynomial (Fin (n + 1)) R)) (i : Fin (n + 1))
    {t : ℕ} {F : MvPolynomial (Fin (n + 1)) R} (hF : F.IsHomogeneous t) :
    aeval (ratio R n i) F ∈ (formIdeal J).ideal ⟨chart R n i, isAffineOpen_chart R n i⟩ ↔
      ∃ k : ℕ, X i ^ k * F ∈ J := by
  have hone : ratio R n i i = 1 := ratioOn_self
  have hsurj := aeval_ratio_surjective R n i
  have key : (formIdeal J).ideal ⟨chart R n i, isAffineOpen_chart R n i⟩ = valueIdeal hone hsurj J := by
    rw [formIdeal, Scheme.IdealSheafData.ideal_iSup, iSup_apply]
    simp only [ideal_secIdeal_formSec]
    apply le_antisymm
    · refine iSup_le fun p => ?_
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_valueIdeal_of_eq_one]
      exact ⟨p.1.1, p.1.2, p.2.1, p.2.2, rfl⟩
    · intro a ha
      obtain ⟨m, G, hG, jG, rfl⟩ := (mem_valueIdeal_of_eq_one hone hsurj J a).1 ha
      refine Ideal.mem_iSup_of_mem
        (⟨(m, G), hG, jG⟩ : {p : ℕ × MvPolynomial (Fin (n + 1)) R // p.2.IsHomogeneous p.1 ∧ p.2 ∈ J}) ?_
      exact Ideal.subset_span (Set.mem_singleton _)
  rw [key, mem_valueIdeal_of_eq_one]
  constructor
  · rintro ⟨m, G, hG, jG, e⟩
    refine ⟨m, ?_⟩
    have h₁ : (X i ^ m * F).IsHomogeneous (m + t) := (isHomogeneous_X_pow i m).mul hF
    have h₂ : (X i ^ t * G).IsHomogeneous (m + t) := by
      simpa only [Nat.add_comm t m] using (isHomogeneous_X_pow i t).mul hG
    have hEq : X i ^ m * F = X i ^ t * G := by
      rw [← formOn_chart_inj R n i h₁ h₂, formOn_eq_aeval, formOn_eq_aeval]
      change aeval (ratio R n i) (X i ^ m * F) = aeval (ratio R n i) (X i ^ t * G)
      rw [aeval_X_pow_mul hone, aeval_X_pow_mul hone, e]
    rw [hEq]
    exact J.mul_mem_left _ jG
  · rintro ⟨k, hk⟩
    exact ⟨k + t, X i ^ k * F, (isHomogeneous_X_pow i k).mul hF, hk, aeval_X_pow_mul hone k F⟩

private theorem resG_refl' {Y : Scheme.{0}} {U : Y.Opens} (h : U ≤ U) (a : Γ(Y, U)) :
    resG Y h a = a := by
  have e : homOfLE h = 𝟙 U := Subsingleton.elim _ _
  rw [resG, e, op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id, RingHom.id_apply]

private theorem appLE_congr_of_eq' {Y Z : Scheme.{0}} (φ : Y ⟶ Z) {U : Z.Opens} {V : Y.Opens} (e : V ≤ φ ⁻¹ᵁ U)
    (a : Γ(Z, U)) : (φ.appLE U V e).hom a = resG Y e ((φ.app U).hom a) := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply]

private theorem cst_comp_eq_resG_app {Y Z : Scheme.{0}} {S : Type} [CommRing S] (φ : Y ⟶ Z)
    (g : Z ⟶ Spec (CommRingCat.of S)) (U : Z.Opens) (V : Y.Opens) (e : V ≤ φ ⁻¹ᵁ U)
    (h : U ≤ g ⁻¹ᵁ ⊤) (a : S) :
    GlobalTheory.AbLaw.cst (φ ≫ g) V a = resG Y e ((φ.app U).hom ((g.appLE ⊤ U h).hom
      ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom a))) := by
  rw [← appLE_congr_of_eq', ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, appLE_congr_of_eq']
  rfl

theorem eval₂Hom_secPull_coord {Y : Scheme.{0}} (φ : Y ⟶ PSpace R n) (k : PUnit → Fin (n + 1))
    (F : MvPolynomial (Fin (n + 1)) R) :
    eval₂Hom (cst (φ ≫ PSpace.str R n) (((O1 R n).pull φ).U k))
        (fun j => (Cartier.secPull (coord R n j) φ).f k) F =
      resG Y (Cartier.pull_U (O1 R n) φ k).le
        ((φ.app (chart R n (k ⟨⟩))).hom (aeval (ratio R n (k ⟨⟩)) F)) := by
  have hle := (Cartier.pull_U (O1 R n) φ k).le
  have key : (eval₂Hom (cst (φ ≫ PSpace.str R n) (((O1 R n).pull φ).U k))
      fun j => (Cartier.secPull (coord R n j) φ).f k) =
      (resG Y hle).comp ((φ.app (chart R n (k ⟨⟩))).hom.comp (aeval (ratio R n (k ⟨⟩))).toRingHom) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · show _ = resG Y hle ((φ.app (chart R n (k ⟨⟩))).hom (aeval (ratio R n (k ⟨⟩)) (C a)))
      rw [eval₂Hom_C, aeval_C, algebraMap_sections_eq, CommRingCat.comp_apply]
      exact cst_comp_eq_resG_app φ (PSpace.str R n) _ _ hle le_top a
    · show _ = resG Y hle ((φ.app (chart R n (k ⟨⟩))).hom (aeval (ratio R n (k ⟨⟩)) (X j)))
      rw [eval₂Hom_X', aeval_X, ← resG_refl' (le_refl (((O1 R n).pull φ).U k)) ((Cartier.secPull (coord R n j) φ).f k),
        resG_secPull_coord φ j k (le_refl _), pullRatio, appLE_congr_of_eq']
      rfl
  exact RingHom.congr_fun key F

private theorem eq_zero_of_resG_eq_zero_of_eq {Y : Scheme.{0}} {U V : Y.Opens} (hUV : V = U) {h : V ≤ U}
    {a : Γ(Y, U)} (ha : resG Y h a = 0) : a = 0 := by
  subst hUV
  have e : homOfLE h = 𝟙 V := Subsingleton.elim _ _
  rwa [resG, e, op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id, RingHom.id_apply] at ha

theorem exists_veryAmpleBy_of_ideal : ∀ (R : Type) [CommRing R] (n : ℕ) (J : Ideal (MvPolynomial (Fin (n + 1)) R)), (∀ F ∈ J, ∀ t, MvPolynomial.homogeneousComponent t F ∈ J) → ∃ (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (s : Fin (n + 1) → LB.Sec H), H.IsLB ∧ VeryAmpleBy f H s ∧ ∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → ((∀ k : (H).ι, MvPolynomial.eval₂Hom (cst (f) ((H).U k)) (fun j => (s j).f k) (F) = 0) ↔ ∀ i, ∃ k : ℕ, MvPolynomial.X i ^ k * F ∈ J) := by
  intro R _ n J _
  refine ⟨(formIdeal J).subscheme, (formIdeal J).subschemeι ≫ PSpace.str R n,
    (O1 R n).pull (formIdeal J).subschemeι,
    fun j => Cartier.secPull (coord R n j) (formIdeal J).subschemeι,
    pull_isLB (O1_isLB R n) _, veryAmpleBy_secPull_coord _, fun t F hF => ?_⟩
  constructor
  · intro h i
    rw [← aeval_mem_formIdeal_iff J i hF, ← Scheme.IdealSheafData.ker_subschemeι_app, RingHom.mem_ker]
    exact eq_zero_of_resG_eq_zero_of_eq (Cartier.pull_U (O1 R n) _ (fun _ => i))
      ((eval₂Hom_secPull_coord _ (fun _ => i) F).symm.trans (h (fun _ => i)))
  · intro h k
    obtain ⟨m, hm⟩ := h (k ⟨⟩)
    have hz := (aeval_mem_formIdeal_iff J (k ⟨⟩) hF).2 ⟨m, hm⟩
    rw [← Scheme.IdealSheafData.ker_subschemeι_app, RingHom.mem_ker] at hz
    exact ((eval₂Hom_secPull_coord _ k F).trans (congrArg _ hz)).trans (map_zero _)

end GlobalTheory.ProjQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfGenericAbelianOfClosedIsGt
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem isSemiAbelian_of_grpIso {S : Scheme.{0}} {G₁ G₂ : Over S} [GrpObj G₁] [GrpObj G₂] [hc : IsCommMonObj G₂]
    (e : G₂ ≅ G₁) [IsMonHom e.hom] (h : IsSemiAbelian G₁) : IsSemiAbelian G₂ := by
  have hi : IsIso e.hom.left := ((Over.forget S).mapIso e).isIso_hom
  have hw : G₂.hom = e.hom.left ≫ G₁.hom := (Over.w e.hom).symm
  have := h.smooth
  have := h.separated
  have := h.quasiCompact
  have hg := h.geomConnected
  refine ⟨hc, ?_, ?_, ?_, ?_, fun Ω _ _ q => ?_⟩
  · rw [hw]; infer_instance
  · rw [hw]; infer_instance
  · rw [hw]; infer_instance
  · refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ q => ?_⟩
    have hi' : IsIso ((Over.pullback q).map e.hom).left :=
      ((Over.pullback q ⋙ Over.forget _).mapIso e).isIso_hom
    have h1 : ConnectedSpace ((Over.pullback q).obj G₁).left := pullback_of_geometrically hg.1 K q
    exact (((Over.pullback q).map e.hom).left.homeomorph.connectedSpace_iff).2 h1
  · obtain ⟨E⟩ := h.fibres Ω q
    have : IsMonHom ((Over.pullback q).mapIso e).hom := inferInstanceAs (IsMonHom ((Over.pullback q).map e.hom))
    have : IsMonHom ((Over.pullback q).mapIso e).symm.hom :=
      inferInstanceAs (IsMonHom ((Over.pullback q).mapIso e).inv)
    exact ⟨torusExtOfIso ((Over.pullback q).mapIso e).symm E⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaExpansionFunctionalEquationDegreeOne
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU

theorem fe_one_of_psiRel : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → PsiRel D (𝟙_ _) f → U.FE (Kbar V) 1) := by
  intro h₁ h₂ V _ _ _ hV D A G _ _ U θ f hθ hψ t s hts
  obtain ⟨hp, hq⟩ := PullSec.pullEx V hV D A G U (Kbar V) (𝟙_ _) (toUnit _) 1
  obtain ⟨th, hth, -⟩ := hp θ
  obtain ⟨s₀, hs₀, -⟩ := hq f
  obtain ⟨c, hc⟩ := (GlobalTheory.T.expF_of_theta_degree_one h₁ h₂ V hV D A G U θ f hθ th s₀ hth hs₀).2.2 t s hts
  exact famFE_one_of_psiRel h₁.globalFns V D (Kbar V) s₀ s c (GlobalTheory.T.thetaPsiRelation_of_pullback_extension_field V D (Kbar V) f s₀ hs₀ hψ) hc

end GlobalTheory.UU
end
end

