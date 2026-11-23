module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0743
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRootStalk
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1961
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DotProductMulVecEqTransposeMulVec
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitIffValEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.ScaleAtModel

open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusExt GlobalTheory.ZH.TestVal GlobalTheory.ThetaDvr.Scale

theorem isUnit_iff_val_eq {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}
    (hv : ValOver ϖ F v) {s y : FractionRing V} (hs : s ≠ 0) {w : V}
    (hw : y = s * algebraMap V (FractionRing V) w)
    (hle : v (algebraMap (FractionRing V) F s) ≤ v (algebraMap (FractionRing V) F y)) :
    IsUnit w ↔ v (algebraMap (FractionRing V) F y) = v (algebraMap (FractionRing V) F s) := by
  have inj := IsFractionRing.injective V (FractionRing V)
  constructor
  · intro hu
    by_contra hne
    have hlt := lt_of_le_of_ne hle (fun h => hne h.symm)
    obtain ⟨w'', hw'', hm⟩ := GlobalTheory.ThetaDvr.exists_mul_of_val_le hϖ hv hs hle
    have e : w'' = w := by
      apply inj
      have : s * (algebraMap V (FractionRing V) w'' - algebraMap V (FractionRing V) w) = 0 := by
        linear_combination hw - hw''
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hs)
    exact (IsLocalRing.mem_maximalIdeal _).1 (e ▸ hm hlt) hu
  · intro heq
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero, AddValuation.map_zero] at heq
      exact hs ((map_eq_zero_iff _ (algebraMap (FractionRing V) F).injective).1 ((AddValuation.top_iff v).1 heq.symm))
    obtain ⟨w', hw', -⟩ := GlobalTheory.ThetaDvr.exists_mul_of_val_le hϖ hv hy0 heq.le
    have e : s * (algebraMap V (FractionRing V) (w * w') - 1) = 0 := by
      rw [map_mul]; linear_combination -hw' - (algebraMap V (FractionRing V) w') * hw
    have e' : w * w' = 1 := inj (by rw [map_one]; exact sub_eq_zero.1 ((mul_eq_zero.1 e).resolve_left hs))
    exact IsUnit.of_mul_eq_one w' e'


open MonObj in
attribute [local instance] gtGroup in
theorem scale_at_model : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (maximalIdeal V) V → IsUnit ((S.r * S.N : ℕ) : V) →
    ∀ (σ : S.R →+* FractionRing V) (A : PolAV (Sp (FractionRing V))) (φ : A.A.left ⟶ ρ.P.A.left),
    IsGrpPullback A.A ρ.P.A (spMap σ) φ → LBIso A.L (ρ.P.L.pull φ) →
    ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (D : DegData V (maximalIdeal V)) (U : Unif (maximalIdeal V) D A G), (∃ a, σ ⟨S.th a, S.th_mem a⟩ ≠ 0) →
    ∃ (s : FractionRing V) (v : S.Gam → V), s ≠ 0 ∧
      (∀ a, σ ⟨S.th a, S.th_mem a⟩ = s * algebraMap V (FractionRing V) (v a)) ∧
      (∀ a, ∃ (pk : QkPt D.toPre (AlgebraicClosure (FractionRing V)) (S.r * S.N)) (x : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A),
        QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) (S.r * S.N) pk x ∧
        x.left ≫ φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp σ) ≫ (ρ.pt a).left) ∧
      (∀ a (pk : QkPt D.toPre (AlgebraicClosure (FractionRing V)) (S.r * S.N)) (x : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A),
        QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) (S.r * S.N) pk x →
        x.left ≫ φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp σ) ≫ (ρ.pt a).left →
        (IsUnit (v a) → ∃ z, pk.y = (S.r * S.N) • z) ∧
        ((∃ z, pk.y = (S.r * S.N) • z) → ∃ b : S.Gam, ρ.n • b = 0 ∧ IsUnit (v (a + b)))) := by
  intro o' Ω _ _ _ S ρ V _ _ _ _ hc hu σ A φ cart lb G _ _ semi D U hne
  obtain ⟨hL, hL₂, -⟩ := GlobalTheory.allSixLaws
  obtain ⟨H, h₁, h₂, h₃, h₄⟩ := GlobalTheory.ZH.TestVal.hyps hL hL₂
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨v, hv, -⟩ := GlobalTheory.ValClosure.exists_valuation_closure V ϖ hϖ
  have hm := odd_level' ρ
  have hA : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  have hB := D.tau_bimult
  choose Q hQ using QForm.exists_QVal hϖ D
  obtain ⟨x, hx, xadd, xinj, xonto⟩ := GlobalTheory.ThetaDvr.torsion_points σ cart
  obtain ⟨rig, e, hrig, he, hsec⟩ := GlobalTheory.ThetaDvr.frames σ cart lb x hx
  obtain ⟨t, ht⟩ := hsec 1 ρ.th₁
  obtain ⟨w₀, hw₀⟩ := EvalZero.exists_normW U.toUnifPre rig hrig
  obtain ⟨th, ϑ, hE, hP, hgen⟩ := exists_prim_generator H h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ _ v hv A G
    semi U w₀ hw₀.1
  have key := val_theta H h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ _ v hv A G semi U w₀ rig hw₀ th ϑ hE hP
    _ hm hu
  obtain ⟨f, f₁, f₂, f₃, -⟩ := GlobalTheory.TorsionIso.torsion_eq H V _ hA D A G semi U
    (AlgebraicClosure (FractionRing V)) _ hm.pos
  obtain ⟨r, hr⟩ := hgen t
  obtain ⟨sc, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure (FractionRing V)))).inv).2 r
  set F := AlgebraicClosure (FractionRing V) with hF
  set iK := algebraMap (FractionRing V) F with hiK
  set y₀ : S.R →+* F := iK.comp σ with hy₀
  have tv : ∀ a z J, Good A.L z J → cst (R := V) F z sc *
      @id ((TF (R := V) F).left.presheaf.stalk z) (sA th (ptSecT A.A (x a)).left z J) =
      cst (R := V) F z (y₀ ⟨S.th a, S.th_mem a⟩) * @id ((TF (R := V) F).left.presheaf.stalk z)
        (val (powFrame A.A A.L (x a) (e a) ((1 : ℕ) : ℤ)) (𝟙 _) z J).val := fun a z J hJ =>
    (ThetaCompare.sval_smul hr (x a) hJ).symm.trans (ht a _ (by
      have b := ρ.th_val a
      rw [← powFrame_one' (ρ.pt a) (ρ.fr a)] at b
      exact b) z J hJ)
  have uniq : ∀ a (x' : TFK (R := V) F ⟶ A.A), x'.left ≫ φ = spMap (iK.comp σ) ≫ (ρ.pt a).left → x' = x a :=
    fun a x' h' => by
      apply Over.OverMorphism.ext
      exact cart.1.hom_ext (h'.trans (hx a).symm) ((Over.w x').trans (Over.w (x a)).symm)
  have h0 : sc ≠ 0 := by
    intro h0
    obtain ⟨a, ha⟩ := hne
    apply ha
    obtain ⟨z⟩ := CoefBasic.exists_pt (R := V) (F := F)
    obtain ⟨J, hJ⟩ := CoefBasic.exists_good' (Z := (TFK (R := V) F).left) A.isLB z
    have := tv a z J hJ
    rw [h0, CoefBasic.cst_eq, CoefBasic.cst_eq, map_zero, zero_mul] at this
    have z0 : y₀ ⟨S.th a, S.th_mem a⟩ = 0 :=
      CoefBasic.cstH_inj (R := V) z (((Units.mul_left_eq_zero _).1 this.symm).trans (map_zero _).symm)
    exact (map_eq_zero_iff _ iK.injective).1 z0
  have tv' : ∀ a z J, Good A.L z J → sA th (ptSecT A.A (x a)).left z J =
      @id ((TFK (R := V) F).left.presheaf.stalk z)
        (cst (R := V) F z (sc⁻¹ * y₀ ⟨S.th a, S.th_mem a⟩)) *
        (val (powFrame A.A A.L (x a) (e a) ((1 : ℕ) : ℤ)) (𝟙 _) z J).val := fun a z J hJ => by
    have b := congrArg (CoefBasic.cstH (R := V) z sc⁻¹ * ·) (tv a z J hJ)
    simp only [CoefBasic.cst_eq, ← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ h0, map_one, _root_.one_mul] at b
    rw [CoefBasic.cst_eq]
    exact b
  have hvs : v sc ≠ ⊤ := v.ne_top_iff.2 h0
  have split : ∀ a, v (y₀ ⟨S.th a, S.th_mem a⟩) = v sc + v (sc⁻¹ * y₀ ⟨S.th a, S.th_mem a⟩) := fun a => by
    rw [← v.map_mul, ← _root_.mul_assoc, mul_inv_cancel₀ h0, _root_.one_mul]
  have nz : ∀ a, v (sc⁻¹ * y₀ ⟨S.th a, S.th_mem a⟩) = 0 ↔ v (y₀ ⟨S.th a, S.th_mem a⟩) = v sc := fun a => by
    rw [split a]
    constructor
    · intro h; rw [h, add_zero]
    · intro h
      obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 hvs
      rw [← hs] at h
      have e1 := congrArg (((-s : ℚ) : WithTop ℚ) + ·) h
      simp only [← add_assoc, ← WithTop.coe_add, neg_add_cancel, WithTop.coe_zero, zero_add] at e1
      exact e1

  have low : ∀ b, v sc ≤ v (y₀ ⟨S.th b, S.th_mem b⟩) := fun b => by
    obtain ⟨q, hq⟩ := f₂ (x b) (he b).1
    have hk := (key q _ ((f₁ _ _).2 hq.symm)).1 _ _ (he b) (tv' b)
    have lo : (0 : WithTop ℚ) ≤ v (sc⁻¹ * y₀ ⟨S.th b, S.th_mem b⟩) := by
      have := hk.1 0 fun χ => by
        by_cases c : (S.r * S.N) • χ + q.y = 0
        · rw [c, QForm.Q_zero hϖ D hQ]; simp
        · exact div_nonneg (Int.cast_nonneg (zero_le_one.trans (QForm.Q_pos hϖ D hQ c))) (Nat.cast_nonneg _)
      simpa using this
    rw [split b]; exact le_add_of_nonneg_right lo
  have dvd : ∀ b (q : QkPt D.toPre F (S.r * S.N)), QkToAkU U.toUnifPre F (S.r * S.N) q (x b) →
      v (y₀ ⟨S.th b, S.th_mem b⟩) = v sc → ∃ z, q.y = (S.r * S.N) • z := fun b q hq h =>
    ((key q _ hq).1 _ _ (he b) (tv' b)).2 ((nz b).2 h)

  obtain ⟨j, hj, hrj⟩ := ρ.r_eq
  have hnd : ρ.n ∣ S.r * S.N := by
    rw [hrj, ρ.N_eq]
    exact Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) _
  have coset : ∀ a (q : QkPt D.toPre F (S.r * S.N)), QkToAkU U.toUnifPre F (S.r * S.N) q (x a) →
      (∃ z, q.y = (S.r * S.N) • z) → ∃ a', ρ.n • (a' - a) = 0 ∧ v (y₀ ⟨S.th a', S.th_mem a'⟩) = v sc := by
    rintro a q hq₁ ⟨z, hz'⟩
    let q₀ : QkPt D.toPre F (S.r * S.N) := qkMk hB 0 (q.g + iota hB _ (-z)) (by
      rw [smul_add, qk_nsmul hB, ← map_nsmul, ← map_add (f := _), smul_neg, ← hz', add_neg_cancel])
    have e₀ : f q = f q₀ := (f₃ _ _).2 ((equiv_iff hB _ _).2 ⟨-z, by
      rw [smul_neg, ← hz', add_neg_cancel]; rfl, rfl⟩)
    obtain ⟨q', x', hy', hx', hpow, hval⟩ :=
      (key q₀ (x a) ((f₁ _ _).2 (((f₁ _ _).1 hq₁).trans e₀))).2 ρ.n ρ.n_prime.two_le hnd (by simp [q₀])
    obtain ⟨a', rfl⟩ := xonto x' (hx' w₀ hw₀.1).1
    have := A.isAb.comm
    let X : Multiplicative S.Gam →* (TFK (R := V) F ⟶ A.A) :=
      MonoidHom.mk' (fun a => x a.toAdd) fun a b => xadd _ _
    refine ⟨a', xinj ?_, (nz a').1 (hval _ _ (he a') (tv' a'))⟩
    have b : X ((Multiplicative.ofAdd a' * (Multiplicative.ofAdd a)⁻¹) ^ ρ.n) = X 1 := by
      rw [map_pow, map_mul, map_inv, map_one]; exact hpow
    rw [sub_eq_add_neg]
    exact b

  have q0 : QkToAkU U.toUnifPre F (S.r * S.N)
      (qkMk hB 0 0 (by rw [smul_zero, map_zero]) : QkPt D.toPre F (S.r * S.N)) (f (qkMk hB 0 0 (by rw [smul_zero, map_zero]))) :=
    (f₁ _ _).2 rfl
  obtain ⟨a₁, ha₁⟩ := xonto _ (q0 w₀ hw₀.1).1
  obtain ⟨a₀, -, ha₀⟩ := coset a₁ _ (ha₁ ▸ q0) ⟨0, by simp⟩
  set s := σ ⟨S.th a₀, S.th_mem a₀⟩ with hs_def
  have hs0 : s ≠ 0 := by
    intro h
    have : v (y₀ ⟨S.th a₀, S.th_mem a₀⟩) = ⊤ := by
      show v (iK s) = ⊤
      rw [h, map_zero, AddValuation.map_zero]
    exact hvs (ha₀.symm.trans this)
  have hle : ∀ b, v (iK s) ≤ v (iK (σ ⟨S.th b, S.th_mem b⟩)) := fun b => by
    have h1 : v (iK s) = v sc := ha₀
    rw [h1]; exact low b
  choose w hw using fun b => (GlobalTheory.ThetaDvr.exists_mul_of_val_le hϖ hv hs0 (hle b))
  have hw' : ∀ b, σ ⟨S.th b, S.th_mem b⟩ = s * algebraMap V (FractionRing V) (w b) := fun b => by
    rw [(hw b).1, mul_comm]
  have unit_iff : ∀ b, IsUnit (w b) ↔ v (y₀ ⟨S.th b, S.th_mem b⟩) = v sc := fun b => by
    rw [← ha₀]
    exact isUnit_iff_val_eq hϖ hv hs0 (hw' b) (hle b)
  refine ⟨s, w, hs0, hw', fun a => ?_, fun a pk x' hpk hx' => ?_⟩
  · obtain ⟨q, hq⟩ := f₂ (x a) (he a).1
    exact ⟨q, x a, (f₁ _ _).2 hq.symm, hx a⟩
  · obtain rfl := uniq a x' hx'
    refine ⟨fun hu' => dvd a pk hpk ((unit_iff a).1 hu'), fun hd => ?_⟩
    obtain ⟨a', hn, hv'⟩ := coset a pk hpk hd
    refine ⟨a' - a, hn, ?_⟩
    rw [add_sub_cancel]
    exact (unit_iff a').2 hv'

end GlobalTheory.Poinc.ScaleAtModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyTorsionGeneratorPower
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KillSquare

open GlobalTheory.CechPic

section SlopeTestRemainingChoices

open GlobalTheory GlobalTheory.CM GlobalTheory.KerPow GlobalTheory.CM.PairingIso

theorem eq_one_of_lam_eq_zero {S : Scheme.{0}} (P : Out.PolAV S) [IsCommMonObj P.A] {T : Over S}
    (z : T ⟶ P.A) (h : lam (cls P.L P.isLB) (fst T P.A ≫ z) (snd T P.A) = 0) : z = 1 := by
  have hL := P.isLB
  have hc : (cubeLB P.A ![fst T P.A ≫ z, snd T P.A] P.L).IsLB := LB.isLB_linComb hL _ _
  have g₂ : GlobalTheory.KerPow.HasGen P.L
      (fun I : ULift.{0} (Finset (Fin 2)) => (psum P.A ![fst T P.A ≫ z, snd T P.A] I.down).left)
      (fun I => (-1) ^ (2 - I.down.card)) :=
    (cls_eq_zero_iff hc).1 ((cls_cube_two hL _ _ hc).trans h)
  have g₃ : LocGen P.L (fst T P.A).left
      (fun I : ULift.{0} (Finset (Fin 2)) => (psum P.A ![fst T P.A ≫ z, snd T P.A] I.down).left)
      (fun I => (-1) ^ (2 - I.down.card)) := fun _ => ⟨⊤, trivial, g₂.pull _ fun _ => rfl⟩
  have b₁ := locGen_base hL (fst T P.A).left z.left (b := (fst T P.A ≫ z).left) rfl
  have b₀ := locGen_base hL (fst T P.A).left (1 : T ⟶ P.A).left (b := (1 : T ⊗ P.A ⟶ P.A).left)
    (congrArg (fun q : T ⊗ P.A ⟶ P.A => q.left) (MonObj.comp_one (fst T P.A) : fst T P.A ≫ (1 : T ⟶ P.A) = 1).symm)
  have b := b₀.comb hL b₁ (φ'' := ![(1 : T ⊗ P.A ⟶ P.A).left, (fst T P.A ≫ z).left]) (ε'' := ![1, -1])
    fun U _ k => by simp [Fin.prod_univ_two]
  refine eq_one_of_locGen P.ktriv z (g₃.comb hL b fun U _ k => ?_)
  rw [PrimNorm.prod_square_id, Fin.prod_univ_two, Fin.prod_univ_two]
  show k ((fst T P.A ≫ z) * snd T P.A).left * (k (fst T P.A ≫ z).left)⁻¹ * (k (snd T P.A).left)⁻¹ *
    k (1 : T ⊗ P.A ⟶ P.A).left *
    (k (1 : T ⊗ P.A ⟶ P.A).left ^ (1 : ℤ) * k (fst T P.A ≫ z).left ^ (-1 : ℤ))⁻¹ =
    k ((fst T P.A ≫ z) * snd T P.A).left ^ (1 : ℤ) * k (snd T P.A).left ^ (-1 : ℤ)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

end SlopeTestRemainingChoices

end GlobalTheory.KillSquare

namespace GlobalTheory.KillSquare

open GlobalTheory.CechPic

theorem pow_sq_eq_one_of_lam_trivial : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB →
    ∀ (P : Out.PolAV (Sp ℂ)) (ψ : A ⟶ P.A) (ρ : P.A ⟶ A) (N : ℕ), IsMonHom ψ → IsMonHom ρ →
      ψ ≫ ρ = (𝟙 A) ^ N → ρ ≫ ψ = (𝟙 P.A) ^ N →
      LBIso (abelian₂ A M) ((abelian₂ P.A P.L).pull (lift (fst A A ≫ ψ) (snd A A ≫ ψ)).left) →
    ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), HasGen ((abelian₂ A M).pull (lift (fst A T) (snd A T ≫ x)).left) → x ^ (N * N) = 1 := by
  intro A _ hA M hM P ψ ρ N hψ hρ h1 h2 hiso T x hx
  haveI : IsCommMonObj A := hA.comm
  haveI := P.isAb
  have hL := P.isLB
  have hΘ := GlobalTheory.exists_gen_theta_of_isAbelianScheme ℂ P.A P.isAb P.L hL
  set ℓ := cls P.L hL
  set m := cls M hM

  have hlamA : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
  have hpair : lam m (fst A A) (snd A A) = lam ℓ (fst A A ≫ ψ) (snd A A ≫ ψ) := by
    have hlamP : (abelian₂ P.A P.L).IsLB := LB.isLB_linComb hL _ _
    have e := (cls_eq_iff hlamA (pull_isLB hlamP _)).2 hiso
    exact (cls_cube_two hM (fst A A) (snd A A) hlamA).symm.trans (e.trans (Elliptic.cls_pull_lam hL _ _ _))

  have hx0 : lam m (fst A T) (snd A T ≫ x) = 0 := by
    rw [← Elliptic.cls_pull_lam hM _ _ (pull_isLB hlamA _)]
    exact (cls_eq_zero_iff _).2 hx
  have e1 := congrArg (pull (lift (fst A T) (snd A T ≫ x)).left) hpair
  simp only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] at e1
  rw [e1] at hx0

  have e2 := congrArg (pull (lift (fst P.A T ≫ ρ) (snd P.A T)).left) hx0
  simp only [pull_lam, map_zero, lift_fst_assoc, lift_snd_assoc, Category.assoc] at e2
  have e3 : fst P.A T ≫ ρ ≫ ψ = fst P.A T ^ N := by
    rw [h2, MonObj.comp_pow, Category.comp_id]
  rw [e3, lam_pow_left hL hΘ, ← lam_pow_right hL hΘ, ← MonObj.comp_pow] at e2

  have hz : (x ≫ ψ) ^ N = 1 := by
    refine GlobalTheory.KillSquare.eq_one_of_lam_eq_zero P _ ?_
    have e4 := congrArg (pull (lift (snd T P.A) (fst T P.A)).left) e2
    simp only [pull_lam, map_zero, lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd] at e4
    rw [lam_comm] at e4
    simpa only [Category.assoc] using e4
  rw [pow_mul]
  have e5 : x ^ N = (x ≫ ψ) ≫ ρ := by
    rw [Category.assoc, h1, MonObj.comp_pow, Category.comp_id]
  rw [e5, ← MonObj.pow_comp, hz, MonObj.one_comp]

end GlobalTheory.KillSquare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetFamilyDeriv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.JetFam

open TrivSqZeroExt in
theorem dual_unit {a a' : ℂ} (ha : a ≠ 0) : IsUnit (inl a + inr a' : DualNumber ℂ) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
  simpa using ha

open TrivSqZeroExt in
theorem dual_mul {S V : DualNumber ℂ} {a a' r r' p p' e : ℂ} {k : ℕ} (ha : a ≠ 0) (hr : r ≠ 0)
    (h1 : S * inl a * (inl r + inr r') = (inl p + inr p') * (inl r + inr r') ^ k * (inl a + inr a') * inl r)
    (h2 : V * (inl a + inr a') * inl r = (1 + inr e) * inl a * (inl r + inr r')) :
    (S * V).fst / r ^ k = p ∧ (S * V).snd / r ^ k = p' + e * p + k * (r' / r) * p := by
  have ua : IsUnit (inl a : DualNumber ℂ) := by simpa using dual_unit (a' := 0) ha
  have ur : IsUnit (inl r : DualNumber ℂ) := by simpa using dual_unit (a' := 0) hr
  have hu := ((ua.mul (dual_unit (a' := r') hr)).mul (dual_unit (a' := a') ha)).mul ur
  have key : S * V = (inl p + inr p') * (inl r + inr r') ^ k * (1 + inr e) := by
    apply hu.mul_right_cancel
    linear_combination (V * (inl a + inr a') * inl r) * h1 +
      ((inl p + inr p') * (inl r + inr r') ^ k * (inl a + inr a') * inl r) * h2
  rw [key]
  constructor
  · simp [hr]
  · rcases k with _ | k
    · simp; ring
    · simp [TrivSqZeroExt.snd_pow]
      field_simp
      ring

open TrivSqZeroExt in
theorem dual_zero {V : DualNumber ℂ} {a r e : ℂ} (ha : a ≠ 0) (hr : r ≠ 0)
    (h2 : V * (inl a + inr 0) * inl r = (1 + inr e) * inl a * (inl r + inr 0)) : V = 1 + inr e := by
  have ua : IsUnit (inl a : DualNumber ℂ) := by simpa using dual_unit (a' := 0) ha
  have ur : IsUnit (inl r : DualNumber ℂ) := by simpa using dual_unit (a' := 0) hr
  apply (ua.mul ur).mul_right_cancel
  rw [inr_zero, add_zero, add_zero] at h2
  linear_combination h2

variable {g' r g : ℕ} (σ : Fin g ≃ Fin g' ⊕ Fin r)

def join (z : Fin g' → ℂ) (t : Fin r → ℂ) : Fin g → ℂ := fun j => Sum.elim z t (σ j)

theorem leftComponent_join (z : Fin g' → ℂ) (t : Fin r → ℂ) : zP σ (join σ z t) = z := by
  funext i; simp [zP, join]

theorem secondBlock_join (z : Fin g' → ℂ) (t : Fin r → ℂ) : tP σ (join σ z t) = t := by
  funext i; simp [tP, join]

theorem join_zero : join σ 0 0 = 0 := by
  funext j; simp only [join]; rcases σ j with i | i <;> simp

theorem diff_join : Differentiable ℂ fun z : Fin g' → ℂ => join σ z 0 := by
  refine differentiable_pi.2 fun j => ?_
  simp only [join]
  rcases σ j with i | i
  · simp only [Sum.elim_inl]; fun_prop
  · simp

def zL : (Fin g → ℂ) →L[ℂ] (Fin g' → ℂ) := ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (σ.symm (Sum.inl i))

def tL (c : ℂ) (v : Fin r → ℂ) : (Fin g → ℂ) →L[ℂ] ℂ :=
  c • ∑ l, v l • ContinuousLinearMap.proj (σ.symm (Sum.inr l))

theorem zL_apply (Y : Fin g → ℂ) : zL σ Y = zP σ Y := rfl

theorem tL_apply (c : ℂ) (v : Fin r → ℂ) (Y : Fin g → ℂ) : tL σ c v Y = c * (v ⬝ᵥ tP σ Y) := by
  simp [tL, tP, dotProduct]

theorem fderiv_eq (c : ℂ) (v : Fin r → ℂ) {F : (Fin g → ℂ) → ℂ} {φ : (Fin g' → ℂ) → ℂ} (hφ : Differentiable ℂ φ)
    (h : ∀ Y, F Y = Complex.exp (c * (v ⬝ᵥ tP σ Y)) * φ (zP σ Y)) (Z : Fin g → ℂ) :
    fderiv ℂ F 0 Z = fderiv ℂ φ 0 (zP σ Z) + c * (v ⬝ᵥ tP σ Z) * φ 0 := by
  have e : F = fun Y => Complex.exp (tL σ c v Y) * φ (zL σ Y) := by
    funext Y; rw [h, tL_apply, zL_apply]
  have h1 : HasFDerivAt (fun Y => Complex.exp (tL σ c v Y)) _ (0 : Fin g → ℂ) := (tL σ c v).hasFDerivAt.cexp
  have h2 : HasFDerivAt (fun Y => φ (zL σ Y)) _ (0 : Fin g → ℂ) :=
    (hφ (zL σ 0)).hasFDerivAt.comp (0 : Fin g → ℂ) (zL σ).hasFDerivAt
  have h3 := (h1.mul h2).fderiv
  rw [e]
  refine (congrArg (fun L => L Z) h3).trans ?_
  rw [map_zero, map_zero]
  simp [tL_apply, zL_apply, mul_comm]

end GlobalTheory.MBLow.Cl.JetFam

namespace GlobalTheory.MBLow.Cl

open JetFam

theorem jet_family_deriv : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g' r g : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r) (_ : Geo ν d.toAB) (gm : GtPt D (TE R ℂ)) (W : Fin g' → ℂ), (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) → IsD ν d.toAB W gm.b → ∃ (Z : Fin g → ℂ) (c₀ : ℂ), zP σ Z = W ∧ (W = 0 → ∀ χ, vE (gm.s (ν.eX χ)) (𝟙 _) ν.J = 1 + TrivSqZeroExt.inr ((2 * Real.pi * Complex.I : ℂ) * (co bX χ ⬝ᵥ tP σ Z))) ∧ ∀ (k : ℕ) (s : Fam D ℂ k) (f : N.X → N.A → ℂ) (α : N.X) (F : (Fin g → ℂ) → ℂ), ν.FamV s f → Differentiable ℂ F → (∀ Y h, d.IsPt σ Y h → f α h.b * h.s α = (d.fr (zP σ Y) : ℂ) ^ k * F Y) → (jc ν s gm α).fst / ν.rg ^ k = F 0 ∧ (jc ν s gm α).snd / ν.rg ^ k = fderiv ℂ F 0 Z + k * c₀ * F 0 := by
  intro R _ _ _ _ D hE hT _ N ν g' r g bX d σ G gm W ho hW
  obtain ⟨T, hT'⟩ := _root_.GlobalTheory.MBLow.Cl.JetGen.tangent_generators R D hE hT N ν g' r bX d G gm W ho hW
  have hrg : ν.rg ≠ 0 := GlobalTheory.Ex.FamVal.rg_ne ν
  have hne : ∀ z, G.frG (ν.J (ν.eA (d.ex z)).left) z ≠ 0 := fun z => by
    rw [← G.fr_eq]; exact mul_ne_zero (Units.ne_zero _) hrg
  have h0 : G.frG (ν.J (ν.eA (d.ex 0)).left) 0 = ν.rg := by
    rw [← G.fr_eq, d.fr_zero]; simp
  refine ⟨join σ W T, fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W / ν.rg, leftComponent_join σ W T, ?_, ?_⟩
  · intro hW0 χ
    have := hT' χ _ rfl
    subst hW0
    rw [map_zero, map_zero] at this
    rw [secondBlock_join]
    exact dual_zero (hne _) (hne _) this
  · intro k s f α F hs hF hf
    obtain ⟨o, hz, hp⟩ := ho
    have hb : redE ℂ ≫ gm.b.left = (DegPre.zeroF D ℂ).left := by
      rw [← hz.1]; exact hp.1.symm
    have hpt := fun Y => ((GlobalTheory.MBLow.Cl.exp_onto_torusExt N g' r g bX d σ).1 Y).exists
    have hφ : Differentiable ℂ fun z => F (join σ z 0) := hF.comp (diff_join σ)
    have hA : ∀ z, f α (d.ex z) * d.fr (d.t12 *ᵥ co bX α) * d.fr z =
        F (join σ z 0) * (d.fr z : ℂ) ^ k * d.fr (d.t12 *ᵥ co bX α + z) := fun z => by
      obtain ⟨h, hh⟩ := hpt (join σ z 0)
      have e1 := hf _ h hh
      have e2 := hh.2 α
      rw [hh.1] at e1
      rw [leftComponent_join] at e1 e2
      rw [secondBlock_join] at e2
      simp only [dotProduct_zero, mul_zero, Complex.exp_zero, one_mul] at e2
      linear_combination (d.fr (d.t12 *ᵥ co bX α + z) : ℂ) * e1 - f α (d.ex z) * e2
    have hB : ∀ Y, F Y = Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (co bX α ⬝ᵥ tP σ Y)) * F (join σ (zP σ Y) 0) :=
      fun Y => by
      obtain ⟨h, hh⟩ := hpt Y
      have e1 := hf _ h hh
      have e2 := hh.2 α
      have e3 := hA (zP σ Y)
      rw [hh.1] at e1
      apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero k (d.fr (zP σ Y)).ne_zero)
        (d.fr (d.t12 *ᵥ co bX α + zP σ Y)).ne_zero)
      linear_combination (-(d.fr (d.t12 *ᵥ co bX α + zP σ Y) : ℂ)) * e1 + f α (d.ex (zP σ Y)) * e2 +
        Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (co bX α ⬝ᵥ tP σ Y)) * e3
    have h1 := GlobalTheory.T.familyMember_tangentValue_eq_firstJet R D hE hT N ν g' d.toAB G gm.b W hb hW k s f α _ _ hs (d.c_eq α) hφ hA
    have h2 := dual_mul (hne _) (hne _) h1 (hT' α _ rfl)
    rw [h0, join_zero] at h2
    rw [fderiv_eq σ _ _ hφ hB, leftComponent_join, secondBlock_join, join_zero]
    exact h2

end GlobalTheory.MBLow.Cl

end
end

