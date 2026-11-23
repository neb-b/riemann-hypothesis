module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRootStalk
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0051
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGlobalGenerators
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0177
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0078

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantBoundedByShortestVector
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH.TestVal

open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusExt

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

theorem odd_level (ρ : S.Real) : Odd (S.r * S.N) := by
  obtain ⟨j, -, hj⟩ := ρ.r_eq
  rw [hj, ρ.N_eq]
  exact ρ.n_odd.pow.mul ρ.n_odd.pow.pow

theorem powFrame_one {B : Scheme.{0}} {A T : Over B} {L : LB A.left} (x : T ⟶ A)
    (τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))) :
    powFrame A L x τ 1 = τ :=
  congrArg LB.Gen.mk (funext fun j => zpow_one (τ.s j))

theorem mk_add_smul {X : Type} [AddCommGroup X] (m : ℕ) (χ y : X) :
    (QuotientAddGroup.mk y : X ⧸ (nsmulAddMonoidHom m : X →+ X).range) = QuotientAddGroup.mk (m • χ + y) :=
  QuotientAddGroup.eq.2 ⟨χ, by simp⟩


attribute [local instance] gtGroup in
theorem exists_scale (hL : Laws) (hL₂ : Laws2) {ρ : S.Real} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p}
    (u : ρ.UTest p y₀) (l : u.Lab) (h : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) :
    ∃ sc : ℝ, 0 ≤ sc ∧
      (∀ a, ∃ w : u.D.toPre.X, l.yy a = QuotientAddGroup.mk w ∧
        ‖y₀ ⟨S.th a, S.th_mem a⟩‖ ≤ sc * Real.exp (-(l.q w / ((S.r * S.N : ℕ) : ℝ) ^ 2))) ∧
      (∀ a, sc ≠ 0 → ‖y₀ ⟨S.th a, S.th_mem a⟩‖ = sc → a ∈ l.yy.ker) ∧
      ∀ n : ℕ, 2 ≤ n → n ∣ S.r * S.N → ∀ a ∈ l.yy.ker, ∃ a' ∈ l.yy.ker, n • (a' - a) = 0 ∧
        ‖y₀ ⟨S.th a', S.th_mem a'⟩‖ = sc := by
  obtain ⟨H, h₁, h₂, h₃, h₄⟩ := hyps hL hL₂
  have := charZero u
  have hm := odd_level ρ
  have hA : AdmBase u.V (IsLocalRing.maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  have hB := u.D.tau_bimult
  obtain ⟨ϖ, hϖ, Q, hQ, v, hv, lam, hlam, v₁, v₂, hq⟩ := exists_val u
  obtain ⟨x, hx, xadd, xinj, xonto⟩ := GlobalTheory.T.uniformised_model_labelled_torsion_points o Ω S ρ p y₀ u
  obtain ⟨rig, e, hrig, he, hsec⟩ := GlobalTheory.T.exists_frames_on_uniformisedModel_fibre o Ω S ρ p y₀ u x hx
  obtain ⟨t, ht⟩ := hsec 1 ρ.th₁
  obtain ⟨w₀, hw₀⟩ := EvalZero.exists_normW u.U.toUnifPre rig hrig
  obtain ⟨th, ϑ, hE, hP, hgen⟩ := exists_prim_generator H h₁ h₂ h₃ h₄ u.V u.complete ϖ hϖ u.D Q hQ _ v hv u.A u.G
    u.semi u.U w₀ hw₀.1
  have key := val_theta H h₁ h₂ h₃ h₄ u.V u.complete ϖ hϖ u.D Q hQ _ v hv u.A u.G u.semi u.U w₀ rig hw₀ th ϑ hE hP
    _ hm (isUnit_level u h)
  obtain ⟨f, f₁, f₂, f₃, -⟩ := GlobalTheory.TorsionIso.torsion_eq H u.V _ hA u.D u.A u.G u.semi u.U (PadicAlgCl p) _ hm.pos
  obtain ⟨r, hr⟩ := hgen t
  obtain ⟨sc, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl p))).inv).2 r
  have tv : ∀ a z J, Good u.A.L z J → cst (R := u.V) (PadicAlgCl p) z sc *
      @id ((TF (R := u.V) (PadicAlgCl p)).left.presheaf.stalk z) (sA th (ptSecT u.A.A (x a)).left z J) =
      cst (R := u.V) (PadicAlgCl p) z (y₀ ⟨S.th a, S.th_mem a⟩) * @id ((TF (R := u.V) (PadicAlgCl p)).left.presheaf.stalk z)
        (val (powFrame u.A.A u.A.L (x a) (e a) ((1 : ℕ) : ℤ)) (𝟙 _) z J).val := fun a z J hJ =>
    (ThetaCompare.sval_smul hr (x a) hJ).symm.trans (ht a _ (by
      have b := ρ.th_val a
      rw [← powFrame_one (ρ.pt a) (ρ.fr a)] at b
      exact b) z J hJ)
  have ex : ∀ a, ∃ q, QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) q (x a) ∧ l.yy a = QuotientAddGroup.mk q.y :=
    fun a => by
      obtain ⟨q, hq⟩ := f₂ (x a) (he a).1
      exact ⟨q, (f₁ _ _).2 hq.symm, l.yy_eq a q _ ((f₁ _ _).2 hq.symm) (hx a)⟩
  by_cases h0 : sc = 0
  · have z0 : ∀ a, y₀ ⟨S.th a, S.th_mem a⟩ = 0 := fun a => by
      obtain ⟨z⟩ := CoefBasic.exists_pt (R := u.V) (F := PadicAlgCl p)
      obtain ⟨J, hJ⟩ := CoefBasic.exists_good' (Z := (TFK (R := u.V) (PadicAlgCl p)).left) u.A.isLB z
      have := tv a z J hJ
      rw [h0, CoefBasic.cst_eq, CoefBasic.cst_eq, map_zero, zero_mul] at this
      exact CoefBasic.cstH_inj (R := u.V) z (((Units.mul_left_eq_zero _).1 this.symm).trans (map_zero _).symm)
    refine ⟨0, le_rfl, fun a => ?_, fun a hne => absurd rfl hne, fun n _ _ a ha => ⟨a, ha, by simp, by simp [z0]⟩⟩
    obtain ⟨q, -, hq⟩ := ex a
    exact ⟨q.y, hq, by simp [z0]⟩
  have hsc : 0 < ‖sc‖ := norm_pos_iff.2 h0
  have tv' : ∀ a z J, Good u.A.L z J → sA th (ptSecT u.A.A (x a)).left z J =
      @id ((TFK (R := u.V) (PadicAlgCl p)).left.presheaf.stalk z)
        (cst (R := u.V) (PadicAlgCl p) z (sc⁻¹ * y₀ ⟨S.th a, S.th_mem a⟩)) *
        (val (powFrame u.A.A u.A.L (x a) (e a) ((1 : ℕ) : ℤ)) (𝟙 _) z J).val := fun a z J hJ => by
    have b := congrArg (CoefBasic.cstH (R := u.V) z sc⁻¹ * ·) (tv a z J hJ)
    simp only [CoefBasic.cst_eq, ← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ h0, map_one, _root_.one_mul] at b
    rw [CoefBasic.cst_eq]
    exact b
  have nz : ∀ a, v (sc⁻¹ * y₀ ⟨S.th a, S.th_mem a⟩) = 0 ↔ ‖y₀ ⟨S.th a, S.th_mem a⟩‖ = ‖sc‖ := fun a => by
    refine (v₁ _ 0).trans ?_
    rw [norm_mul, norm_inv, Rat.cast_zero, mul_zero, neg_zero, Real.exp_zero, inv_mul_eq_one₀ hsc.ne', eq_comm]
  refine ⟨‖sc‖, hsc.le, fun a => ?_, fun a _ ha => ?_, fun n hn hnm a ha => ?_⟩
  · obtain ⟨q, hq₁, hq₂⟩ := ex a
    obtain ⟨_, ⟨χ, rfl⟩, hχ⟩ := Int.exists_least_of_bdd (P := fun k => ∃ χ, Q ((S.r * S.N) • χ + q.y) = k)
      ⟨0, by
        rintro _ ⟨χ, rfl⟩
        by_cases c : (S.r * S.N) • χ + q.y = 0
        · rw [c, QForm.Q_zero hϖ u.D hQ]
        · exact zero_le_one.trans (QForm.Q_pos hϖ u.D hQ c)⟩ ⟨_, 0, rfl⟩
    refine ⟨_, hq₂.trans (mk_add_smul _ χ _), ?_⟩
    have b := (v₂ _ _).1 (((key q _ hq₁).1 _ _ (he a) (tv' a)).1
      ((Q ((S.r * S.N) • χ + q.y) : ℚ) / ((S.r * S.N) ^ 2 : ℕ)) fun χ' =>
        div_le_div_of_nonneg_right (Int.cast_le.2 (hχ _ ⟨χ', rfl⟩)) (Nat.cast_nonneg _))
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ hsc] at b
    refine b.trans (le_of_eq ?_)
    rw [hq]
    push_cast
    rw [mul_div_assoc]
  · obtain ⟨q, hq₁, hq₂⟩ := ex a
    obtain ⟨z, hz⟩ := ((key q _ hq₁).1 _ _ (he a) (tv' a)).2 ((nz a).2 ha)
    exact hq₂.trans ((QuotientAddGroup.eq_zero_iff _).2 ⟨z, hz.symm⟩)
  · obtain ⟨q, hq₁, hq₂⟩ := ex a
    obtain ⟨z, hz⟩ := (QuotientAddGroup.eq_zero_iff _).1 (hq₂.symm.trans ha)
    have hz' : (S.r * S.N) • z = q.y := hz
    letI := gtGroup (D := u.D.toPre) (F := PadicAlgCl p)
    let iota : u.D.toPre.X →+ GtPtF u.D.toPre (PadicAlgCl p) :=
      AddMonoidHom.mk' (fun x => (exists_iota (F := PadicAlgCl p) hB x).choose) fun x x' => by
        obtain ⟨b, v⟩ := (isIota_iff_val _ _).1 (exists_iota (F := PadicAlgCl p) hB x).choose_spec
        obtain ⟨b', v'⟩ := (isIota_iff_val _ _).1 (exists_iota (F := PadicAlgCl p) hB x').choose_spec
        obtain ⟨b'', v''⟩ := (isIota_iff_val _ _).1 (exists_iota (F := PadicAlgCl p) hB (x + x')).choose_spec
        refine (isAdd_iff_eq _ _ _).1 ((isAdd_iff_val _ _ _).2 ⟨by rw [b, b', b'', cPoint_add], fun χ y J hJ => ?_⟩)
        have C : IsCub (ReciprocityTheory.ChartRestriction.G.DVR.th u.D.toPre (T := TF (R := u.V) (PadicAlgCl p)) y J) := isCub_cubV u.D.toPre.cub hJ
        rw [v χ y J hJ, v' χ y J hJ, v'' χ y J hJ, b, b', C.s01, C.s12]
        exact tau_mul (𝟙 (TF (R := u.V) (PadicAlgCl p))) hJ hB x x' χ
    have iota_spec (x : u.D.toPre.X) : GtPtF.IsIota x (iota x) := (exists_iota hB x).choose_spec
    have iota_iff (x : u.D.toPre.X) (g : GtPtF u.D.toPre (PadicAlgCl p)) : GtPtF.IsIota x g ↔ g = iota x :=
      ⟨fun h => isIota_unique h (iota_spec x), fun h => h ▸ iota_spec x⟩
    have q_nsmul : (S.r * S.N) • q.g = iota q.y := by
      obtain ⟨_, h₁, h₂⟩ := q.eq
      exact ((isNsmul_iff_eq _ _ _).1 h₁).symm.trans ((iota_iff _ _).1 h₂)
    let g₀ := q.g + iota (-z)
    have hg₀ : (S.r * S.N) • g₀ = iota 0 := by
      dsimp [g₀]
      rw [smul_add, q_nsmul, ← map_nsmul, ← map_add (f := _), smul_neg, hz', add_neg_cancel]
    let q₀ : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N) :=
      ⟨0, g₀, _, (isNsmul_iff_eq _ _ _).2 rfl, (iota_iff _ _).2 hg₀⟩
    have e₀ : f q = f q₀ := (f₃ _ _).2 ⟨-z, by
      change 0 = q.y + (S.r * S.N) • (-z)
      rw [smul_neg, hz', add_neg_cancel], _, iota_spec _, (isAdd_iff_eq _ _ _).2 rfl⟩
    obtain ⟨q', x', hy', hx', hpow, hval⟩ := (key q₀ (x a) ((f₁ _ _).2 (((f₁ _ _).1 hq₁).trans e₀))).2 n hn hnm (by simp [q₀])
    obtain ⟨a', rfl⟩ := xonto x' (hx' w₀ hw₀.1).1
    have := u.A.isAb.comm
    let X : Multiplicative S.Gam →* (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) :=
      MonoidHom.mk' (fun a => x a.toAdd) fun a b => xadd _ _
    refine ⟨a', (l.yy_eq a' q' _ hx' (hx a')).trans (by rw [hy']; rfl), xinj ?_, (nz a').1 (hval _ _ (he a') (tv' a'))⟩
    have b : X ((Multiplicative.ofAdd a' * (Multiplicative.ofAdd a)⁻¹) ^ n) = X 1 := by
      rw [map_pow, map_mul, map_inv, map_one]; exact hpow
    rw [sub_eq_add_neg]
    exact b

theorem norm_le_delta {p : ℕ} [Fact p.Prime] (ρ : S.Real) (y₀ : S.R →+* PadicAlgCl p) (a : S.Gam) :
    ‖y₀ ⟨S.th a, S.th_mem a⟩‖ ≤ S.delta y₀ := by
  have : NeZero (S.r * S.N) := ⟨(odd_level ρ).pos.ne'⟩
  exact le_ciSup (f := fun x => ‖y₀ ⟨S.th x, S.th_mem x⟩‖) (Set.finite_range _).bddAbove a

theorem main : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → (∀ x, y₀ ⟨S.th x, S.th_mem x⟩ ≠ 0 → ∃ w : u.D.toPre.X, l.yy x = QuotientAddGroup.mk w ∧ ‖y₀ ⟨S.th x, S.th_mem x⟩‖ ≤ S.delta y₀ * Real.exp (-(l.q w / ((S.r * S.N : ℕ) : ℝ) ^ 2))) := by
  intro hL hL₂ _ o Ω _ _ _ _ S ρ p _ y₀ u l h a _
  obtain ⟨sc, -, h₁, -, h₃⟩ := exists_scale hL hL₂ u l h
  have h2 : 2 ≤ S.r * S.N := S.N_ge.trans (Nat.le_mul_of_pos_left _ S.r_pos)
  obtain ⟨a', -, -, ha'⟩ := h₃ _ h2 dvd_rfl 0 (zero_mem _)
  obtain ⟨w, hw, b⟩ := h₁ a
  exact ⟨w, hw, b.trans (mul_le_mul_of_nonneg_right (ha' ▸ norm_le_delta ρ y₀ a') (Real.exp_pos _).le)⟩

end GlobalTheory.ZH.TestVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemOrthogonalLabelsAreTorusPoints
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section
namespace GlobalTheory.TestFibre

theorem perp_torus_point : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), PtsOver u x → ∀ t : S.perp l.yy.ker, ∃ (τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ) (q : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)), q.y = 0 ∧ IsTor τ q.g ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) q (x t) ∧ ∀ a β, l.yy a = QuotientAddGroup.mk β → (τ (Multiplicative.ofAdd β) : PadicAlgCl p) = y₀ (algebraMap o S.R S.ζ) ^ (S.r * S.N * (eStd S.g _ (t : S.Gam) a).val) := by
  intro h h₂ hT o Ω _ _ _ _ S ρ p _ y₀ u l _ x hx t
  obtain ⟨x', h₁, hadd, -, hs⟩ := utest_torsion_points o Ω S ρ p y₀ u
  obtain rfl : x = x' := funext fun a => Over.OverMorphism.ext
    (u.cart.1.hom_ext ((hx a).trans (h₁ a).symm) (by rw [Over.w, Over.w]))
  obtain ⟨q, τ, a, b, c, d⟩ := PerpCharacter.exists_torus_point_eStd (laws_all h h₂).1 hT o Ω S ρ p y₀ u l x h₁ hadd hs
    t t.2
  exact ⟨τ, q, a, b, c, fun a β e => (d a β e).trans (by rw [map_pow, map_pow])⟩

end GlobalTheory.TestFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemSumCharacterOrthogonalEqZero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

namespace GlobalTheory

theorem thetaSys_sum_perp_char_eq_zero :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (F : Type) [Field F] (ζ : F), IsPrimitiveRoot ζ ((S.r * S.N) ^ 2) → ∀ (H : AddSubgroup S.Gam) [Fintype (S.perp H)] (a : S.Gam), a ∉ H → ∑ t : S.perp H, ζ ^ (S.r * S.N * (eStd S.g _ (t : S.Gam) a).val) = 0 := by
  intro o Ω _ _ _ _ S F _ ζ hζ H _ a ha
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : NeZero ((S.r * S.N) ^ 2) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
  have hω : IsPrimitiveRoot (ζ ^ (S.r * S.N)) (S.r * S.N) :=
    hζ.pow (NeZero.pos _) (by ring)
  let χ : AddChar (ZMod (S.r * S.N)) F := AddChar.zmodChar _ hω.pow_eq_one
  have hχ : ∀ b, χ b = 1 → b = 0 := fun b hb =>
    ((AddChar.zmodChar_primitive_of_primitive_root _ hω).zmod_char_eq_one_iff _ b).mp hb
  let f : S.perp H →+ ZMod (S.r * S.N) :=
    { toFun := fun t => eStd S.g _ (t : S.Gam) a
      map_zero' := by simp [eStd]
      map_add' := fun x y => by
        simp only [eStd, AddSubgroup.coe_add, Pi.add_apply, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring }
  have hne : χ.compAddMonoidHom f ≠ 1 := by
    intro h
    apply ha
    rw [← (thetaSys_FF_mem_finite_perp_proj o Ω S).2.2.1 H]
    intro t ht
    have h1 : f ⟨t, ht⟩ = 0 := hχ _ (DFunLike.congr_fun h ⟨t, ht⟩)
    have h2 : eStd S.g _ t a = 0 := h1
    rw [ThetaProj.eStd_swap, h2, neg_zero]
  have h0 : ∑ t : S.perp H, χ (f t) = 0 := AddChar.sum_eq_zero_of_ne_one hne
  rw [← h0]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [pow_mul]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemWeightProjectorFixesEigenvector
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section
namespace GlobalTheory.TestFibre

theorem proj_fixes_eigen : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (F : Type) [Field F] (y : o →+* F) (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N), S.IsoFree T → ∀ (b E : S.J → F), (∀ t : T, ∑ j, (∑ i, y (S.ρ t j i) * b i) * E j = y S.ζN ^ (c t).val * ∑ j, b j * E j) → ∑ i, b i * ∑ j, y (S.proj T c j i) * E j = ∑ j, b j * E j := by
  intro o Ω _ _ _ S F _ y T c hT b E h
  have := Fintype.ofFinite T
  have h1 : ∀ t : T, y (GlobalGen.chi S (c t)) * y S.ζN ^ (c t).val = 1 := fun t => by
    have h2 := GlobalGen.chi_add S (c t) (-(c t))
    rw [add_neg_cancel, GlobalGen.chi_zero] at h2
    rw [← map_pow, ← map_one y, h2, map_mul, GlobalGen.chi.eq_1 S (-(c t)), neg_neg]
  have h3 : y (Ring.inverse (Nat.card T : o)) * (Fintype.card T : F) = 1 := by
    rw [← Nat.card_eq_fintype_card, ← map_natCast y, ← map_mul,
      Ring.inverse_mul_cancel _ (GlobalGen.isUnit_card hT), map_one]
  have h4 : ∑ i, b i * ∑ j, y (S.proj T c j i) * E j =
      y (Ring.inverse (Nat.card T : o)) * ∑ t : T, y (GlobalGen.chi S (c t)) *
        ∑ j, (∑ i, y (S.ρ t j i) * b i) * E j := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [GlobalGen.proj_eq, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, map_mul, map_sum,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h4]
  simp only [h, ← _root_.mul_assoc, h1, _root_.one_mul]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← _root_.mul_assoc, h3, _root_.one_mul]

end GlobalTheory.TestFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelAdaptedBasisIsModelWithSeries
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem utest_nonempty_mod : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (f : S.J → ∀ α, u.D.toPre.SecB S.N α), u.Basis l S.N σ cls f → Nonempty (Mod p u.j u.G S.g S.N l.q (u.H S.N) σ cls) := by
  intro hL hT o Ω _ _ _ _ S ρ p _ y₀ u l σ cls f hb
  obtain ⟨-, hdim, hsm, h4, -⟩ := utest_dim_and_split hL o Ω S ρ p y₀ u
  have h1 : 1 ≤ S.N := le_trans (by norm_num) h4
  obtain ⟨fb⟩ := _root_.GlobalTheory.ZH.UFib.nonempty_fibOf hL o Ω S ρ p y₀ u S.N h1
  obtain ⟨F, hF, hred⟩ := fb.exp S.J σ f (fun i => hb.2.2.2.1 i 0)
  refine ⟨{ isLB := LB.isLB_linComb u.U.LG.isLB _ _
            smooth := hsm
            Φ := fb.Φ
            r := fb.r
            cart := fb.cart
            xe := fb.xe
            F := F
            good := _root_.GlobalTheory.ZH.RedGood.good_reduction hL o Ω S ρ p y₀ u l S.N fb h1 S.J σ cls f hb F hF
            pol := fb.pol
            dim := ?_
            red := hred
            ser := _root_.GlobalTheory.ZH.SeriesAtPoint.main hL hT o Ω S ρ p y₀ u l σ cls f hb }⟩
  rw [fb.dim, fb.xe.toIntLinearEquiv.finrank_eq]
  exact hdim

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelTorsionPointsGroupPairing
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre
noncomputable section
namespace GlobalTheory.TestFibre

theorem ptsOver_group_pairing : Laws → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), (∃ x, PtsOver u x) ∧ ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), PtsOver u x → (∀ a b, x (a + b) = x a * x b) ∧ (∀ a, x a ^ (S.r * S.N) = 1) ∧ (∀ z, z ^ (S.r * S.N) = 1 → ∃! a, x a = z) ∧ ∀ a b (c : (PadicAlgCl p)ˣ), (c : PadicAlgCl p) = y₀ (algebraMap o S.R S.ζ) ^ (S.r * S.N * (eStd S.g _ a b).val) → WeilIs u.A.A u.A.L (S.r * S.N : ℕ) (x a) (x b) (unitOn c) := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u
  obtain ⟨x₀, h₀, hadd, hinj, hsurj⟩ := utest_torsion_points o Ω S ρ p y₀ u
  refine ⟨⟨x₀, h₀⟩, fun x hx => ?_⟩
  obtain rfl : x = x₀ := funext fun a => Over.OverMorphism.ext
    (u.cart.1.hom_ext ((hx a).trans (h₀ a).symm) ((Over.w _).trans (Over.w _).symm))
  refine ⟨hadd, fun a => GlobalTheory.FrameMove.pow_eq_one_of (T := baseOver (Sp S.R)) u.cart (hx a) (ρ.fr_tors a).1,
    fun z hz => ?_, fun a b c hc => weilIs_uTest hL o Ω S ρ p y₀ u x hx a b c ?_⟩
  · obtain ⟨a, ha⟩ := hsurj z hz
    exact ⟨a, ha.symm, fun b hb => hinj (hb.trans ha)⟩
  · rw [hc, map_pow, map_pow]

end GlobalTheory.TestFibre
end
end

