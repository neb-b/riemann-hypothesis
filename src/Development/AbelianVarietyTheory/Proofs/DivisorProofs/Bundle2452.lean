module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1358
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0543
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2365
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0572
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1959
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBidualNaturalityDualSheafTranspose
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0552
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2354
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2285
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomBirationalModelsAmpleFrames
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0576
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaModelRelAmpleAndPrincipalAbelianLocus
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasValOfUnitMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.IntTerm.DvrScale

open GlobalTheory.TorusExt GlobalTheory.ZH.TestVal GlobalTheory.ThetaDvr.Scale
open Classical

theorem hasVal_of_unit_mul {V : Type} [CommRing V] [IsDomain V] {ϖ : V} (u : Vˣ) {r : V} {n : ℤ}
    (h : HasVal ϖ (algebraMap V (FractionRing V) ((u : V) * r)) n) :
    HasVal ϖ (algebraMap V (FractionRing V) r) n := by
  obtain ⟨u', hu'⟩ := h
  refine ⟨u' * u⁻¹, ?_⟩
  have e1 : algebraMap V (FractionRing V) r =
      algebraMap V (FractionRing V) ((u⁻¹ : Vˣ) : V) * algebraMap V (FractionRing V) ((u : V) * r) := by
    rw [← map_mul, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
  rw [e1, hu', Units.val_mul, map_mul]
  ring


attribute [local instance] gtGroup in
theorem exists_dvd_pow : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsDiscreteValuationRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∃ b, ∀ a, ∃ (w : Fin 8 → X) (r : V), 𝔪.YY a w ∧ 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2) = algebraMap V (FractionRing V) r * 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2) * algebraMap V (FractionRing V) (mono W t δ w) := by
  intro g n F W Z i X₁ z₁ act V _ _ _ _ ev X _ m t δ 𝔪
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hc : IsAdicComplete (maximalIdeal V) V := 𝔪.cn.2.2.1
  obtain ⟨hL, hL₂⟩ := abelianSchemeLaws_all
  obtain ⟨H, h₁, h₂, h₃, h₄⟩ := hyps hL hL₂
  have hm := odd_level' X₁.ρ
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, hc⟩
  have hB := 𝔪.D.tau_bimult
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  choose Q hQ using QForm.exists_QVal hϖ 𝔪.D
  obtain ⟨v, hv, -⟩ := GlobalTheory.ValClosure.exists_valuation_closure V ϖ hϖ
  have hu : IsUnit ((X₁.S.r * X₁.S.N : ℕ) : V) := by
    have := X₁.S.unit.map (ev.comp ((X₁.M.stalkEquiv z₁).symm.toRingHom.comp (algebraMap X₁.o₁ (X₁.M.O z₁))))
    rwa [map_natCast] at this
  obtain ⟨x, hx, xadd, xinj, xonto⟩ := GlobalTheory.ThetaDvr.torsion_points 𝔪.yK 𝔪.cart
  obtain ⟨rig, e, hrig, he, hsec⟩ := GlobalTheory.ThetaDvr.frames 𝔪.yK 𝔪.cart ⟨𝔪.wl, 𝔪.wl_gen⟩ x hx
  obtain ⟨t', ht⟩ := hsec 1 X₁.ρ.th₁
  obtain ⟨w₀, hw₀⟩ := EvalZero.exists_normW 𝔪.U.toUnifPre rig hrig
  obtain ⟨th, ϑ, hE, hP, hgen⟩ := exists_prim_generator H h₁ h₂ h₃ h₄ V hc ϖ hϖ 𝔪.D Q hQ _ v hv 𝔪.A 𝔪.G
    𝔪.semi 𝔪.U w₀ hw₀.1
  have key := val_theta H h₁ h₂ h₃ h₄ V hc ϖ hϖ 𝔪.D Q hQ _ v hv 𝔪.A 𝔪.G 𝔪.semi 𝔪.U w₀ rig hw₀ th ϑ hE hP
    _ hm hu
  obtain ⟨f, f₁, f₂, f₃, -⟩ := GlobalTheory.TorsionIso.torsion_eq H V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) _ hm.pos
  obtain ⟨r, hr⟩ := hgen t'
  obtain ⟨sc, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure (FractionRing V)))).inv).2 r
  set Fc := AlgebraicClosure (FractionRing V) with hF
  set y₀ : X₁.S.R →+* Fc := (algebraMap (FractionRing V) Fc).comp 𝔪.yK with hy₀
  have tv : ∀ a z J, Good 𝔪.A.L z J → cst (R := V) Fc z sc *
      @id ((TF (R := V) Fc).left.presheaf.stalk z) (sA th (ptSecT 𝔪.A.A (x a)).left z J) =
      cst (R := V) Fc z (y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩) * @id ((TF (R := V) Fc).left.presheaf.stalk z)
        (val (powFrame 𝔪.A.A 𝔪.A.L (x a) (e a) ((1 : ℕ) : ℤ)) (𝟙 _) z J).val := fun a z J hJ =>
    (ThetaCompare.sval_smul hr (x a) hJ).symm.trans (ht a _ (by
      have b := X₁.ρ.th_val a
      rw [← powFrame_one' (X₁.ρ.pt a) (X₁.ρ.fr a)] at b
      exact b) z J hJ)
  have ex : ∀ a, ∃ q, QkToAkU 𝔪.U.toUnifPre Fc (X₁.S.r * X₁.S.N) q (x a) := fun a => by
    obtain ⟨q, hq⟩ := f₂ (x a) (he a).1
    exact ⟨q, (f₁ _ _).2 hq.symm⟩
  have yyOf : ∀ a q (χ : 𝔪.D.toPre.X), QkToAkU 𝔪.U.toUnifPre Fc (X₁.S.r * X₁.S.N) q (x a) →
      𝔪.YY a (𝔪.e₈.symm ((X₁.S.r * X₁.S.N) • χ + q.y)) := fun a q χ hq =>
    ⟨qkShift hB q χ, x a, by
      rw [AddEquiv.apply_symm_apply]
      show q.y + (X₁.S.r * X₁.S.N) • χ = _
      rw [add_comm],
      (f₁ _ _).2 (((f₁ _ _).1 hq).trans ((f₃ _ _).2 (equiv_qkShift hB q _))), hx a⟩
  have hM2 : (X₁.S.r * X₁.S.N) ^ 2 ≠ 0 := pow_ne_zero _ hm.pos.ne'
  by_cases h0 : sc = 0
  · have z0 : ∀ a, y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩ = 0 := fun a => by
      obtain ⟨z⟩ := CoefBasic.exists_pt (R := V) (F := Fc)
      obtain ⟨J, hJ⟩ := CoefBasic.exists_good' (Z := (TFK (R := V) Fc).left) 𝔪.A.isLB z
      have := tv a z J hJ
      rw [h0, CoefBasic.cst_eq, CoefBasic.cst_eq, map_zero, zero_mul] at this
      exact CoefBasic.cstH_inj (R := V) z (((Units.mul_left_eq_zero _).1 this.symm).trans (map_zero _).symm)
    have z1 : ∀ a, 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ = 0 := fun a =>
      (map_eq_zero_iff _ (algebraMap (FractionRing V) Fc).injective).1 (z0 a)
    refine ⟨0, fun a => ?_⟩
    obtain ⟨q, hq⟩ := ex a
    refine ⟨_, 0, yyOf a q 0 hq, ?_⟩
    rw [z1 a, zero_pow hM2, map_zero, zero_mul, zero_mul]

  have tv' : ∀ a z J, Good 𝔪.A.L z J → sA th (ptSecT 𝔪.A.A (x a)).left z J =
      @id ((TFK (R := V) Fc).left.presheaf.stalk z)
        (cst (R := V) Fc z (sc⁻¹ * y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩)) *
        (val (powFrame 𝔪.A.A 𝔪.A.L (x a) (e a) ((1 : ℕ) : ℤ)) (𝟙 _) z J).val := fun a z J hJ => by
    have b := congrArg (CoefBasic.cstH (R := V) z sc⁻¹ * ·) (tv a z J hJ)
    simp only [CoefBasic.cst_eq, ← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ h0, map_one, _root_.one_mul] at b
    rw [CoefBasic.cst_eq]
    exact b
  have hvs : v sc ≠ ⊤ := v.ne_top_iff.2 h0
  have split : ∀ a, v (y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩) = v sc + v (sc⁻¹ * y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩) := fun a => by
    rw [← v.map_mul, ← _root_.mul_assoc, mul_inv_cancel₀ h0, _root_.one_mul]
  have nz : ∀ a, v (sc⁻¹ * y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩) = 0 → v (y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩) = v sc :=
    fun a h => by rw [split a, h, add_zero]
  have h2 : 2 ≤ X₁.S.r * X₁.S.N := X₁.S.N_ge.trans (Nat.le_mul_of_pos_left _ X₁.S.r_pos)
  obtain ⟨b, hb⟩ : ∃ b, v (y₀ ⟨X₁.S.th b, X₁.S.th_mem b⟩) = v sc := by
    obtain ⟨p₀, hp₀⟩ := exists_qkPt (F := Fc) H.1.mulN (Or.inr H.1.polBaseChange) hB
      (n := X₁.S.r * X₁.S.N) hm.pos.ne' 0
    obtain ⟨q', x', -, hx', -, hval⟩ := (key p₀ (f p₀) ((f₁ _ _).2 rfl)).2 (X₁.S.r * X₁.S.N) h2 dvd_rfl hp₀
    obtain ⟨a', rfl⟩ := xonto x' (hx' w₀ hw₀.1).1
    exact ⟨a', nz a' (hval _ _ (he a') (tv' a'))⟩
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 hvs
  refine ⟨b, fun a => ?_⟩
  obtain ⟨q, hq₁⟩ := ex a
  obtain ⟨_, ⟨χ, rfl⟩, hχ⟩ := Int.exists_least_of_bdd (P := fun k => ∃ χ, Q ((X₁.S.r * X₁.S.N) • χ + q.y) = k)
    ⟨0, by
      rintro _ ⟨χ, rfl⟩
      by_cases c : (X₁.S.r * X₁.S.N) • χ + q.y = 0
      · rw [c, QForm.Q_zero hϖ 𝔪.D hQ]
      · exact zero_le_one.trans (QForm.Q_pos hϖ 𝔪.D hQ c)⟩ ⟨_, 0, rfl⟩
  have hk := ((key q _ hq₁).1 _ _ (he a) (tv' a)).1
    ((Q ((X₁.S.r * X₁.S.N) • χ + q.y) : ℚ) / ((X₁.S.r * X₁.S.N) ^ 2 : ℕ)) fun χ' =>
      div_le_div_of_nonneg_right (Int.cast_le.2 (hχ _ ⟨χ', rfl⟩)) (Nat.cast_nonneg _)
  set w := 𝔪.e₈.symm ((X₁.S.r * X₁.S.N) • χ + q.y) with hw
  have hew : 𝔪.e₈ w = (X₁.S.r * X₁.S.N) • χ + q.y := AddEquiv.apply_symm_apply _ _
  have hmono : v (algebraMap (FractionRing V) Fc (algebraMap V (FractionRing V) (mono W t δ w))) =
      (((Q ((X₁.S.r * X₁.S.N) • χ + q.y) : ℤ) : ℚ) : WithTop ℚ) := by
    obtain ⟨u, hpc⟩ := 𝔪.psi w
    rw [hew] at hpc
    exact hv _ _ (hasVal_of_unit_mul u (GlobalTheory.ValForm.hasVal_coord (hQ _) hpc))
  have hb0 : 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ≠ 0 := fun h => hvs (by
    rw [← hb]; show v (algebraMap (FractionRing V) Fc (𝔪.yK _)) = ⊤; rw [h, map_zero, AddValuation.map_zero])
  have hne : 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2) *
      algebraMap V (FractionRing V) (mono W t δ w) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hb0)
      ((map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 (𝔪.mono_ne_zero w))
  have hle : v (algebraMap (FractionRing V) Fc (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2) *
      algebraMap V (FractionRing V) (mono W t δ w))) ≤
      v (algebraMap (FractionRing V) Fc (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2))) := by
    rw [map_mul, map_pow, map_pow, v.map_mul, v.map_pow, v.map_pow, hmono]
    change (X₁.S.r * X₁.S.N) ^ 2 • v (y₀ ⟨X₁.S.th b, X₁.S.th_mem b⟩) + _ ≤
      (X₁.S.r * X₁.S.N) ^ 2 • v (y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩)
    rw [hb, split a, ← hs]

    have hN : (((X₁.S.r * X₁.S.N) ^ 2 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hM2
    have e : (((X₁.S.r * X₁.S.N) ^ 2 • (s : WithTop ℚ)) + (((Q ((X₁.S.r * X₁.S.N) • χ + q.y) : ℤ) : ℚ) : WithTop ℚ)) =
        (X₁.S.r * X₁.S.N) ^ 2 • ((s : WithTop ℚ) +
          (((Q ((X₁.S.r * X₁.S.N) • χ + q.y) : ℚ) / ((X₁.S.r * X₁.S.N) ^ 2 : ℕ) : ℚ) : WithTop ℚ)) := by
      rw [← WithTop.coe_add, ← WithTop.coe_nsmul, ← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_eq_coe,
        nsmul_eq_mul, nsmul_eq_mul, mul_add, mul_div_cancel₀ _ hN]
    rw [e]
    exact nsmul_le_nsmul_right (add_le_add le_rfl hk) _
  obtain ⟨r', hr', -⟩ := GlobalTheory.ThetaDvr.exists_mul_of_val_le hϖ hv hne hle
  refine ⟨w, r', yyOf a q χ hq₁, ?_⟩
  rw [hr', _root_.mul_assoc]

end GlobalTheory.Poinc.IntTerm.DvrScale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeadWeightLineNef
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefHodge

def chartwise {X C : Scheme.{0}} (A : LB X) (g : C ⟶ X) : LB C :=
  ⟨A.ι, fun k => g ⁻¹ᵁ A.U k, fun k k' => pullU g (A.U k ⊓ A.U k') (A.g k k')⟩

theorem isLB_chartwise {X C : Scheme.{0}} {A : LB X} (hA : A.IsLB) (g : C ⟶ X) :
    (chartwise A g).IsLB ∧ LBIso (chartwise A g) (A.pull g) := by
  let a : ChartPull (chartwise A g) (A.pull g) (𝟙 C) :=
    ⟨fun k _ => k, fun k y hy => mem_pull.2 hy, fun y k k' hk hk' =>
      (gm_pull (𝟙 C) g y (A.U k ⊓ A.U k') ⟨hk, hk'⟩ _).trans
        (gm_pull_g A g (𝟙 C) y (fun _ => k) (fun _ => k') (mem_pull.2 hk) (mem_pull.2 hk')).symm⟩
  refine ⟨NefFibre.isLB_of_chartPull a (LB.isLB_pull hA g) fun y => ?_, iso_of_chart (LB.isLB_pull hA g) a⟩
  exact (Opens.mem_iSup (s := A.U)).1 (hA.cover.ge (Set.mem_univ (g y)))


open GlobalTheory.VB GlobalTheory.DualPull in
theorem isIso_theta_of_frames {X C : Scheme.{0}} {F : X.Modules} (g : C ⟶ X)
    (h : ∀ x : X, ∃ (U : X.Opens) (n : ℕ) (e : Fin n → Γ(F, U)), x ∈ U ∧ IsFrame e) : IsIso (theta g F) := by
  have := OmegaGlobal.isQuasicoherent_of_frames h
  have : (VB.dual F).IsQuasicoherent := OmegaGlobal.isQuasicoherent_of_frames fun x =>
    have ⟨U, n, _, hx, he⟩ := h x
    ⟨U, n, _, hx, he.dual⟩
  choose U n e hx he using h
  refine Twist.isIso_of_cover _ (U := fun y => g ⁻¹ᵁ U (g y))
    (top_le_iff.1 fun y _ => Opens.mem_iSup.2 ⟨y, hx (g y)⟩) fun y W hW => ?_
  have H (i : Fin (n (g y))) : (theta g F).app _ (QCoh.pullbackSections g (VB.dual F) (le_refl (g ⁻¹ᵁ U (g y)))
      ((he (g y)).coord i)) = ((he (g y)).pullback g).coord i :=
    dual_pull_ext g le_rfl fun W hW S hS e' s => by
      rw [dualApp_theta g _ hW, IsFrame.dualApp_coord, IsFrame.dualApp_coord]
      exact ((he (g y)).pullback_basis_repr g hW e' s i).symm
  have : QCoh.appLinear (theta g F) W =
      (((he (g y)).dual.pullback g).equiv ((he (g y)).pullback g).dual hW).toLinearMap :=
    (((he (g y)).dual.pullback g).basis hW).ext fun i => by
      rw [IsFrame.basis_apply, LinearEquiv.coe_coe, IsFrame.equiv_resM_frame, ← H]
      exact Twist.app_resM (theta g F) hW _
  rw [← QCoh.coe_appLinear, this]
  exact LinearEquiv.bijective _

section Step

open GlobalTheory.FlagMod GlobalTheory.Reg GlobalTheory.VB GlobalTheory.LieVB
open GlobalTheory.Twist (resM)
open GlobalTheory.QCoh (pullbackSections)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {Z C : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) (g : C ⟶ Z) (σ : E →+* ℂ)
  (f : ∀ M : MChart Y, Fin M.n → Γ(Lie Y.t.G, M.U))

theorem le_chart {k : F.J} {V : C.Opens} (h : V ≤ g ⁻¹ᵁ F.U k) : V ≤ (g ≫ π) ⁻¹ᵁ (F.M k).U :=
  fun _ hx => F.le k (h hx)

def vecSec (k : F.J) (V : C.Opens) (h : V ≤ g ⁻¹ᵁ F.U k) (i : Fin (Dw.mult σ)) :
    Γ((Scheme.Modules.pullback (g ≫ π)).obj (Lie Y.t.G), V) :=
  ∑ a, g.appLE (F.U k) V h (F.u k σ a i) • pullbackSections (g ≫ π) _ (le_chart F g h) (f (F.M k).toMChart a)

theorem resM_vecSec (k : F.J) {V V' : C.Opens} (h : V ≤ g ⁻¹ᵁ F.U k) (h' : V' ≤ V) (i : Fin (Dw.mult σ)) :
    resM _ h' (vecSec F g σ f k V h i) = vecSec F g σ f k V' (h'.trans h) i := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [vecSec, vecSec, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Twist.resM_smul, DualPull.resG_appLE]
  exact congrArg _ (QCoh.res_pullbackSections _ _ _ _ _)

theorem linearIndependent_vecSec (hf : ∀ M, IsFrame (f M)) (k : F.J) {V : C.Opens} (h : V ≤ g ⁻¹ᵁ F.U k) :
    LinearIndependent Γ(C, V) (vecSec F g σ f k V h) := by
  have := Y.t.semi
  have := Y.t.semi.smooth
  have : (Lie Y.t.G).IsQuasicoherent := OmegaGlobal.isQuasicoherent_of_frames fun x =>
    have ⟨U, n, _, hx, he⟩ := exists_isFrame_omega Y.t.G x
    ⟨U, n, _, hx, he.dual⟩
  let b := ((hf (F.M k).toMChart).pullback (g ≫ π)).basis (le_chart F g h)
  have hb : ∀ a, b a = pullbackSections (g ≫ π) _ (le_chart F g h) (f (F.M k).toMChart a) := fun a =>
    (IsFrame.basis_apply _ _ a).trans (QCoh.res_pullbackSections _ _ _ _ _)
  obtain ⟨w, hw⟩ := F.split k σ
  rw [Fintype.linearIndependent_iff]
  intro a ha
  simp only [vecSec, ← hb, Finset.smul_sum, smul_smul] at ha
  rw [Finset.sum_comm] at ha
  simp only [← Finset.sum_smul] at ha
  have h₁ : ((F.u k σ).map (g.appLE (F.U k) V h).hom).mulVec a = 0 := funext fun j =>
    show ∑ i, g.appLE (F.U k) V h (F.u k σ j i) * a i = 0 from
    Eq.trans (Finset.sum_congr rfl fun i _ => _root_.mul_comm _ _)
      (Fintype.linearIndependent_iff.1 b.linearIndependent _ ha j)
  have h₂ := congrArg (w.map (g.appLE (F.U k) V h).hom).mulVec h₁
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hw, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec,
    Matrix.mulVec_zero] at h₂
  exact congrFun h₂

theorem vecSec_chg (hc : ∀ (M M' : MChart Y) (j : Fin M'.n), resM _ (inf_le_right : M.U ⊓ M'.U ≤ M'.U) (f M' j) =
      ∑ i, chg M M' i j • resM _ (inf_le_left : M.U ⊓ M'.U ≤ M.U) (f M i))
    (k k' : F.J) {V : C.Opens} (h : V ≤ g ⁻¹ᵁ F.U k) (h' : V ≤ g ⁻¹ᵁ F.U k') (hh : V ≤ g ⁻¹ᵁ (F.U k ⊓ F.U k'))
    (i : Fin (Dw.mult σ)) : vecSec F g σ f k' V h' i =
      ∑ j, g.appLE _ V hh (F.B k k' σ j i) • vecSec F g σ f k V h j := by
  have hM : V ≤ (g ≫ π) ⁻¹ᵁ ((F.M k).U ⊓ (F.M k').U) := fun _ hx => ⟨le_chart F g h hx, le_chart F g h' hx⟩
  have e₁ : ∀ a, pullbackSections (g ≫ π) _ (le_chart F g h') (f (F.M k').toMChart a) =
      ∑ b, (g ≫ π).appLE _ V hM (chg (F.M k).toMChart (F.M k').toMChart b a) •
        pullbackSections (g ≫ π) _ (le_chart F g h) (f (F.M k).toMChart b) := fun a => by
    have := congrArg (pullbackSections (g ≫ π) _ hM) (hc (F.M k).toMChart (F.M k').toMChart a)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    refine ((QCoh.pullbackSections_res _ _ _ _ _).symm.trans this).trans (Finset.sum_congr rfl fun b _ => ?_)
    rw [QCoh.pullbackSections_smul]
    exact congrArg _ (QCoh.pullbackSections_res _ _ _ _ _)
  have e₂ : ∀ b, ∑ a, g.appLE _ V h' (F.u k' σ a i) *
      (g ≫ π).appLE _ V hM (chg (F.M k).toMChart (F.M k').toMChart b a) =
      ∑ j, g.appLE _ V hh (F.B k k' σ j i) * g.appLE _ V h (F.u k σ b j) := fun b => by
    have e₀ : ∑ a, π.appLE ((F.M k).U ⊓ (F.M k').U) (F.U k ⊓ F.U k') (inf_le_inf (F.le k) (F.le k'))
        (chg (F.M k).toMChart (F.M k').toMChart b a) * resG Z inf_le_right (F.u k' σ a i) =
        ∑ j, resG Z inf_le_left (F.u k σ b j) * F.B k k' σ j i :=
      congrFun (congrFun (F.tri k k' σ).choose_spec.2 b) i
    have := congrArg (g.appLE _ V hh).hom e₀
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum] at this
    refine (Finset.sum_congr rfl fun a _ => ?_).trans (this.trans (Finset.sum_congr rfl fun j _ => ?_))
    · rw [_root_.mul_comm, map_mul, ← Scheme.Hom.appLE_comp_appLE g π _ _ V (inf_le_inf (F.le k) (F.le k')) hh]
      exact congrArg₂ (· * ·) rfl (DualPull.appLE_resG g _ hh _).symm
    · rw [map_mul, _root_.mul_comm]
      exact congrArg₂ (· * ·) rfl (DualPull.appLE_resG g _ hh _)
  simp only [vecSec, e₁, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset (Fin (Dw.mult σ))))]
  simp only [← Finset.sum_smul, e₂]


open Classical in
theorem val_dual_LL_stepEx {j : ℕ} (hj : j ≤ Dw.mult σ) (k k' : F.J) :
    ((CechPic.dual (F.LL (NefStep.stepEx σ j))).g k k').val =
      ((F.B k k' σ).submatrix (Fin.castLE hj) (Fin.castLE hj)).det := by
  have ht : ((F.B k k' σ).submatrix (Fin.castLE hj) (Fin.castLE hj)).BlockTriangular id := fun a b h =>
    F.B_tri k k' σ (show Fin.castLE hj b < Fin.castLE hj a from h)
  rw [Matrix.det_of_upperTriangular ht]
  change ((∏ ix, F.T k k' ix ^ (-NefStep.stepEx σ j ix))⁻¹).val = _
  have e : (∏ ix, F.T k k' ix ^ (-NefStep.stepEx σ j ix))⁻¹ = ∏ i : Fin j, F.T k k' (some ⟨σ, Fin.castLE hj i⟩) := by
    rw [← Finset.prod_inv_distrib]
    refine (Finset.prod_of_injOn (fun i : Fin j => (some ⟨σ, Fin.castLE hj i⟩ : Ix Dw)) (fun a _ b _ h => ?_)
      (fun _ _ => Finset.mem_univ _) (fun ix _ h => ?_) fun i _ => ?_).symm
    · exact Fin.castLE_injective hj (eq_of_heq (Sigma.mk.inj (Option.some.inj h)).2)
    · have : NefStep.stepEx σ j ix = 0 := by
        rcases ix with _ | ⟨σ', i⟩
        · rfl
        · refine if_neg ?_
          rintro ⟨rfl, hi⟩
          exact h ⟨⟨i, hi⟩, Finset.mem_coe.2 (Finset.mem_univ _), rfl⟩
      rw [this, neg_zero, zpow_zero, inv_one]
    · have : NefStep.stepEx σ j (some ⟨σ, Fin.castLE hj i⟩ : Ix Dw) = 1 := if_pos ⟨rfl, i.2⟩
      rw [this, zpow_neg_one, inv_inv]
  rw [e, Units.coe_prod]
  rfl

theorem exists_step {j : ℕ} (hj : j ≤ Dw.mult σ) :
    ∃ (W : C.Modules) (ι : W ⟶ (Scheme.Modules.pullback (g ≫ π)).obj (Lie Y.t.G)), Mono ι ∧ IsVB W j ∧
      LBIso (chartwise (CechPic.dual (F.LL (NefStep.stepEx σ j))) g) (det W j) := by
  obtain ⟨f, hf, hc⟩ := _root_.GlobalTheory.ChartLieFrame.exists_lieFrame E H Dw l Xo c O β Y
  refine _root_.GlobalTheory.SubGlue.exists_sub_isVB_lbIso_det C _ j _ (isLB_chartwise (isLB_dual (F.isLB_LL _)) g).1
    (fun k i => vecSec F g σ f k (g ⁻¹ᵁ F.U k) le_rfl (Fin.castLE hj i))
    (fun k k' => ((F.B k k' σ).submatrix (Fin.castLE hj) (Fin.castLE hj)).map (g.app (F.U k ⊓ F.U k')).hom)
    (fun k V h => ?_) (fun k k' i => ?_) fun k k' => ?_
  · have := (linearIndependent_vecSec F g σ f hf k h).comp _ (Fin.castLE_injective hj)
    exact (funext fun i => resM_vecSec F g σ f k le_rfl h (Fin.castLE hj i)) ▸ this
  · refine (resM_vecSec F g σ f k' le_rfl _ _).trans ((vecSec_chg F g σ f hc k k'
      (V := g ⁻¹ᵁ F.U k ⊓ g ⁻¹ᵁ F.U k') inf_le_left inf_le_right le_rfl _).trans ?_)
    refine (Finset.sum_of_injOn (Fin.castLE hj) (Fin.castLE_injective hj).injOn (fun _ _ => Finset.mem_univ _)
      (fun a _ h => ?_) fun a _ => ?_).symm
    · have : F.B k k' σ a (Fin.castLE hj i) = 0 := F.B_tri k k' σ (by
        by_contra h'
        exact h ⟨⟨a, lt_of_le_of_lt (not_lt.1 h') i.2⟩, Finset.mem_coe.2 (Finset.mem_univ _), rfl⟩)
      rw [this, map_zero, zero_smul]
    · exact congrArg₂ (· • ·) congr($(g.appLE_eq_app (U := F.U k ⊓ F.U k')) _).symm
        (resM_vecSec F g σ f k le_rfl _ _)
  · exact (congrArg (g.app (F.U k ⊓ F.U k')).hom (val_dual_LL_stepEx F σ hj k k')).trans (RingHom.map_det _ _)


open scoped CategoryTheory.Obj in
theorem curveTest_stepEx (hS : Published.SemiAbelianLieSeminegative) (K : Type) [Field K] [CharZero K] {j : ℕ}
    (hj : j ≤ Dw.mult σ) : NefCurveTest.CurveTest K (F.LL (NefStep.stepEx σ j)) := by
  intro C _ hs hp hc g
  obtain ⟨W, ι, _, hW, e⟩ := exists_step F g σ hj
  have := Y.t.semi
  have := Y.t.semi.smooth
  have := IsSemiAbelian.pullback (g ≫ π) Y.t.G Y.t.semi
  have hG := isGrpPullback_pullback Y.t.G (g ≫ π)
  have := isIso_theta_of_frames (g ≫ π) (exists_isFrame_omega Y.t.G)
  have : IsIso (lieBase hG) :=
    inferInstanceAs (IsIso (DualPull.theta _ (omega Y.t.G) ≫ (dualIso (asIso (omegaBase hG)).symm).hom))
  have hL := F.isLB_LL (NefStep.stepEx σ j)
  have h₁ := isLB_chartwise (isLB_dual hL) g
  refine (hS.dual_det_nonneg hs hp hc _ hW (ι ≫ lieBase hG)).trans_eq (interNum_congr_cls K _
    (isLB_vecOne (isLB_dual hW.isLB_det)) (isLB_vecOne (LB.isLB_pull hL g)) fun i => ?_)
  fin_cases i
  change cls (CechPic.dual (det W j)) (isLB_dual hW.isLB_det) =
    cls ((F.LL (NefStep.stepEx σ j)).pull g) (LB.isLB_pull hL g)
  rw [cls_dual hW.isLB_det, ← (cls_eq_iff h₁.1 hW.isLB_det).2 e,
    (cls_eq_iff h₁.1 (LB.isLB_pull (isLB_dual hL) g)).2 h₁.2, cls_pull (isLB_dual hL), cls_dual hL, map_neg, neg_neg,
    cls_pull hL]

end Step

theorem isNef_stepEx (hS : Published.SemiAbelianLieSeminegative) (hN : Published.NefProductNonneg) {E : Type} [Field E]
    [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagMod.FlagCover Y) (Z : Comp Xo c) (σ : E →+* ℂ) {j : ℕ}
    (hj : j ≤ Dw.mult σ) : letI := algebraΓOfHom (str₀ X Z); IsNef c.F (LL₀ X Z (NefStep.stepEx σ j)) :=
  letI := algebraΓOfHom (str₀ X Z)
  ((curveTest_stepEx X.F σ hS _ hj).pull (X.F.isLB_LL _) _).isNef hN (LB.isLB_pull (X.F.isLB_LL _) _)

end GlobalTheory.NefHodge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeBundlePowerIsoMinimalSiegelCompactification
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.HodgeMin

open GlobalTheory.CechPic

theorem hodge_pow_iso_pull_pow_of_minimal_compactification : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left), MinAt5 F z i OZ → Geo.Tor.IsNormalScheme S → IsProjOver (π ≫ z) → Dense (Set.range j) → j ≫ π = i → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → IsGrpPullback F.univ.A G j e → ∃ a N : ℕ, 1 ≤ a ∧ 1 ≤ N ∧ LBIso (lbPow (hodge G g) N) (lbPow (OZ.pull π) a) := by
  intro g n F Z z i OZ S π j _ G _ e hM hS hp hj hji hG hsm he
  obtain ⟨o', _, β, S', s', U, c, π', G', _, e', _, N, ⟨-, hz, -, hiz, -, hO, -⟩,
    ⟨-, -, -, hS', -, _, _, hU, -, -, _, _⟩, ⟨hG', hsm', he'⟩, hN, hiso⟩ := hM
  have := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway n
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver hp
  have : QuasiSeparated π := .of_comp π z
  have : IsLocallyNoetherian S' := LocallyOfFiniteType.isLocallyNoetherian π'
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ z)
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (π ≫ z)
  have : AlgebraicGeometry.IsNoetherian S := {}
  have hd : Dense (⇑(c ≫ j) '' {x | (((c ≫ j) ≫ π ≫ z) x).asIdeal = ⊥}) := by
    refine (DenseRange.dense_image hj j.continuous F.isReduced_and_dense.2).mono ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, rfl⟩ := c.surjective x
    refine ⟨y, ?_, by simp⟩
    rw [Category.assoc, reassoc_of% hji, hiz]
    exact hx
  obtain ⟨W, p, p', H, _, α, α', _, _, hw, h₁, h₂⟩ := exists_common_cover z π π' (GlobalTheory.IsNormalScheme.pred S') (c ≫ j) U.ι
    (by rw [Category.assoc, hji, hU]) hd hG hG' ((isGrpPullback_pullback F.univ.A c).comp he) he'
  have := hG.separated
  have := hG'.separated
  have v₁ := GlobalTheory.LieVB.isVB_omega G g
  have v₂ := GlobalTheory.LieVB.isVB_omega G' g
  have l₁ : (hodge G g).IsLB := v₁.isLB_det
  have l₂ : (hodge G' g).IsLB := v₂.isLB_det
  have l₃ : (hodge H g).IsLB := (GlobalTheory.LieVB.isVB_omega_of_isGrpPullback h₁ v₁).isLB_det
  have e₁ := (cls_eq_iff (pull_isLB l₁ p) l₃).2 (HodgeGenDesc.lbIso_hodge_pull h₁ v₁)
  have e₂ := (cls_eq_iff (pull_isLB l₂ p') l₃).2 (HodgeGenDesc.lbIso_hodge_pull h₂ v₂)
  have e₃ := (cls_eq_iff (pull_isLB hO π') (isLB_lbPow l₂ N)).2 hiso
  rw [cls_pull l₁] at e₁
  rw [cls_pull l₂] at e₂
  rw [cls_pull hO, cls_lbPow l₂] at e₃
  obtain ⟨d, hd, h⟩ := exists_nsmul_eq_zero hS p (N • cls _ l₁ - pull π (cls _ hO)) (by
    rw [map_sub, map_nsmul, ← pull_comp, hw, pull_comp, e₃, map_nsmul, e₁, e₂, sub_self])
  refine ⟨d, d * N, hd, Nat.mul_pos hd hN,
    (cls_eq_iff (isLB_lbPow l₁ _) (isLB_lbPow (pull_isLB hO π) _)).1 ?_⟩
  rw [cls_lbPow l₁, cls_lbPow (pull_isLB hO π), cls_pull hO, mul_smul, ← sub_eq_zero, ← smul_sub, h]

end GlobalTheory.HodgeMin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRelationUniformisedHomConvolutionExpansiAlt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section
namespace GlobalTheory.Mum.Two.Mix

def mixφ {R : Type} [CommRing R] [IsDomain R] (D₁ D₂ : DegPre R) (b : D₁.P.A ⟶ D₂.P.A) (α : D₁.X) :
    PUnit.{1} ⊕ Fin 4 → (D₁.P.A.left ⟶ D₁.P.A.left ⨿ D₂.P.A.left) :=
  Sum.elim (fun _ => b.left ≫ coprod.inr) (fun k => D₁.famφB α k ≫ coprod.inl)

end GlobalTheory.Mum.Two.Mix
end
end

