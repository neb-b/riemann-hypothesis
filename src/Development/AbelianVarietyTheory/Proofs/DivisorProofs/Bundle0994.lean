module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0873
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0951
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0959
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0911
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0382
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0956
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0929
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0920
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0968
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0939
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleBoundRingActionPullback
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

noncomputable section

namespace GlobalTheory.OEndDegree

open GlobalTheory.CechPic GlobalTheory.EffBound

variable {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B]

theorem pull_one (M : GlobalTheory.UU.CP B) : pull (1 : B ⟶ B).left (cls M.L.L M.L.isLB) = 0 := by
  have e : (1 : B ⟶ B).left = (toUnit B).left ≫ eSec B := by
    rw [Hom.one_def]; rfl
  rw [e, pull_comp, ← cls_pull M.L.isLB _ (pull_isLB M.L.isLB _),
    (cls_eq_zero_iff (pull_isLB M.L.isLB _)).2 ⟨M.L.rig, M.L.rigGen⟩, map_zero]

theorem pull_inv (M : GlobalTheory.UU.CP B) (f : B ⟶ B) :
    pull (f⁻¹).left (cls M.L.L M.L.isLB) = pull f.left (cls M.L.L M.L.isLB) := by
  have h0 := (cls_eq_zero_iff (LB.isLB_linComb M.L.isLB _ _)).2 ⟨M.sym, M.sym_gen⟩
  rw [cls_linComb M.L.isLB, Fin.sum_univ_two] at h0
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, pull_id, one_zsmul,
    neg_one_zsmul] at h0
  have hι : pull (ι[B]).left (cls M.L.L M.L.isLB) = cls M.L.L M.L.isLB := by
    rw [← sub_eq_zero, sub_eq_add_neg]; exact h0
  rw [Hom.inv_def, Over.comp_left, pull_comp, hι]

end GlobalTheory.OEndDegree

namespace GlobalTheory.OEndDegree

open GlobalTheory.CechPic GlobalTheory.EffBound

theorem pull_pow (k : Type) [Field k] (B : Over (Sp k)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (f : B ⟶ B) (n : ℕ) :
    pull (f ^ n).left (cls M.L.L M.L.isLB) = (n ^ 2) • pull f.left (cls M.L.L M.L.isLB) := by
  have h := _root_.GlobalTheory.UU.lbIso_pw_pull_pow_local k B M n
  have e : pull (𝟙 B ^ n).left (cls M.L.L M.L.isLB) = ((n : ℤ) ^ 2) • cls M.L.L M.L.isLB := by
    rw [← cls_pull M.L.isLB _ (pull_isLB M.L.isLB _),
      ← (cls_eq_iff (isLB_pw M.L.isLB _) (pull_isLB M.L.isLB _)).2 h, cls_pw]
  have e2 : f ^ n = f ≫ 𝟙 B ^ n := by rw [MonObj.comp_pow, Category.comp_id]
  rw [e2, Over.comp_left, pull_comp, e, map_zsmul]
  norm_cast

end GlobalTheory.OEndDegree

namespace GlobalTheory.OEndDegree

open GlobalTheory.CechPic GlobalTheory.EffBound

theorem act_zsmul {O : Type} [CommRing O] {S : Scheme.{0}} {B : Over S} [GrpObj B] (act : OAct O B) (a : O) (n : ℤ) :
    act.act (n • a) = act.act a ^ n := by
  have h0 : act.act 0 = 1 := by
    have := act.add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this |>.symm ▸ rfl
  induction n using Int.induction_on with
  | zero => rw [zero_zsmul, zpow_zero, h0]
  | succ k ih => rw [add_zsmul, one_zsmul, act.add, ih, zpow_add_one]
  | pred k ih =>
    rw [sub_zsmul, one_zsmul, zpow_sub_one, ← ih]
    refine eq_mul_inv_of_mul_eq ?_
    rw [← act.add]; congr 1; abel

end GlobalTheory.OEndDegree

namespace GlobalTheory.OEndDegree

open GlobalTheory.CechPic GlobalTheory.EffBound

theorem pull_zpow (k : Type) [Field k] (B : Over (Sp k)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (f : B ⟶ B) (n : ℤ) :
    pull (f ^ n).left (cls M.L.L M.L.isLB) = (n.natAbs ^ 2) • pull f.left (cls M.L.L M.L.isLB) := by
  cases n with
  | ofNat m => rw [Int.ofNat_eq_natCast, zpow_natCast, pull_pow, Int.natAbs_natCast]
  | negSucc m => rw [zpow_negSucc, pull_inv, pull_pow, Int.natAbs_negSucc]

theorem eff_nsmul {X : Scheme.{0}} [IsIntegral X] (hE0 : Eff (0 : Pic X)) {x : Pic X} (hx : Eff x) :
    ∀ n : ℕ, Eff (n • x)
  | 0 => by rw [zero_smul]; exact hE0
  | n + 1 => by rw [succ_nsmul]; exact GlobalTheory.T.isEffectivePicClass_add_integral _ _ (eff_nsmul hE0 hx n) hx

theorem eff_sum {O : Type} [CommRing O] {S : Scheme.{0}} {B : Over S} [GrpObj B] (act : OAct O B)
    {X : Scheme.{0}} [IsIntegral X] (F : (B ⟶ B) → Pic X) (c0 : Pic X) (hE0 : Eff (0 : Pic X))
    (hc0 : Eff c0) (h1 : F 1 = 0) (hpar : ∀ f g, Eff (2 • F f + 2 • F g - F (f * g))) :
    ∀ (l : ℕ) (b : Fin l → O) (t : Fin l → ℕ), (∀ i, Eff (t i • c0 - F (act.act (b i)))) →
      Eff ((2 ^ l * ∑ i, t i) • c0 - F (act.act (∑ i, b i))) := by
  have h0 : act.act 0 = 1 := by rw [← zero_smul ℤ (0 : O), act_zsmul, zpow_zero]
  intro l
  induction l with
  | zero =>
    intro b t _
    rw [Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_empty, h0, h1, mul_zero, zero_smul, sub_zero]
    exact hE0
  | succ l ih =>
    intro b t ht
    rw [Fin.sum_univ_castSucc (f := b), Fin.sum_univ_castSucc (f := t), act.add]
    have hP := ih (fun i => b i.castSucc) (fun i => t i.castSucc) fun i => ht _
    set P := act.act (∑ i : Fin l, b i.castSucc)
    set g := act.act (b (Fin.last l))
    set T := ∑ i : Fin l, t i.castSucc
    set u := t (Fin.last l)
    have h2 : 2 ≤ 2 ^ (l + 1) := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (l + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e : (2 ^ (l + 1) * (T + u)) • c0 - F (P * g) =
        (2 • F P + 2 • F g - F (P * g)) + 2 • ((2 ^ l * T) • c0 - F P) + 2 • (u • c0 - F g) +
          ((2 ^ (l + 1) - 2) * u) • c0 := by
      simp only [← natCast_zsmul]
      push_cast [Nat.cast_sub h2]
      module
    rw [e]
    exact GlobalTheory.T.isEffectivePicClass_add_integral _ _ (GlobalTheory.T.isEffectivePicClass_add_integral _ _ (GlobalTheory.T.isEffectivePicClass_add_integral _ _ (hpar P g) (eff_nsmul hE0 hP 2)) (eff_nsmul hE0 (ht _) 2))
      (eff_nsmul hE0 hc0 _)

end GlobalTheory.OEndDegree

namespace GlobalTheory.OEndDegree

open GlobalTheory.CechPic GlobalTheory.EffBound

theorem exists_effective_bound : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : Over (Sp k)) [GrpObj A] (act : OAct (𝓞 E) A) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (d : ℕ) (a : Fin d → 𝓞 E), ∃ (H : LB A.left) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (c : ℕ), H.IsLB ∧ GlobalTheory.AbLaw.VeryAmpleBy A.hom H s ∧ 1 ≤ c ∧ ∀ (n : Fin d → ℤ) (K : ℕ), 1 ≤ K → (∀ i, (n i).natAbs ≤ K) → ∃ (σ : LB.Sec (LB.div (GlobalTheory.AbLaw.pw H ((c * K ^ 2 : ℕ) : ℤ)) (H.pull (act.act (∑ i, n i • a i)).left))) (j : (LB.div (GlobalTheory.AbLaw.pw H ((c * K ^ 2 : ℕ) : ℤ)) (H.pull (act.act (∑ i, n i • a i)).left)).ι), σ.f j ≠ 0 := by
  intro E _ _ k _ _ _ A _ act g hB hg d a
  haveI := hB.comm
  haveI := hB.smooth
  haveI := hB.proper
  haveI : GeometricallyIntegral A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected
  haveI : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have hproj := _root_.GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme k A hB
  obtain ⟨H, m, s, hH, hs, hsym⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmpleBy k A hB hproj
  obtain ⟨r, hr⟩ : ∃ r : LB.Gen (H.pull (eSec A)), r.IsGen :=
    DVR.exists_gen_of_isLB_local (V := k) _ (pull_isLB hH _)
  obtain ⟨M, hM⟩ := (GlobalTheory.T.abelianScheme_cubical_bundle_exists_and_maps GlobalTheory.globalFns_holds _ A hB).1 ⟨H, r, hH, hr⟩
    (GlobalTheory.AbLaw.CubeProj.exists_gen_theta_abelianVariety GlobalTheory.globalFns_holds k A hB hproj H hH) hsym
  have hL : M.L.L = H := by rw [hM]
  subst hL
  obtain ⟨c0, hc0⟩ : ∃ c0, cls M.L.L M.L.isLB = c0 := ⟨_, rfl⟩
  have hEF : ∀ φ : A ⟶ A, Eff (pull φ.left c0) := fun φ =>
    hc0 ▸ GlobalTheory.EffBound.eff_pull_of_veryAmpleBy k A.hom M.L.L m s M.L.isLB hs φ.left inferInstance
  have h1 : pull (1 : A ⟶ A).left c0 = 0 := hc0 ▸ pull_one A M
  have hE0 : Eff (0 : Pic A.left) := h1 ▸ hEF 1
  have hEc : Eff c0 := by
    have := hEF (𝟙 A)
    rwa [Over.id_left, pull_id] at this
  have hpar : ∀ f g : A ⟶ A, Eff (2 • pull f.left c0 + 2 • pull g.left c0 - pull (f * g).left c0) := by
    intro f g
    have e := GlobalTheory.CubeThm.cube_pic A M f g g⁻¹
    rw [mul_inv_cancel_right, mul_inv_cancel, pull_one, pull_inv A M g, hc0] at e
    have e' : 2 • pull f.left c0 + 2 • pull g.left c0 - pull (f * g).left c0 = pull (f * g⁻¹).left c0 := by
      rw [← sub_eq_zero, ← sub_eq_zero.2 e]
      abel
    rw [e']
    exact hEF _
  have hc : ∀ i, ∃ ci : ℕ, Eff (ci • c0 - pull (act.act (a i)).left c0) := fun i => by
    let N := M.L.L.pull (act.act (a i)).left
    have hN : N.IsLB := pull_isLB M.L.isLB _
    have hD : (dual N).IsLB := isLB_dual hN
    obtain ⟨t₀, ht⟩ := exists_sec_tw_ne_zero k A.left A.hom M.L.L m s (dual N) M.L.isLB hD hs
    have hc' : t₀ ≤ ((max t₀ 0).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg (le_max_right _ _)]; exact le_max_left _ _
    obtain ⟨σ, j, hσ⟩ := ht _ hc'
    have h := eff_of_sec _ (isLB_tw hD M.L.isLB _) σ j hσ
    have e : cls (tw (dual N) M.L.L ((max t₀ 0).toNat : ℤ)) (isLB_tw hD M.L.isLB _) =
        cls (dual N) hD - cls (pw M.L.L (-((max t₀ 0).toNat : ℤ))) (isLB_pw M.L.isLB _) :=
      cls_div hD (isLB_pw M.L.isLB _) (isLB_tw hD M.L.isLB _)
    rw [e, cls_pw M.L.isLB, cls_dual hN hD, neg_zsmul, natCast_zsmul] at h
    have h' : Eff ((max t₀ 0).toNat • cls M.L.L M.L.isLB - cls N hN) := by
      convert h using 1 <;> abel
    change Eff ((max t₀ 0).toNat • cls M.L.L M.L.isLB - cls (M.L.L.pull (act.act (a i)).left) _) at h'
    rw [cls_pull M.L.isLB, hc0] at h'
    exact ⟨_, h'⟩
  choose ci hci using hc
  refine ⟨M.L.L, m, s, 2 ^ d * ∑ i, ci i + 1, M.L.isLB, hs, by omega, fun n K _ hn => ?_⟩
  have hterm : ∀ i, Eff ((K ^ 2 * ci i) • c0 - pull (act.act (n i • a i)).left c0) := by
    intro i
    have hle : (n i).natAbs ^ 2 ≤ K ^ 2 := Nat.pow_le_pow_left (hn i) 2
    have e : (K ^ 2 * ci i) • c0 - pull (act.act (n i • a i)).left c0 =
        (n i).natAbs ^ 2 • (ci i • c0 - pull (act.act (a i)).left c0) +
          ((K ^ 2 - (n i).natAbs ^ 2) * ci i) • c0 := by
      rw [act_zsmul, ← hc0, pull_zpow, hc0]
      simp only [← natCast_zsmul]
      push_cast [Nat.cast_sub hle]
      module
    rw [e]
    exact GlobalTheory.T.isEffectivePicClass_add_integral _ _ (eff_nsmul hE0 (hci i) _) (eff_nsmul hE0 hEc _)
  have hsum := eff_sum act (fun φ => pull φ.left c0) c0 hE0 hEc h1 hpar d (fun i => n i • a i)
    (fun i => K ^ 2 * ci i) hterm
  refine GlobalTheory.T.exists_section_nonzero_chart_of_effective_class _ (LB.isLB_div (isLB_pw M.L.isLB _) (pull_isLB M.L.isLB _)) ?_
  rw [cls_div (isLB_pw M.L.isLB _) (pull_isLB M.L.isLB _), cls_pw M.L.isLB, cls_pull M.L.isLB, hc0]
  have e : (((2 ^ d * ∑ i, ci i + 1) * K ^ 2 : ℕ) : ℤ) • c0 - pull (act.act (∑ i, n i • a i)).left c0 =
      ((2 ^ d * ∑ i, K ^ 2 * ci i) • c0 - pull (act.act (∑ i, n i • a i)).left c0) + (K ^ 2) • c0 := by
    simp only [← Finset.mul_sum, ← natCast_zsmul]
    push_cast
    module
  rw [e]
  exact GlobalTheory.T.isEffectivePicClass_add_integral _ _ hsum (eff_nsmul hE0 hEc _)

end GlobalTheory.OEndDegree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationBigCellRelationFourier
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section

namespace GlobalTheory.KSp.WeylCellRel

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {ν : Type} [Fintype ν] [DecidableEq ν]

theorem mat_mul (p q : UG c (stdJ ν E)) : mat c (p * q) = mat c p * mat c q := rfl

theorem mat_weyl_inv : mat c (weyl c ν)⁻¹ = -stdJ ν E := rfl

theorem mat_unip_inv (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) : mat c (unip c b hb)⁻¹ = fromBlocks 1 (-b) 0 1 := rfl

theorem mat_weyl : mat c (weyl c ν) = fromBlocks 0 1 (-1) 0 := rfl

theorem mat_levi (hc : ∀ z, c (c z) = z) (a : GL ν E) :
    mat c (levi c hc a) = fromBlocks (a : Matrix ν ν E) 0 0 (((a⁻¹ : GL ν E) : Matrix ν ν E).map c)ᵀ := rfl

theorem mat_unip (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) : mat c (unip c b hb) = fromBlocks 1 b 0 1 := rfl

theorem splitUnitaryElementMatrix_bigCell_product (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) (hb0 : b.det ≠ 0) (hb' : ((-b⁻¹).map c)ᵀ = -b⁻¹) :
    mat c (weyl c ν * unip c b hb * weyl c ν * (unip c (-b⁻¹) hb')⁻¹ * (weyl c ν)⁻¹) =
      fromBlocks (-b⁻¹) 1 0 (-b) := by
  have h1 : b * b⁻¹ = 1 := mul_nonsing_inv b (isUnit_iff_ne_zero.mpr hb0)
  rw [mat_mul, mat_mul, mat_mul, mat_mul, mat_weyl_inv, mat_unip_inv, mat_unip, mat_weyl]
  simp only [stdJ, fromBlocks_multiply, fromBlocks_neg, h1]
  simp [h1]

theorem conj_levi_mem (hc : ∀ z, c (c z) = z) (a : GL ν E) :
    weyl c ν * levi c hc a * (weyl c ν)⁻¹ ∈ sieg c ν := by
  rw [mem_sieg, mat_mul, mat_mul, mat_weyl_inv, mat_weyl, mat_levi]
  simp [stdJ, fromBlocks_multiply, fromBlocks_neg]

theorem herm_neg_inv (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) (hb0 : b.det ≠ 0) : ((-b⁻¹).map c)ᵀ = -b⁻¹ := by
  have h1 : ((b⁻¹).map c)ᵀ * b = 1 := by
    have h3 : ((b⁻¹).map c)ᵀ * (b.map c)ᵀ = 1 := by
      rw [← transpose_mul, ← Matrix.map_mul (f := c), mul_nonsing_inv b (isUnit_iff_ne_zero.mpr hb0),
        Matrix.map_one _ (map_zero c) (map_one c), transpose_one]
    rwa [hb] at h3
  have h2 : ((b⁻¹).map c)ᵀ = b⁻¹ := (Matrix.inv_eq_left_inv h1).symm
  rw [Matrix.map_neg _ (map_neg c), transpose_neg, h2]

theorem lower_left (hc : ∀ z, c (c z) = z) (a : GL ν E) (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) :
    (mat c (weyl c ν * (levi c hc a * unip c b hb) * weyl c ν)).toBlocks₂₁ = (a : Matrix ν ν E) * b := by
  rw [mat_mul, mat_mul, mat_mul, mat_weyl, mat_levi, mat_unip]
  simp [fromBlocks_multiply]

end GlobalTheory.KSp.WeylCellRel

theorem GlobalTheory.KSp.WeylCellRel.gauss_const_ne_zero : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (γ₀ : ℂ), (∀ b : Matrix ν ν E, (b.map c)ᵀ = b → b.det ≠ 0 → HasGauss μ (fun x => ψ (2⁻¹ * pr c Q x (x * b))) (γ₀ * sc F χ (Fintype.card α) b.det⁻¹)) → γ₀ ≠ 0 := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψne χ hχ hres _ _ μ _ γ₀ hγ hγ0
  obtain ⟨hfd, -, -, -, -, -, -, hmat⟩ := _root_.GlobalTheory.quadExt_topology F E c δ hE
  obtain ⟨hmt, hgood⟩ := hmat α ν
  haveI : FiniteDimensional F (Matrix α ν E) := inferInstance
  obtain ⟨β, hβ, hsymm, hnd, -, -⟩ := _root_.GlobalTheory.KSp.pr_alg F E c δ hE α ν Q hQ
  have hpair := _root_.GlobalTheory.KSp.isPair_addChar_form F (Matrix α ν E) ψ hψ hψ1 hψne β hsymm hnd
  have hfou : ∀ f, fou c ψ Q μ f = four μ (fun x y => ψ (β x y)) f := by
    intro f
    have hfe : (fun x y => ψ (β x y)) = (fun x y => ψ (pr c Q x y)) := by funext x y; rw [hβ]
    rw [hfe]; rfl
  obtain ⟨C, hC, hinv⟩ := GlobalTheory.T.bicharacterFourierTransform_twice_eq_pos_smul_reflect (Matrix α ν E) hgood μ _ hpair
  have inj : ∀ g ∈ SB (Matrix α ν E), fou c ψ Q μ g = 0 → g = 0 := by
    intro g hg h0
    funext x
    have h1 := hinv g hg (-x)
    rw [← hfou g, h0, neg_neg] at h1
    have h2 : four μ (fun x y => ψ (β x y)) (0 : Matrix α ν E → ℂ) (-x) = 0 := by simp [four]
    rw [h2] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left (by exact_mod_cast hC.ne')
  haveI := hgood.grp
  haveI := hgood.t2
  obtain ⟨L, hLc, hLo, -⟩ := hgood.small Set.univ Filter.univ_mem
  have hLcl : IsClopen (L : Set (Matrix α ν E)) :=
    ⟨AddSubgroup.isClosed_of_isOpen L hLo, hLo⟩
  set φ : Matrix α ν E → ℂ := (L : Set (Matrix α ν E)).indicator 1 with hφd
  have hφ : φ ∈ SB (Matrix α ν E) := by
    refine ⟨?_, HasCompactSupport.intro hLc fun x hx => Set.indicator_of_notMem hx _⟩
    have := (LocallyConstant.indicator (1 : LocallyConstant (Matrix α ν E) ℂ) hLcl).isLocallyConstant
    convert this using 1
    funext y
    exact (LocallyConstant.indicator_apply (1 : LocallyConstant (Matrix α ν E) ℂ) hLcl y).symm
  have hφ0 : φ 0 = 1 := by simp [hφd, Set.indicator_of_mem (zero_mem L)]
  have hfφ : fou c ψ Q μ φ ∈ SB (Matrix α ν E) := by
    rw [hfou]; exact _root_.GlobalTheory.KSp.FourMem.four_mem_SB (Matrix α ν E) hgood μ _ hpair φ hφ
  have h1 : ((1 : Matrix ν ν E).map c)ᵀ = 1 := by
    rw [Matrix.map_one _ (map_zero c) (map_one c), transpose_one]
  have hu : unip c 1 h1 ∈ sieg c ν := by rw [mem_sieg, WeylCellRel.mat_unip]; simp
  have hg := GlobalTheory.T.siegelParabolic_preserves_schwartzBruhat F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres (unip c 1 h1) hu _ hfφ
  obtain ⟨sc1, scmul, -⟩ := GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties F E c δ hE (Fintype.card α) χ hres
  have sc_ne : ∀ z : E, z ≠ 0 → sc F χ (Fintype.card α) z ≠ 0 := fun z hz h => by
    have h' := scmul z z⁻¹
    rw [mul_inv_cancel₀ hz, sc1, h, zero_mul] at h'
    exact one_ne_zero h'
  have br := GlobalTheory.T.fourier_hermitianMultiplier_braid_relation F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres μ 1 _ h1 (by simp)
    (hγ 1 h1 (by simp)) φ hφ
  rw [hγ0, zero_mul, zero_smul] at br
  have hs : sc F χ (Fintype.card α) (-(1 : Matrix ν ν E)⁻¹).det ≠ 0 := sc_ne _ (by simp [det_neg])
  have hX := (smul_eq_zero.mp br).resolve_left hs
  have hpar0 := inj _ hg hX
  apply one_ne_zero (α := ℂ)
  rw [← hφ0]
  have hF0 : fou c ψ Q μ φ = 0 := by
    funext x
    have h2 := congrFun hpar0 x
    have hψ0 : ∀ t, ψ t ≠ 0 := by
      intro t h4; have := hψ1 t; rw [h4, norm_zero] at this; exact zero_ne_one this
    simpa [parFun, WeylCellRel.mat_unip, sc1, hψ0] using h2
  rw [inj φ hφ hF0]; rfl

theorem GlobalTheory.KSp.weyl_cell_relation : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∃ κ : ℂ, κ ≠ 0 ∧ ∀ p ∈ sieg c ν, InCell c (weyl c ν * p * weyl c ν) → ∃ p₁ ∈ sieg c ν, ∃ p₂ ∈ sieg c ν, weyl c ν * p * weyl c ν = p₁ * weyl c ν * p₂ ∧ ∀ φ ∈ SB (Matrix α ν E), κ • fou c ψ Q μ (parFun c ψ χ Q (mat c p) (κ • fou c ψ Q μ φ)) = parFun c ψ χ Q (mat c p₁) (κ • fou c ψ Q μ (parFun c ψ χ Q (mat c p₂) φ)) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψne χ hχ hres _ _ μ _
  obtain ⟨γ₀, hγ⟩ := GlobalTheory.T.hasGaussIntegral_hermitian_quadratic_character F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres μ
  have hγ0 : γ₀ ≠ 0 :=
    GlobalTheory.KSp.WeylCellRel.gauss_const_ne_zero F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres μ γ₀ hγ
  obtain ⟨sc1, scmul, -⟩ := GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties F E c δ hE (Fintype.card α) χ hres
  have sc_ne : ∀ z : E, z ≠ 0 → sc F χ (Fintype.card α) z ≠ 0 := fun z hz h => by
    have h' := scmul z z⁻¹
    rw [mul_inv_cancel₀ hz, sc1, h, zero_mul] at h'
    exact one_ne_zero h'
  have hs1 : sc F χ (Fintype.card α) (-1 : Matrix ν ν E).det ≠ 0 := sc_ne _ (by simp [det_neg])
  refine ⟨sc F χ (Fintype.card α) (-1 : Matrix ν ν E).det / γ₀, div_ne_zero hs1 hγ0, ?_⟩
  intro p hp hcell
  obtain ⟨-, -, a, b, hb, rfl⟩ := _root_.GlobalTheory.KSp.sieg_blocks F E c δ hE ν p hp
  have hb0 : b.det ≠ 0 := by
    have h := (_root_.GlobalTheory.KSp.inCell_iff_det_ne_zero F E c δ hE ν _).mp hcell
    rw [WeylCellRel.lower_left, det_mul] at h
    exact right_ne_zero_of_mul h
  have hb' := WeylCellRel.herm_neg_inv c b hb hb0
  have hunip : ∀ (b' : Matrix ν ν E) (h' : (b'.map c)ᵀ = b'), unip c b' h' ∈ sieg c ν := by
    intro b' h'; rw [mem_sieg, WeylCellRel.mat_unip]; simp
  have hlevi : levi c hE.invol a ∈ sieg c ν := by rw [mem_sieg, WeylCellRel.mat_levi]; simp
  obtain ⟨q, hqd⟩ : ∃ q, q = weyl c ν * levi c hE.invol a * (weyl c ν)⁻¹ := ⟨_, rfl⟩
  obtain ⟨p₀, hp0d⟩ : ∃ p₀, p₀ = weyl c ν * unip c b hb * weyl c ν * (unip c (-b⁻¹) hb')⁻¹ * (weyl c ν)⁻¹ :=
    ⟨_, rfl⟩
  have hq : q ∈ sieg c ν := hqd ▸ WeylCellRel.conj_levi_mem c hE.invol a
  have hp0m : mat c p₀ = fromBlocks (-b⁻¹) 1 0 (-b) := hp0d ▸ WeylCellRel.splitUnitaryElementMatrix_bigCell_product c b hb hb0 hb'
  have hp0 : p₀ ∈ sieg c ν := by rw [mem_sieg, hp0m]; simp
  refine ⟨q * p₀, mul_mem hq hp0, unip c (-b⁻¹) hb', hunip _ _, by rw [hqd, hp0d]; group, ?_⟩
  intro φ hφ
  obtain ⟨-, pm⟩ := GlobalTheory.T.parFun_sieg_mul' F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres
  have fl := GlobalTheory.T.fourier_intertwines_siegelLeviOperator F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres μ (levi c hE.invol a) hlevi q hq
    (by rw [hqd]; group)
  have br := GlobalTheory.T.fourier_hermitianMultiplier_braid_relation F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres μ b _ hb hb0 (hγ b hb hb0) φ hφ
  rw [← WeylCellRel.mat_unip c b hb, ← WeylCellRel.mat_unip c (-b⁻¹) hb', ← hp0m] at br
  have pf_smul : ∀ (g : Matrix (ν ⊕ ν) (ν ⊕ ν) E) (k : ℂ) (f : Matrix α ν E → ℂ),
      parFun c ψ χ Q g (k • f) = k • parFun c ψ χ Q g f := by
    intro g k f; funext x; simp only [parFun, Pi.smul_apply, smul_eq_mul]; ring
  have fou_smul : ∀ (k : ℂ) (f : Matrix α ν E → ℂ), fou c ψ Q μ (k • f) = k • fou c ψ Q μ f := by
    intro k f; funext x; simp only [fou, four, Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]; congr 1; funext y; ring
  have e : (-b⁻¹ : Matrix ν ν E).det = (-1 : Matrix ν ν E).det * b.det⁻¹ := by
    rw [← neg_one_mul, det_mul, det_nonsing_inv, Ring.inverse_eq_inv']
  have hκγ : sc F χ (Fintype.card α) (-1 : Matrix ν ν E).det / γ₀ * (γ₀ * sc F χ (Fintype.card α) b.det⁻¹) =
      sc F χ (Fintype.card α) (-b⁻¹).det := by
    rw [e, scmul]; field_simp
  have hs : sc F χ (Fintype.card α) (-b⁻¹).det ≠ 0 := sc_ne _ (by
    rw [e]; exact mul_ne_zero (by simp [det_neg]) (inv_ne_zero hb0))
  have hγne : γ₀ * sc F χ (Fintype.card α) b.det⁻¹ ≠ 0 := by
    intro h; rw [h, mul_zero] at hκγ; exact hs hκγ.symm
  set κ := sc F χ (Fintype.card α) (-1 : Matrix ν ν E).det / γ₀ with hκ
  have key : κ • fou c ψ Q μ (parFun c ψ χ Q (mat c (unip c b hb)) (fou c ψ Q μ φ)) =
      parFun c ψ χ Q (mat c p₀) (fou c ψ Q μ (parFun c ψ χ Q (mat c (unip c (-b⁻¹) hb')) φ)) := by
    apply smul_right_injective _ hγne
    simp only
    rw [smul_smul, mul_comm, hκγ, br]
  rw [pf_smul, fou_smul, pm _ hlevi _ (hunip _ _), fl, ← pf_smul, key, pf_smul, pm _ hq _ hp0]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorDerivativeIsDifferential
section
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.LogDR.isExtD_extD : ∀ (K : Type) [Field K], IsExtD ℤ K (extD K) := by
  intro K _
  refine { mul := ?_, sq := ?_, alg := ?_ }
  ·
    intro x y
    rw [extD_apply, extD_apply, extD_apply, CechDR.dDR_mul, add_comm]
    rfl
  · intro x
    rw [extD_apply, extD_apply, CechDR.dDR_dDR]
  · intro a
    rw [extD_apply, CechDR.dDR_algebraMap]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDenBdd
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.FinFix

theorem finite_den_bdd (N : ℕ) (hN : 0 < N) (R : ℝ) :
    {q : ℚ | (∃ k : ℤ, q * N = k) ∧ |(q : ℝ)| ≤ R}.Finite := by
  have hN' : (0 : ℚ) < N := by exact_mod_cast hN
  refine ((Set.finite_Icc (-⌈R * N⌉) ⌈R * N⌉).image (fun k : ℤ => (k : ℚ) / N)).subset ?_
  rintro q ⟨⟨k, hk⟩, hR⟩
  refine ⟨k, ?_, ?_⟩
  · have hkR : |(k : ℝ)| ≤ R * N := by
      have : (k : ℝ) = (q : ℝ) * N := by exact_mod_cast hk.symm
      rw [this, abs_mul, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_right hR (Nat.cast_nonneg _)
    have h1 := abs_le.1 hkR
    constructor
    · have : -(R * N) ≤ (k : ℝ) := h1.1
      have h3 : (-⌈R * N⌉ : ℝ) ≤ k := by
        have := Int.le_ceil (R * N); push_cast; linarith
      exact_mod_cast h3
    · have h3 : (k : ℝ) ≤ ⌈R * N⌉ := le_trans h1.2 (Int.le_ceil _)
      exact_mod_cast h3
  · show (k : ℚ) / N = q
    rw [← hk]; field_simp

end GlobalTheory.FinFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionsLieRationalWeightsCommute
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem fock_lie_wts_comm : ∀ P Q R S : ℕ, IsLieAct (fockAct1 P Q R S) ∧ IsLieAct (fockAct2 P Q R S) ∧
    (∀ v, v ∈ ⨆ μ : Ix P Q → ℚ, wtSub (fockAct1 P Q R S) μ) ∧ (∀ v, v ∈ ⨆ μ : Ix R S → ℚ, wtSub (fockAct2 P Q R S) μ) ∧
    ∀ X Y f, fockAct1 P Q R S X (fockAct2 P Q R S Y f) = fockAct2 P Q R S Y (fockAct1 P Q R S X f) := by
  intro P Q R S
  obtain ⟨h1, h2, hc⟩ := GlobalTheory.FockPair.pair_lie_commute P Q R S
  obtain ⟨w1, w2⟩ := GlobalTheory.FockPolGK.pol_locFin_weights P Q R S
  refine ⟨h1, h2, fun v => (w1 v).2, fun v => (w2 v).2, fun X Y f => ?_⟩
  have := LinearMap.congr_fun (hc X Y) f
  simpa only [Module.End.mul_apply] using this

end GlobalTheory.HoweR
end

