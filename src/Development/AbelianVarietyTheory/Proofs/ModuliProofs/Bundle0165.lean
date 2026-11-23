module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0113
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0159
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0162
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleFormBundlePowerOfPosDef
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PosDefAmple

open GlobalTheory.CechPic

theorem exists_smul_eq_transpose_mul_self {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℤ)
    (hQ : (Q.map (Int.cast : ℤ → ℝ)).PosDef) :
    ∃ (N m : ℕ) (d : ℤ) (c : Matrix (Fin m) (Fin n) ℤ) (b : Matrix (Fin n) (Fin m) ℤ), 0 < N ∧ d ≠ 0 ∧
      (N : ℤ) • Q = c.transpose * c ∧ b * c = d • (1 : Matrix (Fin n) (Fin n) ℤ) := by
  obtain ⟨N, a, l, hN, ha, hl, h⟩ := exists_smul_eq_transpose_mul_diagonal_mul n Q hQ
  let e := Fintype.equivFin (Σ i, Fin (a i))
  let c : Matrix (Fin (Fintype.card (Σ i, Fin (a i)))) (Fin n) ℤ := fun j => l (e.symm j).1
  have hc : c.transpose * c = l.transpose * Matrix.diagonal (fun i => (a i : ℤ)) * l := by
    ext u v
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine ((e.symm.sum_comp (fun p => l p.1 u * l p.1 v)).trans (Fintype.sum_sigma _)).trans
      (Finset.sum_congr rfl fun i _ => ?_)
    simp [Matrix.mul_diagonal]
    ring
  refine ⟨N, _, (c.transpose * c).det, c, (c.transpose * c).adjugate * c.transpose, hN, ?_, h.trans hc.symm, ?_⟩
  · rw [hc, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
    exact mul_ne_zero (mul_ne_zero hl (Finset.prod_ne_zero_iff.2 fun i _ => by exact_mod_cast (ha i).ne')) hl
  · rw [Matrix.mul_assoc, Matrix.adjugate_mul]

variable {S : Scheme.{0}}

theorem relAmple_pull_of_isAffineHom {G G' : Over S} [IsProper G.hom] (φ : G ⟶ G') [IsAffineHom φ.left]
    {L : LB G'.left} (hL : L.IsLB) (h : Out.RelAmple G' L) : Out.RelAmple G (L.pull φ.left) := by
  refine relAmple_of_isAmpleLB G (pull_isLB hL _) fun U hU => ?_
  have e : G.hom ⁻¹ᵁ U = φ.left ⁻¹ᵁ (G'.hom ⁻¹ᵁ U) := by rw [← Scheme.Hom.comp_preimage, Over.w φ]
  rw [e]
  have : IsAffineHom (φ.left ∣_ (G'.hom ⁻¹ᵁ U)) := MorphismProperty.of_isPullback (P := @IsAffineHom)
    (isPullback_morphismRestrict φ.left (G'.hom ⁻¹ᵁ U)).flip inferInstance
  have h₁ := (isAmpleLB_of_relAmple G' hL h U hU).pull_of_isAffineHom (φ.left ∣_ (G'.hom ⁻¹ᵁ U))
  have h₂ := pull_isLB (pull_isLB hL φ.left) (φ.left ⁻¹ᵁ (G'.hom ⁻¹ᵁ U)).ι
  refine h₁.of_lbIso h₂ ((cls_eq_iff h₂ h₁.isLB).1 ?_)
  rw [cls_pull (pull_isLB hL _), cls_pull hL, cls_pull (pull_isLB hL _), cls_pull hL, ← pull_comp, ← pull_comp,
    morphismRestrict_ι]

theorem relAmple_of_nsmul {G : Over S} [IsProper G.hom] {L M : LB G.left} (hL : L.IsLB) (hM : M.IsLB) {N : ℕ}
    (hN : 1 ≤ N) (e : N • cls L hL = cls M hM) (h : Out.RelAmple G M) : Out.RelAmple G L := by
  refine relAmple_of_isAmpleLB G hL fun U hU => ?_
  have h₁ := isAmpleLB_of_relAmple G hM h U hU
  have h₂ := pull_isLB hL (G.hom ⁻¹ᵁ U).ι
  refine (isAmpleLB_pow_iff h₂ hN).1 (h₁.of_lbIso (isLB_lbPow h₂ N) ((cls_eq_iff (isLB_lbPow h₂ N) h₁.isLB).1 ?_))
  rw [cls_lbPow h₂, cls_pull hL, cls_pull hM, ← e, map_nsmul]

theorem isProper_powObj (A : Over S) [IsProper A.hom] : ∀ n, IsProper (Out.powObj A n).hom
  | 0 => inferInstanceAs (IsProper (𝟙 S))
  | n + 1 => by
    have := isProper_powObj A n
    exact inferInstanceAs (IsProper (pullback.fst A.hom (Out.powObj A n).hom ≫ A.hom))

theorem comp_prod_zpow {T T' A : Over S} [GrpObj A] [IsCommMonObj A] (f : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ A))
    (c : Fin n → ℤ) : f ≫ (∏ i, x i ^ c i) = ∏ i, (f ≫ x i) ^ c i := by
  let F : (T ⟶ A) →* (T' ⟶ A) := MonoidHom.mk' (fun y => f ≫ y) (comp_mul f)
  change F _ = ∏ i, F (x i) ^ c i
  simp only [map_prod, map_zpow]

theorem cls_form_eq_sum (hG : Out.GlobalFnsSt) {h k : ℕ} {B : Type} [CommRing B] {ζ : B} {s : S ⟶ Sp B}
    (o : SiegPre h k ζ s) (hA : Out.RelAmple o.A o.diag) {T : Over S} {n m : ℕ} (x : Fin n → (T ⟶ o.A))
    (W : Matrix (Fin n) (Fin n) ℤ) (c : Matrix (Fin m) (Fin n) ℤ)
    (hW : W + W.transpose = (2 : ℤ) • (c.transpose * c)) :
    ∑ uv : Fin n × Fin n, W uv.1 uv.2 • pull (lift (x uv.1) (x uv.2)).left (cls o.P o.isLB) =
      ∑ j, pull (∏ i, x i ^ c j i).left (cls o.diag (pull_isLB o.isLB _)) := by
  have H := (cls_eq_iff (LB.isLB_linComb o.isLB _ _) (LB.isLB_linComb o.isLB _ _)).2
    (GlobalTheory.BilinCalc.main S o.A o.P o.isLB
      (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S o.A o.diag o.ab (pull_isLB o.isLB _) hA o.P o.isLB o.rig₁ o.rig₂) o.symm T n m x 1 W c
      (by rw [hW, Matrix.transpose_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, two_smul]))
  rw [cls_linComb o.isLB, cls_linComb o.isLB] at H
  rw [H, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single j (fun v _ hv => by rw [Matrix.one_apply_ne hv.symm, zero_smul]) (by simp),
    Matrix.one_apply_eq, one_smul]
  refine Eq.trans ?_ (pull_comp (∏ i, x i ^ c j i).left (lift (𝟙 o.A) (𝟙 o.A)).left (cls o.P o.isLB))
  rw [← Over.comp_left, comp_lift, Category.comp_id]

theorem pull_cls_boxLB {T G A : Over S} {n : ℕ} (pr : Fin n → (G ⟶ A)) {L : LB A.left} (hL : L.IsLB) (φ : T ⟶ G) :
    pull φ.left (cls (Out.boxLB L pr) (LB.isLB_linComb hL _ _)) = ∑ j, pull (φ ≫ pr j).left (cls L hL) := by
  refine (congrArg _ (cls_linComb hL _ _ _)).trans ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, one_smul, ← pull_comp, Over.comp_left]

theorem relAmple_linComb_of_posDef : Out.GlobalFnsSt → ∀ (h k n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s : S ⟶ Sp B) (c : SiegPre h k ζ s) (G : Over S) [GrpObj G] (pr : Fin n → (G ⟶ c.A)) (W : Matrix (Fin n) (Fin n) ℤ), (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin n → (T ⟶ c.A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → Out.RelAmple c.A c.diag → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → Out.RelAmple G (LB.LinComb c.P (K := Fin n × Fin n) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) := by
  intro hG h k n B _ ζ S s o G _ pr W hpr up hA hW
  have := o.ab.proper
  have hD : o.diag.IsLB := pull_isLB o.isLB _
  let p : Out.IsPowGrp G o.A n := ⟨pr, hpr, mkFanLimit _ (fun t => (up t.pt t.proj).choose)
    (fun t j => (up t.pt t.proj).choose_spec.1 j) (fun t y hy => (up t.pt t.proj).choose_spec.2 y hy)⟩
  have hp : IsProper G.hom := by
    have := isProper_powObj o.A n
    let e : G ≅ Out.powObj o.A n := p.lim.conePointUniqueUpToIso (Out.powIsLimit o.A n)
    have : IsIso e.hom.left := ((Over.forget S).mapIso e).isIso_hom
    rw [← Over.w e.hom]
    infer_instance
  obtain ⟨N, m, d, c, b, hN, hd, hc, hb⟩ := exists_smul_eq_transpose_mul_self _ hW
  have := isProper_powObj o.A m
  let φ : G ⟶ Out.powObj o.A m := (Out.powIsLimit o.A m).lift (Fan.mk G fun j => ∏ i, pr i ^ c j i)
  have hφ : ∀ j, φ ≫ Out.powPr o.A j = ∏ i, pr i ^ c j i := fun j => (Out.powIsLimit o.A m).fac _ ⟨j⟩
  obtain ⟨ψ, hψ, -⟩ := up (Out.powObj o.A m) fun i => ∏ j, Out.powPr o.A j ^ b i j
  have hμ : ∀ u, (φ ≫ ψ) ≫ pr u = ∏ i, pr i ^ (d • (1 : Matrix (Fin n) (Fin n) ℤ)) u i := fun u => by
    rw [Category.assoc, hψ, comp_prod_zpow, ← hb]
    simp only [hφ, ← Finset.prod_zpow, ← zpow_mul, Matrix.mul_apply]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [mul_comm (c _ i)]
    exact (map_prod (zpowersHom _ (pr i)) (fun j => Multiplicative.ofAdd (b u j * c j i)) Finset.univ).symm
  have hE : (Out.boxLB o.diag pr).IsLB := LB.isLB_linComb hD _ _
  have hfin : IsFinite (φ ≫ ψ).left := by
    obtain ⟨α, hα⟩ := (cls_eq_zero_iff (LB.isLB_linComb hE (K := Fin 2) ![𝟙 G.left, (φ ≫ ψ).left]
      ![((d.natAbs ^ 2 : ℕ) : ℤ), -1])).1 (by
        have e₁ := cls_form_eq_sum hG o hA pr ((d * d) • (1 : Matrix (Fin n) (Fin n) ℤ)) (d • 1) (by
          rw [Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul,
            smul_smul d, two_smul])
        have e₂ := cls_form_eq_sum hG o hA pr 1 1 (by rw [Matrix.transpose_one, Matrix.one_mul, two_smul])
        have e₃ : ∀ j, ∏ i, pr i ^ (1 : Matrix (Fin n) (Fin n) ℤ) j i = 𝟙 G ≫ pr j := fun j => by
          rw [Finset.prod_eq_single j (fun v _ hv => by rw [Matrix.one_apply_ne hv.symm, zpow_zero]) (by simp),
            Matrix.one_apply_eq, zpow_one, Category.id_comp]
        simp only [← hμ] at e₁
        simp only [e₃] at e₂
        rw [← pull_cls_boxLB pr hD] at e₁ e₂
        rw [cls_linComb hE, Fin.sum_univ_two]
        change _ • pull (𝟙 G : G ⟶ G).left _ + (-1 : ℤ) • pull (φ ≫ ψ).left _ = 0
        rw [← e₁, ← e₂]
        simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, Matrix.cons_val_zero]
        rw [Nat.cast_pow, Int.natAbs_sq, pow_two, mul_smul, neg_one_smul, add_neg_cancel])
    exact MulFinite.isFinite_of_relAmple G _ hE (relAmple_boxLB S G o.A n p _ hD hA) (φ ≫ ψ) _
      (pow_ne_zero _ (Int.natAbs_ne_zero.2 hd)) α hα
  have : IsSeparated (ψ.left ≫ G.hom) := by rw [Over.w ψ]; infer_instance
  have : IsSeparated ψ.left := .of_comp _ G.hom
  have : IsAffineHom (φ.left ≫ ψ.left) := inferInstanceAs (IsAffineHom (φ ≫ ψ).left)
  have : IsAffineHom φ.left := .of_comp _ ψ.left
  have hF : (Out.boxLB o.diag (Out.powPr o.A (n := m))).IsLB := LB.isLB_linComb hD _ _
  refine relAmple_of_nsmul (LB.isLB_linComb o.isLB _ _) (pull_isLB hF φ.left) (N := 2 * N) (by omega) ?_
    (relAmple_pull_of_isAffineHom φ hF (relAmple_boxLB S _ o.A m (Out.powIsPowGrp o.A m) _ hD hA))
  have e := cls_form_eq_sum hG o hA pr (((2 * N : ℕ) : ℤ) • W) c (by
    rw [← hc, Matrix.transpose_smul, ← smul_add, smul_smul, Nat.cast_mul, Nat.cast_ofNat])
  simp only [← hφ] at e
  rw [cls_pull hF, pull_cls_boxLB _ hD, ← e, cls_linComb o.isLB, Finset.smul_sum]
  simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, natCast_zsmul]

end GlobalTheory.PosDefAmple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrincipalObjectDescendsLargeSubfield
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SiegDesc

theorem exists_isSquare {S' S : Scheme.{0}} {A' : Over S'} {A : Over S} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (w : φ ≫ A.hom = A'.hom ≫ f) :
    ∃ φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left, Geo.Tor.IsSquare φ φ₂ := by
  have v₁ : (fst A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  have v₂ : (snd A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  exact ⟨pullback.lift ((fst A' A').left ≫ φ) ((snd A' A').left ≫ φ)
    (by rw [Category.assoc, Category.assoc, w, reassoc_of% v₁, reassoc_of% v₂]),
    pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem isSquare_w {S' S : Scheme.{0}} {A' : Over S'} {A : Over S} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (w : φ ≫ A.hom = A'.hom ≫ f) {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} (h : Geo.Tor.IsSquare φ φ₂) :
    φ₂ ≫ (A ⊗ A).hom = (A' ⊗ A').hom ≫ f := by
  have w₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have v₁ : (fst A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  have h₁ := h.1
  rw [← w₁, reassoc_of% h₁, w, reassoc_of% v₁]

theorem isSquare_comp {S'' S' S : Scheme.{0}} {A'' : Over S''} {A' : Over S'} {A : Over S}
    {ψ : A''.left ⟶ A'.left} {φ : A'.left ⟶ A.left} {χ : A''.left ⟶ A.left} (e : ψ ≫ φ = χ)
    {ψ₂ : (A'' ⊗ A'').left ⟶ (A' ⊗ A').left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}
    {χ₂ : (A'' ⊗ A'').left ⟶ (A ⊗ A).left} (hψ : Geo.Tor.IsSquare ψ ψ₂) (hφ : Geo.Tor.IsSquare φ φ₂)
    (hχ : Geo.Tor.IsSquare χ χ₂) : ψ₂ ≫ φ₂ = χ₂ := by
  have a₁ := hψ.1
  have a₂ := hψ.2
  apply pullback.hom_ext
  · change _ ≫ (fst A A).left = _ ≫ (fst A A).left
    rw [Category.assoc, hφ.1, reassoc_of% a₁, hχ.1, e]
  · change _ ≫ (snd A A).left = _ ≫ (snd A A).left
    rw [Category.assoc, hφ.2, reassoc_of% a₂, hχ.2, e]

theorem isPullback_of_isSquare {S' S : Scheme.{0}} {A' : Over S'} {A : Over S} {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (hA : IsPullback φ A'.hom A.hom f) {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}
    (h : Geo.Tor.IsSquare φ φ₂) : IsPullback φ₂ (A' ⊗ A').hom (A ⊗ A).hom f := by
  have w₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have w₂ : (snd A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have v₁ : (fst A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  have v₂ : (snd A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  have h₁ := h.1
  have h₂ := h.2
  refine ⟨⟨isSquare_w hA.w h⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => pullback.lift
      (hA.lift (s.fst ≫ (fst A A).left) s.snd (by rw [Category.assoc, w₁, s.condition]))
      (hA.lift (s.fst ≫ (snd A A).left) s.snd (by rw [Category.assoc, w₂, s.condition]))
      (by rw [IsPullback.lift_snd, IsPullback.lift_snd])) (fun s => ?_) (fun s => ?_)
    (fun s m h1 h2 => ?_)⟩⟩
  · apply pullback.hom_ext
    · change _ ≫ (fst A A).left = _ ≫ (fst A A).left
      rw [Category.assoc, h₁, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
    · change _ ≫ (snd A A).left = _ ≫ (snd A A).left
      rw [Category.assoc, h₂, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_snd _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
  · rw [← v₁, ← Category.assoc]
    exact (congrArg (· ≫ A'.hom) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_snd _ _ _ _)
  · apply pullback.hom_ext
    · refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
      change _ ≫ (fst A' A').left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₁]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₁]
    · refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      change _ ≫ (snd A' A').left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₂]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₂]

theorem spMap_subtype_inclusion {K : Type} [Field K] {K₀ K₁ : Subfield K} (h : K₀ ≤ K₁) :
    spMap K₁.subtype ≫ spMap (Subfield.inclusion h) = spMap K₀.subtype := by
  rw [← Spec.map_comp]
  rfl

theorem siegPre_descends : ∀ (h M : ℕ) (o : Type) [CommRing o] (ζ : o) (K : Type) [Field K] (K₀ : Subfield K) (s₀ : Sp K₀ ⟶ Sp o) (s : Sp K ⟶ Sp o) (c : SiegPre h M ζ s), s = spMap K₀.subtype ≫ s₀ → c.Principal → ∃ F : Finset K, ∀ (K₁ : Subfield K) (hK : K₀ ≤ K₁), (F : Set K) ⊆ K₁ → ∃ c₁ : SiegPre h M ζ (spMap (Subfield.inclusion hK) ≫ s₀), c₁.Principal ∧ SiegPB c c₁ (spMap K₁.subtype) := by
  intro h M o _ ζ K _ K₀ s₀ s c hs hc
  classical
  obtain ⟨sA, hA⟩ := _root_.GlobalTheory.exists_finset_isProjOver_descends K K₀ c.A.left c.A.hom (GlobalTheory.ProjSpace.isProjOver_of_relAmple hc.1)
  let K' : Subfield K := K₀ ⊔ Subfield.closure (sA : Set K)
  obtain ⟨X', p', φ', hproj, hpb⟩ := hA K' le_sup_left
    (Subfield.subset_closure.trans (SetLike.coe_subset_coe.2 le_sup_right))
  have : IsProper p' := by
    obtain ⟨N, i, _, rfl⟩ := hproj
    have := isProper_str K' N
    infer_instance
  have : LocallyOfFinitePresentation p' :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  let A' : Over (Sp K') := Over.mk p'
  have : IsProper A'.hom := ‹IsProper p'›
  have : LocallyOfFinitePresentation A'.hom := ‹LocallyOfFinitePresentation p'›
  have hpb' : IsPullback (φ' : c.A.left ⟶ A'.left) c.A.hom A'.hom (spMap K'.subtype) := hpb
  obtain ⟨sG, hG⟩ := GlobalTheory.grpObj_descends_to_large_subfield K K' A' c.A φ' hpb'
  obtain ⟨φ₂', hsq'⟩ := exists_isSquare hpb'.w
  have : IsProper (A' ⊗ A').hom := by
    change IsProper (pullback.fst A'.hom A'.hom ≫ A'.hom)
    infer_instance
  obtain ⟨sL, hL⟩ := _root_.GlobalTheory.LBDescent.exists_lb_subfield K K' (A' ⊗ A').left (c.A ⊗ c.A).left (A' ⊗ A').hom (c.A ⊗ c.A).hom φ₂'
    c.P c.isLB (isPullback_of_isSquare hpb' hsq')
  obtain ⟨lv, hlv⟩ : ∃ lv : Fin h ⊕ Fin h → (Sp K ⟶ c.A.left), ∀ u, lv u = (c.lev (Pi.single u 1)).left :=
    ⟨_, fun _ => rfl⟩
  have hlev : ∀ u, lv u ≫ c.A.hom = 𝟙 (Sp K) := fun u =>
    (congrArg (· ≫ c.A.hom) (hlv u)).trans (Over.w (c.lev (Pi.single u 1)))
  obtain ⟨sP, hP⟩ := _root_.GlobalTheory.morphisms_descend_to_large_subfield K K' (Sp K') (Sp K) (𝟙 _) (𝟙 _) (spMap K'.subtype) X' p' (Fin h ⊕ Fin h)
    (fun u => lv u ≫ φ') IsPullback.of_id_snd
    (fun u => by
      have e := hlev u
      rw [Category.comp_id, Category.assoc, hpb.w, reassoc_of% e])
  refine ⟨sA ∪ sG ∪ sL ∪ sP, fun K₁ hK hF => ?_⟩
  simp only [Finset.coe_union, Set.union_subset_iff] at hF
  obtain ⟨⟨⟨hsA, hsG⟩, hsL⟩, hsP⟩ := hF
  have h' : K' ≤ K₁ := sup_le hK (Subfield.closure_le.2 hsA)
  let j := spMap (Subfield.inclusion h')
  have hj : spMap K₁.subtype ≫ j = spMap K'.subtype := spMap_subtype_inclusion h'
  let A₁ : Over (Sp K₁) := Over.mk (pullback.snd p' j)
  let φ₁ : A₁.left ⟶ A'.left := pullback.fst p' j
  have hpb₁ : IsPullback φ₁ A₁.hom A'.hom j := IsPullback.of_hasPullback p' j
  let ψ : c.A.left ⟶ A₁.left := hpb₁.lift φ' (c.A.hom ≫ spMap K₁.subtype)
    (by rw [Category.assoc, hj]; exact hpb.w)
  have hψ₁ : ψ ≫ φ₁ = φ' := hpb₁.lift_fst _ _ _
  have hψ₂ : ψ ≫ A₁.hom = c.A.hom ≫ spMap K₁.subtype := hpb₁.lift_snd _ _ _
  obtain ⟨grp, hgrp⟩ := hG K₁ h' hsG A₁ φ₁ ψ hpb₁ hψ₁ hψ₂
  obtain ⟨φ₂, hsq₁⟩ := exists_isSquare hpb₁.w
  obtain ⟨ψ₂, hsqψ⟩ := exists_isSquare hψ₂
  obtain ⟨P₁, hP₁, hiso⟩ := hL K₁ h' hsL (A₁ ⊗ A₁).left (A₁ ⊗ A₁).hom φ₂ ψ₂
    (isPullback_of_isSquare hpb₁ hsq₁) (isSquare_comp hψ₁ hsqψ hsq₁ hsq') (isSquare_w hψ₂ hsqψ)
  obtain ⟨f₁, hf₁⟩ := hP K₁ h' hsP (Sp K₁) (𝟙 _) j (spMap K₁.subtype) IsPullback.of_id_snd hj (by simp)
  let l : Fin h ⊕ Fin h → (Sp K₁ ⟶ A₁.left) := fun u => hpb₁.lift (f₁ u) (𝟙 _)
    (by rw [Category.id_comp]; exact (hf₁ u).2.trans (Category.comp_id _))
  have hl₁ : ∀ u, l u ≫ φ₁ = f₁ u := fun u => hpb₁.lift_fst _ _ _
  have hl₂ : ∀ u, l u ≫ A₁.hom = 𝟙 _ := fun u => hpb₁.lift_snd _ _ _
  let lev₁ : Fin h ⊕ Fin h → (𝟙_ (Over (Sp K₁)) ⟶ A₁) := fun u => Over.homMk (l u) (hl₂ u)
  obtain ⟨c₁, hc₁⟩ := _root_.GlobalTheory.exists_siegPre_of_descended_data h M o ζ K₁ K K₁.subtype (spMap (Subfield.inclusion hK) ≫ s₀) s c A₁ ψ ψ₂ P₁
    lev₁ (by rw [hs, ← Category.assoc, spMap_subtype_inclusion]) hgrp hsqψ hP₁ hiso (fun u => by
      have e := hlev u
      have key : lv u ≫ ψ = spMap K₁.subtype ≫ l u := by
        apply hpb₁.hom_ext
        · rw [Category.assoc, Category.assoc, hψ₁, hl₁]
          exact (hf₁ u).1.symm
        · rw [Category.assoc, Category.assoc, hψ₂, hl₂, reassoc_of% e, Category.comp_id]
      exact (congrArg (· ≫ ψ) (hlv u)).symm.trans key)
  exact ⟨c₁, GlobalTheory.SiegelDescent.principal_of_fieldExtension h M o ζ K₁ K K₁.subtype _ s c₁ c hc₁ hc, hc₁⟩

end GlobalTheory.SiegDesc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelObjectDescendsFgSubfield
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ThetaDescent

def gen {o K : Type} [CommRing o] [Field K] (β : o →+* K) (s : Finset K) : Subfield K :=
  Subfield.closure (Set.range β ∪ s)

theorem gen_mono {o K : Type} [CommRing o] [Field K] (β : o →+* K) {s s' : Finset K} (h : s ⊆ s') :
    gen β s ≤ gen β s' :=
  Subfield.closure_mono (Set.union_subset_union_right _ (Finset.coe_subset.2 h))

theorem subset_gen {o K : Type} [CommRing o] [Field K] (β : o →+* K) {s s' : Finset K} (h : s ⊆ s') :
    (s : Set K) ⊆ gen β s' :=
  fun _ hx => Subfield.subset_closure (Or.inr (h hx))

theorem mem_gen {o K : Type} [CommRing o] [Field K] (β : o →+* K) (s : Finset K) (a : o) : β a ∈ gen β s :=
  Subfield.subset_closure (Or.inl ⟨a, rfl⟩)

theorem countable_gen {o K : Type} [CommRing o] [Field K] (β : o →+* K) (s : Finset K) [Countable o] :
    Countable (gen β s) := by
  have hc : (Set.range β ∪ (s : Set K)).Countable := (Set.countable_range β).union s.countable_toSet
  rw [← Cardinal.mk_le_aleph0_iff]
  refine (Subfield.cardinalMk_closure_le_max _).trans ?_
  exact max_le (Cardinal.mk_le_aleph0_iff.2 hc.to_subtype) le_rfl

theorem spMap_subtype {K : Type} [Field K] {K₀ K₁ : Subfield K} (h : K₀ ≤ K₁) :
    spMap K₁.subtype ≫ spMap (Subfield.inclusion h) = spMap K₀.subtype := by
  rw [← Spec.map_comp]; rfl

theorem isProper_of_isProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsProjOver f) :
    IsProper f := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have := isProper_str R N
  infer_instance

theorem descends_of
    (hproj : ∀ (K : Type) [Field K] (K₀ : Subfield K) (X : Scheme.{0}) (p : X ⟶ Sp K), IsProjOver p → ∃ s : Finset K, ∀ K₁ : Subfield K, K₀ ≤ K₁ → (s : Set K) ⊆ K₁ → ∃ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (φ : X ⟶ X₁), IsProjOver p₁ ∧ IsPullback φ p p₁ (spMap K₁.subtype))
    (hmor : ∀ (K : Type) [Field K] (K₀ : Subfield K) (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀) (Z : Scheme.{0}) (q : Z ⟶ Sp K₀) [QuasiCompact p₀] [QuasiSeparated p₀] [LocallyOfFinitePresentation q] (I : Type) [Finite I] (f : I → (X ⟶ Z)), IsPullback φ p p₀ (spMap K₀.subtype) → (∀ j, f j ≫ q = φ ≫ p₀) → ∃ s : Finset K, ∀ (K₁ : Subfield K) (h : K₀ ≤ K₁), (s : Set K) ⊆ K₁ → ∀ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (φ₁ : X₁ ⟶ X₀) (ψ : X ⟶ X₁), IsPullback φ₁ p₁ p₀ (spMap (Subfield.inclusion h)) → ψ ≫ φ₁ = φ → ψ ≫ p₁ = p ≫ spMap K₁.subtype → ∃ f₁ : I → (X₁ ⟶ Z), ∀ j, ψ ≫ f₁ j = f j ∧ f₁ j ≫ q = φ₁ ≫ p₀)
    (hgrp : ∀ (K : Type) [Field K] (K₀ : Subfield K) (A₀ : Over (Sp K₀)) (A : Over (Sp K)) [GrpObj A] (φ : A.left ⟶ A₀.left) [QuasiCompact A₀.hom] [QuasiSeparated A₀.hom] [LocallyOfFinitePresentation A₀.hom], IsPullback φ A.hom A₀.hom (spMap K₀.subtype) → ∃ s : Finset K, ∀ (K₁ : Subfield K) (h : K₀ ≤ K₁), (s : Set K) ⊆ K₁ → ∀ (A₁ : Over (Sp K₁)) (φ₁ : A₁.left ⟶ A₀.left) (ψ : A.left ⟶ A₁.left), IsPullback φ₁ A₁.hom A₀.hom (spMap (Subfield.inclusion h)) → ψ ≫ φ₁ = φ → ψ ≫ A₁.hom = A.hom ≫ spMap K₁.subtype → ∃ _ : GrpObj A₁, IsGrpPullback A A₁ (spMap K₁.subtype) ψ)
    (hlb : ∀ (K : Type) [Field K] (K₀ : Subfield K) (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀) [QuasiCompact p₀] [QuasiSeparated p₀] (L : LB X), L.IsLB → IsPullback φ p p₀ (spMap K₀.subtype) → ∃ s : Finset K, ∀ (K₁ : Subfield K) (h : K₀ ≤ K₁), (s : Set K) ⊆ K₁ → ∀ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (φ₁ : X₁ ⟶ X₀) (ψ : X ⟶ X₁), IsPullback φ₁ p₁ p₀ (spMap (Subfield.inclusion h)) → ψ ≫ φ₁ = φ → ψ ≫ p₁ = p ≫ spMap K₁.subtype → ∃ L₁ : LB X₁, L₁.IsLB ∧ LBIso L (L₁.pull ψ))
    (hobj : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (β₀ : o →+* K₀) (β : o →+* K) (t : TObj g k J b (spMap β)) (A₀ : Over (Sp K₀)) [GrpObj A₀] (φ : t.A.left ⟶ A₀.left) (L₀ : LB A₀.left) (pt₀ : Fin (2 * g) → (Out.baseOver (Sp K₀) ⟶ A₀)) (act₀ : J → (A₀ ⟶ A₀)), i.comp β₀ = β → IsGrpPullback t.A A₀ (spMap i) φ → L₀.IsLB → LBIso t.L (L₀.pull φ) → (∀ a, (t.pt a).left ≫ φ = spMap i ≫ (pt₀ a).left) → (∀ j, (t.act j).left ≫ φ = φ ≫ (act₀ j).left) → ∃ t₀ : TObj g k J b (spMap β₀), TMap t t₀ (spMap i)) :
    ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) [Finite J] (K : Type) [Field K] (β : o →+* K) (t : TObj g k J b (spMap β)), ∃ (K₀ : Subfield K) (β₀ : o →+* K₀) (t₀ : TObj g k J b (spMap β₀)), K₀.subtype.comp β₀ = β ∧ (Countable o → Countable K₀) ∧ (∃ s : Finset K, K₀ = Subfield.closure (Set.range β ∪ s)) ∧ TMap t t₀ (spMap K₀.subtype) := by
  intro o _ g k J b _ K _ β t
  classical
  obtain ⟨s₀, H₀⟩ := hproj K (gen β ∅) t.A.left t.A.hom (GlobalTheory.ProjSpace.isProjOver_of_relAmple t.ample)
  obtain ⟨X₀, p₀, φ, hp₀, sq⟩ := H₀ (gen β s₀) (gen_mono β (Finset.empty_subset _)) (subset_gen β le_rfl)
  have : IsProper p₀ := isProper_of_isProjOver hp₀
  have : LocallyOfFinitePresentation p₀ := inferInstance
  have : QuasiCompact (Over.mk p₀).hom := inferInstanceAs (QuasiCompact p₀)
  have : QuasiSeparated (Over.mk p₀).hom := inferInstanceAs (QuasiSeparated p₀)
  have : LocallyOfFinitePresentation (Over.mk p₀).hom := inferInstanceAs (LocallyOfFinitePresentation p₀)
  obtain ⟨s₁, H₁⟩ := hgrp K (gen β s₀) (Over.mk p₀) t.A φ sq
  obtain ⟨s₂, H₂⟩ := hlb K (gen β s₀) X₀ t.A.left p₀ t.A.hom φ t.L t.isLB sq
  obtain ⟨s₃, H₃⟩ := hmor K (gen β s₀) X₀ t.A.left p₀ t.A.hom φ X₀ p₀ J (fun j => (t.act j).left ≫ φ) sq
    (fun j => by rw [Category.assoc, sq.w, ← Category.assoc, Over.w])
  obtain ⟨s₄, H₄⟩ := hmor K (gen β s₀) (Sp (gen β s₀)) (Sp K) (𝟙 _) (𝟙 _) (spMap (gen β s₀).subtype) X₀ p₀
    (Fin (2 * g)) (fun a => (t.pt a).left ≫ φ) (IsPullback.of_vert_isIso ⟨by simp⟩)
    (fun a => by
      have e : (t.pt a).left ≫ t.A.hom = 𝟙 _ := Over.w (t.pt a)
      rw [Category.assoc, sq.w, ← Category.assoc, e]; simp)
  let s : Finset K := s₀ ∪ s₁ ∪ s₂ ∪ s₃ ∪ s₄
  have h : gen β s₀ ≤ gen β s := gen_mono β (fun x hx => by simp [s, hx])
  let inc := spMap (Subfield.inclusion h)
  let A₁ : Over (Sp (gen β s)) := Over.mk (pullback.snd p₀ inc)
  let φ₁ : A₁.left ⟶ X₀ := pullback.fst p₀ inc
  have sq₁ : IsPullback φ₁ A₁.hom p₀ inc := IsPullback.of_hasPullback p₀ inc
  let ψ : t.A.left ⟶ A₁.left := sq₁.lift φ (t.A.hom ≫ spMap (gen β s).subtype)
    (by rw [Category.assoc, spMap_subtype h, sq.w])
  have hψ₁ : ψ ≫ φ₁ = φ := sq₁.lift_fst _ _ _
  have hψ₂ : ψ ≫ A₁.hom = t.A.hom ≫ spMap (gen β s).subtype := sq₁.lift_snd _ _ _
  obtain ⟨gr₁, hG⟩ := H₁ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) A₁ φ₁ ψ sq₁ hψ₁ hψ₂
  obtain ⟨L₁, hL₁, hL⟩ := H₂ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) A₁.left A₁.hom φ₁ ψ
    sq₁ hψ₁ hψ₂
  obtain ⟨f₁, hf₁⟩ := H₃ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) A₁.left A₁.hom φ₁ ψ
    sq₁ hψ₁ hψ₂
  obtain ⟨x₁, hx₁⟩ := H₄ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) (Sp (gen β s)) (𝟙 _) inc
    (spMap (gen β s).subtype) (IsPullback.of_vert_isIso ⟨by simp [inc]⟩) (spMap_subtype h) (by simp)
  let act₁ : J → (A₁ ⟶ A₁) := fun j =>
    Over.homMk (sq₁.lift (f₁ j) A₁.hom (by rw [(hf₁ j).2, sq₁.w])) (sq₁.lift_snd _ _ _)
  let pt₁ : Fin (2 * g) → (Out.baseOver (Sp (gen β s)) ⟶ A₁) := fun a =>
    Over.homMk (sq₁.lift (x₁ a) (𝟙 _) (by rw [(hx₁ a).2]; simp)) (sq₁.lift_snd _ _ _)
  let β₁ : o →+* gen β s := β.codRestrict _ (mem_gen β s)
  have hβ : (gen β s).subtype.comp β₁ = β := rfl
  obtain ⟨t₀, ht₀⟩ := hobj o g k J b (gen β s) K (gen β s).subtype β₁ β t A₁ ψ L₁ pt₁ act₁ hβ hG hL₁ hL
    (fun a => by
      have e : (t.pt a).left ≫ t.A.hom = 𝟙 _ := Over.w (t.pt a)
      have e₁ : (pt₁ a).left ≫ φ₁ = x₁ a := sq₁.lift_fst _ _ _
      have e₂ : (pt₁ a).left ≫ A₁.hom = 𝟙 _ := sq₁.lift_snd _ _ _
      apply sq₁.hom_ext
      · rw [Category.assoc, hψ₁]
        exact ((hx₁ a).1.symm.trans (congrArg _ e₁.symm)).trans (Category.assoc _ _ _).symm
      · rw [Category.assoc, hψ₂, ← Category.assoc, e]
        refine (Category.id_comp _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
        exact ((congrArg _ e₂).trans (Category.comp_id _)).symm)
    (fun j => by
      have e₁ : (act₁ j).left ≫ φ₁ = f₁ j := sq₁.lift_fst _ _ _
      apply sq₁.hom_ext
      · rw [Category.assoc, hψ₁, Category.assoc, e₁, (hf₁ j).1]
      · rw [Category.assoc, hψ₂, ← Category.assoc, Over.w, Category.assoc, Over.w, hψ₂])
  exact ⟨gen β s, β₁, t₀, hβ, fun _ => countable_gen β s, ⟨s, rfl⟩, ht₀⟩

theorem descends_to_fg_subfield :
    ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) [Finite J] (K : Type) [Field K] (β : o →+* K) (t : TObj g k J b (spMap β)), ∃ (K₀ : Subfield K) (β₀ : o →+* K₀) (t₀ : TObj g k J b (spMap β₀)), K₀.subtype.comp β₀ = β ∧ (Countable o → Countable K₀) ∧ (∃ s : Finset K, K₀ = Subfield.closure (Set.range β ∪ s)) ∧ TMap t t₀ (spMap K₀.subtype) :=
  descends_of (@_root_.GlobalTheory.exists_finset_isProjOver_descends) (@_root_.GlobalTheory.morphisms_descend_to_large_subfield) (@GlobalTheory.grpObj_descends_to_large_subfield) (@_root_.GlobalTheory.LBDescent.exists_lb_subfield) (@GlobalTheory.exists_thetaObj_of_descended_data)

end GlobalTheory.ThetaDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilPairingTorsionBasisSymplecticStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_pairing_torsion_basis_symplectic : Out.Laws → Out.Laws2 → ∀ (g N k : ℕ) (Mat : Matrix (Fin (2 * g)) (Fin (2 * g)) (ZMod k)), ∃ S : Matrix (Fin (2 * g)) (Fin (2 * g)) (ZMod k), ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (pt : Fin (2 * g) → (Out.baseOver (Sp K) ⟶ P.A)) (ζ : Kˣ) (f s : P.A ⟶ P.A), (k : K) ≠ 0 → IsPrimitiveRoot ζ k → TorsBasis P.A k pt → (∀ i j, Out.WeilIs P.A P.L k (pt i) (pt j) (unitOn (ζ ^ Out.stdSymp g i j))) → IsMonHom f → ActsBy pt f Mat → FormIs P (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, f.left] ![(N : ℤ), (N : ℤ)]) s → ActsBy pt s S := by
  first | exact @GlobalTheory.FormTorsion.exists_matrix_form | exact GlobalTheory.FormTorsion.exists_matrix_form | (intros; apply GlobalTheory.FormTorsion.exists_matrix_form <;> assumption)
end

