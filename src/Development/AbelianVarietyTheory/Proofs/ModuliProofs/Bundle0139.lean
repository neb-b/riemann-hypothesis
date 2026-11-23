module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFgForallOverLbIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LamIsoOfPairings
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PairingDetermines

open Out CommutatorPairing DescentPairing PrimCocycle IsoDescent

section OnePoint

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A}

theorem exists_gen_transl (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (cb : CubicalStr A L) {T : Over S} (p₀ : T.left)
    (hT : ∀ p : T.left, p = p₀) (n : ℕ) (x : T ⟶ A) (hx : x ^ n = 1) :
    ∃ u : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(mulT A T n ≫ translPt A x).left, (snd T A ^ n).left] ![1, -1]),
      u.IsGen ∧ ∀ (y : T ⟶ A) (c : Γ(T.left, ⊤)ˣ), y ^ n = 1 → WeilIs A L.L n x y c →
        ∀ (Z : Over S) (t : Z ⟶ T) (a : Z ⟶ A) (z : Z.left) (J), Good L.L z J →
          val u (lift t ((t ≫ y) * a)).left z J = val u (lift t a).left z J * gm t.left z ⊤ c := by
  obtain ⟨θx, rfl, -⟩ := exists_theta cb p₀ hT n x hx
  obtain ⟨u, hu, vu⟩ := exists_triv cb p₀ hT n θx
  refine ⟨u, hu, fun y c hy hc Z t a z J hJ => ?_⟩
  obtain ⟨θy, rfl, vy⟩ := exists_theta cb p₀ hT n y hy
  have hcm := (commIsOf_iff L.isLB θx θy c).1 ((GlobalLift.weilIs_iff_commIsOf hG hA L.isLB θx θy c).1 hc)
  obtain ⟨s, hs⟩ := vu _ t z J hJ
  obtain ⟨s', hs'⟩ := vy _ t z J hJ
  have k₁ := hcm _ t a z J hJ
  have k₂ := cubN_transl (isCub_cubV cb hJ) n (t ≫ θy.pt) a (t ≫ θx.pt)
    ((map_pow (preHom t) θy.pt n).symm.trans (by rw [hy]; exact map_one _))
  refine (hs _).trans (Eq.trans ?_ (congrArg₂ (· * ·) (hs _) k₁.symm).symm)
  have t₁ := hs' a
  have t₂ := hs' ((t ≫ θx.pt) * a)
  apply Additive.ofMul.injective
  have E := fun {p q : (Z.left.presheaf.stalk z)ˣ} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E t₁; have a₂ := E t₂; have a₃ := E k₂
  simp only [commVal, ofMul_mul, ofMul_inv] at a₁ a₂ a₃ ⊢
  linear_combination (norm := abel) a₃ + a₁ - a₂

end OnePoint

section Field

variable {k : Type} [Field k] {A : Over (Sp k)} [GrpObj A] [IsCommMonObj A]

theorem exists_gen_lam (hG : GlobalFnsSt) (hC : CubeSt) (P : PolAV (Sp k)) (α : A ⟶ P.A) [IsMonHom α] (d n : ℕ)
    (x : 𝟙_ (Over (Sp k)) ⟶ A) (hx : x ^ n = 1) :
    ∃ u : LB.Gen (LB.LinComb P.L
        (fun I => (mulA A n).left ≫ (lift (toUnit A ≫ x) (𝟙 A)).left ≫ lamφ A I ≫ α.left) (fun I => lamε I * d)),
      u.IsGen ∧ ∀ (y : 𝟙_ (Over (Sp k)) ⟶ A) (c : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ), y ^ n = 1 →
        WeilIs P.A P.L n (x ≫ α) (y ≫ α) c → ∀ (z : A.left) (J), Good P.L z J →
          val u ((toUnit A ≫ y) * 𝟙 A).left z J = val u (𝟙 _) z J * gm (toUnit A).left z ⊤ (c ^ d) := by
  have := P.isAb.comm
  obtain ⟨rig, hrig⟩ := P.rigid
  let L : RigLB P.A := ⟨P.L, rig, P.isLB, hrig⟩
  obtain ⟨⟨cb⟩, -⟩ := hC _ P L rfl
  let T := 𝟙_ (Over (Sp k))
  let p₀ : T.left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
  have hT : ∀ p : T.left, p = p₀ := fun p => Subsingleton.elim (α := PrimeSpectrum k) p p₀
  have hpow : ∀ y : T ⟶ A, y ^ n = 1 → (y ≫ α) ^ n = 1 := fun y hy => by
    rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  obtain ⟨u₀, hu₀, v₀⟩ := exists_gen_transl hG P.isAb cb p₀ hT n (x ≫ α) (hpow x hx)
  obtain ⟨σ, hσ⟩ := exists_frame P.isLB (K := Fin 2) ![(x ≫ α).left, (1 : T ⟶ P.A).left] ![-1, 1] p₀ hT
  obtain ⟨u₁, hu₁, v₁⟩ := exists_gen P.isLB
    (φ' := fun I => (mulA A n).left ≫ (lift (toUnit A ≫ x) (𝟙 A)).left ≫ lamφ A I ≫ α.left) (ε' := lamε)
    (fun U _ h => by
      have e₀ : mulA A n ≫ lift (toUnit A ≫ x) (𝟙 A) = lift (toUnit A ≫ x) (𝟙 A ^ n) := by
        rw [comp_lift, comp_toUnit_assoc, Category.comp_id]
      have e₁ : lift (toUnit A) α ≫ mulT P.A T n ≫ translPt P.A (x ≫ α) = ((toUnit A ≫ x) * 𝟙 A ^ n) ≫ α := by
        rw [← Category.assoc, mulT, comp_lift, lift_translPt, lift_fst, MonObj.comp_pow, lift_snd, MonObj.mul_comp,
          MonObj.pow_comp, Category.id_comp, Category.assoc]
      have e₂ : lift (toUnit A) α ≫ snd T P.A ^ n = (𝟙 A ^ n) ≫ α := by
        rw [MonObj.comp_pow, lift_snd, MonObj.pow_comp, Category.id_comp]
      have e₃ : toUnit A ≫ (1 : T ⟶ P.A) = (1 : A ⟶ A) ≫ α := by rw [MonObj.comp_one, MonObj.one_comp]
      have e := prod_lam (toUnit A ≫ x) (𝟙 A ^ n) (fun q => h (q ≫ α.left))
      refine Eq.trans ?_ (e.symm.trans (Finset.prod_congr rfl fun I _ => by
        rw [← e₀, Over.comp_left, Category.assoc, Category.assoc]))
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, ← Over.comp_left, e₁, e₂, e₃, Category.assoc, zpow_neg, zpow_one, _root_.mul_one]
      ac_rfl)
    (LB.mulGen P.L _ _ _ _ (LB.pullGen P.L _ _ u₀ (lift (toUnit A) α).left) (LB.pullGen P.L _ _ σ (toUnit A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu₀ _) (DVR.pullGen_isGen _ _ _ _ hσ _))
  obtain ⟨u, hu, v⟩ := WeilIsogeny.exists_gen_pow (ε' := fun I => lamε I * d) d (fun _ => rfl) u₁ hu₁
  refine ⟨u, hu, fun y c hy hc z J hJ => ?_⟩
  have w : ∀ a : A ⟶ A, val u a.left z J =
      (val u₀ (lift (toUnit A) (a ≫ α)).left z J * val σ (toUnit A).left z J) ^ d := fun a => by
    rw [v, v₁ _ _ z J hJ, val_mul hJ, val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, comp_lift,
      comp_toUnit]
  have w₀ := v₀ (y ≫ α) c (hpow y hy) hc A (toUnit A) (𝟙 A ≫ α) z J hJ
  refine (w _).trans (Eq.trans ?_ (congrArg (· * _) (w (𝟙 A))).symm)
  rw [MonObj.mul_comp, Category.assoc, map_pow, ← mul_pow, mul_right_comm]
  exact congrArg (fun q => (q * _) ^ d) w₀

theorem exists_gen_axis {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : A.left ⟶ X) (e : ℤ) :
    ∃ u : LB.Gen (LB.LinComb L (fun I => (lift (𝟙 A) (1 : A ⟶ A)).left ≫ lamφ A I ≫ F) (fun I => lamε I * e)),
      u.IsGen := by
  obtain ⟨u, hu, -⟩ := exists_gen hL (φ := PEmpty.elim) (ε := PEmpty.elim)
    (φ' := fun I => (lift (𝟙 A) (1 : A ⟶ A)).left ≫ lamφ A I ≫ F) (ε' := fun I => lamε I * e) (fun U _ h => by
      have q := prod_lam (𝟙 A) (1 : A ⟶ A) (fun q => h (q ≫ F) ^ e)
      rw [_root_.mul_one, mul_inv_cancel, _root_.one_mul, inv_mul_cancel] at q
      refine (Fintype.prod_empty _).trans (q.symm.trans (Finset.prod_congr rfl fun I _ => ?_))
      rw [← zpow_mul, mul_comm e, Category.assoc]) (LB.oneGen L)
    (fun _ _ => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  exact ⟨u, hu⟩

end Field

end GlobalTheory.PairingDetermines

namespace GlobalTheory

open PairingDetermines IsoDescent PrimCocycle

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoCubeLBOfWeilIsAdjoint
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.AdjointOfPairing

open ReciprocityTheory.ChartRestriction.G.Out CommutatorPairing DescentPairing

theorem lbIso_of_gen {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (t : LB.Gen (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' (fun k => - ε k)))) (ht : t.IsGen) :
    LBIso (LB.LinComb L φ ε) (LB.LinComb L φ' ε') := by
  have le : ∀ p : (K' → L.ι) × (K → L.ι), LB.wchart L φ' p.1 ⊓ LB.wchart L φ p.2 ≤
      LB.wchart L (Sum.elim φ' φ) (Sum.elim p.1 p.2) := fun p y hy => Set.mem_iInter.2 fun k => by
    rcases k with k | k
    exacts [Set.mem_iInter.1 hy.1 k, Set.mem_iInter.1 hy.2 k]
  refine gen_chartPull (A' := LB.div (LB.LinComb L φ' ε') (LB.LinComb L φ ε)) (h := 𝟙 Y)
    (A := LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' (fun k => - ε k)))
    ⟨fun p => Sum.elim p.1 p.2, le, fun y p q hp hq => ?_⟩ t ht
  refine (gm_div (LB.LinComb L φ ε) (LB.LinComb L φ' ε') (𝟙 Y) y p q ⟨hp, hq⟩).trans
    (Eq.trans ?_ (gm_linComb L _ _ (𝟙 Y) y _ _ (le p hp) (le q hq)).symm)
  refine (congrArg₂ (fun a b => a * b⁻¹) (gm_linComb L φ' ε' (𝟙 Y) y _ _ hp.1 hq.1)
    (gm_linComb L φ ε (𝟙 Y) y _ _ hp.2 hq.2)).trans (Eq.trans ?_ (Fintype.prod_sum_type _).symm)
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rfl

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

theorem exists_gen_pairing (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {L : RigLB A} (cb : CubicalStr A L)
    {T : Over S} (p₀ : T.left) (hT : ∀ p : T.left, p = p₀) (n : ℕ) (x : T ⟶ A) (hx : x ^ n = 1) :
    ∃ u : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(mulT A T n ≫ translPt A x).left, (snd T A ^ n).left] ![1, -1]),
      u.IsGen ∧ ∀ (y : T ⟶ A) (c : Γ(T.left, ⊤)ˣ), y ^ n = 1 → WeilIs A L.L n x y c →
        ∀ (Z : Over S) (t : Z ⟶ T) (w : Z ⟶ A) (z : Z.left) (J), Good L.L z J →
          val u (lift t ((t ≫ y) * w)).left z J = val u (lift t w).left z J * gm t.left z ⊤ c := by
  obtain ⟨θx, rfl, -⟩ := exists_theta cb p₀ hT n x hx
  obtain ⟨u, hu, vu⟩ := exists_triv cb p₀ hT n θx
  refine ⟨u, hu, fun y c hy hc Z t w z J hJ => ?_⟩
  obtain ⟨θy, rfl, vy⟩ := exists_theta cb p₀ hT n y hy
  have hcm := (commIsOf_iff L.isLB θx θy c).1 ((GlobalLift.weilIs_iff_commIsOf hG hA L.isLB θx θy c).1 hc)
  obtain ⟨s, hs⟩ := vu _ t z J hJ
  obtain ⟨s', hs'⟩ := vy _ t z J hJ
  have k₁ := hcm _ t w z J hJ
  have k₂ := cubN_transl (isCub_cubV cb hJ) n (t ≫ θy.pt) w (t ≫ θx.pt)
    ((map_pow (preHom t) θy.pt n).symm.trans (by rw [hy]; exact map_one _))
  refine (hs _).trans (Eq.trans ?_ (congrArg₂ (· * ·) (hs _) k₁.symm).symm)
  have t₁ := hs' w
  have t₂ := hs' ((t ≫ θx.pt) * w)
  apply Additive.ofMul.injective
  have E := fun {p q : (Z.left.presheaf.stalk z)ˣ} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E t₁; have a₂ := E t₂; have a₃ := E k₂
  simp only [commVal, ofMul_mul, ofMul_inv] at a₁ a₂ a₃ ⊢
  linear_combination (norm := abel) a₃ + a₁ - a₂


omit [IsCommMonObj A] in
theorem prod_mulT {T Z : Over S} (n : ℕ) (x : T ⟶ A) (t : Z ⟶ T) (w : Z ⟶ A) {U : Type} [CommGroup U]
    (h : (Z.left ⟶ A.left) → U) :
    ∏ i : Fin 2, h ((lift t w).left ≫ ![(mulT A T n ≫ translPt A x).left, (snd T A ^ n).left] i) ^ ![(1 : ℤ), -1] i =
      h ((t ≫ x) * w ^ n).left * (h (w ^ n).left)⁻¹ := by
  rw [Fin.prod_univ_two]
  show h (lift t w ≫ mulT A T n ≫ translPt A x).left ^ (1 : ℤ) * h (lift t w ≫ snd T A ^ n).left ^ (-1 : ℤ) = _
  rw [mulT, comp_lift_assoc, lift_fst, lift_translPt, MonObj.comp_pow, lift_snd, zpow_one, zpow_neg_one]

theorem exists_gen_of_formEq_zero {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = 1) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  obtain ⟨t, ht, -⟩ := exists_gen hL (φ' := φ) (ε' := ε) (fun U _ g => (Fintype.prod_empty _).trans (h U g).symm)
    (LB.oneGen L (Y := Y)) (fun i j => (map_one _).trans
      ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  exact ⟨t, ht⟩

theorem exists_gen_fibre (hl : Laws) {k : Type} [Field k] [IsAlgClosed k] (P : PolAV (Sp k)) (a a' : P.A ⟶ P.A)
    [IsMonHom a] [IsMonHom a'] (n : ℕ) (hn : (n : k) ≠ 0) (x : 𝟙_ (Over (Sp k)) ⟶ P.A) (hx : x ^ n = 1)
    (H : ∀ (y : 𝟙_ (Over (Sp k)) ⟶ P.A) (c : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ), y ^ n = 1 →
      WeilIs P.A P.L n (x ≫ a) y c → WeilIs P.A P.L n x (y ≫ a') c) :
    ∃ t : LB.Gen (LB.LinComb P.L
      (fun i => (lift (toUnit P.A ≫ x) (𝟙 P.A)).left ≫ rosatiφ P.A a a' i) rosatiε), t.IsGen := by
  have := P.isAb.comm
  obtain ⟨rig, hrig⟩ := P.rigid
  let L : RigLB P.A := ⟨P.L, rig, P.isLB, hrig⟩
  obtain ⟨⟨cb⟩, -⟩ := hl.cube _ P L rfl
  let p₀ : (𝟙_ (Over (Sp k))).left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
  have hT : ∀ p : (𝟙_ (Over (Sp k))).left, p = p₀ := fun p => Subsingleton.elim (α := PrimeSpectrum k) p p₀
  have hxa : (x ≫ a) ^ n = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  obtain ⟨u₁, hu₁, v₁⟩ := exists_gen_pairing hl.globalFns P.isAb cb p₀ hT n (x ≫ a) hxa
  obtain ⟨u₂, hu₂, v₂⟩ := exists_gen_pairing hl.globalFns P.isAb cb p₀ hT n x hx
  obtain ⟨σ, hσ⟩ := exists_frame P.isLB (K := Fin 2) ![(x ≫ a).left, x.left] ![-1, 1] p₀ hT
  obtain ⟨u, hu, vu⟩ := exists_gen P.isLB
    (φ' := fun i => (mulA P.A n).left ≫ (lift (toUnit P.A ≫ x) (𝟙 P.A)).left ≫ rosatiφ P.A a a' i) (ε' := rosatiε)
    (fun U _ h => by
      have e : ∀ i, (mulA P.A n).left ≫ (lift (toUnit P.A ≫ x) (𝟙 P.A)).left ≫ rosatiφ P.A a a' i =
          (lift (toUnit P.A ≫ x) (𝟙 P.A ^ n)).left ≫ rosatiφ P.A a a' i := fun i => by
        rw [← Category.assoc, ← Over.comp_left, comp_lift, comp_toUnit_assoc, Category.comp_id]
      have e' : (𝟙 P.A ^ n) ≫ a' = a' ^ n := by rw [MonObj.pow_comp, Category.id_comp]
      have f : ∏ i : Fin 2, h ((toUnit P.A).left ≫ ![(x ≫ a).left, x.left] i) ^ ![(-1 : ℤ), 1] i =
          (h (toUnit P.A ≫ x ≫ a).left)⁻¹ * h (toUnit P.A ≫ x).left := by
        rw [Fin.prod_univ_two]
        exact congrArg₂ (· * ·) (zpow_neg_one _) (zpow_one _)
      refine (DVR.prod_sum₂ (K := Fin 2 ⊕ Fin 2) (K' := Fin 2) (U := U) _
        (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _ (prod_mulT n (x ≫ a) (toUnit P.A) (𝟙 P.A) h)
        (DVR.prod_neg _ _ (prod_mulT n x (toUnit P.A) a' h))) f).trans ?_
      simp only [e]
      rw [prod_ros, e', Category.assoc]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.mulGen P.L _ _ _ _ (LB.mulGen P.L _ _ _ _ (LB.pullGen P.L _ _ u₁ (lift (toUnit P.A) (𝟙 P.A)).left)
      (LB.invGen P.L _ _ (LB.pullGen P.L _ _ u₂ (lift (toUnit P.A) a').left))) (LB.pullGen P.L _ _ σ (toUnit P.A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu₁ _)
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu₂ _))) (DVR.pullGen_isGen _ _ _ _ hσ _))
  have vw : ∀ (w : P.A ⟶ P.A) (z : P.A.left) (J), Good P.L z J → val u w.left z J =
      val u₁ (lift (toUnit P.A) w).left z J * (val u₂ (lift (toUnit P.A) (w ≫ a')).left z J)⁻¹ *
        val σ (toUnit P.A).left z J := fun w z J hJ => by
    refine (vu _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) ((val_pull hJ _ _ _).trans ?_) ((val_inv _ _).trans (congrArg (·⁻¹)
        ((val_pull hJ _ _ _).trans ?_))))) ((val_pull hJ _ _ _).trans ?_)))
    · rw [← Over.comp_left, comp_lift, comp_toUnit, Category.comp_id]
    · rw [← Over.comp_left, comp_lift, comp_toUnit]
    · rw [← Over.comp_left, comp_toUnit]
  refine exists_isGen_of_invariant P.isLB _ _ (mulA P.A n).left
    (I := {y : 𝟙_ (Over (Sp k)) ⟶ P.A // y ^ n = 1}) (fun y => ((toUnit P.A ≫ y.1) * 𝟙 P.A).left)
    (fun y => by
      rw [← Over.comp_left, GoodPoint.comp_mulA, mul_pow, ← MonObj.comp_pow, y.2, MonObj.comp_one, _root_.one_mul])
    (fun U f hf => torsion_invariant_descends (fun S _ Q m hm =>
      ⟨(hl.mulN S Q m hm).1, (hl.mulN S Q m hm).2.1, (hl.mulN S Q m hm).2.2.1, (hl.mulN S Q m hm).2.2.2.1⟩)
      k P n hn U f fun y hy => hf ⟨y, hy⟩) _ (fun _ => rfl) u hu fun y z J hJ => ?_
  obtain ⟨c, hc, -⟩ := (hl.weil _ P n _).1 (x ≫ a) y.1 hxa y.2
  have hya : (y.1 ≫ a') ^ n = 1 := by rw [← MonObj.pow_comp, y.2, MonObj.one_comp]
  refine (vw _ z J hJ).trans (Eq.trans ?_ (vw (𝟙 P.A) z J hJ).symm)
  rw [v₁ y.1 c y.2 hc _ _ _ z J hJ, MonObj.mul_comp, Category.assoc, v₂ _ c hya (H y.1 c y.2 hc) _ _ _ z J hJ,
    mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.mul_one]

end GlobalTheory.AdjointOfPairing

namespace GlobalTheory

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoGenericSpreadsOut
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

namespace GenericLB

open Spread

private theorem lbIso_pull_iff_lbIso_pull_pull_of_eq_comp {W X Y : Scheme.{0}} {M N : LB X} (hM : M.IsLB) (hN : N.IsLB) {a : Y ⟶ X}
    (j : W ⟶ Y) {a' : W ⟶ X} (ha : a' = j ≫ a) :
    LBIso (M.pull a') (N.pull a') ↔ LBIso ((M.pull a).pull j) ((N.pull a).pull j) := by
  have hM' := LB.isLB_pull hM a'
  have hN' := LB.isLB_pull hN a'
  have hMj := LB.isLB_pull (LB.isLB_pull hM a) j
  have hNj := LB.isLB_pull (LB.isLB_pull hN a) j
  constructor
  · intro h
    exact LBIso.trans hMj hM' hNj (LBIso.symm (lbIso_pull_pull hM j ha))
      (LBIso.trans hM' hN' hNj h (lbIso_pull_pull hN j ha))
  · intro h
    exact LBIso.trans hM' hMj hN' (lbIso_pull_pull hM j ha)
      (LBIso.trans hMj hNj hN' h (LBIso.symm (lbIso_pull_pull hN j ha)))

theorem exists_finset_lbIso {k A : Type} [CommRing k] [CommRing A] [Algebra k A] {B : Scheme.{0}} (pB : B ⟶ Sp k)
    [QuasiCompact pB] [QuasiSeparated pB] {M N : LB B} (hM : M.IsLB) (hN : N.IsLB)
    (H : LBIso (M.pull (pullback.fst pB (spMap (algebraMap k A)))) (N.pull (pullback.fst pB (spMap (algebraMap k A))))) :
    ∃ s : Finset A, LBIso (M.pull (pullback.fst pB (spMap (algebraMap k (Algebra.adjoin k (s : Set A))))))
      (N.pull (pullback.fst pB (spMap (algebraMap k (Algebra.adjoin k (s : Set A)))))) := by
  classical
  obtain ⟨j, g, hg⟩ := exists_lbIso_of_isLimit (bcDiagram pB A)
    (bcCone pB A).π.app (fun {_ _} f => (bcCone pB A).w f) (isLimitBcCone pB A)
    (i := Opposite.op ∅)
    (M.pull (pullback.fst _ _)) (N.pull (pullback.fst _ _))
    (LB.isLB_pull hM _) (LB.isLB_pull hN _)
    ((lbIso_pull_iff_lbIso_pull_pull_of_eq_comp hM hN _ (bcMap_fst pB _).symm).mp H)
  exact ⟨j.unop, (lbIso_pull_iff_lbIso_pull_pull_of_eq_comp hM hN ((bcDiagram pB A).map g) (bcMap_fst pB _).symm).mpr hg⟩

theorem exists_denom {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (s : Finset K) : ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) →
      ∃ ψ : Algebra.adjoin R (s : Set K) →+* R', ψ.comp (algebraMap R _) = φ := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors R) s
  refine ⟨b, nonZeroDivisors.ne_zero b.2, ?_⟩
  intro R' _ φ hφ
  have hb0 : (b : R) ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hunit : IsUnit (algebraMap R K (b : R)) := IsLocalization.map_units K b
  let g0 : Localization.Away (b : R) →+* K := IsLocalization.Away.lift (b : R) hunit
  have hg0 : ∀ r : R, g0 (algebraMap R _ r) = algebraMap R K r := fun r => IsLocalization.lift_eq _ r
  let g : Localization.Away (b : R) →ₐ[R] K := { g0 with commutes' := hg0 }
  have hinj : Function.Injective g := by
    change Function.Injective g0
    refine (IsLocalization.lift_injective_iff _).mpr fun x y => ?_
    exact ((IsLocalization.injective (Localization.Away (b : R))
      (powers_le_nonZeroDivisors_of_noZeroDivisors hb0)).eq_iff).trans
      (IsFractionRing.injective R K).eq_iff.symm
  have hle : Algebra.adjoin R (s : Set K) ≤ g.range := by
    refine Algebra.adjoin_le fun x hx => ?_
    obtain ⟨a, ha⟩ := hb x hx
    refine ⟨IsLocalization.mk' (Localization.Away (b : R)) a ⟨(b : R), Submonoid.mem_powers _⟩, ?_⟩
    show IsLocalization.Away.lift (b : R) hunit _ = x
    unfold IsLocalization.Away.lift
    rw [IsLocalization.lift_mk'_spec]
    rw [ha, Algebra.smul_def]
  refine ⟨((IsLocalization.Away.lift (b : R) hφ).comp
    ((AlgEquiv.ofInjective g hinj).symm : g.range →ₐ[R] Localization.Away (b : R)).toRingHom).comp
    (Subalgebra.inclusion hle).toRingHom, ?_⟩
  ext r
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]
  exact IsLocalization.lift_eq _ r

end GenericLB

theorem lbIso_generic_spreads_out : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (B : Scheme.{0}) (pB : B ⟶ Sp R) (M N : LB B), QuasiCompact pB → QuasiSeparated pB → M.IsLB → N.IsLB → LBIso (M.pull (pullback.fst pB (spMap (algebraMap R K)))) (N.pull (pullback.fst pB (spMap (algebraMap R K)))) → ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) → LBIso (M.pull (pullback.fst pB (spMap φ))) (N.pull (pullback.fst pB (spMap φ))) := by
  intro R K _ _ _ _ _ _ B pB M N hqc hqs hM hN H
  have := hqc
  have := hqs
  obtain ⟨s, hs⟩ := GenericLB.exists_finset_lbIso pB hM hN H
  obtain ⟨f, hf0, hf⟩ := GenericLB.exists_denom (R := R) s
  refine ⟨f, hf0, fun R' _ φ hφ => ?_⟩
  obtain ⟨ψ, hψ⟩ := hf R' φ hφ
  have key : spMap φ = spMap ψ ≫ spMap (algebraMap R (Algebra.adjoin R (s : Set K))) := by
    rw [spMap_comp_ring, hψ]
  exact Spread.lbIso_pull_comp
    (pullback.lift (pullback.fst pB (spMap φ)) (pullback.snd _ _ ≫ spMap ψ)
      (by rw [pullback.condition, key, Category.assoc]))
    (pullback.lift_fst _ _ _).symm (pullback.lift_fst _ _ _).symm hs

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelDescentCoefficientField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.LevelMapField

private theorem KA_mono_of_A_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {l₀ l : Level H} (h : l₀.A ∣ l.A) : KA l₀ ≤ KA l := by
  unfold KA
  rw [IntermediateField.adjoin_le_iff]
  intro x hx
  rcases hx with rfl | rfl
  · exact IntermediateField.subset_adjoin _ _ (by simp)
  · rw [GlobalTheory.LevelCover.zeta_dvd l.A_pos h]
    exact pow_mem (IntermediateField.subset_adjoin _ _ (by simp)) _

private theorem M'_dvd_of_level_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {l₀ l : Level H} (h : l₀.Dvd l) : l₀.M' ∣ l.M' := by
  unfold Level.Dvd at h
  unfold Level.M'
  exact Nat.lcm_dvd (h.1.trans (Nat.dvd_lcm_left _ _)) (h.2.2.trans (Nat.dvd_lcm_right _ _))

private theorem M'_pos' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (l : Level H) : 0 < l.M' := by
  unfold Level.M'
  have h3 := l.three_le
  exact Nat.lcm_pos (by omega) l.A_pos

theorem exists_levelMap : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l : Level H) (c : Coeff l) (o : Obj D l (baseKA l) (pullback.fst (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ (Xo l).s)) (_ : ObjMap o (Xo l).univ (pullback.fst _ _)), l₀.Dvd l → ∃ (k : KA l₀ →+* c.F) (r : (Xo l).XF c ⟶ (Xo l₀).X) (ν : SABMap o.t (Xo l₀).univ.t r) (hr : r ≫ (Xo l₀).s = pullback.snd _ _ ≫ spMap k), IsInc (KA l₀).val.toRingHom c.F.val.toRingHom k ∧ LevComp o (Xo l₀).univ r ν ∧ IsFinite (pullback.lift r _ hr) ∧ Etale (pullback.lift r _ hr) ∧ Surjective (pullback.lift r _ hr) := by
  intro _ _ _ E _ _ _ H D Xo hN l₀ l c o mo hd
  have hA : l₀.A ∣ l.A := by
    unfold Level.Dvd at hd
    exact hd.2.2
  have hle : KA l₀ ≤ c.F := (KA_mono_of_A_dvd hA).trans c.le
  have hz : zeta l₀.M' ∈ c.F := by
    rw [GlobalTheory.LevelCover.zeta_dvd (M'_pos' l) (M'_dvd_of_level_dvd hd)]
    exact pow_mem c.zeta_mem _
  obtain ⟨r₀, -, m, -, -, hm1, hm2, -, hF⟩ := hN l₀ l (Xo l₀) (Xo l) hd
  obtain ⟨rF, h1, h2, hfin, het, hsurj, -⟩ := hF ⟨c.F, c.fin, c.conj, hz, hle⟩ c rfl
  have hid : spMap (IntermediateField.inclusion (le_refl c.F)).toRingHom = 𝟙 (Sp c.F) :=
    GlobalTheory.LevelCover.spMap_inclusion_self _
  have hr : (rF ≫ pullback.fst _ _) ≫ (Xo l₀).s =
      pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hle).toRingHom := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, h2]
    erw [hid, Category.comp_id]
  have hlift : pullback.lift (rF ≫ pullback.fst _ _) (pullback.snd _ _) hr = rF := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
    · rw [pullback.lift_snd, h2]
      erw [hid, Category.comp_id]
  obtain ⟨ν, hν⟩ := GlobalTheory.LevelCover.sab_comp mo.toSABMap m (e := rF ≫ pullback.fst _ _) h1.symm
  refine ⟨(IntermediateField.inclusion hle).toRingHom, rF ≫ pullback.fst _ _, ν, hr,
    fun x => rfl, ?_, ?_, ?_, ?_⟩
  · unfold LevComp
    refine ⟨fun a => ?_, fun a => ?_⟩
    · rw [hν, ← Category.assoc,
        GlobalTheory.LevelCover.sec_pow mo.toSABMap (o.eta a) ((Xo l).univ.eta a) (mo.eta a),
        Category.assoc, hm1 a, ← Category.assoc, ← h1]
    · rw [hν, ← Category.assoc,
        GlobalTheory.LevelCover.sec_pow mo.toSABMap (o.etaA a) ((Xo l).univ.etaA a) (mo.etaA a),
        Category.assoc, hm2 a, ← Category.assoc, ← h1]
  · rw [hlift]; exact hfin
  · rw [hlift]; exact het
  · rw [hlift]; exact hsurj

end GlobalTheory.LevelMapField
end

