module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0062
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianModelSplitSpecialFibre
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0063
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRatLog
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.NormValuation

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing in
open scoped CategoryTheory.Obj in
open Classical in
attribute [local instance] Over.cartesianMonoidalCategory in
private lemma exists_rat_norm_eq_rpow {p : ℕ} [Fact p.Prime] {x : PadicAlgCl p} (hx : x ≠ 0) :
    ∃ t : ℚ, ‖x‖ = (p : ℝ) ^ (t : ℝ) := by
  have hint : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
  have hc := minpoly.coeff_zero_ne_zero hint hx
  refine ⟨(-((minpoly ℚ_[p] x).coeff 0).valuation : ℚ) / (minpoly ℚ_[p] x).natDegree, ?_⟩
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow,
    Padic.norm_eq_zpow_neg_valuation hc, ← Real.rpow_intCast,
    ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  push_cast
  ring


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing in
open scoped CategoryTheory.Obj in
open Classical in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.NormValuation.main : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra (FractionRing V) (PadicAlgCl p)], (∀ x : FractionRing V, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → ∀ ϖ : V, Irreducible ϖ → ∃ v : AddValuation (PadicAlgCl p) (WithTop ℚ), _root_.ReciprocityTheory.ChartRestriction.G.DVR.ValOver ϖ (PadicAlgCl p) v ∧ _root_.GlobalTheory.ZH.NormVal (algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) ϖ)) v ∧ ∀ x : PadicAlgCl p, (0 ≤ v x ↔ ‖x‖ ≤ 1) ∧ (v x = 0 ↔ ‖x‖ = 1) := by
  intro p _ V _ _ _ _ hV ϖ hϖ
  set π : PadicAlgCl p :=
    algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) ϖ) with hπ
  have hinjV := IsFractionRing.injective V (FractionRing V)
  have hπne : π ≠ 0 := by
    rw [hπ, map_ne_zero]
    exact fun h => hϖ.ne_zero (hinjV (by rw [h, map_zero]))
  have hπle : ‖π‖ ≤ 1 := (hV _).2 ⟨ϖ, rfl⟩
  have hπlt : ‖π‖ < 1 := by
    refine lt_of_le_of_ne hπle fun h1 => hϖ.not_isUnit ?_
    have hle : ‖algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) ϖ)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv, ← hπ, h1, inv_one]
    obtain ⟨a, ha⟩ := (hV _).1 hle
    refine isUnit_iff_exists_inv.2 ⟨a, hinjV ?_⟩
    rw [map_mul, ha, map_one]
    exact mul_inv_cancel₀ fun h => hϖ.ne_zero (hinjV (by rw [h, map_zero]))
  have hb0 : 0 < ‖π‖ := norm_pos_iff.2 hπne
  have hle : ∀ s t : ℝ, ‖π‖ ^ s ≤ ‖π‖ ^ t ↔ t ≤ s := fun s t =>
    Real.rpow_le_rpow_left_iff_of_base_lt_one hb0 hπlt
  have hinj : ∀ s t : ℝ, ‖π‖ ^ s = ‖π‖ ^ t → s = t := fun s t h =>
    le_antisymm ((hle t s).1 h.ge) ((hle s t).1 h.le)
  obtain ⟨s, hs⟩ := exists_rat_norm_eq_rpow hπne
  have hs0 : (s : ℝ) ≠ 0 := by
    intro h0
    rw [h0, Real.rpow_zero] at hs
    exact hπlt.ne hs
  obtain ⟨r, hexp⟩ : ∃ r : PadicAlgCl p → ℚ, ∀ x, x ≠ 0 → ‖x‖ = ‖π‖ ^ (r x : ℝ) := by
    refine ⟨fun x => if h : x = 0 then 0 else (exists_rat_norm_eq_rpow h).choose / s, ?_⟩
    intro x hx
    simp only [dif_neg hx]
    rw [hs, ← Real.rpow_mul (Nat.cast_nonneg _)]
    push_cast
    rw [mul_div_cancel₀ _ hs0]
    exact (exists_rat_norm_eq_rpow hx).choose_spec
  have hr_one : r 1 = 0 := by
    have h := hexp 1 one_ne_zero
    rw [norm_one, ← Real.rpow_zero ‖π‖] at h
    exact_mod_cast (hinj _ _ h).symm
  have hr_mul : ∀ x y : PadicAlgCl p, x ≠ 0 → y ≠ 0 → r (x * y) = r x + r y := by
    intro x y hx hy
    have h := hexp (x * y) (mul_ne_zero hx hy)
    rw [norm_mul, hexp x hx, hexp y hy, ← Real.rpow_add hb0] at h
    exact_mod_cast (hinj _ _ h).symm
  have hr_add : ∀ x y : PadicAlgCl p, x ≠ 0 → y ≠ 0 → x + y ≠ 0 →
      min (r x) (r y) ≤ r (x + y) := by
    intro x y hx hy hxy
    have h := (PadicAlgCl.isNonarchimedean p) x y
    rw [hexp x hx, hexp y hy, hexp _ hxy] at h
    rcases le_total (r x) (r y) with hxy' | hxy'
    · rw [min_eq_left hxy']
      have hm : max (‖π‖ ^ (r x : ℝ)) (‖π‖ ^ (r y : ℝ)) = ‖π‖ ^ (r x : ℝ) :=
        max_eq_left ((hle _ _).2 (by exact_mod_cast hxy'))
      rw [hm, hle] at h
      exact_mod_cast h
    · rw [min_eq_right hxy']
      have hm : max (‖π‖ ^ (r x : ℝ)) (‖π‖ ^ (r y : ℝ)) = ‖π‖ ^ (r y : ℝ) :=
        max_eq_right ((hle _ _).2 (by exact_mod_cast hxy'))
      rw [hm, hle] at h
      exact_mod_cast h
  set w : PadicAlgCl p → WithTop ℚ := fun x => if x = 0 then ⊤ else (r x : WithTop ℚ) with hw
  have hw0 : w 0 = ⊤ := by simp [hw]
  have hw1 : w 1 = 0 := by simp [hw, hr_one]
  have hwadd : ∀ x y, min (w x) (w y) ≤ w (x + y) := by
    intro x y
    by_cases hx : x = 0
    · simp [hw, hx]
    by_cases hy : y = 0
    · simp [hw, hy]
    by_cases hxy : x + y = 0
    · simp [hw, hxy]
    simp only [hw, if_neg hx, if_neg hy, if_neg hxy]
    rw [← WithTop.coe_min, WithTop.coe_le_coe]
    exact hr_add x y hx hy hxy
  have hwmul : ∀ x y, w (x * y) = w x + w y := by
    intro x y
    by_cases hx : x = 0
    · simp [hw, hx]
    by_cases hy : y = 0
    · simp [hw, hy]
    simp only [hw, if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy)]
    rw [hr_mul x y hx hy, WithTop.coe_add]
  let v : AddValuation (PadicAlgCl p) (WithTop ℚ) := AddValuation.of w hw0 hw1 hwadd hwmul
  have hv : ∀ x, v x = w x := fun x => rfl
  have hunit : ∀ u : Vˣ,
      ‖algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) u)‖ = 1 := by
    intro u
    have h1 := (hV (algebraMap V (FractionRing V) u)).2 ⟨u, rfl⟩
    have h2 := (hV (algebraMap V (FractionRing V) (u⁻¹ : Vˣ))).2 ⟨_, rfl⟩
    have h3 : ‖algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) u)‖ *
        ‖algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) (u⁻¹ : Vˣ))‖
          = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
    nlinarith [norm_nonneg (algebraMap (FractionRing V) (PadicAlgCl p)
      (algebraMap V (FractionRing V) u)), norm_nonneg (algebraMap (FractionRing V) (PadicAlgCl p)
      (algebraMap V (FractionRing V) (u⁻¹ : Vˣ)))]
  refine ⟨v, ?_, ?_, ?_⟩
  · unfold _root_.ReciprocityTheory.ChartRestriction.G.DVR.ValOver
    intro c n hc
    unfold _root_.ReciprocityTheory.ChartRestriction.G.DVR.HasVal at hc
    obtain ⟨u, rfl⟩ := hc
    have hne : algebraMap (FractionRing V) (PadicAlgCl p)
        ((algebraMap V (FractionRing V)) ϖ ^ n * (algebraMap V (FractionRing V)) u) ≠ 0 := by
      rw [map_mul, map_zpow₀]
      refine mul_ne_zero (zpow_ne_zero _ hπne) ?_
      intro h
      have := hunit u
      rw [h, norm_zero] at this
      exact zero_ne_one this
    rw [hv]
    simp only [hw, if_neg hne]
    have h2 : ‖algebraMap (FractionRing V) (PadicAlgCl p)
        ((algebraMap V (FractionRing V)) ϖ ^ n * (algebraMap V (FractionRing V)) u)‖ =
          ‖π‖ ^ (n : ℝ) := by
      rw [map_mul, map_zpow₀, norm_mul, norm_zpow, hunit u, _root_.mul_one, ← hπ,
        Real.rpow_intCast]
    have := hinj _ _ ((hexp _ hne).symm.trans h2)
    rw [WithTop.coe_eq_coe]
    exact_mod_cast this
  · unfold _root_.GlobalTheory.ZH.NormVal
    refine ⟨hb0, hπlt, fun x q => ?_⟩
    by_cases hx : x = 0
    · subst hx
      rw [hv, hw0, norm_zero]
      constructor
      · intro h; exact absurd h WithTop.top_ne_coe
      · intro h; exact absurd h.symm (Real.rpow_pos_of_pos hb0 _).ne'
    rw [hv]
    simp only [hw, if_neg hx, WithTop.coe_eq_coe]
    rw [hexp x hx]
    constructor
    · rintro rfl; rfl
    · intro h; exact_mod_cast hinj _ _ h
  · intro x
    by_cases hx : x = 0
    · subst hx
      simp [hv, hw0]
    rw [hv]
    simp only [hw, if_neg hx]
    rw [hexp x hx]
    have h1 := hle (r x : ℝ) 0
    rw [Real.rpow_zero] at h1
    refine ⟨?_, ?_⟩
    · rw [h1, WithTop.coe_nonneg]
      exact_mod_cast Iff.rfl
    · rw [WithTop.coe_eq_zero]
      constructor
      · rintro h; rw [h]; simp
      · intro h
        have := hinj (r x : ℝ) 0 (by rw [Real.rpow_zero]; exact h)
        exact_mod_cast this

end GlobalTheory.NormValuation
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionPullbackMulGenerator
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib

theorem gm_chartPull_g {Y Y' Z : Scheme.{0}} {A' : LB Y'} {A : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h)
    (r : Z ⟶ Y') (z : Z) (i j : A'.ι) (hi : r z ∈ A'.U i) (hj : r z ∈ A'.U j) :
    gm r z (A'.U i ⊓ A'.U j) (A'.g i j) =
      gm (r ≫ h) z (A.U (a.idx i) ⊓ A.U (a.idx j)) (A.g (a.idx i) (a.idx j)) := by
  have le : A'.U i ⊓ A'.U j ≤ h ⁻¹ᵁ (A.U (a.idx i) ⊓ A.U (a.idx j)) := fun y hy => ⟨a.le i hy.1, a.le j hy.2⟩
  have e : A'.g i j = res le (pullU h _ (A.g (a.idx i) (a.idx j))) := unit_ext fun y hy =>
    (a.g y i j hy.1 hy.2).trans ((gm_res (𝟙 Y') y le hy _).trans
      ((gm_pull (𝟙 Y') h y _ (le hy) _).trans (by rw [Category.id_comp]))).symm
  have hm : r z ∈ A'.U i ⊓ A'.U j := ⟨hi, hj⟩
  rw [e]
  exact (gm_res r z le hm _).trans (gm_pull r h z _ (le hm) _)

theorem exists_red : ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (π : Φ.E.B.left ⟶ Y) (N : ℕ) (c : ChartPull Φ.N₀ (npw L N) π) (K K' : Type) [Fintype K] [Fintype K'] (ψ : K → (Φ.E.B.left ⟶ Y)) (ε : K → ℤ) (φt : K' → (Φ.G.left ⟶ Y)) (εt : K' → ℤ) (t : LB.Gen (LB.LinComb L φt εt)), t.IsGen → FormEq (Sum.elim (fun a => Φ.D.q.left ≫ ψ a) φt) (Sum.elim ε εt) (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => (N : ℤ)) → ∀ b : LB.Sec (LB.LinComb L ψ ε), ∃ φ : (Φ.H 1).Sec, UFib.Red Φ c t b φ := by
  intro k _ _ Φ Y L hL π N c K K' _ _ ψ ε φt εt t ht hF b
  obtain ⟨s, hs⟩ := exists_sec hL hF (pullMulSec b Φ.D.q.left t ht)
  have le : ∀ l : Φ.N₀.ι, Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l ≤
      LB.wchart L (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => c.idx l) :=
    fun l y hy => Set.mem_iInter.2 fun _ => c.le l hy
  refine ⟨⟨fun l => (Φ.G.left.presheaf.map (homOfLE (le l)).op).hom (s.f (fun _ => c.idx l)),
    fun l l' => fn_ext fun y hy => ?_⟩, fun Z r z J hJ l hl e => ?_⟩
  · refine ((gs_res (𝟙 _) y _ hy _).trans (gs_res (𝟙 _) y (le l) hy.1 _)).trans
      ((sec_trans s (𝟙 _) y (le l hy.1) (le l' hy.2)).trans (Eq.trans ?_ ((gs_mul (𝟙 _) y _ hy _ _).trans
        (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _)
          ((gs_res (𝟙 _) y _ hy _).trans (gs_res (𝟙 _) y (le l') hy.2 _)))).symm))
    refine congrArg₂ (· * ·) (congrArg Units.val ?_) rfl
    have e₁ := gm_chartPull_g c (𝟙 _ ≫ Φ.D.q.left) y l l' hy.1 hy.2
    have e₂ := gm_pull (𝟙 _) Φ.D.q.left y (Φ.N₀.U l ⊓ Φ.N₀.U l') ⟨hy.1, hy.2⟩ (Φ.N₀.g l l')
    refine Eq.trans ?_ (((congrArg (gm (𝟙 _) y _) (pow_one _)).trans e₂).trans e₁).symm
    refine Eq.trans ?_ (map_pow _ _ _).symm
    refine (Fintype.prod_unique _).trans ((zpow_natCast _ _).trans ?_)
    rw [Category.assoc]
    rfl
  · refine (gs_res r z (le l) hl _).trans ?_
    rw [← sval_pullMulSec b Φ.D.q.left t ht r z hJ, ← hs Z r z J hJ]
    exact (sval_of s r z J (fun _ => c.idx l) (fun _ => e)).symm

end GlobalTheory.ZH.UFib
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTwistedSectionThetaTranslateCoef
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

namespace GlobalTheory.PsiCoef

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem cT_zero (T : Over (Spec (CommRingCat.of R))) : cT D T 0 = 1 := by
  have h : D.c 0 = D.c 0 * D.c 0 := by
    have := D.c_add 0 0
    rwa [add_zero] at this
  have h1 : D.c 0 = 1 := left_eq_mul.1 h
  rw [cT, h1, MonObj.comp_one]

theorem comp_cT {T T' : Over (Spec (CommRingCat.of R))} (r : T ⟶ T') (α : D.X) : r ≫ cT D T' α = cT D T α := by
  rw [← Category.assoc, comp_toUnit]

theorem exists_untwist (χ : D.X)
    (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (hu : u.IsGen)
    (g : SecBT D (𝟙_ _) 1 χ) :
    ∃ g₀ : SecBT D (𝟙_ _) 1 0, ∀ (T : Over (Spec (CommRingCat.of R))) (y : T ⟶ D.P.A) (z : T.left) (J),
      Good D.P.L z J → sval g₀ (lift (toUnit T) (y * cT D T χ)).left z J =
        sval g (lift (toUnit T) y).left z J * ((val u (toUnit T).left z J * rigV D z J)⁻¹).val := by
  let Y : Over (Spec (CommRingCat.of R)) := 𝟙_ _ ⊗ D.P.A
  let τ : Y ⟶ Y := lift (toUnit Y) (snd _ _ * (cT D Y χ)⁻¹)
  have hF : FormEq
      (Sum.elim (fun k => τ.left ≫ famφT D (𝟙_ _) χ k)
        (fun k => (toUnit Y).left ≫ Sum.elim (fun _ : PUnit => (D.c χ).left) (fun _ : PUnit => eSec D.P.A) k))
      (Sum.elim (DegPre.famε 1) (fun k => -(Sum.elim (fun _ => -1) (fun _ => 1) k)))
      (famφT D (𝟙_ _) 0) (DegPre.famε 1) := by
    intro U _ h
    have e₀ : famφT D (𝟙_ _) 0 0 = famφT D (𝟙_ _) 0 1 := by
      change (snd _ _ : Y ⟶ D.P.A).left = (snd _ _ * cT D Y 0).left
      rw [cT_zero, _root_.mul_one]
    have e₀' : famφT D (𝟙_ _) 0 2 = famφT D (𝟙_ _) 0 3 := by
      change (cT D Y 0).left = (1 : Y ⟶ D.P.A).left
      rw [cT_zero]
    have e₁ : τ.left ≫ famφT D (𝟙_ _) χ 1 = famφT D (𝟙_ _) 0 1 := by
      change (τ ≫ (snd _ _ * cT D Y χ)).left = (snd _ _ * cT D Y 0).left
      rw [cT_zero, _root_.mul_one, MonObj.comp_mul, comp_cT, lift_snd, inv_mul_cancel_right]
    have e₂ : τ.left ≫ famφT D (𝟙_ _) χ 2 = famφT D (𝟙_ _) χ 2 := by
      change (τ ≫ cT D Y χ).left = (cT D Y χ).left
      rw [comp_cT]
    have e₃ : τ.left ≫ famφT D (𝟙_ _) χ 3 = famφT D (𝟙_ _) 0 3 := by
      change (τ ≫ (1 : Y ⟶ D.P.A)).left = (1 : Y ⟶ D.P.A).left
      rw [MonObj.comp_one]
    have e₄ : (toUnit Y).left ≫ (D.c χ).left = famφT D (𝟙_ _) χ 2 := rfl
    have e₅ : (toUnit Y).left ≫ eSec D.P.A = famφT D (𝟙_ _) 0 3 := rfl
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, Fin.prod_univ_four,
      e₀, e₀', e₁, e₂, e₃, e₄, e₅]
    simp [DegPre.famε, _root_.mul_assoc]
  obtain ⟨g₀, hg₀⟩ := exists_sec D.P.isLB hF (pullMulSec g τ.left
    (LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ u D.rig) (toUnit Y).left))
    (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hu D.rig_gen) _)))
  refine ⟨g₀, fun T y z J hJ => ?_⟩
  have e₂ : (lift (toUnit T) (y * cT D T χ)).left ≫ τ.left = (lift (toUnit T) y).left := by
    rw [← Over.comp_left]
    congr 1
    refine (comp_lift _ _ _).trans (congrArg₂ lift (toUnit_unique _ _) ?_)
    rw [MonObj.comp_mul, GrpObj.comp_inv, comp_cT, lift_snd, mul_inv_cancel_right]
  have e₃ : (lift (toUnit T) (y * cT D T χ)).left ≫ (toUnit Y).left = (toUnit T).left := by
    rw [← Over.comp_left]
    exact congrArg _ (toUnit_unique _ _)
  rw [hg₀ _ _ z J hJ, sval_pullMulSec _ _ _ _ _ _ hJ, e₂, val_inv, val_pull hJ, e₃, val_mul hJ]
  congr 5

theorem exists_coef : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (th : SecBT D (𝟙_ _) 1 0), (∀ g : SecBT D (𝟙_ _) 1 0, ∃ b : R, Mult D th g b) → ∀ (χ : D.X) (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))), u.IsGen → ∀ g : SecBT D (𝟙_ _) 1 χ, ∃ b : R, Coef D χ u th g b := by
  intro R _ _ D th hth χ u hu g
  obtain ⟨g₀, hg₀⟩ := exists_untwist D χ u hu g
  obtain ⟨b, hb⟩ := hth g₀
  exact ⟨b, fun T y z J hJ => by
    have e₁ : (lift (toUnit T) (y * cT D T χ)).left ≫ (𝟙_ _ ⊗ D.P.A).hom = T.hom := Over.w _
    have h := hb _ (lift (toUnit T) (y * cT D T χ)).left z J hJ
    rw [e₁, hg₀ T y z J hJ, Units.mul_inv_eq_iff_eq_mul] at h
    rw [h]
    ring⟩

end GlobalTheory.PsiCoef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisedModel
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UniformisedModel

theorem exists_finite_factor {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {p : ℕ} [Fact p.Prime]
    (y₀ : R →+* PadicAlgCl p) (Fs : Finset (PadicAlgCl p)) :
    ∃ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] K) (y : R →+* K),
      (∀ a, (y a : PadicAlgCl p) = y₀ a) ∧ ∀ x ∈ Fs, x ∈ K := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := ℤ) (A := R)
  let t : Finset (PadicAlgCl p) := s.image y₀ ∪ Fs
  let K := IntermediateField.adjoin ℚ_[p] (t : Set (PadicAlgCl p))
  have hK : FiniteDimensional ℚ_[p] K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hy : ∀ a, y₀ a ∈ K := fun a => by
    have ha : a ∈ Algebra.adjoin ℤ (s : Set R) := hs ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      exact IntermediateField.subset_adjoin _ _
        (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx)))
    | algebraMap n => rw [eq_intCast, map_intCast]; exact intCast_mem K n
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact K.add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact K.mul_mem ha hb
  exact ⟨K, hK, y₀.codRestrict K hy, fun _ => rfl, fun x hx =>
    IntermediateField.subset_adjoin _ _ (Finset.mem_coe.2 (Finset.mem_union_right _ hx))⟩

theorem spMap_spMap {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] (a : R →+* R₁) (b : R₁ →+* R₂) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem exists_polBaseChange (hB : PolBaseChangeSt) {S S' : Scheme.{0}} (f : S' ⟶ S) (P : PolAV S) :
    ∃ (P' : PolAV S') (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f φ ∧ LBIso P'.L (P.L.pull φ) := by
  obtain ⟨P', φ, hφ, -, hm, t, ht⟩ := hB S S' f P
  refine ⟨P', φ, ⟨hφ, fun T x y x₀ y₀ hx hy => ?_⟩, LBIso.symm ⟨t, ht⟩⟩
  rw [(Over.OverMorphism.ext hx : x₀ = toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = toBase hφ.w y), ← hm]
  rfl

theorem exists_isGrpPullback_jK {V K R : Type} [CommRing V] [IsDomain V] [CommRing K] [CommRing R] (a : V →+* K)
    (b : K →+* FractionRing V) (e : b.comp a = algebraMap V (FractionRing V)) (u : R →+* K)
    (G : Over (Sp V)) [GrpObj G] (A : Over (Sp R)) [GrpObj A] {φ : pullback G.hom (spMap a) ⟶ A.left}
    (hφ : IsGrpPullback ((Over.pullback (spMap a)).obj G) A (spMap u) φ) :
    ∃ ψ, IsGrpPullback ((Over.pullback (jK V)).obj G) A (spMap (b.comp u)) ψ := by
  obtain ⟨i, hi, -⟩ := grpPullback_iso (isGrpPullback_pullback G (jK V))
    (((isGrpPullback_pullback ((Over.pullback (spMap a)).obj G) (spMap b)).comp
      (isGrpPullback_pullback G _)).congr (by rw [spMap_spMap, e]) rfl)
  exact ⟨_, ((isGrpPullback_of_iso i).comp ((isGrpPullback_pullback _ (spMap b)).comp hφ)).congr
    (by rw [Category.id_comp, spMap_spMap]) rfl⟩

end GlobalTheory.UniformisedModel

namespace GlobalTheory


open UniformisedModel in
theorem exists_uniformised_model : GlobalTheory.Published.SemistableReductionSt → ThmUSt → PolBaseChangeSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (Fs : Finset (PadicAlgCl p)), ∃ u : ρ.UTest p y₀, ∀ x ∈ Fs, x ∈ Set.range (algebraMap (FractionRing u.V) (PadicAlgCl p)) := by
  intro hN hU hB o Ω _ _ _ _ S ρ p _ y₀ Fs
  haveI := ArithBase.ft (o := o) (Ω := Ω)
  haveI : Algebra.FiniteType o S.R := (Subalgebra.fg_iff_finiteType S.R).1 S.fg
  haveI : Algebra.FiniteType ℤ S.R := Algebra.FiniteType.trans (S := o) inferInstance inferInstance
  obtain ⟨K, _, y, hy, hFs⟩ := exists_finite_factor y₀ Fs
  obtain ⟨P, φ₀, hφ₀, -⟩ := exists_polBaseChange hB (spMap y) ρ.P
  obtain ⟨K', h, _, _, G, _, hG, hE, φ, hφ⟩ := exists_semiAbelian_model_split_specialFibre hN p K P
  let V := integralClosure ℤ_[p] K'
  let e : FractionRing V ≃ₐ[V] K' := FractionRing.algEquiv V K'
  let y' : S.R →+* K' := (IntermediateField.inclusion h).toRingHom.comp y
  let b : K' →+* FractionRing V := e.symm.toRingEquiv.toRingHom
  have hb : b.comp (algebraMap V K') = algebraMap V (FractionRing V) := RingHom.ext fun x => e.symm.commutes x
  obtain ⟨ψ, hψ⟩ := exists_isGrpPullback_jK (algebraMap V K') b hb y' G ρ.P.A
    ((hφ.comp hφ₀).congr (spMap_spMap _ _) rfl)
  obtain ⟨A, χ, hχ, hL⟩ := exists_polBaseChange hB (spMap (b.comp y')) ρ.P
  obtain ⟨gen, hgen, -⟩ := grpPullback_iso hψ hχ
  haveI : CharZero V := charZero_integralClosure_padicInt
  haveI := hG.comm
  have hc : IsAdicComplete (IsLocalRing.maximalIdeal V) V :=
    CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[p] V
  obtain ⟨D, U, -⟩ := hU V hc A G hG hE
    (SymBaseChange.hypS_baseChange _ _ ρ.P.A A.A _ χ ρ.P.L A.L ρ.P.isLB A.isLB hχ hL ρ.hypS) gen hgen
  let c : FractionRing V →+* PadicAlgCl p := (algebraMap K' (PadicAlgCl p)).comp e.toRingEquiv.toRingHom
  have hcb : ∀ x : K', c (b x) = x := fun x => congrArg Subtype.val (e.apply_symm_apply x)
  refine ⟨{ V := V, complete := hc, alg := c.toAlgebra, norm_le := fun x => ?_, yK := b.comp y'
            fac := RingHom.ext fun a => (hcb (y' a)).trans (hy a), A := A, φ := χ, cart := hχ, lb := hL, G := G
            semi := hG, D := D, U := U }, fun x hx => ⟨b ⟨x, h (hFs x hx)⟩, hcb _⟩⟩
  refine (mem_integralClosure_padicInt_iff K' (e x)).symm.trans ⟨fun hx => ⟨⟨e x, hx⟩, ?_⟩, ?_⟩
  · exact e.injective (e.commutes _)
  · rintro ⟨v, rfl⟩
    rw [e.commutes]
    exact v.2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FourthSideRespectsRigSymmetryCubeStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourthSide_respects_rig_symmetry_cube : ∀ (hG : GlobalFnsSt) (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V), I.map φ ≤ I' → ∀ (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (P' : CP G') (F : G'.left ⟶ G.left) (hF : F ≫ G.hom = G'.hom ≫ spMap φ) (wL : LB.Iso P'.L.L (U.P.L.L.pull F)), IsCPMap P' U.P (spMap φ) F hF wL → ∀ (β : D'.P.A.left ⟶ D.P.A.left) (hβ : β ≫ D.P.A.hom = D'.P.A.hom ≫ spMap φ) (v : LB.Iso D'.P.L (D.P.L.pull β)), IsCPMap (CP.ofDegPre hG D') (CP.ofDegPre hG D) (spMap φ) β hβ v → ∀ (e : ℕ) (g' : GtCoord I' D' e G') (h : (thickObj V I' e G').left ⟶ (thickObj R I e G).left), h ≫ (fstG I e G).left = (fstG I' e G').left ≫ F → g'.pG.left ≫ β = h ≫ (U.gt e).pG.left → ∀ w' : LB.Iso (P'.L.L.pull (fstG I' e G').left) (D'.P.L.pull g'.pG.left), (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj V I' e G').left) (z : Z) (jM : D.P.L.ι) (jM' : D'.P.L.ι) (jL : U.P.L.L.ι) (jL' : P'.L.L.ι), β (g'.pG.left (r z)) ∈ D.P.L.U jM → g'.pG.left (r z) ∈ D'.P.L.U jM' → F ((fstG I' e G').left (r z)) ∈ U.P.L.L.U jL → (fstG I' e G').left (r z) ∈ P'.L.L.U jL' → gw v (r ≫ g'.pG.left) z jM jM' * gw w' r z jM' (fun _ => jL') = gw (U.w e) (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ (fstG I' e G').left) z jL jL') → ∀ (T : Over (Spec (CommRingCat.of (V ⧸ I' ^ (e + 1))))) (z : T.left) (JG : (T.left ⟶ G'.left) → P'.L.L.ι) (J : (T.left ⟶ D'.P.A.left) → D'.P.L.ι), Good P'.L.L z JG → Good D'.P.L z J → ∀ W : (T ⟶ thickObj V I' e G') → (T.left.presheaf.stalk z)ˣ, (∀ x, W x = gw w' x.left z (J (x.left ≫ g'.pG.left)) (fun _ => JG (x.left ≫ (fstG I' e G').left))) → (val (L := D'.P.L) (φ := fun _ : PUnit => eSec D'.P.A) (ε := fun _ => 1) D'.rig (T.hom ≫ thick V I' e) z J = W 1 * val (L := P'.L.L) (φ := fun _ : PUnit => eSec G') (ε := fun _ => 1) P'.L.rig (T.hom ≫ thick V I' e) z JG) ∧ (∀ x : T ⟶ thickObj V I' e G', val D'.sym (x.left ≫ g'.pG.left) z J * W x = W x⁻¹ * val P'.sym (x.left ≫ (fstG I' e G').left) z JG) ∧ ∀ x y u : T ⟶ thickObj V I' e G', @id (T.left.presheaf.stalk z)ˣ (cubV D'.cub (T := (Over.map (thick V I' e)).obj T) z J ((Over.map (thick V I' e)).map x ≫ g'.pG) ((Over.map (thick V I' e)).map y ≫ g'.pG) ((Over.map (thick V I' e)).map u ≫ g'.pG)) * W (x * y) * W (x * u) * W (y * u) * W 1 = W (x * y * u) * W x * W y * W u * @id (T.left.presheaf.stalk z)ˣ (cubV P'.c (T := (Over.map (thick V I' e)).obj T) z JG ((Over.map (thick V I' e)).map x ≫ fstG I' e G') ((Over.map (thick V I' e)).map y ≫ fstG I' e G') ((Over.map (thick V I' e)).map u ≫ fstG I' e G')) := by
  first | exact @GlobalTheory.LN.FourthSide.fourth_side_vals | exact GlobalTheory.LN.FourthSide.fourth_side_vals | (intros; apply GlobalTheory.LN.FourthSide.fourth_side_vals <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelPointExtendsTorsionPointMulStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.modelPointExtendsTorsionPoint_mul : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (a b : S.Gam) (h h' : baseOver (Sp u.V) ⟶ u.G), GlobalTheory.UnitTheta.Extends u a h → GlobalTheory.UnitTheta.Extends u b h' → GlobalTheory.UnitTheta.Extends u (a + b) (h * h') := by
  first | exact @GlobalTheory.UnitTheta.extends_mul | exact GlobalTheory.UnitTheta.extends_mul | (intros; apply GlobalTheory.UnitTheta.extends_mul <;> assumption)
end

