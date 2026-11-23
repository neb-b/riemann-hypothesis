module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1948
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0084
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0100
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIdPowEqOneOfIsFiniteOfFlat
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FiniteFaithfullyFlatKer
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1961
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1868
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1966

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedMultiplicationPullbackFunction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.MulFrame

open GlobalTheory.ThetaFn GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter

theorem exists_two_mul_dot {g : ℕ} {a : Fin g → ℂ} (ha : Half a) (M : Fin g → ℤ) :
    ∃ n : ℤ, 2 * (a ⬝ᵥ cv M) = n := by
  have h : ∀ i, ∃ n : ℤ, 2 * a i = n := fun i => by
    rcases ha i with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  choose n hn using h
  refine ⟨∑ i, n i * M i, ?_⟩
  simp only [dotProduct, cv, Finset.mul_sum, ← _root_.mul_assoc, hn]
  push_cast
  rfl

theorem cv_nsmul {g : ℕ} (m : ℕ) (M : Fin g → ℤ) : cv (m • M) = (m : ℂ) • cv M := by
  funext i
  simp [cv]

theorem perV_nsmul {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (m : ℕ) (M N : Fin g → ℤ) :
    perV τ (m • M) (m • N) = (m : ℂ) • perV τ M N := by
  rw [perV, perV, cv_nsmul, cv_nsmul, Matrix.mulVec_smul, smul_add]

theorem autV_nsmul {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) {a b : Fin g → ℂ} (ha : Half a) (hb : Half b) (m : ℕ)
    (M N : Fin g → ℤ) (z : Fin g → ℂ) :
    autV τ a b (m • M) (m • N) ((m : ℂ) • z) = autV τ a b M N z ^ (m ^ 2) := by
  obtain ⟨p, hp⟩ := exists_two_mul_dot ha M
  obtain ⟨q, hq⟩ := exists_two_mul_dot hb N
  obtain ⟨k, hk⟩ := Int.even_mul_pred_self (m : ℤ)
  have hk' : (m : ℂ) * (m - 1) = k + k := by exact_mod_cast hk
  rw [autV, autV, ← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-(k * (p - q)), ?_⟩
  simp only [cv_nsmul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  push_cast
  rw [← hp, ← hq]
  linear_combination (-(2 * Real.pi * Complex.I * (a ⬝ᵥ cv M - b ⬝ᵥ cv N))) * hk'

section Origin

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g}
  {T : Over (Sp ℂ)} {p : 𝟙_ (Over (Sp ℂ)) ⟶ T}

theorem val_origin {rig : LB.Gen (L.pull (eSec A))} (hrig : u.IsRig rig) {m : T ⊗ A ⟶ A} {ε : Fin 2 → ℤ} {c : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ε)}
    (hn : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ α (ptSecT A 1).left) (rigT A L rig T c)) (i : L.ι)
    (hi : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ L.U i)
    (hj : ⊤ ≤ exAt u p 0 ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] (fun _ => i)) :
    valAt' (exAt u p 0) (LB.wchart L ![(snd T A).left, m.left] (fun _ => i)) (α.s fun _ => i).val = u.fr i 0 ^ c := by
  have he := comp_ptSecT u p (comp_one_eq_ex_zero u p)
  have h1 : ⊤ ≤ p.left ⁻¹ᵁ LB.wchart L (fun k => (ptSecT A (1 : T ⟶ A)).left ≫ ![(snd T A).left, m.left] k)
      (fun _ => i) := by
    rw [← he] at hj
    exact fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (hj hy) k
  have h2 := (mem_ptChart_iff (comp_one_eq_ex_zero u p) (fun _ => i)).2 hi
  have h12 := (le_preimage_inf p.left _ _).2 ⟨h1, h2⟩
  have e := congrArg (fun t => valAt' p.left _ (Units.val t))
    (hn (fun _ => i) (fun _ => i) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl))
  refine Eq.trans ?_ (((ThetaFn.valAt'_res p.left inf_le_left h12 _).symm.trans
    (e.trans (ThetaFn.valAt'_res p.left inf_le_right h12 _))).trans (valAt'_rigT p hrig c (fun _ => i) hi))
  rw [← he]
  exact (valAt'_appLE' p.left (ptSecT A (1 : T ⟶ A)).left _ h1 _).symm

end Origin

theorem fnT_iff {g : ℕ} {P : PolAV (Sp ℂ)} (u : HolUnif P.A P.L g) (k : ℕ)
    (t : LB.Sec (LPow P.A P.L (k : ℤ) (baseOver (Sp ℂ)))) (f : (Fin g → ℂ) → ℂ) :
    FnT u k t f ↔ IsFnAt u basePt (k : ℤ) t f := by
  constructor
  · intro h j z hj
    obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim _ _)⟩
    rw [zpow_natCast]
    exact h i z ((exAt_mem_chart_iff u basePt _ _ z).1 hj)
  · intro h i z hi
    rw [← zpow_natCast]
    exact h (fun _ => i) z ((exAt_mem_chart_iff u basePt _ _ z).2 hi)

end GlobalTheory.MBLow.Cl.MulFrame

namespace GlobalTheory.MBLow.Cl


open GlobalTheory.ThetaFn GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter MulFrame in
theorem exists_normalised_mulPull_fnT : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (W : Fin g → Fin g → ℂ), NF x hg u τ a b c W → ∀ (m : ℕ) (th : LB.Sec (LPow x.P.A x.P.L ((1 : ℕ) : ℤ) (baseOver (Sp ℂ)))) (f : (Fin g → ℂ) → ℂ), FnT u 1 th f → ∃ (α : LB.Gen (LB.LinComb x.P.L (K := Fin 2) ![(snd (baseOver (Sp ℂ)) x.P.A).left, (snd (baseOver (Sp ℂ)) x.P.A ^ m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])) (s₁ : LB.Sec (LPow x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp ℂ)))), α.IsGen ∧ LB.Gen.Corr x.P.L _ _ _ _ (LB.pullGen x.P.L _ _ α (ptSecT x.P.A 1).left) (rigT x.P.A x.P.L x.rig (baseOver (Sp ℂ)) (((m ^ 2 : ℕ) : ℤ) - 1)) ∧ IsTwistPull x.P.A x.P.L (mulT x.P.A (baseOver (Sp ℂ)) m) (snd (baseOver (Sp ℂ)) x.P.A ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α th s₁ ∧ FnT u (m ^ 2) s₁ fun z => f ((m : ℂ) • z) := by
  intro g x hg u τ a b c W hNF m th f hf
  have hfr := frame_eq_autV_mul g x hg u τ a b c W hNF
  obtain ⟨-, -, ha, hb, -, hΛ, hrig, -⟩ := hNF
  have hL := x.P.isLB
  have H := GlobalTheory.exists_mulPull_gen_over GlobalTheory.abelianSchemeLaws_all.1.mulPull x.P (baseOver (Sp ℂ)) m
  rw [← Nat.cast_pow] at H
  obtain ⟨α₀, hα₀⟩ := H
  obtain ⟨α, hα, hn⟩ := NormTheta.exists_normalised hL x.rig_gen m ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ)
    (((m ^ 2 : ℕ) : ℤ) - 1) rfl α₀ hα₀
  obtain ⟨s₁, hs₁⟩ := ThetaPtExist.exists_isTwistPull hL (mulT x.P.A (baseOver (Sp ℂ)) m)
    (snd (baseOver (Sp ℂ)) x.P.A ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α hα th
  refine ⟨α, s₁, hα, hn, hs₁, ?_⟩
  have hψ := exAt_mulT u basePt m
  have hΦ : ∀ z, exAt u basePt z ≫ (snd (baseOver (Sp ℂ)) x.P.A ^ m).left = (u.ex ((m : ℂ) • z)).left := fun z => by
    rw [← lift_snd (fst (baseOver (Sp ℂ)) x.P.A) (snd (baseOver (Sp ℂ)) x.P.A ^ m), Over.comp_left, ← Category.assoc]
    exact (congrArg (· ≫ _) (hψ z)).trans (exAt_snd _ _ _)
  obtain ⟨r, hr, hne, hrj⟩ := exists_fn_of_isGen (Φ := fun z => (m : ℂ) • z) hL (by fun_prop) hΦ hα
  haveI := u.discrete
  obtain ⟨-, -, k3⟩ := appellHumbert_trivial_of_nowhere_vanishing g u.Λ u.full 0 (fun _ => 1) r
    Matrix.isHermitian_zero (fun _ => norm_one) hr hne (fun l z => by
      obtain ⟨i, hi⟩ := exists_chart u valueRules hL z
      obtain ⟨i', hi'⟩ := exists_chart u valueRules hL ((m : ℂ) • z)
      have hj := (exAt_mem_pairChart_iff (hΦ z) ![i, i']).2 ⟨hi, hi'⟩
      have hj' := hj
      rw [← exAt_add_period u basePt z l l.2] at hj'
      rw [hrj _ _ hj', hrj _ _ hj, exAt_add_period u basePt z l l.2]
      obtain ⟨M, N, hl⟩ := (hΛ l).1 l.2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hermForm, Matrix.zero_mulVec, dotProduct_zero]
      rw [hfr M N i z hi, hfr (m • M) (m • N) i' _ hi', autV_nsmul τ ha hb, perV_nsmul, hl, smul_add]
      have n1 : autV τ a b M N z ≠ 0 := Complex.exp_ne_zero _
      simp only [_root_.zpow_neg, zpow_natCast, mul_pow, pow_one, mul_zero, add_zero, Complex.exp_zero]
      field_simp)
  have h0 : r 0 = 1 := by
    obtain ⟨i, hi⟩ := exists_chart u valueRules hL 0
    have hj := (exAt_mem_pairChart_iff (hΦ 0) (fun _ => i)).2 ⟨hi, by rw [smul_zero]; exact hi⟩
    have n := u.fr_ne i 0 hi
    rw [hrj _ _ hj, val_origin hrig hn i hi hj, smul_zero, ← zpow_add₀ n, ← zpow_add₀ n]
    simp
  have hc : IsPullConst u basePt (fun z => (m : ℂ) • z) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α 1 := fun j z hj => by
    have n := zpow_ne_zero ((m ^ 2 : ℕ) : ℤ) (u.fr_ne _ _ ((exAt_mem_pairChart_iff (hΦ z) j).1 hj).1)
    rw [← h0, ← k3 z, hrj j z hj, _root_.zpow_neg, inv_mul_cancel_right₀ n]
  have h2 := isFnAt_fnAt u basePt hL _ s₁
  have e := funext (hc.fn_eq hL hψ hs₁ ((fnT_iff u 1 th f).1 hf) h2)
  rw [fnT_iff]
  simpa only [e, _root_.one_mul] using h2

end GlobalTheory.MBLow.Cl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNowhereZeroSectionNearOfFlatTrivial
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FlatTrivSec

variable {X Y : Scheme.{0}}

theorem isUnit_gs_iff {Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (U : X.Opens) (h : f z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs f z U a) ↔ f z ∈ X.basicOpen a := by
  rw [gs_eq f z U h, ← Scheme.mem_basicOpen Z _ z h, ← Scheme.preimage_basicOpen]
  rfl

def pullSec (L : LB X) (θ : LB.Sec L) (F : Y ⟶ X) : LB.Sec (L.pull F) where
  f := fun I => (Y.presheaf.map (homOfLE (LB.wchart_le L (fun _ : PUnit => F) I PUnit.unit)).op).hom
    ((F.app _).hom (θ.f (I PUnit.unit)))
  compat := fun I J => fn_ext fun y hy => by
    have hI : F y ∈ L.U (I PUnit.unit) := mem_pull.1 hy.1
    have hJ : F y ∈ L.U (J PUnit.unit) := mem_pull.1 hy.2
    have hm : (𝟙 Y ≫ F) y ∈ L.U (I PUnit.unit) ⊓ L.U (J PUnit.unit) := ⟨hI, hJ⟩
    refine (gs_res (𝟙 Y) y _ hy _).trans ((gs_res (𝟙 Y) y _ hy.1 _).trans ((gs_pull (𝟙 Y) F y _ hI _).trans ?_))
    refine Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_pull_g L F (𝟙 Y) y I J hy.1 hy.2)))
      ((gs_res (𝟙 Y) y _ hy _).trans ((gs_res (𝟙 Y) y _ hy.2 _).trans (gs_pull (𝟙 Y) F y _ hJ _))))).symm
    exact (gs_res _ y inf_le_left hm _).symm.trans ((congrArg (gs _ y _) (θ.compat _ _)).trans
      ((gs_mul _ y _ hm _ _).trans (congrArg₂ (· * ·) (gs_unit _ y _ hm _) (gs_res _ y _ hm _))))

theorem gs_pullSec (L : LB X) (θ : LB.Sec L) (F : Y ⟶ X) (y : Y) (J : PUnit → L.ι) (hy : y ∈ (L.pull F).U J) :
    gs (𝟙 Y) y _ ((pullSec L θ F).f J) = gs F y (L.U (J PUnit.unit)) (θ.f (J PUnit.unit)) := by
  have hI : F y ∈ L.U (J PUnit.unit) := mem_pull.1 hy
  refine (gs_res (𝟙 Y) y _ hy _).trans ((gs_pull (𝟙 Y) F y _ hI _).trans ?_)
  rw [Category.id_comp]

theorem cst_bijective_of {C : Type} [CommRing C] (V : (Sp C).Opens)
    (hV : Function.Bijective ((Sp C).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom) :
    Function.Bijective (cst V.ι ⊤) := by
  have key : ∀ (V' : (Sp C).Opens) (h : V' ≤ ⊤), V' = V →
      Function.Bijective ((Sp C).presheaf.map (homOfLE h).op).hom := by
    rintro V' h rfl
    exact hV
  have h₁ : Function.Bijective V.ι.appTop.hom := by
    rw [Scheme.Opens.ι_appTop]
    exact key _ _ V.ι_image_top
  have h₀ : Function.Bijective (rs V.toScheme (le_top : (⊤ : V.toScheme.Opens) ≤ ⊤)) := by
    have : ⇑(rs V.toScheme (le_top : (⊤ : V.toScheme.Opens) ≤ ⊤)) = id := funext fun x => rs_self _ x
    rw [this]
    exact Function.bijective_id
  have h₃ : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of C)).inv
  exact h₀.comp (h₁.comp h₃)

theorem gs_cst_top {C : Type} [CommRing C] {Z : Scheme.{0}} (f : Z ⟶ Sp C) (z : Z) (x : C) :
    gs (𝟙 Z) z ⊤ (cst f ⊤ x) = gs f z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom x) := by
  refine (gs_res (𝟙 Z) z (U := f ⁻¹ᵁ ⊤) (V := ⊤) le_top trivial _).trans ((gs_pull (𝟙 Z) f z ⊤ trivial _).trans ?_)
  rw [Category.id_comp]

theorem exists_sec_near : ∀ (B C : Type) [CommRing B] [IsNoetherianRing B] [CommRing C] (g : B →+* C), g.Flat → ∀ (W : (Sp B).Opens), Function.Bijective ((Sp C).presheaf.map (homOfLE (le_top : spMap g ⁻¹ᵁ W ≤ ⊤)).op).hom → ∀ (M : LB W.toScheme), M.IsLB → Triv (M.pull (spMap g ∣_ W)) → ∀ y : Sp C, ∃ (s : M.Sec) (D : (Sp C).Opens), y ∈ D ∧ ∀ z : (spMap g ⁻¹ᵁ W).toScheme, (spMap g ⁻¹ᵁ W).ι z ∈ D → (spMap g ∣_ W) z ∈ Out.nonzeroLocus s := by
  intro B C _ _ _ g hg W hbij M hM hT y
  classical
  haveI : CompactSpace W.toScheme :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (W : Set (Sp B)))
  obtain ⟨t, ht⟩ := hT
  obtain ⟨n, c, u, hcomb⟩ := FlatSec.exists_comb_of_flat B C g hg W.toScheme W.ι _ (spMap g ∣_ W)
    (spMap g ⁻¹ᵁ W).ι (isPullback_morphismRestrict (spMap g) W) M hM (genSec t ht)
  choose a ha using fun i => DVR.ValuationAtUnit.exists_glue_ratio
    (DVR.linComb_cover M hM (fun _ : PUnit => spMap g ∣_ W) (fun _ => 1)) (pullSec M (u i) (spMap g ∣_ W)) t ht
  have hb := cst_bijective_of _ hbij
  choose e he using fun i => hb.2 (a i)
  have chart : ∀ z : (spMap g ⁻¹ᵁ W).toScheme, ∃ k, (spMap g ∣_ W) z ∈ M.U k := fun z => by
    have hz : (spMap g ∣_ W) z ∈ ⨆ k, M.U k := by rw [hM.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hz
  have key : ∀ (z : (spMap g ⁻¹ᵁ W).toScheme) (k : M.ι), (spMap g ∣_ W) z ∈ M.U k → ∀ i,
      gs (spMap g ∣_ W) z _ ((u i).f k) = gs (𝟙 _) z ⊤ (a i) * (gm (𝟙 _) z _ (t.s (fun _ => k))).val := by
    intro z k hk i
    have hz : z ∈ (M.pull (spMap g ∣_ W)).U (fun _ => k) := mem_pull.2 hk
    refine (gs_pullSec M (u i) _ z (fun _ => k) hz).symm.trans ?_
    refine (congrArg (gs (𝟙 _) z _) (ha i (fun _ => k))).trans ?_
    rw [gs_mul (𝟙 _) z _ hz, gs_res (𝟙 _) z _ hz, gs_unit (𝟙 _) z _ hz]
  have hsum : ∑ i, c i * e i = 1 := by
    apply hb.1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one]
    refine fn_ext fun z _ => ?_
    obtain ⟨k, hk⟩ := chart z
    have hz : z ∈ (M.pull (spMap g ∣_ W)).U (fun _ => k) := mem_pull.2 hk
    have h1 := hcomb z k hk
    simp only [key z k hk] at h1
    have h2 : gs (𝟙 _) z _ ((genSec t ht).f (fun _ => k)) = (gm (𝟙 _) z _ (t.s (fun _ => k))).val :=
      gs_unit (𝟙 _) z _ hz _
    rw [h2] at h1
    simp only [map_mul, he]
    rw [FlatSec.gs_sum (𝟙 _) z ⊤ trivial, gs_eq (𝟙 _) z ⊤ trivial 1, map_one, map_one]
    simp only [gs_mul (𝟙 _) z ⊤ trivial]
    have h3 : (∑ i, gs (𝟙 _) z ⊤ (cst (spMap g ⁻¹ᵁ W).ι ⊤ (c i)) * gs (𝟙 _) z ⊤ (a i)) *
        (gm (𝟙 _) z _ (t.s (fun _ => k))).val = 1 * (gm (𝟙 _) z _ (t.s (fun _ => k))).val := by
      rw [_root_.one_mul, Finset.sum_mul]
      refine Eq.trans (Finset.sum_congr rfl fun i _ => _root_.mul_assoc _ _ _) h1.symm
    exact (Units.mul_left_inj _).1 h3
  obtain ⟨i, hi⟩ : ∃ i, e i ∉ y.asIdeal := by
    by_contra hne
    push_neg at hne
    apply y.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hsum]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hne i)
  refine ⟨u i, PrimeSpectrum.basicOpen (e i), hi, fun z hz => ?_⟩
  obtain ⟨k, hk⟩ := chart z
  have hu1 : IsUnit (gs (𝟙 _) z ⊤ (a i)) := by
    rw [← he i, gs_cst_top, isUnit_gs_iff _ z ⊤ trivial, basicOpen_eq_of_affine]
    exact hz
  have hu2 : IsUnit (gs (spMap g ∣_ W) z _ ((u i).f k)) := by
    rw [key z k hk i]
    exact hu1.mul (Units.isUnit _)
  rw [isUnit_gs_iff _ z _ hk] at hu2
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hu2⟩

end GlobalTheory.FlatTrivSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientAbelianSchemeFiniteFlatSubgroup
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbQuotientAny

open GlobalTheory.AffineQuotient GlobalTheory.AbelianQuotient


set_option backward.isDefEq.respectTransparency false in
theorem exists_quotient_abelianScheme :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (H : Over (Sp R)) [GrpObj H] (i : H ⟶ A), IsAbelianScheme A → IsMonHom i → Mono i → IsFinite H.hom → Flat H.hom → ∃ (B : Over (Sp R)) (_ : GrpObj B) (q : A ⟶ B) (π : B ⟶ A), IsAbelianScheme B ∧ IsMonHom q ∧ IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧ IsFinite π.left ∧ IsPullback ((fst H A ≫ i) * snd H A) (snd H A) q q := by
  intro R _ _ A _ H _ i hA _ _ _ _
  have := hA.comm
  have := hA.proper
  have := hA.smooth
  have := hA.geomConnected
  have : IsCommMonObj H := ⟨by
    rw [← cancel_mono i, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
      IsCommMonObj.mul_comm]⟩
  obtain ⟨N, hN, hH⟩ := GlobalTheory.FiniteFlatKilled.main R H ‹_› ‹_›
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have := (GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_mulA _ A hA N hN).1
  obtain ⟨Λ, _, _, _, _, e, _⟩ := exists_hopfAlgebra R H
  have hi : i ^ N = 1 := by
    rw [← Category.id_comp i, ← MonObj.pow_comp, hH, MonObj.one_comp]
  obtain ⟨Q, q, π, h₁, h₂, h₃, h₄, h₅⟩ := exists_quotient_hopf
    (GlobalTheory.HopfQuot.affine_quotient GlobalTheory.exists_basis_mem_of_span_eq_top_of_semilocal) (e.hom ≫ i)
    (mulA A N) (by
    rw [mulA, comp_pow, comp_pow, Category.comp_id, Category.comp_id, mul_pow, ← comp_pow,
      ← comp_pow i, hi, comp_one, comp_one, _root_.one_mul])
  have hq : IsPullback ((fst H A ≫ i) * snd H A) (snd H A) q q := by
    refine h₅.of_iso (whiskerRightIso e A) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
      <;> simp [comp_mul]
  obtain ⟨inst, hcomm, hhom, -⟩ := exists_grpObj i q hq
  refine ⟨Q, inst, q, π, ?_, hhom, h₂, h₃, h₄, h₁, hq⟩
  have : IsSeparated Q.hom := by rw [← Over.w π]; infer_instance
  have : LocallyOfFiniteType Q.hom := by rw [← Over.w π]; infer_instance
  have hw : q.left ≫ Q.hom = A.hom := Over.w q
  have := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom
    hA.smooth hA.geomConnected
  have : Flat (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : UniversallyClosed (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : GeometricallyReduced (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : GeometricallyConnected (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have := flat_of_comp_of_flat_of_surjective q.left Q.hom
  have := UniversallyClosed.of_comp_surjective q.left Q.hom
  have := geometricallyReduced_of_comp q.left Q.hom
  have : LocallyOfFinitePresentation Q.hom := inferInstance
  exact ⟨hcomm, smooth_of_grpObj_of_flat Q, ⟨⟩, geometricallyConnected_of_comp q.left Q.hom⟩

end GlobalTheory.AbQuotientAny
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScalarCuspFormIndefiniteUnitaryShimura
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.ScalarCuspTwist

theorem exists_scalar_cusp_indefinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → 1 ≤ Dw.p → 1 ≤ Dw.q → ¬ (∃ m : ℕ, 1 ≤ m ∧ m ^ 4 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.f E ∧ (ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 2 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ∧ 16 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ∧ (Dw.p ≤ m ∨ Dw.q ≤ m)) → ∀ (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (Z : Comp Xo c), ∃ n₀ : ℕ, 0 < n₀ ∧ Even n₀ ∧ ∃ f₀ ∈ cusp Xo c U 0 n₀, ∃ z ∈ framesOn (U σ) Z, rdU (U σ) f₀ z.1 z.2 ≠ 0 := by
  intro E _ _ _ H Dw l Xo c r U x hL hp hq _ σ hσ Z
  exact exists_scalar_of_models (_root_.GlobalTheory.ScalarPoin.exists_cusp_ne_some E r) hL hp hq hσ Z

end GlobalTheory.ScalarCuspTwist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTransportAlongGeneratingIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.SecTransport

theorem main : ∀ {X : Scheme.{0}} {M L : LB X} (e : LB.Iso M L), e.IsGen → M.IsLB → L.IsLB →
    ∀ σ : L.Sec, ∃ σ' : M.Sec, GlobalTheory.Cartier.SecMaps e σ' σ ∧ Out.nonzeroLocus σ ≤ Out.nonzeroLocus σ' := by
  intro X M L e he hM hL σ
  refine ⟨DVR.secOfIso (u := e) σ he hM hL, ?_, DVR.nonzeroLocus_secOfIso e σ he hM hL⟩
  intro p
  apply GlobalTheory.Cartier.ext_germ
  intro x hx
  set σ' := DVR.secOfIso (u := e) σ he hM hL
  have hx' : x ∈ M.U p.2 ⊓ L.U p.1 := ⟨hx.2, hx.1⟩
  have h1 : (X.presheaf.germ _ x hx).hom (resG X (inf_le_left : L.U p.1 ⊓ M.U p.2 ≤ L.U p.1) (σ.f p.1)) =
      (X.presheaf.germ _ x hx.1).hom (σ.f p.1) := GlobalTheory.Cartier.germ_resG _ x hx _
  have h2 : (X.presheaf.germ _ x hx).hom (resG X (inf_le_right : L.U p.1 ⊓ M.U p.2 ≤ M.U p.2) (σ'.f p.2)) =
      (X.presheaf.germ _ x hx.2).hom (σ'.f p.2) := GlobalTheory.Cartier.germ_resG _ x hx _
  have h3 : (X.presheaf.germ _ x hx.2).hom (σ'.f p.2) =
      (X.presheaf.germ _ x hx').hom (DVR.isoCand e σ p.2 p.1) := by
    rw [← DVR.secOfIso_spec (u := e) σ he hM hL p.2 p.1]
    exact (GlobalTheory.Cartier.germ_resG (inf_le_left : M.U p.2 ⊓ L.U p.1 ≤ M.U p.2) x hx' _).symm
  have h4 : (X.presheaf.germ _ x hx').hom (DVR.isoCand e σ p.2 p.1) =
      (X.presheaf.germ _ x hx').hom (((res (DVR.divLe p.2 p.1) (e.s p))⁻¹ : Γ(X, M.U p.2 ⊓ L.U p.1)ˣ) : Γ(X, M.U p.2 ⊓ L.U p.1)) *
        (X.presheaf.germ _ x hx.1).hom (σ.f p.1) := by
    unfold DVR.isoCand
    rw [map_mul]
    congr 1
    exact GlobalTheory.Cartier.germ_resG (inf_le_right : M.U p.2 ⊓ L.U p.1 ≤ L.U p.1) x hx' _
  have h5 : (X.presheaf.germ _ x hx').hom (((res (DVR.divLe p.2 p.1) (e.s p)) : Γ(X, M.U p.2 ⊓ L.U p.1)ˣ) : Γ(X, M.U p.2 ⊓ L.U p.1)) =
      (X.presheaf.germ _ x hx).hom ((@id (Γ(X, L.U p.1 ⊓ M.U p.2)ˣ) (e.s p) : Γ(X, L.U p.1 ⊓ M.U p.2))) :=
    GlobalTheory.Cartier.germ_resG (DVR.divLe p.2 p.1) x hx' _
  have h6 : (X.presheaf.germ _ x hx').hom (((res (DVR.divLe p.2 p.1) (e.s p)) : Γ(X, M.U p.2 ⊓ L.U p.1)ˣ) : Γ(X, M.U p.2 ⊓ L.U p.1)) *
      (X.presheaf.germ _ x hx').hom (((res (DVR.divLe p.2 p.1) (e.s p))⁻¹ : Γ(X, M.U p.2 ⊓ L.U p.1)ˣ) : Γ(X, M.U p.2 ⊓ L.U p.1)) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [map_mul, h1, h2, h3, h4, ← h5, ← _root_.mul_assoc, h6, _root_.one_mul]

end GlobalTheory.SecTransport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparatingSectionOfIsolatedNonKltPointStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_separatingSection_of_isolatedNonKltPoint : GlobalTheory.Published.NadelVanishingPair → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (M : LB X) (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (D : X → ℚ) (ρ d : ℚ) (x x' : X), M.IsLB → IsEffQDiv Δ → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![M] : ℚ) = interNumRed ℂ C ![toLB G] / m + ρ * interNumRed ℂ C ![N]) → QNum p N d D → d < ρ → IsClosed ({x} : Set X) → x ≠ x' → LcCut p n (Δ + D) x 0 → ¬ KltAt p n (Δ + D) x' → ∃ s : M.Sec, x ∈ nonzeroLocus s ∧ x' ∉ nonzeroLocus s := by
  first | exact @GlobalTheory.PairStep.exists_sec_sep_of_lcCut | exact GlobalTheory.PairStep.exists_sec_sep_of_lcCut | (intros; apply GlobalTheory.PairStep.exists_sec_sep_of_lcCut <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueCmOrderActionMatrixOnAffineOpen
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ActMatrix

open MonoidalCategory CartesianMonoidalCategory MonObj

theorem isTanAtG_act {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] (x0 : Sp S ⟶ X) (a : 𝓞 E)
    {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x0 v) : IsTanAtG t x0 (v ≫ (t.act.act a).left) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, Over.w]; exact hv.1
  · rw [← Category.assoc, hv.2, ← Over.comp_left]
    congr 1
    haveI := t.act.hom a
    rw [Hom.one_def, Category.assoc, IsMonHom.one_hom]

theorem actMatrix : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (GlobalTheory.LogKS.chart U) (v i)) → (∀ w, IsTanAtG t (GlobalTheory.LogKS.chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (GlobalTheory.LogKS.chart U) v cf w) → ∃ A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(X, U.1), ∀ a i, IsCombAtG t (GlobalTheory.LogKS.chart U) v (A a i) (v i ≫ (t.act.act a).left) := by
  intro E _ _ _ H X t U n v hv hb
  refine ⟨fun a i => Classical.choose (hb _ (isTanAtG_act t _ a (hv i))), fun a i => ?_⟩
  exact (Classical.choose_spec (hb _ (isTanAtG_act t _ a (hv i)))).1

end GlobalTheory.ActMatrix
end

