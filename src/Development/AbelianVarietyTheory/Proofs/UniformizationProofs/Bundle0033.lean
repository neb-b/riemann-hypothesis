module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ThetaMove
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PowEqOneOfPush
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGrpPullbackThick
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SymmetricFramePhiPowOrderEqId
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMoveMap
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaSpecialise

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange

section Algebra

variable {S F F' N V V' : Type} [CommRing S] [IsDomain S] [ValuationRing S] [Field F] [Field F']
  [AddCommGroup N] [Module S N] [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F' V']

theorem exists_ratio {fS : S →+* F} {π : S →+* F'} (hf : Function.Injective fS) (mv : N →ₛₗ[fS] V) (mv' : N →ₛₗ[π] V')
    (ind : ∀ (n : ℕ) (c : Fin n → F), (∀ a : Fin n → S, ∑ i, fS (a i) * c i = 0 → ∀ i, a i = 0) →
      ∀ a : Fin n → N, ∑ i, c i • mv (a i) = 0 → ∀ i, a i = 0)
    {I : Type} (a b : I → N) (l : F) (h : ∀ i, mv (a i) = l • mv (b i)) (ha : ∃ i, mv' (a i) ≠ 0)
    (hb : ∃ i, mv' (b i) ≠ 0) : ∃ l' : F', l' ≠ 0 ∧ ∀ i, mv' (a i) = l' • mv' (b i) := by
  have inj : ∀ x y, mv x = mv y → x = y := fun x y e => sub_eq_zero.1 (ind 1 (fun _ => 1) (fun a ha i => by
    rw [Fin.sum_univ_one, _root_.mul_one] at ha
    rw [Subsingleton.elim i 0]; exact hf (ha.trans (map_zero _).symm)) (fun _ => x - y)
    (by rw [Fin.sum_univ_one, one_smul, map_sub, e, sub_self]) 0)
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  by_cases H : ∀ a : Fin 2 → S, ∑ i, fS (a i) * ![1, -l] i = 0 → ∀ i, a i = 0
  · refine absurd ?_ hi
    have e : a i = 0 := ind 2 _ H ![a i, b i] (by simp [Fin.sum_univ_two, h]) 0
    rw [e, map_zero]
  · push_neg at H
    obtain ⟨u, hu, m, hm⟩ := H
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, _root_.mul_one, mul_neg] at hu
    have inj' : ∀ x, fS x = 0 → x = 0 := fun x e => hf (e.trans (map_zero _).symm)
    have h1 : u 1 ≠ 0 := fun e => by
      rw [e, map_zero, zero_mul, neg_zero, add_zero] at hu
      fin_cases m
      exacts [hm (inj' _ hu), hm e]
    have h1' : fS (u 1) ≠ 0 := fun e => h1 (inj' _ e)
    obtain ⟨t, ht | ht⟩ := ValuationRing.cond (u 0) (u 1)
    · have h0 : fS (u 0) ≠ 0 := fun e => h1' (by rw [← ht, map_mul, e, zero_mul])
      have e : fS t * l = 1 := mul_left_cancel₀ h0 (by rw [← ht, map_mul] at hu; linear_combination -hu)
      have k : ∀ i, mv' (b i) = π t • mv' (a i) := fun i => by
        rw [← map_smulₛₗ]
        exact congrArg mv' (inj _ _ (by rw [map_smulₛₗ, h, smul_smul, e, one_smul]))
      have p : π t ≠ 0 := fun e => hj (by rw [k, e, zero_smul])
      exact ⟨(π t)⁻¹, inv_ne_zero p, fun i => by rw [k, smul_smul, inv_mul_cancel₀ p, one_smul]⟩
    · have e : fS t = l := mul_left_cancel₀ h1' (by rw [← ht, map_mul] at hu; linear_combination hu)
      have k : ∀ i, mv' (a i) = π t • mv' (b i) := fun i => by
        rw [← map_smulₛₗ]
        exact congrArg mv' (inj _ _ (by rw [map_smulₛₗ, h, e]))
      exact ⟨π t, fun e => hi (by rw [k, e, zero_smul]), k⟩

end Algebra

section Flat

variable {S F : Type} [CommRing S] [CommRing F] {fS : S →+* F} {X Y Y' : Scheme.{0}}
  {π : Y ⟶ Spec (CommRingCat.of S)} {π' : Y' ⟶ Spec (CommRingCat.of F)} {p : Y' ⟶ Y}
  (H : IsPullback p π' π (Spec.map (CommRingCat.ofHom fS))) [Flat π]

theorem fn_indep {U : Y.Opens} (hU : IsAffineOpen U) {n : ℕ} (c : Fin n → F)
    (hc : ∀ a : Fin n → S, ∑ i, fS (a i) * c i = 0 → ∀ i, a i = 0) (a : Fin n → FnOver π U)
    (h : ∑ i, c i • pullFn H.w (le_refl (p ⁻¹ᵁ U)) (a i) = 0) (i : Fin n) : a i = 0 := by
  let : Algebra S F := fS.toAlgebra
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := p ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  have po' : IsPushout (CommRingCat.ofHom (constHom π U)) (CommRingCat.ofHom fS) (p.app U)
      (CommRingCat.ofHom (constHom π' (p ⁻¹ᵁ U))) := by
    refine po.of_iso (Scheme.ΓSpecIso (.of S)) (Iso.refl _) (Scheme.ΓSpecIso (.of F)) (Iso.refl _) ?_ ?_ ?_ ?_
    · ext x; simp [constHom, Scheme.Hom.appLE]; rfl
    · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    · simp [Scheme.Hom.app_eq_appLE]
    · ext x; simp [constHom, Scheme.Hom.appLE]; rfl
  let : Algebra (FnOver π U) (FnOver π' (p ⁻¹ᵁ U)) := (p.app U).hom.toAlgebra
  let : Algebra S (FnOver π' (p ⁻¹ᵁ U)) := ((constHom π' (p ⁻¹ᵁ U)).comp fS).toAlgebra
  have : IsScalarTower S F (FnOver π' (p ⁻¹ᵁ U)) := .of_algebraMap_eq fun r ↦ rfl
  have : IsScalarTower S (FnOver π U) (FnOver π' (p ⁻¹ᵁ U)) :=
    .of_algebraMap_eq fun r ↦ (congrArg (fun q => q.hom r) po'.w).symm
  have hpo : Algebra.IsPushout S (FnOver π U) F (FnOver π' (p ⁻¹ᵁ U)) :=
    CommRingCat.isPushout_iff_isPushout.mp po'
  have fl : Module.Flat S (FnOver π U) := by
    have f₁ : RingHom.Flat (π.appLE ⊤ U le_top).hom :=
      HasRingHomProperty.appLE (P := @Flat) π inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
    have f₂ : RingHom.Flat (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom :=
      RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
    exact f₂.comp f₁
  have li : LinearIndependent S c := Fintype.linearIndependent_iff.2 fun g hg => hc g hg
  have li' := Fintype.linearIndependent_iff.1 (Module.Flat.linearIndependent_one_tmul (S := FnOver π U) li)
  refine li' a (hpo.out.equiv.injective ?_) i
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_zero, ← h, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, hpo.out.equiv_tmul, one_smul, Algebra.smul_def, Algebra.smul_def, mul_comm]
  congr 1
  show _ = (Y'.presheaf.map (𝟙 _)).hom _
  rw [CategoryTheory.Functor.map_id]; rfl

theorem sec_indep {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} (ε : K → ℤ) {φ' : K → (Y' ⟶ X)}
    (hφ : ∀ k, φ' k = p ≫ φ k) {n : ℕ} (c : Fin n → F)
    (hc : ∀ a : Fin n → S, ∑ i, fS (a i) * c i = 0 → ∀ i, a i = 0) (a : Fin n → SecOver π (LB.LinComb L φ ε))
    (h : ∑ i, c i • pullOver L ε H.w hφ (a i) = 0) (i : Fin n) : a i = 0 := by
  refine SecOver.ext _ _ fun (j : K → L.ι) => fn_ext fun y hy => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hle⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy (LB.wchart L φ j).isOpen
  have hle : U ≤ LB.wchart L φ j := hle
  have hle' : p ⁻¹ᵁ U ≤ LB.wchart L φ' j := fun z hz => (wchart_eq hφ j).ge (hle hz)
  have e := fn_indep H hU c hc (fun i => resFn π hle (chartLin π (LB.LinComb L φ ε) j (a i))) (by
    have := congrArg (resFn π' hle' ∘ₗ chartLin π' (LB.LinComb L φ' ε) j) h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, map_sum] at this
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) this
    rw [map_smul]
    refine congrArg (c i • ·) (fn_ext fun z hz => ?_)
    exact ((gs_pullFn H.w _ _ _ z hz).trans (gs_res (𝟙 Y' ≫ p) z hle hz _)).trans
      ((gs_res _ z hle' hz _).trans (gs_pullFn H.w _ _ _ z (hle' hz))).symm) i
  exact ((gs_res (𝟙 Y) y hle hyU _).symm.trans ((congrArg (gs (𝟙 Y) y U) e).trans (gs_zero' _ y U hyU))).trans
    (gs_zero' _ y _ hy).symm

end Flat

section Move

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {Φ : X' ⟶ X} {K : Type} [Fintype K]

def PSec (w : LB.Iso L' (L.pull Φ)) (φ' : K → (Y' ⟶ X')) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y)
    (s' : LB.Sec (LB.LinComb L' φ' ε)) (s : LB.Sec (LB.LinComb L φ ε)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι),
    (∀ κ, Φ (φ' κ (r z)) ∈ L.U (p κ)) → (∀ κ, φ' κ (r z) ∈ L'.U (q κ)) →
    gs (r ≫ h) z (LB.wchart L φ p) (s.f p) =
      (∏ κ, gw w (r ≫ φ' κ) z (p κ) (q κ) ^ ε κ).val * gs r z (LB.wchart L' φ' q) (s'.f q)

variable {w : LB.Iso L' (L.pull Φ)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y}
  {S F : Type} [CommRing S] [CommRing F] {fS : S →+* F}
  {π : Y ⟶ Spec (CommRingCat.of S)} {π' : Y' ⟶ Spec (CommRingCat.of F)}

theorem exists_moveMap (hL : L.IsLB) (hL' : L'.IsLB) (hw : w.IsGen) (hc : ∀ κ, φ' κ ≫ Φ = h ≫ φ κ)
    (hp : h ≫ π = π' ≫ Spec.map (CommRingCat.ofHom fS)) :
    ∃ mv : SecOver π (LB.LinComb L φ ε) →ₛₗ[fS] SecOver π' (LB.LinComb L' φ' ε),
      ∀ s s', PSec w φ' φ ε h s' s ↔ mv s = s' := by
  have ex := SecPull.existsUnique_secPull _ _ _ _ _ _ _ hL hL' w hw K φ' φ ε h hc
  choose mv hmv using fun s : SecOver π (LB.LinComb L φ ε) => (ex s).exists
  have m : ∀ {Z : Scheme.{0}} {r : Z ⟶ Y'} {z : Z} {p : K → L.ι}, (∀ κ, Φ (φ' κ (r z)) ∈ L.U (p κ)) →
      (r ≫ h) z ∈ LB.wchart L φ p := fun hp => SecPull.mem_wchart_comp hc (Set.mem_iInter.2 hp)
  refine ⟨{ toFun := mv
            map_add' := fun a b => (ex _).unique (hmv _) fun Z r z p q hp hq => ?_
            map_smul' := fun c a => (ex _).unique (hmv _) fun Z r z p q hp₁ hq => ?_ },
    fun s s' => ⟨fun H => (ex s).unique (hmv s) H, fun H => H ▸ hmv s⟩⟩
  · refine (gs_add _ z _ (m hp) _ _).trans (Eq.trans ?_ (congrArg _ (gs_add r z _ (mem_wchart.2 hq) _ _)).symm)
    rw [mul_add]
    exact congrArg₂ (· + ·) (hmv a Z r z p q hp hq) (hmv b Z r z p q hp hq)
  · refine (gs_smul π _ z _ (m hp₁) _ _).trans
      (Eq.trans ?_ (congrArg _ (gs_smul π' r z _ (mem_wchart.2 hq) _ _)).symm)
    rw [mul_left_comm, Category.assoc, hp, ← Category.assoc, constVal_specMap]
    exact congrArg _ (hmv a Z r z p q hp₁ hq)

theorem move_indep (hL : L.IsLB) (hL' : L'.IsLB) (hc : ∀ κ, φ' κ ≫ Φ = h ≫ φ κ)
    (H : IsPullback h π' π (Spec.map (CommRingCat.ofHom fS))) [Flat π]
    (mv : SecOver π (LB.LinComb L φ ε) → SecOver π' (LB.LinComb L' φ' ε)) (hmv : ∀ s, PSec w φ' φ ε h (mv s) s)
    (n : ℕ) (c : Fin n → F) (hi : ∀ a : Fin n → S, ∑ i, fS (a i) * c i = 0 → ∀ i, a i = 0)
    (a : Fin n → SecOver π (LB.LinComb L φ ε)) (e : ∑ i, c i • mv (a i) = 0) (i : Fin n) : a i = 0 := by
  refine sec_indep H ε (φ' := fun κ => h ≫ φ κ) (fun _ => rfl) c hi a (sec_ext' hL fun y J hJ => ?_) i
  choose J' hJ' using fun ψ : Y' ⟶ X' => exists_chart hL' (ψ y)
  have hJ' : Good L' y J' := hJ'
  have e' := congrArg (fun t => sval t (𝟙 _) y J') e
  beta_reduce at e'
  rw [sval_sum' hJ', sval_zero' hJ'] at e'
  rw [sval_sum' hJ, sval_zero' hJ, ← mul_zero (∏ κ, ExpTrans.om w y J J' (𝟙 _ ≫ φ' κ) ^ ε κ).val, ← e',
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sval_smul' hJ, sval_smul' hJ', sval_pullOver _ _ _ _ hJ,
    ExpTrans.sec_val w φ' φ ε h hc _ _ (𝟙 _) y (hmv (a i) _ (𝟙 _) y) hJ hJ', mul_left_comm]

end Move

end GlobalTheory.ThetaSpecialise
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsThetaPow
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaPow

theorem prod_fam_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) {U : Type} [CommGroup U]
    (h : ((DegPre.BF D F).left ⟶ D.P.A.left) → U) :
    ∏ i, h (DegPre.famφ D F 0 i) ^ DegPre.famε k i = h (DegPre.prB D F).left ^ k := by
  have hmul : ∀ {T : Over (Spec (CommRingCat.of R))} (a b : T ⟶ D.P.A), padd D.P.A a b = a * b := by
    intro T a b
    unfold padd
    rfl
  have hc0 : D.c 0 = 1 := by
    have h2 := D.c_add 0 0
    rw [add_zero, hmul] at h2
    exact mul_eq_left.mp h2.symm
  have h1 : toUnit (DegPre.BF D F) ≫ D.c 0 = toUnit (DegPre.BF D F) ≫ η[D.P.A] := by
    rw [hc0]
    rfl
  have h3 : padd D.P.A (DegPre.prB D F) (toUnit (DegPre.BF D F) ≫ η[D.P.A]) = DegPre.prB D F := by
    rw [hmul]
    exact mul_one _
  have hφ : DegPre.famφ D F 0 = ![(DegPre.prB D F).left, (DegPre.prB D F).left,
      (toUnit (DegPre.BF D F) ≫ η[D.P.A]).left, (toUnit (DegPre.BF D F) ≫ η[D.P.A]).left] := by
    unfold DegPre.famφ
    rw [h1, h3]
  have hε : DegPre.famε k = ![(k : ℤ) - 1, 1, -1, 1] := rfl
  rw [Fin.prod_univ_four, hφ, hε]
  show h (DegPre.prB D F).left ^ ((k : ℤ) - 1) * h (DegPre.prB D F).left ^ (1 : ℤ) *
      h (toUnit (DegPre.BF D F) ≫ η[D.P.A]).left ^ (-1 : ℤ) * h (toUnit (DegPre.BF D F) ≫ η[D.P.A]).left ^ (1 : ℤ) =
      h (DegPre.prB D F).left ^ k
  simp only [zpow_neg, zpow_one]
  rw [_root_.inv_mul_cancel_right, ← zpow_add_one, sub_add_cancel, zpow_natCast]

theorem exists_theta_pow : SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 1 ≤ n → ∃ (θ : LB.Sec (D.P.L.pull (DegPre.prB D F).left)) (σ : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F 0) (DegPre.famε n))), (∃ j, θ.f j ≠ 0) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → sval σ r z J = sval (L := D.P.L) (φ := fun _ : PUnit => (DegPre.prB D F).left) (ε := fun _ => 1) θ r z J ^ n := by
  intro hT R _ _ D F _ _ n _
  obtain ⟨s₀, hs₀⟩ := GlobalTheory.FamFree.exists_sec_ne_zero (D := D) (F := F) hT (k := 1) le_rfl 0
  have hF₁ : FormEq (DegPre.famφ D F 0) (DegPre.famε 1)
      (fun _ : PUnit => (DegPre.prB D F).left) (fun _ => (1 : ℤ)) := by
    intro U _ h
    rw [prod_fam_zero D F 1 h]
    simp
  obtain ⟨θ, hθ⟩ := exists_sec D.P.isLB hF₁ s₀
  have hθne : ∃ j, θ.f j ≠ 0 := by
    by_contra hc
    push Not at hc
    have g0 : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens), gs f y U 0 = 0 := by
      intro Y X f y U
      unfold gs
      split <;> simp
    apply hs₀
    intro j
    refine (sec_ext_val D.P.isLB (s' := H1.SectionArithmetic.secZero _) (fun y J hJ => ?_) j).trans rfl
    rw [← hθ _ (𝟙 _) y J hJ]
    exact ((congrArg (gs _ y _) (hc _)).trans (g0 _ _ _)).trans (g0 _ _ _).symm
  let P := H1.SectionArithmetic.powSec (L := D.P.L) (φ := fun _ : PUnit => (DegPre.prB D F).left)
    (ε := fun _ => (1 : ℤ)) (fun _ : Fin n => θ)
  have hFn : FormEq (fun p : Fin n × PUnit => (DegPre.prB D F).left) (fun _ => (1 : ℤ))
      (DegPre.famφ D F 0) (DegPre.famε n) := by
    intro U _ h
    rw [prod_fam_zero D F n h]
    simp
  obtain ⟨σ, hσ⟩ := exists_sec D.P.isLB hFn P
  refine ⟨θ, σ, hθne, fun Z r z J hJ => ?_⟩
  rw [hσ Z r z J hJ, H1.SectionArithmetic.sval_powSec _ r z hJ]
  simp

end GlobalTheory.ThetaPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnifPrePull
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem exists_unifPre_pull : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegData R I) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), I.map φ ≤ I' → IsMonHom bc.hom → ∀ (U : UnifPre I D A G) (eA : (Over.pullback (jK R')).obj G' ≅ A'.A), IsMonHom eA.hom → (∃ wA : LB.Iso (A'.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ))), wA.IsGen) → ∀ (L' : RigLB G') (wL : LB.Iso L'.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf φ)))) (he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = specOf φ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig (rigPullOf (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) (specOf φ) he U.LG.L U.LG.rig) → ∃ (U' : UnifPre I' D' A' G') (wL' : LB.Iso U'.LG.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf φ)))), U'.LG = L' ∧ U'.gen = eA ∧ HEq wL' wL ∧ ∀ e : ℕ, ∃ (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left), h ≫ (fstG I e G).left = (fstG I' e G').left ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ∧ ((U'.gt e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ Geo.Tor.PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (hD.xe x)) h) ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R' I' e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((U'.gt e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → ((bc.hom.left ≫ pullback.fst G.hom (specOf φ))) ((fstG I' e G').left (r z)) ∈ U.LG.L.U jL → (fstG I' e G').left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL' (r ≫ (fstG I' e G').left) z jL jL') := by
  intro hG R R' _ _ _ _ I I' φ D D' hD A A' G _ _ G' _ _ bc hI hbc U eA heA hA L' wL he hwL hrig
  have hgp : IsGrpPullback G' G (specOf φ) (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) :=
    ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G (specOf φ))).congr (Category.id_comp _) rfl
  obtain ⟨c', s', hs', hsr, Hc, Hs⟩ := cubical_symmetry_transport _ _ (specOf φ) G G' _ hgp U.LG L' wL he hwL hrig
    U.cubG U.symG U.symG_gen U.symG_rig
  choose h q' i' hh H using fun e => gtCoord_baseChange_maps R R' φ D.toPre D'.toPre hD I I' hI G G' bc hbc e (U.gt e)
  choose gt' _ Hg using fun e => exists_gtCoord_pull hG R R' φ D.toPre D'.toPre hD I I' hI G G' bc hbc e (U.gt e)
    (h e) (q' e) (i' e) (hh e) (H e)
  have C := fun e => gtCoord_compat_of_pull R R' φ D.toPre D'.toPre hD I I' G G' _ e (U.gt e) (U.gt (e + 1))
    (gt' e) (gt' (e + 1)) (h e) (h (e + 1)) (hh e) (hh (e + 1)) (Hg e) (Hg (e + 1)) (U.gt_q e) (U.gt_t e)
  choose w' hw' sq using fun e => FourthSide.exists_fourth_side _ _ _ _ _ _ D.toPre.P.L D'.toPre.P.L U.LG.L L'.L
    D.toPre.P.isLB D'.toPre.P.isLB U.LG.isLB L'.isLB _ _ (U.gt e).pG.left (gt' e).pG.left (fstG I e G).left
    (fstG I' e G').left (h e) (Hg e).1 (hh e) hD.w wL (U.w e) hD.w_gen hwL (U.w_gen e)
  have RC := unifPull_rig_compat R R' I I' φ D D' hD A A' G G' bc hI hbc U L' wL he hwL hrig gt' w' hw'
    (fun e => (C e).1) (fun e => ⟨h e, hh e, Hg e, sq e⟩)
  have Ev := pulled_comparison_even hG R R' I I' φ D D' hD A A' G G' bc hI hbc U L' wL he hwL hrig gt' w' hw'
    (fun e => (C e).1) (fun e => ⟨h e, hh e, Hg e, sq e⟩) s' hs' Hs
  have Cu := w_cub_pull hG R R' I I' φ D D' hD A A' G G' bc hI hbc U L' wL he hwL hrig gt' w' hw'
    (fun e => (C e).1) (fun e => ⟨h e, hh e, Hg e, sq e⟩) hgp c' Hc
  have ext : LBIso (A'.L.pull eA.hom.left) (L'.L.pull (pullback.fst G'.hom (jK R'))) :=
    LBIso.trans (pull_isLB A'.isLB _) (pull_isLB U.LG.isLB _) (pull_isLB L'.isLB _) hA
      (LBIso.symm (LBIso.chartPull
        (chartPullPull L'.L _ _ rfl) (chartPullSame U.LG.L _ _ _ (pullback.fst G'.hom (jK R')) fun _ => rfl) ⟨wL, hwL⟩))
  exact ⟨{ smooth := MorphismProperty.of_isPullback hgp.1 U.smooth
           separated := MorphismProperty.of_isPullback hgp.1 U.separated
           gen := eA, gen_hom := heA, LG := L', cubG := c', symG := s', symG_gen := hs', symG_rig := hsr
           ext := ext, gt := gt', gt_q := fun e => (C e).1, gt_t := fun e => (C e).2
           w := w', w_gen := hw', w_rig := RC.1, w_even := Ev, w_cub := Cu, w_compat := RC.2 },
    wL, rfl, rfl, HEq.rfl, fun e => ⟨h e, hh e, Hg e, sq e⟩⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LatticePartCongrOfPhiRel
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PhiLattice

open ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem trPt_inv_comp (m : TF (R := R) F ⟶ D.P.A) : DegPre.trPt D F m⁻¹ ≫ DegPre.trPt D F m = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, tr_fst, tr_fst, Category.id_comp]
  · show (DegPre.trPt D F m⁻¹ ≫ DegPre.trPt D F m) ≫ DegPre.prB D F = 𝟙 _ ≫ DegPre.prB D F
    rw [Category.assoc, tr_pr, MonObj.comp_mul, tr_pr, ← Category.assoc, tr_fst, _root_.mul_assoc,
      ← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one, _root_.mul_one, Category.id_comp]

theorem zero_of_phiVal {n : ℕ} (p p' : QkPt D F n)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε n)))
    (w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p'.g.b) (DegPre.lineε n)))
    {s t : Fam D F n} (h : PhiVal p w s.s t.s) (h' : PhiVal p' w' s.s t.s) {α α' : D.X}
    (e : α' + p'.y = α + p.y) (h0 : ∀ j, (s.s α).f j = 0) : ∀ j, (s.s α').f j = 0 := by
  intro j
  refine sec_ext_val (s' := SecOps.secZero) D.P.isLB (fun y J hJ => ?_) j
  have e₁ := h α _ rfl _ (DegPre.trPt D F p'.g.b⁻¹) y J hJ
  have e₂ := h' α' _ e _ (DegPre.trPt D F p'.g.b⁻¹) y J hJ
  rw [UUA.sval_zero_of h0 _ y J (hJ.mem _ _), MulZeroClass.zero_mul] at e₁
  rw [e₁, trPt_inv_comp, Over.id_left] at e₂
  rw [UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _)]
  exact (Units.mul_left_eq_zero _).1 e₂.symm

end GlobalTheory.PhiLattice

namespace GlobalTheory

theorem lattice_part_congr_of_phiRel : GlobalFnsSt → SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 1 ≤ n → ∀ (p p' : QkPt D F n) (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε n))) (w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p'.g.b) (DegPre.lineε n))), w.IsGen → w'.IsGen → (∀ s : Fam D F n, ∃ s' : Fam D F n, PhiRel D F n p w s s' ∧ PhiRel D F n p' w' s s') → ∃ z : D.X, p'.y = p.y + n • z := by
  intro hG hT R _ _ D hB F _ _ n hn p p' w w' hw hw' H
  obtain ⟨s, hs⟩ := FamFree.exists_fam_support (D := D) (F := F) hG hT hB hn 0
  obtain ⟨t, h, h'⟩ := H s
  rw [ReciprocityTheory.ChartRestriction.G.DVR.phiRel_iff hG p w hw] at h
  rw [ReciprocityTheory.ChartRestriction.G.DVR.phiRel_iff hG p' w' hw'] at h'
  have h0 : ¬ ∀ j, (s.s 0).f j = 0 := (hs 0).2 ⟨0, by rw [smul_zero, add_zero]⟩
  obtain ⟨z, hz⟩ := (hs (p'.y - p.y)).1 fun h1 =>
    h0 (PhiLattice.zero_of_phiVal p p' w w' h h' (by rw [zero_add, sub_add_cancel]) h1)
  exact ⟨z, by rw [zero_add] at hz; rw [hz, add_sub_cancel]⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SymmetricFramePhiPowOrderEqIdStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.symmetricFrame_phi_pow_order_eq_id : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (N : ℕ), Odd N → ∀ (p : QkPt D.toPre F N) (w : Frm D.toPre F N p.g.b), TXFrame N p w → ∀ ss : Fin (N + 1) → Fam D.toPre F N, (∀ i : Fin N, PhiRel D.toPre F N p w (ss i.castSucc) (ss i.succ)) → ss (Fin.last N) = ss 0 := by
  first | exact @GlobalTheory.UT.PhiOrder.main | exact GlobalTheory.UT.PhiOrder.main | (intros; apply GlobalTheory.UT.PhiOrder.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValTorusPointAndTranslate
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusCoord

theorem val_torus_point_and_translate : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (τ : Z ⟶ splitTorus _ D.X) (y : Z ⟶ thickObj R I e G) (z : Z.left) (J : (Z.left ⟶ D.P.A.left) → D.P.L.ι), Geo.Tor.Good D.P.L z J → ∀ χ : D.X, Geo.Tor.val (g.t χ) (τ ≫ g.i).left z J = Geo.Tor.gm τ.left z ⊤ (charUnit _ D.X χ) ∧ Geo.Tor.val (g.t χ) ((τ ≫ g.i) * y).left z J = Geo.Tor.gm τ.left z ⊤ (charUnit _ D.X χ) * Geo.Tor.val (g.t χ) y.left z J := by
  intro R _ _ I D e G _ _ g Z τ y z J hJ χ
  refine ⟨?_, GlobalTheory.TorusCoord.val_torus g χ hJ τ y⟩
  rw [GlobalTheory.TorusCoord.val_congr g χ (_root_.mul_one (τ ≫ g.i)).symm z J, GlobalTheory.TorusCoord.val_torus g χ hJ τ 1,
    GlobalTheory.TorusCoord.val_unit g χ hJ, _root_.mul_one]

end GlobalTheory.TorusCoord
end

