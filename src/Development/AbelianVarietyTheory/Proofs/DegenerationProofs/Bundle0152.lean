module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataTorsionStructureAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.VFEqGenValMul
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch.FibCube
open GlobalTheory.FrameValue GlobalTheory.TorusExt

theorem vF_eq_genVal_mul {X Y Y' : Scheme.{0}} {L : LB X} {A : Over (Sp ℂ)} [GrpObj A] {L' : LB A.left} {g : ℕ}
    (u : HolUnif A L' g) (hL' : L'.IsLB) {Φ : A.left ⟶ X} {w : LB.Iso L' (L.pull Φ)} {K : Type} [Fintype K]
    {φ' : K → (Y' ⟶ A.left)} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y} (hψ : ∀ k, φ' k ≫ Φ = h ≫ φ k)
    {a : LB.Gen (LB.LinComb L' φ' ε)} (ha : a.IsGen) {t : LB.Gen (LB.LinComb L φ ε)} (H : PMaps w φ' φ ε a t h)
    {J : (Sp ℂ ⟶ X) → L.ι} (hJ : ∀ ψ : Sp ℂ ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) (fr : (Fin g → ℂ) → ℂˣ)
    (hfr : ∀ z i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U i →
      (fr z : ℂ) = valAt' (u.ex z).left _ (w.s (fun _ => J ((u.ex z).left ≫ Φ), i)).val * u.fr i z)
    {r : Sp ℂ ⟶ Y'} {z : K → Fin g → ℂ} (hz : IsLift u φ' r z) :
    vF t (r ≫ h) J = genVal u hL' a r z * ((∏ k, fr (z k) ^ ε k : ℂˣ) : ℂ) := by
  let p : Sp ℂ := (default : PrimeSpectrum ℂ)
  let J' : (Sp ℂ ⟶ A.left) → L'.ι := chartAt hL'
  have hJ' : ∀ ψ : Sp ℂ ⟶ A.left, ⊤ ≤ ψ ⁻¹ᵁ L'.U (J' ψ) := le_chartAt hL'
  have e := congrArg (fun q => (((stalkUnits p).symm q : ℂˣ) : ℂ))
    (DegPull.pmaps_val hψ H r p (J := J) (J' := J') (fun ψ => hJ ψ trivial) (fun ψ => hJ' ψ trivial))
  have e₁ : vF a r J' = genVal u hL' a r z * frameProd u ε z (fun k => J' (r ≫ φ' k)) :=
    valAt'_gen hL' ha hz (le_wchart_chartAt hL' φ' r)
  have e₂ : ∀ v, (((stalkUnits p).symm (gw w (u.ex v).left p (J ((u.ex v).left ≫ Φ)) (J' (u.ex v).left)) : ℂˣ) : ℂ) *
      u.fr (J' (u.ex v).left) v = fr v := fun v => by
    rw [hfr v _ (hJ' _)]
    refine congrArg (· * _) ((stalkConst p).injective ?_)
    have m : ⊤ ≤ (u.ex v).left ⁻¹ᵁ ((L.pull Φ).U (fun _ => J ((u.ex v).left ≫ Φ)) ⊓ L'.U (J' (u.ex v).left)) :=
      fun y hy => ⟨mem_pull.2 (hJ ((u.ex v).left ≫ Φ) hy), hJ' _ hy⟩
    rw [← stalkUnits_val, MulEquiv.apply_symm_apply]
    exact (gs_unit (u.ex v).left p ((L.pull Φ).U (fun _ => J ((u.ex v).left ≫ Φ)) ⊓ L'.U (J' (u.ex v).left))
      (m trivial) _).symm.trans (gs_eq_stalkConst _ p m _)
  simp only [map_mul, map_prod, map_zpow, Units.val_mul] at e
  rw [GaugeValues.vF_eq hJ, GaugeValues.vF_eq hJ', e₁] at e
  rw [e, mul_left_comm]
  congr 1
  rw [frameProd, Units.coe_prod, Units.coe_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, ← mul_zpow, hz k, e₂]

theorem exists_cube_down {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'} [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left} (gp : IsGrpPullback G' G f F) {L : RigLB G}
    (c : CubicalStr G L) {L' : LB G'.left} (hL' : L'.IsLB) {w : LB.Iso L' (L.L.pull F)} (hw : w.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' (thφ G' (x3 G')) thε), a.IsGen ∧
      PMaps w (thφ G' (x3 G')) (thφ G (x3 G)) thε a c.t (cubeMapOf gp).F3 ∧
      LB.Gen.Corr L' _ _ (Y := (G2 G').left) _ _ (LB.pullGen L' (thφ G' (x3 G')) thε a (faceMap G' 0).left)
        (LB.oneGen L') := by
  have hψ : ∀ I : thK, thφ G' (x3 G') I ≫ F = (cubeMapOf gp).F3 ≫ thφ G (x3 G) I :=
    fun I => (cubeMapOf gp).psum_comm I.down
  obtain ⟨a, ha, H⟩ := DegPull.exists_pmaps ((isGen_iff w).1 hw) L.isLB hL' (ε := thε) (cubeMapOf gp).F3 hψ c.t c.isGen
  refine ⟨a, ha, H, corr_of_val hL' fun y J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := DegPull.exists_good' L.isLB y
  have e := DegPull.pmaps_val hψ H (lift (1 : G2 G' ⟶ G') (lift (x2 G' 0) (x2 G' 1))).left y hJ hJ'
  have q : ∀ a b c : G2 G' ⟶ G', (lift a (lift b c)).left ≫ (cubeMapOf gp).F3 =
      (lift (pushHom gp _ a) (lift (pushHom gp _ b) (pushHom gp _ c))).left := fun a b c =>
    hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp [x3] <;> rfl
  rw [q, map_one] at e
  have p := prod_cub (1 : G2 G' ⟶ G') (x2 G' 0) (x2 G' 1) (fun q => gw w q y (J (q ≫ F)) (J' q))
  rw [_root_.one_mul, _root_.one_mul] at p
  have face : val c.t (lift (1 : Over.mk ((G2 G').hom ≫ f) ⟶ G)
      (lift (pushHom gp _ (x2 G' 0)) (pushHom gp _ (x2 G' 1)))).left y J = 1 := by
    have h := val_corr hJ (c.face 0) (lift (pushHom gp _ (x2 G' 0)) (pushHom gp _ (x2 G' 1))).left
    rw [val_one] at h
    refine Eq.trans ?_ h
    refine Eq.trans ?_ (val_cub c (lift (pushHom gp _ (x2 G' 0)) (pushHom gp _ (x2 G' 1))) hJ (pzero G _) (x2 G 0) (x2 G 1)).symm
    congr 1 <;> simp [x2, pzero, Hom.one_def]
  have e' := face.symm.trans (e.trans (congrArg (· * _) p))
  refine (val_pull hJ' _ _ _).trans (Eq.trans ?_ (val_one _).symm)
  rw [Category.id_comp]
  apply Additive.ofMul.injective
  have e'' := congrArg Additive.ofMul e'
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at e'' ⊢
  refine Eq.trans ?_ e''.symm
  abel

end GlobalTheory.Ex.Arch.FibCube

namespace GlobalTheory.Ex.Arch
open GlobalTheory.FrameValue GlobalTheory.CubeValues

theorem fibCubeSt : Laws → FibCubeSt := by
  rintro - R _ _ _ D J g Λ Hm χ ex fr ⟨hJ, P', φ, w, u, hΛ, gp, hw, hAH, -, -, -, hex, hfr⟩ x y z
  obtain ⟨a, ha, H, hf⟩ := FibCube.exists_cube_down gp D.cub P'.isLB hw
  have e := FibCube.vF_eq_genVal_mul (L := D.P.L) (Φ := φ) (w := w) u P'.isLB (fun I : thK => (cubeMapOf gp).psum_comm I.down) ha H hJ fr
    (fun v i hi => by rw [← hex v]; exact hfr v i hi) (isLift_cube u ![x, y, z])
  replace e := e.trans ((congrArg (· * _) (genVal_cube_of_face P'.isLB hAH a ha hf _)).trans (_root_.one_mul _))
  have q : (pt3 u ![x, y, z]).left ≫ (cubeMapOf gp).F3 = (lift (ex x) (lift (ex y) (ex z))).left :=
    hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp [x3, pt3, hex] <;> rfl
  have p := prod_thK fun I => fr (∑ a ∈ I, ![x, y, z] a)
  simp only [sum_three, Finset.sum_singleton, Finset.sum_empty, Matrix.cons_val] at p
  rw [q] at e
  refine (congrArg (fun s : ℂ => s * fr (x + y) * fr (x + z) * fr (y + z) * fr 0)
    (e.trans (congrArg Units.val p))).trans ?_
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

end GlobalTheory.Ex.Arch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValIsoChart
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.Ex.Arch
open GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter GlobalTheory.EigenNorm GlobalTheory.FrameValue

theorem val_iso_chart {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} (hL' : L'.IsLB) {F : X' ⟶ X}
    {w : LB.Iso L' (L.pull F)} (hw : w.IsGen) (x : Sp ℂ ⟶ X') (j j' : L.ι) (i : L'.ι)
    (hj : ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j) (hj' : ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j') (hi : ⊤ ≤ x ⁻¹ᵁ L'.U i) :
    valAt' x _ (w.s (fun _ => j, i)).val =
      valAt' (x ≫ F) (L.U j ⊓ L.U j') (L.g j j').val * valAt' x _ (w.s (fun _ => j', i)).val := by
  have a : ⊤ ≤ x ⁻¹ᵁ L.wchart (fun _ : PUnit => F) (fun _ => j) := (le_preimage_wchart x L _ _).2 fun _ => hj
  have a' : ⊤ ≤ x ⁻¹ᵁ L.wchart (fun _ : PUnit => F) (fun _ => j') := (le_preimage_wchart x L _ _).2 fun _ => hj'
  have b := (le_preimage_inf x _ _).2 ⟨a, hi⟩
  have b' := (le_preimage_inf x _ _).2 ⟨a', hi⟩
  have c := (le_preimage_inf x _ _).2 ⟨b, b'⟩
  refine (val_sec x (genSec w hw) (fun _ => j, i) (fun _ => j', i) b b').trans (congrArg₂ (· * ·) ?_ rfl)
  have e₁ := val_linComb x valueRules L (fun _ : PUnit => F) (fun _ => 1) (fun _ => j) (fun _ => j') a a'
  rw [Fintype.prod_unique, zpow_one] at e₁
  have e₂ : valAt' x (L'.U i ⊓ L'.U i) (L'.g i i).val = 1 := by
    obtain ⟨e, he⟩ := (valueRules X' x).2.1 _ hi
    rw [← val_res x valueRules (le_inf le_rfl le_rfl) hi, hL'.g_self i, he]
    exact map_one e
  obtain ⟨e, he⟩ := (valueRules X' x).2.1 _ c
  refine (val_unit_mul x valueRules c _ _).trans ?_
  refine (congrArg₂ (· * ·) ((val_res x valueRules _ c _).trans e₁) ((he _).trans ((map_units_inv e _).trans
    (congrArg (·⁻¹) ((he _).symm.trans ((val_res x valueRules _ c _).trans e₂)))))).trans ?_
  simp

theorem fibSec : FibSecSt := by
  intro R _ _ _ D J g Λ Hm χ ex fr h s
  obtain ⟨hJ, P', φ, w, u, hΛ, -, hw, -, -, -, -, hex, hfr⟩ := h
  refine ⟨fun z => sF s (ex z).left J / fr z, fun z₀ => ?_, fun z => (div_mul_cancel₀ _ (fr z).ne_zero).symm⟩
  obtain ⟨i, hi⟩ : ∃ i, ⊤ ≤ (u.ex z₀).left ⁻¹ᵁ P'.L.U i := ⟨_, le_chartAt P'.isLB _⟩
  obtain ⟨j, hj⟩ : ∃ j, ⊤ ≤ ((u.ex z₀).left ≫ φ) ⁻¹ᵁ D.P.L.U j := ⟨_, hJ _⟩
  have ch : ∀ (y : Sp ℂ ⟶ D.P.A.left) (k : D.P.L.ι), ⊤ ≤ y ⁻¹ᵁ D.P.L.U k →
      ⊤ ≤ y ⁻¹ᵁ D.P.L.wchart (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => k) := fun y k hk =>
    (le_preimage_wchart y _ _ _).2 fun _ => by rwa [Category.comp_id]
  have a : ⊤ ≤ (u.ex z₀).left ⁻¹ᵁ (D.P.L.wchart (fun _ : PUnit => φ) (fun _ => j) ⊓ P'.L.U i) :=
    (le_preimage_inf _ _ _).2 ⟨(le_preimage_wchart _ _ _ _).2 fun _ => hj, hi⟩
  obtain ⟨o₁, d₁⟩ := u.hol (φ ⁻¹ᵁ D.P.L.wchart (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => j))
    ((φ.app _).hom (s.f fun _ => j))
  obtain ⟨o₂, d₂⟩ := u.hol _ (w.s (fun _ => j, i)).val
  have n₂ := o₂.mem_nhds a
  have d := (d₁.differentiableAt (o₁.mem_nhds (ch _ j hj))).fun_mul (((d₂.differentiableAt n₂).fun_mul
    ((u.fr_hol i).differentiableAt ((u.hol _ 0).1.mem_nhds hi))).fun_inv
    (mul_ne_zero (val_unit_ne_zero _ valueRules a _) (u.fr_ne i _ hi)))
  refine d.congr_of_eventuallyEq ?_
  filter_upwards [n₂] with z hz
  obtain ⟨h₁, h₂⟩ := (le_preimage_inf _ _ _).1 hz
  have h₃ := (le_preimage_wchart _ _ _ _).1 h₁ PUnit.unit
  have e₀ : sF s (ex z).left J = valAt' (ex z).left _ (s.f fun _ => J (ex z).left) := by
    rfl
  have e₁ := val_sec (ex z).left s (fun _ => J (ex z).left) (fun _ => j) (ch _ _ (hJ _)) (ch _ _ (hex z ▸ h₃))
  have e₂ := val_linComb (ex z).left valueRules D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => ((1 : ℕ) : ℤ))
    (fun _ => J (ex z).left) (fun _ => j) (ch _ _ (hJ _)) (ch _ _ (hex z ▸ h₃))
  rw [Fintype.prod_unique, Nat.cast_one, zpow_one, Category.comp_id] at e₂
  have e₃ := val_iso_chart P'.isLB hw (u.ex z).left (J (ex z).left) j i (hex z ▸ hJ _) h₃ h₂
  have n := val_unit_ne_zero (ex z).left valueRules ((le_preimage_inf _ _ _).2 ⟨hJ _, hex z ▸ h₃⟩)
    (D.P.L.g (J (ex z).left) j)
  have e₄ := (valueRules _ (u.ex z).left).2.2.2.1 _ φ _ (s.f fun _ => j)
  rw [← hex z] at e₃ e₄
  rw [e₀, e₁, hfr z i h₂, e₃, _root_.mul_assoc]
  exact (congrArg (fun q => q * _ / _) e₂).trans ((mul_div_mul_left _ _ n).trans ((div_eq_mul_inv _ _).trans
    (congrArg₂ (· * ·) e₄.symm rfl)))

end GlobalTheory.Ex.Arch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValuationOverFiniteDvrExtension
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

namespace GlobalTheory.FiniteDVRValuation

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing in
open scoped CategoryTheory.Obj BigOperators in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} in
theorem _root_.GlobalTheory.FiniteDVRValuation.exists_nat_val (hϖ : Irreducible ϖ) (hv : _root_.ReciprocityTheory.ChartRestriction.G.DVR.ValOver ϖ F v) {c : V}
    (hc : c ≠ 0) :
    ∃ n : ℕ, v (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) c)) =
        ((n : ℚ) : WithTop ℚ) ∧ (n = 0 → IsUnit c) := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  refine ⟨n, ?_, fun hn => by subst hn; simp⟩
  rw [hv _ n ⟨u, by rw [zpow_natCast, map_mul, map_pow, mul_comm]⟩]
  norm_cast

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing in
open scoped CategoryTheory.Obj BigOperators in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} in
theorem _root_.GlobalTheory.FiniteDVRValuation.val_nonneg (hϖ : Irreducible ϖ) (hv : _root_.ReciprocityTheory.ChartRestriction.G.DVR.ValOver ϖ F v) (c : V) :
    0 ≤ v (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) c)) := by
  by_cases hc : c = 0
  · subst hc
    simp
  · obtain ⟨n, hn, -⟩ := _root_.GlobalTheory.FiniteDVRValuation.exists_nat_val hϖ hv hc
    rw [hn]
    exact_mod_cast n.cast_nonneg

end

def nonnegSubring {F K : Type} [Field F] [Field K] (v : AddValuation F (WithTop ℚ)) (e : K →+* F) :
    ValuationSubring K where
  carrier := {x | 0 ≤ v (e x)}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_mul, AddValuation.map_mul] at *
    exact add_nonneg ha hb
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add (f := _)] at *
    exact v.map_le_add ha hb
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, map_neg, AddValuation.map_neg] at *
    exact ha
  mem_or_inv_mem' := by
    intro x
    simp only [Set.mem_setOf_eq]
    by_cases hx : x = 0
    · left; simp [hx]
    by_contra hcon
    push_neg at hcon
    have h1 : v (e x) + v (e x⁻¹) = 0 := by
      rw [← AddValuation.map_mul, ← map_mul, mul_inv_cancel₀ hx, map_one, AddValuation.map_one]
    have h2 : v (e x) + v (e x⁻¹) < 0 := by
      calc v (e x) + v (e x⁻¹) ≤ 0 + v (e x⁻¹) := by gcongr; exact hcon.1.le
        _ = v (e x⁻¹) := zero_add _
        _ < 0 := hcon.2
    exact h2.ne h1

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing in
open scoped CategoryTheory.Obj BigOperators in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.FiniteDVRValuation.main :
    ∀ (W W' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CommRing W']
      [IsDomain W'] [IsDiscreteValuationRing W'] (i : W →+* W'), Function.Injective i →
      i.Finite → ∀ (ϖ : W'), Irreducible ϖ → ∀ (F : Type) [Field F]
      [Algebra (FractionRing W') F] (v : AddValuation F (WithTop ℚ)), _root_.ReciprocityTheory.ChartRestriction.G.DVR.ValOver ϖ F v →
      (∀ r : W', 0 ≤ v (algebraMap (FractionRing W') F (algebraMap W' _ r))) ∧
      (∃ i' : FractionRing W →+* FractionRing W',
        (∀ r, i' (algebraMap W _ r) = algebraMap W' _ (i r)) ∧
        ∀ a : FractionRing W, v (algebraMap (FractionRing W') F (i' a)) = 0 →
          ∃ u : Wˣ, algebraMap W (FractionRing W) u = a) ∧
      ∀ (K : Type) [Field K] (e : K →+* F), ∃ S : ValuationSubring K,
        ∀ x, (x ∈ S ↔ 0 ≤ v (e x)) ∧ (S.valuation x = 1 → v (e x) = 0) := by
  intro W W' _ _ _ _ _ _ i hi hfin ϖ hϖ F _ _ v hv
  refine ⟨fun r => _root_.GlobalTheory.FiniteDVRValuation.val_nonneg hϖ hv r, ?_,
    fun K _ e => ⟨_root_.GlobalTheory.FiniteDVRValuation.nonnegSubring v e, fun x => ⟨Iff.rfl, fun h => ?_⟩⟩⟩
  · have hinj : Function.Injective ((algebraMap W' (FractionRing W')).comp i) :=
      (IsFractionRing.injective W' (FractionRing W')).comp hi
    have hunit : ∀ x : W,
        v (algebraMap (FractionRing W') F (algebraMap W' _ (i x))) = 0 → IsUnit x := by
      intro x hx
      by_contra hxu
      have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hx
      have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' i hfin.to_isIntegral
        (IsLocalRing.maximalIdeal W')
      have hcomap : (IsLocalRing.maximalIdeal W').comap i = IsLocalRing.maximalIdeal W :=
        IsLocalRing.eq_maximalIdeal hmax
      have hmem : x ∈ (IsLocalRing.maximalIdeal W').comap i := by
        rw [hcomap]
        exact (IsLocalRing.mem_maximalIdeal x).2 hxu
      have hix : ¬IsUnit (i x) := (IsLocalRing.mem_maximalIdeal _).1 (Ideal.mem_comap.1 hmem)
      have hle := (_root_.ReciprocityTheory.ChartRestriction.G.DVR.TWO.v_of_V v hϖ hv (i x)).2 hix ((map_ne_zero_iff i hi).2 hx0)
      have hle' : (1 : WithTop ℚ) ≤ 0 := by
        rw [← hx]
        exact hle
      exact absurd hle' (by norm_num)
    refine ⟨IsFractionRing.lift hinj, fun r => IsFractionRing.lift_algebraMap hinj r,
      fun a ha => ?_⟩
    by_cases ha0 : a = 0
    · subst ha0
      simp at ha
    rcases ValuationRing.isInteger_or_isInteger W a with ⟨x, hx⟩ | ⟨x, hx⟩
    · subst hx
      rw [IsFractionRing.lift_algebraMap, RingHom.comp_apply] at ha
      exact ⟨(hunit x ha).unit, rfl⟩
    · have hinv : v (algebraMap (FractionRing W') F (IsFractionRing.lift hinj a⁻¹)) = 0 := by
        have hsum : v (algebraMap (FractionRing W') F (IsFractionRing.lift hinj a)) +
            v (algebraMap (FractionRing W') F (IsFractionRing.lift hinj a⁻¹)) = 0 := by
          rw [← AddValuation.map_mul, ← map_mul, ← map_mul, mul_inv_cancel₀ ha0, map_one, map_one,
            AddValuation.map_one]
        rwa [ha, zero_add] at hsum
      rw [← hx, IsFractionRing.lift_algebraMap, RingHom.comp_apply] at hinv
      refine ⟨(hunit x hinv).unit⁻¹, ?_⟩
      rw [← inv_inv a, ← hx, map_units_inv, IsUnit.unit_spec]
  · have hx0 : x ≠ 0 := by
      rintro rfl
      simp at h
    have h1 : x ∈ _root_.GlobalTheory.FiniteDVRValuation.nonnegSubring v e := (ValuationSubring.valuation_le_one_iff _ _).1 h.le
    have h2 : x⁻¹ ∈ _root_.GlobalTheory.FiniteDVRValuation.nonnegSubring v e :=
      (ValuationSubring.valuation_le_one_iff _ _).1 (by rw [map_inv₀, h, inv_one])
    change 0 ≤ v (e x) at h1
    change 0 ≤ v (e x⁻¹) at h2
    have hsum : v (e x) + v (e x⁻¹) = 0 := by
      rw [← AddValuation.map_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, AddValuation.map_one]
    exact le_antisymm (le_add_of_nonneg_right h2 |>.trans_eq hsum) h1

end GlobalTheory.FiniteDVRValuation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValuesIsoCommActionAbelianPartTorsion
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
noncomputable section
namespace GlobalTheory.Ex.ActPt

section
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem equiv_parts {k : ℕ} {p p' : QkPt D F k} (h : QkPt.Equiv D F p p') :
    ∃ z : D.X, p'.y = p.y + k • z ∧ p'.g.b = p.g.b * DegPre.cF D F z := by
  obtain ⟨z, h₁, g, h₂, h₃⟩ := h
  exact ⟨z, h₁, by rw [h₃.1, h₂.1]; rfl⟩

variable {O : Type} [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O)

theorem mul_cF_act (x : O) (b : TF (R := R) F ⟶ D.P.A) (z : D.X) :
    (b * DegPre.cF D F z) ≫ oa.onB.act x = (b ≫ oa.onB.act x) * DegPre.cF D F (x • z) := by
  have := oa.onB.hom x
  rw [MonObj.mul_comp, DegPre.cF, DegPre.cF, oa.c_lin, Category.assoc]

theorem act_parts {k : ℕ} {x : O} {p p' : QkPt D F k} (h : QkAct oa x p p') :
    ∃ z : D.X, p'.y = x • p.y + k • z ∧ p'.g.b = (p.g.b ≫ oa.onB.act x) * DegPre.cF D F z := by
  obtain ⟨q, h₁, h₂, h₃⟩ := h
  obtain ⟨z, e₁, e₂⟩ := equiv_parts h₃
  exact ⟨z, by rw [e₁, h₁], by rw [e₂, h₂.1]⟩
end

theorem exists_image {C : Type} [CommRing C] {N N' : NumD C} (J : NumD.Iso N N') {k : ℕ} (p : N.QT k) :
    ∃ q : N'.QT k, q.1.1.toAdd = J.e p.1.1.toAdd ∧ J.Rel p.1.2 q.1.2 := by
  obtain ⟨h₁, h₂, h₃, -⟩ := NumD.hom_transport C C (RingHom.id C) N N' (TateInh.homOfIso J)
  obtain ⟨g, hg, -⟩ := h₁ p.1.2
  have hp : ∀ n : ℕ, (TateInh.homOfIso J).Rel (p.1.2 ^ n) (g ^ n) := fun n => by
    induction n with
    | zero => rw [pow_zero, pow_zero]; exact J.rel_one
    | succ n ih => rw [pow_succ, pow_succ]; exact h₂ _ _ _ _ ih hg
  have e := hp k
  rw [N.mem_QT.1 p.2] at e
  exact ⟨⟨(Multiplicative.ofAdd (J.e p.1.1.toAdd), g), (h₁ _).unique e (h₃ _)⟩, rfl, hg⟩

theorem main : GlobalTheory.UT.LL → BrGtSt → AllS fun {E} _ _ _ {H} {_} {_} {_} {_} _ {_} {_} _ _ {_} a {_} _ _ A u r {_} M _ {_} ν' J => M.P.TorsionIso → ∀ k : ℕ, 0 < k → Labels A u r M ν' J k → (∀ (x : 𝓞 E) y, ν'.eX (J.e (A.arc.act x y)) = x • ν'.eX (J.e y)) → ∀ (x : 𝓞 E) (y y' : A.N.A), y ^ k = 1 → (letI := H.starRing; A.ν.eA y' = A.ν.eA y ≫ a.oa.onB.act x → ν'.eA (J.φ y') = ν'.eA (J.φ y) ≫ M.P.oD.onB.act x) := by
  intro hL hB E _ _ _ H D l c O _ β O' _ _ _ b a C _ _ _ _ _ _ A u r o M f N' ν' J hr _ hT k hk hlab hlin x y y' hy hy'
  letI := H.starRing
  obtain ⟨-, -, -, -, B⟩ := hB O' a.D₀ a.even a.bimult C A.N A.ν
  obtain ⟨-, -, -, -, B'⟩ := hB M.W M.P.D.toPre M.P.D.psi_even M.P.D.tau_bimult C N' ν'
  obtain ⟨t, t₁, -, t₃, -, t₅, -⟩ := hT C k hk
  have im : ∀ w : D.La, ∃ p' : QkPt M.P.D.toPre C k, (t p').left = (o.I.ev k w).left ≫ M.φ ∧
      p'.y = ν'.eX (J.e (A.q k w).1.1.toAdd) ∧ p'.g.b = ν'.eA (J.φ (A.q k w).1.2.b) := fun w => by
    obtain ⟨p, hp, -⟩ := existsUnique_twRel A.be u (r k) (hr.pow hk) (A.q k w)
    obtain ⟨q, q₁, q₂⟩ := exists_image J p
    obtain ⟨p', hp'⟩ := (B' k).2.1 q
    let z : TFK (R := M.W) C ⟶ M.P.A.A := Over.homMk ((o.I.ev k w).left ≫ M.φ) (by
      rw [Category.assoc, M.cart.1.w, ← Category.assoc, Over.w]
      exact Category.id_comp _)
    have hz := (t₁ _ _).1 (hlab w p q p' z hp q₁ q₂ hp' rfl)
    refine ⟨p', by rw [← hz]; rfl, ?_, ?_⟩
    · rw [← hp'.1, q₁, hp.1]; rfl
    · rw [← hp'.2.1, q₂.1]; exact congrArg (fun s => ν'.eA (J.φ s)) hp.2.1
  obtain ⟨gm, hγ, hγ'⟩ := QStr.root_over A.N hk.ne' 1 y hy
  obtain ⟨p₀, hp₀⟩ := (B k).2.1 ⟨(1, gm), hγ'.trans A.N.io_zero.symm⟩
  obtain ⟨v, hv⟩ := A.I.onto k hk p₀
  obtain ⟨z₀, -, e₀⟩ := equiv_parts hv
  obtain ⟨z₁, d₁, e₁⟩ := act_parts a.oa (A.I.lin k hk x v)
  obtain ⟨p₁, a₁, b₁, c₁⟩ := im v
  obtain ⟨p₂, a₂, b₂, c₂⟩ := im (x • v)
  obtain ⟨p₃, h₃⟩ := qkAct_exists hL.1.globalFns M.P.D.tau_bimult M.P.oD x p₁
  have e₃ : t p₃ = t p₂ := by
    rw [t₅ _ _ _ h₃]
    ext1
    rw [a₂, o.I.lin, Over.comp_left, Over.comp_left, a₁, Category.assoc, Category.assoc, M.act]
  have h₂ : QkAct M.P.oD x p₁ p₂ :=
    (TorusExt.qkAct_iff_of_equiv M.P.D.tau_bimult hL.1.globalFns M.P.oD
      (qk_equiv_refl M.P.D.tau_bimult p₁) h₃).2
      ((t₃ _ _).1 e₃)
  obtain ⟨z₂, d₂, e₂⟩ := act_parts M.P.oD h₂
  obtain ⟨w₀, rfl⟩ := A.ν.eX.surjective z₀
  obtain ⟨w₁, rfl⟩ := A.ν.eX.surjective z₁
  rw [← (A.hq k v).1, ← (A.hq k (x • v)).1] at d₁
  rw [← (A.hq k v).2.1, ← (A.hq k (x • v)).2.1] at e₁
  rw [← (A.hq k v).2.1, ← hp₀.2.1] at e₀
  rw [b₁, b₂] at d₂
  rw [c₁, c₂] at e₂
  generalize (A.q k v).1.1.toAdd = s₁ at d₁ d₂
  generalize (A.q k (x • v)).1.1.toAdd = s₂ at d₁ d₂
  generalize (A.q k v).1.2.b = β₁ at e₀ e₁ e₂
  generalize (A.q k (x • v)).1.2.b = β₂ at e₁ e₂
  let e : A.N.X ≃+ N'.X := J.e
  let φ : A.N.A ≃* N'.A := J.φ
  have hc : ∀ χ, N'.c (e χ) = φ (A.N.c χ) := J.c_eq
  let act : A.N.X → A.N.X := fun s => A.ν.eX.symm (x • A.ν.eX s)
  have hl : ∀ s, ν'.eX (e (act s)) = x • ν'.eX (e s) := hlin x
  have ha : ∀ s, A.ν.eX (act s) = x • A.ν.eX s := fun s => A.ν.eX.apply_symm_apply _
  change ν'.eX (e s₂) = x • ν'.eX (e s₁) + k • z₂ at d₂
  change ν'.eA (φ β₂) = ν'.eA (φ β₁) ≫ _ * _ at e₂
  change ν'.eA (φ y') = ν'.eA (φ y) ≫ _
  have g₁ : s₂ = act s₁ + k • w₁ := A.ν.eX.injective (by rw [d₁, map_add (f := _), map_nsmul, ha])
  have g₂ : z₂ = ν'.eX (e w₁) := by
    rw [g₁, map_add (f := _), map_add (f := _), map_nsmul, map_nsmul, hl, add_right_inj, ← natCast_zsmul, ← natCast_zsmul] at d₂
    exact (smul_right_injective _ (Int.natCast_ne_zero.2 hk.ne') d₂).symm
  have g₀ : y = β₁ * A.N.c w₀ := A.ν.eA.injective (by rw [map_mul, A.ν.c_eq, ← e₀, hγ])
  have g₃ : y' * A.N.c w₁ = β₂ * A.N.c (act w₀) := A.ν.eA.injective (by
    rw [map_mul, map_mul, hy', g₀, map_mul, A.ν.c_eq, A.ν.c_eq, A.ν.c_eq, mul_cF_act, e₁, ha, mul_right_comm])
  have g₄ := congrArg (fun s => ν'.eA (φ s)) g₃
  simp only [map_mul, ← hc, ν'.c_eq, hl, e₂, ← g₂] at g₄
  rw [mul_right_comm, mul_left_inj] at g₄
  rw [g₄, g₀, map_mul, map_mul, ← hc, ν'.c_eq, mul_cF_act]

end GlobalTheory.Ex.ActPt
end
end

