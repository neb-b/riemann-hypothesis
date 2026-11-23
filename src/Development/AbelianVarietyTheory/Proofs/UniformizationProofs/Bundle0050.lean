module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenV
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefVal
open TWM TWO CoefBasic

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)
  {X : Scheme.{0}} {L : LB X}

theorem isDominant_ι : IsDominant (ιS hϖ hv).left := by
  refine ⟨?_⟩
  show DenseRange (PrimeSpectrum.comap (algebraMap (Ov v) F))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective (Ov v) F)]
  exact bot_le

theorem ι_inj [X.IsSeparated] : Function.Injective fun ψ : (TO hϖ hv).left ⟶ X => (ιS hϖ hv).left ≫ ψ := by
  intro a b h
  have := isDominant_ι hϖ hv
  have : IsReduced (TO hϖ hv).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of (Ov v))))
  exact ext_of_isDominant (ιS hϖ hv).left h

theorem gs_ι (z : (TF (R := V) F).left) (a : Γ(Spec (CommRingCat.of (Ov v)), ⊤)) :
    gs (ιS hϖ hv).left z ⊤ a = cst F z (ιr (v := v) a) := by
  rw [cst_eq, gs_eq _ z ⊤ trivial]
  exact congrArg ((TF (R := V) F).left.presheaf.germ ⊤ z trivial).hom
    (appTop_specMap (CommRingCat.ofHom (algebraMap (Ov v) F)) a)

theorem sec_int [X.IsSeparated] (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → ((TO hϖ hv).left ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε))
    (hf : ∀ (U : Type) [CommGroup U] (h : ((TF (R := V) F).left ⟶ X) → U), ∏ i, h ((ιS hϖ hv).left ≫ φ i) ^ ε i = 1) :
    ∃ a : F, 0 ≤ v a ∧ ∀ z J, Good L z J → sval s (ιS hϖ hv).left z J = cst F z a := by
  obtain ⟨s₀, hs⟩ := exists_sec hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
    refine Eq.trans ?_ ((hf U (Function.extend (fun ψ => (ιS hϖ hv).left ≫ ψ) h 1)).trans (Fintype.prod_empty _).symm)
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [(ι_inj hϖ hv).extend_apply]) s
  have le : (⊤ : (TO hϖ hv).left.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → ((TO hϖ hv).left ⟶ X)) PEmpty.elim :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  refine ⟨ιr (v := v) (((TO hϖ hv).left.presheaf.map (homOfLE le).op).hom (s₀.f PEmpty.elim)), v_ιr _,
    fun z J hJ => ?_⟩
  rw [← hs _ _ z J hJ, sval_of s₀ _ z J PEmpty.elim (fun k => k.elim), ← gs_ι hϖ hv]
  exact (gs_res _ z le trivial _).symm

abbrev FS (V F : Type) [CommRing V] [IsDomain V] [Field F] [Algebra (FractionRing V) F] (X : Scheme.{0}) : Type 1 :=
  ∀ (U : Type) [CommGroup U], (((TF (R := V) F).left ⟶ X) → U) → U

def HV (L : LB X) (σ : FS V F X)
    (f : ∀ z : (TF (R := V) F).left, (((TF (R := V) F).left ⟶ X) → L.ι) → (TF (R := V) F).left.presheaf.stalk z)
    (x : F) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → ((TO hϖ hv).left ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : ((TF (R := V) F).left ⟶ X) → U), ∏ i, h ((ιS hϖ hv).left ≫ φ i) ^ ε i = σ U h) ∧
    ∀ z J, Good L z J → f z J = cst F z x * (val t (ιS hϖ hv).left z J).val

variable {hϖ hv}

theorem HV.mul {σ σ' : FS V F X} {f f'} {x x' : F} (H : HV hϖ hv L σ f x) (H' : HV hϖ hv L σ' f' x') :
    HV hϖ hv L (fun U _ h => σ U h * σ' U h) (fun z J => f z J * f' z J) (x * x') := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  obtain ⟨K', _, φ', ε', t', ht', hs', e'⟩ := H'
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L _ _ _ _ t t', mulGen_isGen _ _ _ _ _ _ _ ht ht', fun U _ h => ?_,
    fun z J hJ => ?_⟩
  · rw [Fintype.prod_sum_type]
    exact congrArg₂ (· * ·) (hs U h) (hs' U h)
  · rw [val_mul hJ]
    simp only [e z J hJ, e' z J hJ, cst_eq, map_mul, Units.val_mul]
    ring

theorem HV.one : HV hϖ hv L (fun _ _ _ => 1) (fun _ _ => 1) 1 :=
  ⟨PEmpty, inferInstance, _, _, LB.oneGen L (Y := (TO hϖ hv).left),
    fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm,
    fun U _ h => Fintype.prod_empty _, fun z J _ => by rw [val_one, cst_eq, map_one, Units.val_one, _root_.mul_one]⟩

theorem HV.congr {σ σ' : FS V F X} {f f'} {x : F} (H : HV hϖ hv L σ f x)
    (hσ : ∀ (U : Type) [CommGroup U] h, σ U h = σ' U h) (hf : ∀ z J, Good L z J → f' z J = f z J) :
    HV hϖ hv L σ' f' x := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  exact ⟨K, _, φ, ε, t, ht, fun U _ h => (hs U h).trans (hσ U h), fun z J hJ => (hf z J hJ).trans (e z J hJ)⟩

theorem HV.pow {σ : FS V F X} {f} {x : F} (H : HV hϖ hv L σ f x) (n : ℕ) :
    HV hϖ hv L (fun U _ h => σ U h ^ n) (fun z J => f z J ^ n) (x ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using HV.one
  | succ n ih => simpa only [pow_succ] using ih.mul H

theorem HV.smul {σ : FS V F X} {f} {x : F} (H : HV hϖ hv L σ f x) (c : F) :
    HV hϖ hv L σ (fun z J => cst F z c * f z J) (c * x) := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  refine ⟨K, _, φ, ε, t, ht, hs, fun z J hJ => ?_⟩
  simp only [e z J hJ, cst_eq, map_mul, _root_.mul_assoc]

theorem HV.le [X.IsSeparated] (hL : L.IsLB) {σ : FS V F X} {f} {x x' : F} (H : HV hϖ hv L σ f x)
    (H' : HV hϖ hv L σ f x') : v x ≤ v x' := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  obtain ⟨K', _, φ', ε', t', ht', hs', e'⟩ := H'
  have hu := mulGen_isGen _ _ _ _ _ _ _ ht (invGen_isGen _ _ _ _ ht')
  obtain ⟨a, ha, hav⟩ := sec_int hϖ hv hL (Geo.Tor.genSec _ hu) (fun U _ h => by
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
    rw [hs, hs', mul_inv_cancel])
  obtain ⟨z⟩ := exists_pt (R := V) (F := F)
  obtain ⟨J, hJ⟩ := exists_good' hL z
  have b := hav z J hJ
  rw [sval_genSec _ hu _ z hJ, val_mul hJ, val_inv] at b
  have c : x' = x * a := by
    apply cstH_inj (R := V) z
    have d := (e z J hJ).symm.trans (e' z J hJ)
    rw [map_mul, ← cst_eq, ← cst_eq, ← cst_eq, ← b, Units.val_mul, ← _root_.mul_assoc, d, _root_.mul_assoc,
      Units.mul_inv, _root_.mul_one]
  rw [c, AddValuation.map_mul]
  exact le_add_of_nonneg_right ha

theorem HV.cmp [X.IsSeparated] (hL : L.IsLB) {σ σ' : FS V F X} {f f'} {x x' : F} (H : HV hϖ hv L σ f x)
    (H' : HV hϖ hv L σ' f' x') (hσ : ∀ (U : Type) [CommGroup U] h, σ U h = σ' U h)
    (hf : ∀ z J, Good L z J → f' z J = f z J) : v x = v x' :=
  le_antisymm ((H.congr hσ hf).le hL H') (H'.le hL (H.congr hσ hf))

variable {K : Type} [Fintype K] {ε : K → ℤ}

theorem hv_gen {Y : Scheme.{0}} {φ : K → (Y ⟶ X)} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen)
    (r₀ : (TO hϖ hv).left ⟶ Y) {r : (TF (R := V) F).left ⟶ Y} (hr : (ιS hϖ hv).left ≫ r₀ = r) :
    HV hϖ hv L (fun _ _ h => ∏ i, h (r ≫ φ i) ^ ε i) (fun z J => (val t r z J).val) 1 := by
  subst hr
  exact ⟨K, _, _, ε, LB.pullGen L φ ε t r₀, pullGen_isGen _ _ _ _ ht _, fun U _ h => by simp only [Category.assoc],
    fun z J hJ => by rw [val_pull hJ, cst_eq, map_one, _root_.one_mul]⟩

theorem hv_sec [X.IsSeparated] (hL : L.IsLB) {Y : Scheme.{0}} {φ : K → (Y ⟶ X)} (s : LB.Sec (LB.LinComb L φ ε))
    (r₀ : (TO hϖ hv).left ⟶ Y) {r : (TF (R := V) F).left ⟶ Y} (hr : (ιS hϖ hv).left ≫ r₀ = r) :
    ∃ x, 0 ≤ v x ∧ HV hϖ hv L (fun _ _ h => ∏ i, h (r ≫ φ i) ^ ε i) (fun z J => sval s r z J) x := by
  subst hr
  obtain ⟨t, ht⟩ := exists_gen_of_local (V := Ov v) L hL (fun i => r₀ ≫ φ i) ε
  have hi := invGen_isGen _ _ _ _ ht
  obtain ⟨a, ha, hav⟩ := sec_int hϖ hv hL (pullMulSec s r₀ _ hi) (fun U _ h => by
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
  refine ⟨a, ha, K, _, _, ε, t, ht, fun U _ h => by simp only [Category.assoc], fun z J hJ => ?_⟩
  have b := hav z J hJ
  rw [sval_pullMulSec _ _ _ hi _ z hJ, val_inv] at b
  rw [← b, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]

theorem hv_of_genV {φ : K → ((TF (R := V) F).left ⟶ X)} {t : LB.Gen (LB.LinComb L φ ε)} {r : ℚ}
    (H : GenV hϖ hv t r) :
    ∃ x, v x = r ∧ HV hϖ hv L (fun _ _ h => ∏ i, h (φ i) ^ ε i) (fun z J => (val t (𝟙 _) z J).val) x := by
  obtain ⟨φ₀, h₀, t₀, ht₀, x, hx, e⟩ := H
  exact ⟨x, hx, K, _, φ₀, ε, t₀, ht₀, fun U _ h => by simp only [h₀], e⟩

theorem genV_unique [X.IsSeparated] (hL : L.IsLB) {φ : K → ((TF (R := V) F).left ⟶ X)}
    {t : LB.Gen (LB.LinComb L φ ε)} {r r' : ℚ} (H : GenV hϖ hv t r) (H' : GenV hϖ hv t r') : r = r' := by
  obtain ⟨x, hx, a⟩ := hv_of_genV H
  obtain ⟨x', hx', a'⟩ := hv_of_genV H'
  have := a.cmp hL a' (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  rw [hx, hx'] at this
  exact_mod_cast this

theorem exists_genV (hL : L.IsLB) {φ : K → ((TF (R := V) F).left ⟶ X)} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen)
    (hφ : ∀ i, ∃ ψ, φ i = (ιS hϖ hv).left ≫ ψ) : ∃ r, GenV hϖ hv t r := by
  choose φ₀ h₀ using hφ
  obtain ⟨t₀, ht₀⟩ := exists_gen_of_local (V := Ov v) L hL φ₀ ε
  obtain ⟨c, hc, e⟩ := exists_ratio hL t ht (LB.pullGen L _ _ t₀ (ιS hϖ hv).left) (pullGen_isGen _ _ _ _ ht₀ _)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by rw [h₀])
  obtain ⟨q, hq⟩ := wt_coe_of_ne (v := v) hc
  refine ⟨q, φ₀, h₀, t₀, ht₀, c, hq, fun z J hJ => ?_⟩
  have := e (TF (R := V) F).left (𝟙 (TF (R := V) F).left) z J hJ
  rw [val_pull hJ, Category.id_comp] at this
  exact this

end GlobalTheory.UT.CoefVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGeneratorNeZero
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UT.ExactTerm
open GlobalTheory.ThetaPtMove

theorem gs_zero' {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) : gs r z U 0 = 0 := by
  rw [gs_eq r z U h, map_zero, map_zero]

theorem isUnit_top_of_ne_zero {K : Type} [Field K] {v : Γ(Spec (CommRingCat.of K), ⊤)} (hv : v ≠ 0) : IsUnit v := by
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2 v
  have hc : c ≠ 0 := fun h => hv (by rw [h, map_zero])
  exact (IsUnit.mk0 c hc).map _

theorem exists_good_point (hG : GoodPtSt) (hB : PolBaseChangeSt) {S : Scheme.{0}} (P : PolAV S) {K : Type} [Field K]
    [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) {n : ℕ} (hn : 2 ≤ n) (hK : (n : K) ≠ 0)
    (th₀ : LB.Sec (LPow P.A P.L 1 (Over.mk t))) (h₀ : SecM.ofSec P.A th₀ ≠ 0) (a : Over.mk t ⟶ P.A) :
    ∃ x : Over.mk t ⟶ P.A, x ^ n = 1 ∧ ∀ z J, Good P.L z J →
      IsUnit (VVRank.sv P.A th₀ (ptSecT P.A (a * x)).left z J) := by
  obtain ⟨Q, g, hg, -, hm, t', ht'⟩ := hB S _ t P
  have hp : IsGrpPullback Q.A P.A t g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    have ex : x₀ = Out.toBase hg.w x := Over.OverMorphism.ext hx
    have ey : y₀ = Out.toBase hg.w y := Over.OverMorphism.ext hy
    rw [ex, ey, ← hm]; rfl⟩
  obtain ⟨w, hw⟩ := LBIso.symm (⟨t', ht'⟩ : LBIso _ _)
  let τ : (baseOver (Spec (CommRingCat.of K))).left ⟶ (Over.mk t).left := 𝟙 _
  have : IsIso τ := inferInstanceAs (IsIso (𝟙 (Spec (CommRingCat.of K))))
  have hτ : τ ≫ (Over.mk t).hom = (baseOver (Spec (CommRingCat.of K))).hom ≫ t := rfl
  obtain ⟨th, hth⟩ := exists_secRel hp τ hτ hw P.isLB Q.isLB th₀
  have hne : SecM.ofSec Q.A th ≠ 0 := fun e => h₀ (ThetaAct.sv_ext P.isLB fun y J hJ => by
    obtain ⟨χ, -, h₂⟩ := WeilPull.exists_psi_inv hp τ hτ
    have h₂' : χ ≫ psi hp τ hτ = 𝟙 _ := h₂
    obtain ⟨J', hJ'⟩ := CoefBasic.exists_good' Q.isLB y
    have q := hth _ χ y J J' hJ hJ'
    have q₀ : VVRank.sv Q.A th χ y J' = 0 :=
      (congrArg (fun u => ThetaAct.sv u χ y J') e).trans
        (gs_zero' χ y _ (hJ'.mem (fun _ : Fin 1 => (snd _ Q.A).left) χ))
    rw [h₂', q₀, MulZeroClass.mul_zero] at q
    exact q.trans (gs_zero' _ y _ (hJ.mem (fun _ : Fin 1 => (snd _ P.A).left) (𝟙 _))).symm)
  let a' : baseOver (Spec (CommRingCat.of K)) ⟶ Q.A :=
    Over.homMk (hg.lift a.left (𝟙 _) ((Over.w a).trans (Category.id_comp t).symm)) (hg.lift_snd _ _ _)
  have ha : τ ≫ a.left = a'.left ≫ g := (Category.id_comp _).trans (hg.lift_fst _ _ _).symm
  obtain ⟨x', hx', ρ, v, -, hv, hv₀⟩ := hG K Q n hn hK th hne a'
  let x : Over.mk t ⟶ P.A := Over.homMk (x'.left ≫ g) (by
    rw [Category.assoc, hg.w, ← Category.assoc, Over.w x']; exact Category.id_comp _)
  have hx : τ ≫ x.left = x'.left ≫ g := Category.id_comp _
  refine ⟨x, ?_, fun z J hJ => ?_⟩
  · have e₁ := over_pow hp τ hτ hx n
    rw [hx', ← over_one hp τ hτ] at e₁
    exact Over.OverMorphism.ext ((cancel_epi τ).1 e₁)
  · obtain ⟨J', hJ'⟩ := CoefBasic.exists_good' Q.isLB z
    have q := hth _ (𝟙 _ ≫ (ptSecT Q.A (a' * x')).left) z J J' hJ hJ'
    rw [sv_of_isValueAt hv (𝟙 _) z hJ', Category.assoc, psi_ptSec hp τ hτ (over_mul hp τ hτ ha hx)] at q
    have e : 𝟙 _ ≫ τ ≫ (ptSecT P.A (a * x)).left = (ptSecT P.A (a * x)).left :=
      (Category.id_comp _).trans (Category.id_comp _)
    rw [e] at q
    rw [q, gs_eq _ z ⊤ trivial]
    exact (Units.isUnit _).mul ((((isUnit_top_of_ne_zero hv₀).map _).map _).mul (Units.isUnit _))

theorem exists_generator_ne_zero (hS : SecBaseChangeSt) {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (P : PolAV (Spec (CommRingCat.of R))) :
    ∃ β : LB.Sec (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 1)),
      (∀ s : LB.Sec (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 1)), ∃ c : R,
        ∀ (Z : Scheme.{0}) (r : Z ⟶ P.A.left) (z : Z) (J), Good P.L z J →
          sval s r z J = Geo.Tor.cst (r ≫ P.A.hom) z c * sval β r z J) ∧
      ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)),
        ∃ th : LB.Sec (LPow P.A P.L 1 (Over.mk t)), SecM.ofSec P.A th ≠ 0 ∧
          ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk t ⊗ P.A).left) (z : Z) (J), Good P.L z J →
            VVRank.sv P.A th r z J = sval β (r ≫ (snd (Over.mk t) P.A).left) z J := by
  obtain ⟨U, hU, b, hb⟩ := hS (Spec (CommRingCat.of R)) P 1 le_rfl (closedPoint R)
  obtain rfl : U = ⊤ := eq_top_of_closedPoint_mem U hU
  have hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  let i₀ : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤).left :=
    (Spec (CommRingCat.of R)).topIso.inv
  have hi : i₀ ≫ (overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤).hom = 𝟙 _ := by
    show (Spec (CommRingCat.of R)).topIso.inv ≫ (Scheme.Opens.ι ⊤ ≫ 𝟙 _) = 𝟙 _
    rw [Category.comp_id]
    exact (Spec (CommRingCat.of R)).topIso.inv_hom_id
  have hi' : (overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤).hom ≫ i₀ = 𝟙 _ := by
    show (Scheme.Opens.ι ⊤ ≫ 𝟙 _) ≫ (Spec (CommRingCat.of R)).topIso.inv = 𝟙 _
    rw [Category.comp_id]
    exact (Spec (CommRingCat.of R)).topIso.hom_inv_id
  let u : P.A ⟶ overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤ :=
    Over.homMk (P.A.hom ≫ i₀) (by rw [Category.assoc, hi, Category.comp_id])
  have uniq : ∀ {T : Over (Spec (CommRingCat.of R))} (p q : T ⟶ overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤),
      p = q := fun p q => Over.OverMorphism.ext (by
    rw [← Category.comp_id p.left, ← Category.comp_id q.left, ← hi', ← Category.assoc, ← Category.assoc, Over.w p,
      Over.w q])
  let β : LB.Sec (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 1)) :=
    VVRank.pullTo (φ := fun _ : Fin 1 => (snd (overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤) P.A).left)
      (ε := fun _ => 1) (b hq.default) (lift u (𝟙 P.A)).left
      (fun _ => congrArg (fun q => q.left) (lift_snd u (𝟙 P.A)))
  have key : ∀ (R' : Type) [CommRing R'] (t : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)),
      ∃ th : LB.Sec (LPow P.A P.L 1 (Over.mk t)),
        (∀ r : Γ((Over.mk t).left, ⊤), r • (SecM.ofSec P.A th : SecM P.A P.L 1 (Over.mk t)) = 0 → r = 0) ∧
        (∀ s : SecM P.A P.L 1 (Over.mk t), ∃ r : Γ((Over.mk t).left, ⊤), r • SecM.ofSec P.A th = s) ∧
        ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk t ⊗ P.A).left) (z : Z) (J), Good P.L z J →
          VVRank.sv P.A th r z J = sval β (r ≫ (snd (Over.mk t) P.A).left) z J := by
    intro R' _ t
    obtain ⟨t', rfl⟩ : ∃ t' : Spec (CommRingCat.of R') ⟶ (overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤).left,
        t' ≫ (overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤).hom = t :=
      ⟨t ≫ i₀, by rw [Category.assoc, hi, Category.comp_id]⟩
    obtain ⟨hli, hsp⟩ := hb R' t' (fun i => VVRank.pullS P.A _ (homAt t') (b i)) fun i =>
      VVRank.isPullSec_pullS _ _ _ _
    refine ⟨VVRank.pullS P.A _ (homAt t') (b hq.default), fun r hr => ?_, fun s => ?_, fun Z r z J hJ => ?_⟩
    · exact Fintype.linearIndependent_iff.1 hli (fun _ => r) (by rw [Fintype.sum_unique]; exact hr) hq.default
    · rw [Set.range_unique] at hsp
      exact Submodule.mem_span_singleton.1 (hsp.ge Submodule.mem_top)
    · have e : homAt t' ▷ P.A = snd (baseAt t') P.A ≫ lift u (𝟙 P.A) :=
        CartesianMonoidalCategory.hom_ext _ _ (uniq _ _) (by
          rw [whiskerRight_snd, Category.assoc, lift_snd, Category.comp_id])
      refine (VVRank.sv_pullS P.A _ (homAt t') _ r z hJ).trans (Eq.trans ?_ (VVRank.sval_pullTo _ _ _ _ z hJ).symm)
      rw [e, Over.comp_left, Category.assoc]
  refine ⟨β, fun s => ?_, fun K _ t => ?_⟩
  · obtain ⟨th, -, hsp, hv⟩ := key R (𝟙 _)
    obtain ⟨c, hc⟩ := hsp (SecM.ofSec P.A (VVRank.pullTo (φ' := fun _ : Fin 1 => (snd (Over.mk (𝟙 _)) P.A).left) s
      (snd (Over.mk (𝟙 _)) P.A).left fun _ => Category.comp_id _))
    obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2 c
    refine ⟨c, fun Z r z J hJ => ?_⟩
    let u' : P.A ⟶ Over.mk (𝟙 (Spec (CommRingCat.of R))) := Over.homMk P.A.hom (Category.comp_id _)
    have e₁ : (r ≫ (lift u' (𝟙 P.A)).left) ≫ (snd (Over.mk (𝟙 _)) P.A).left = r := by
      rw [Category.assoc, ← Over.comp_left, lift_snd]; exact Category.comp_id _
    have e₂ : (r ≫ (lift u' (𝟙 P.A)).left) ≫ (fst (Over.mk (𝟙 _)) P.A).left = r ≫ P.A.hom := by
      rw [Category.assoc, ← Over.comp_left, lift_fst]; rfl
    have q := (congrArg (fun w => ThetaAct.sv w (r ≫ (lift u' (𝟙 P.A)).left) z J) hc).symm.trans
      (ThetaAct.sv_smul _ _ _ z hJ)
    have q₁ := (VVRank.sval_pullTo s _ (fun _ => Category.comp_id _) _ z hJ).symm.trans
      (q.trans (congrArg₂ (· * ·) rfl (hv Z _ z J hJ)))
    rw [e₁, e₂] at q₁
    exact q₁
  · obtain ⟨th, hli, -, hv⟩ := key K t
    refine ⟨th, fun e => ?_, hv⟩
    have h1 := hli 1 (by rw [e, smul_zero])
    have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom h1
    exact one_ne_zero ((map_one _).symm.trans (h2.trans (map_zero _)))

theorem exists_secB_good (hL : Laws) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (D : DegPre R) (χ : D.X) : ∃ b : D.SecB 1 χ,
      (∀ σ : D.SecB 1 χ, ∃ c : R, ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
          sval σ r z J = Geo.Tor.cst (r ≫ D.P.A.hom) z c * sval b r z J) ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) (n : ℕ), 2 ≤ n →
        (n : K) ≠ 0 → ∀ a : Over.mk t ⟶ D.P.A, ∃ x : Over.mk t ⟶ D.P.A, x ^ n = 1 ∧
          ∀ z J, Good D.P.L z J → IsUnit (sval b (a * x).left z J) := by
  have hM := D.P.isLB
  obtain ⟨β, hβ, hβ'⟩ := exists_generator_ne_zero hL.secBaseChange D.P
  obtain ⟨ξ₀, hξ₀⟩ := exists_gen_of_local D.P.L hM (K := Fin 2)
    ![(D.c χ).left, (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left] ![-1, 1]
  obtain ⟨ξ, hξ, vξ⟩ := VVRank.exists_gen_pullTo (φ' := ![(SectionScalarValuation.cQ D D.P.A χ).left, (1 : D.P.A ⟶ D.P.A).left]) ξ₀ hξ₀
    D.P.A.hom (fun i => by
      fin_cases i
      · rfl
      · exact congrArg (fun q : D.P.A ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (toUnit D.P.A)))
  let τ : D.P.A ⟶ D.P.A := 𝟙 _ * SectionScalarValuation.cQ D D.P.A χ
  let τ' : D.P.A ⟶ D.P.A := 𝟙 _ * (SectionScalarValuation.cQ D D.P.A χ)⁻¹
  have hτ : ∀ {T : Over (Spec (CommRingCat.of R))} (y : T ⟶ D.P.A), y ≫ τ = y * SectionScalarValuation.cQ D T χ := fun y => by
    rw [MonObj.comp_mul, Category.comp_id, SectionScalarValuation.comp_cQ]
  have hττ : τ ≫ τ' = 𝟙 _ := by
    rw [MonObj.comp_mul, Category.comp_id, GrpObj.comp_inv, SectionScalarValuation.comp_cQ, mul_inv_cancel_right]
  obtain ⟨b, hb⟩ := exists_sec hM (φ' := D.famφB χ) (ε' := DegPre.famε 1) (fun U _ h => by
    have p := SectionScalarValuation.prod_famB D (𝟙 D.P.A) χ 1 h
    simp only [Over.id_left, Category.id_comp] at p
    rw [p, Fintype.prod_sum_type, Fin.prod_univ_one, Fin.prod_univ_two]
    simp [τ, _root_.mul_assoc]) (pullMulSec β τ.left ξ hξ)
  have vb : ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
      sval b r z J = sval β (r ≫ τ.left) z J * (val ξ r z J).val := fun Z r z J hJ =>
    (hb Z r z J hJ).trans (sval_pullMulSec _ _ _ hξ r z hJ)
  refine ⟨b, fun σ => ?_, fun K _ _ t n hn hK a => ?_⟩
  · obtain ⟨s, hs⟩ := exists_sec hM (φ' := fun _ : Fin 1 => 𝟙 D.P.A.left) (ε' := fun _ => 1) (fun U _ h => by
      have p := SectionScalarValuation.prod_famB D τ' χ 1 h
      have e : τ' * SectionScalarValuation.cQ D D.P.A χ = 𝟙 _ := inv_mul_cancel_right _ _
      rw [e] at p
      rw [Fintype.prod_sum_type, Fin.prod_univ_one, Fin.prod_univ_two]
      refine (congrArg₂ (· * ·) p rfl).trans ?_
      simp [_root_.mul_assoc, mul_left_comm]) (pullMulSec σ τ'.left _ (invGen_isGen _ _ _ _ hξ))
    obtain ⟨c, hc⟩ := hβ s
    refine ⟨c, fun Z r z J hJ => ?_⟩
    have q := (hc Z (r ≫ τ.left) z J hJ).symm.trans ((hs Z _ z J hJ).trans (sval_pullMulSec _ _ _ _ _ z hJ))
    rw [val_inv, vξ _ _ z J hJ, Category.assoc, Category.assoc, ← Over.comp_left, hττ, Over.w τ, Over.id_left,
      Category.comp_id, ← vξ _ _ z J hJ] at q
    rw [vb Z r z J hJ, ← _root_.mul_assoc, q, Units.inv_mul_cancel_right]
  · obtain ⟨th, h₀, hth⟩ := hβ' K t
    obtain ⟨x, hx, hu⟩ := exists_good_point hL.goodPt hL.polBaseChange D.P t hn hK th h₀ (a * SectionScalarValuation.cQ D _ χ)
    refine ⟨x, hx, fun z J hJ => ?_⟩
    have q := hu z J hJ
    rw [hth _ _ z J hJ, ptSecT_snd, mul_right_comm, ← hτ, Over.comp_left] at q
    rw [vb _ _ z J hJ]
    exact q.mul (Units.isUnit _)

theorem isUnit_gs_iff {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ X.basicOpen a := by
  rw [gs_eq r z U h]
  refine (Z.mem_basicOpen ((r.app U).hom a) z h).symm.trans ?_
  exact Iff.of_eq (congrArg (z ∈ ·) (Scheme.preimage_basicOpen r a).symm)

theorem exists_gen_of_isUnit {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) {O : Type} [CommRing O] [IsLocalRing O]
    (m : Spec (CommRingCat.of O) ⟶ Y)
    (h : ∀ z J, Good L z J → IsUnit (sval s (Spec.map (CommRingCat.ofHom (residue O)) ≫ m) z J)) :
    ∃ t : LB.Gen (LB.LinComb L (fun k => m ≫ φ k) ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of O)) (z : Z) (J), Good L z J →
        (val t r z J).val = sval s (r ≫ m) z J := by
  let s' := pullSec L φ ε s m
  let z₀ : Spec (CommRingCat.of (ResidueField O)) := closedPoint (ResidueField O)
  obtain ⟨J₀, hJ₀⟩ := CoefBasic.exists_good' hL z₀
  have h₀ := h z₀ J₀ hJ₀
  rw [← SectionScalarValuation.sval_pullSec φ ε s m _ z₀ hJ₀] at h₀
  have h₁ := (isUnit_gs_iff _ z₀ _ (hJ₀.mem (fun k => m ≫ φ k) _) _).1 h₀
  have e : Spec.map (CommRingCat.ofHom (residue O)) z₀ = closedPoint O := IsLocalRing.comap_closedPoint (residue O)
  rw [e] at h₁
  have h₂ := eq_top_of_closedPoint_mem _ h₁
  have hu : ∀ j, IsUnit (s'.f j) := fun j => (Spec (CommRingCat.of O)).toRingedSpace.isUnit_of_isUnit_germ _ _
    fun y hy => by
      have hy₀ := h₂.ge (Set.mem_univ y)
      have hy₁ := Scheme.basicOpen_le _ _ hy₀
      have q := sec_trans s' (𝟙 _) y hy hy₁
      exact (congrArg IsUnit ((gs_eq (𝟙 _) y (LB.wchart L (fun k => m ≫ φ k) j) hy _).symm.trans q)).mpr
        ((Units.isUnit _).mul ((isUnit_gs_iff (𝟙 _) y _ hy₁ _).2 hy₀))
  refine ⟨⟨fun j => (hu j).unit⟩, fun i j => Units.ext (s'.compat i j), fun Z r z J hJ => ?_⟩
  exact (gs_unit r z _ (hJ.mem (fun k => m ≫ φ k) r) _).symm.trans (SectionScalarValuation.sval_pullSec φ ε s m r z hJ)

end GlobalTheory.UT.ExactTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT
open GlobalTheory.TorusExt

theorem isTor_iff {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    (t : Multiplicative D.X →* Fˣ) (g : GtPtF D F) :
    IsTor t g ↔ IsTorusPtF g fun χ => t (Multiplicative.ofAdd χ) := by
  rw [isTorusPtF_iff_val]
  refine and_congr Iff.rfl (forall_congr' fun χ => forall_congr' fun y => forall_congr' fun J => forall_congr' fun _ => ?_)
  have e : ∀ x : F, cst (R := R) F y x = stalkConst (F := F) y x := fun x =>
    gs_eq (𝟙 _) y ⊤ trivial _
  rw [e]

theorem gt_onto_divisible_kernel : LL → AllD fun {R} _ _ {I} D F _ _ => (∀ b : TF (R := R) F ⟶ D.toPre.P.A, ∃ g : GtPtF D.toPre F, g.b = b) ∧ (∀ n, 1 ≤ n → ∀ g : GtPtF D.toPre F, ∃ g', GtPtF.IsNsmul n g' g) ∧ (∀ t, ∃! g : GtPtF D.toPre F, IsTor t g) ∧ (∀ g : GtPtF D.toPre F, g.b = 1 → ∃! t, IsTor t g) ∧ ∀ t t' (g g' g'' : GtPtF D.toPre F), IsTor t g → IsTor t' g' → (g.IsAdd g' g'' ↔ IsTor (t * t') g'') := by
  intro hL R _ _ _ I hA D F _ _ _
  refine ⟨exists_lift, fun n hn g => ?_, fun t => ?_, fun g hb => ?_, fun t t' g g' g'' h h' => ?_⟩
  · letI := gtGroup D.toPre F
    exact (exists_nsmul_eq hL.1.mulN (Or.inl hA.1) (by omega) g).imp fun _ e => (isNsmul_iff_eq _ _ _).2 e.symm
  · exact ⟨_, (isTor_iff _ _).2 (isTorusPtF_torusPt t), fun g h => (isTorusPtF_iff_eq g t).1 ((isTor_iff _ _).1 h)⟩
  · obtain ⟨t, ht⟩ := exists_isTorusPtF_of_b hb
    refine ⟨t, (isTor_iff _ _).2 ht, fun t' ht' => MonoidHom.ext fun χ => Units.ext ?_⟩
    exact congrFun (((isTor_iff _ _).1 ht').fun_unique ht) χ.toAdd
  · letI := gtGroup D.toPre F
    have a := ((isTor_iff _ _).1 h).add ((isTor_iff _ _).1 h')
    rw [isTor_iff]
    exact (isAdd_iff_eq _ _ _).trans ⟨fun e => e ▸ a, fun e => e.unique a⟩

end GlobalTheory.UT
end
end

