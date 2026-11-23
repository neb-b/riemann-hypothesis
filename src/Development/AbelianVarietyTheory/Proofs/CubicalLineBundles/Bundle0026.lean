module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LocZeroTranslDiffComp
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.TripleProd

open GlobalTheory.CechPic

section Local

variable {Y Y' B B' : Scheme.{0}}

def LocZero (π : Y ⟶ B) (c : Pic Y) : Prop :=
  ∀ p : B, ∃ V : B.Opens, p ∈ V ∧ pull (π ⁻¹ᵁ V).ι c = 0

theorem pull_eq_zero_of_range {W : Y.Opens} {c : Pic Y} (H : pull W.ι c = 0) (h : Y' ⟶ Y) (hW : ∀ y, h y ∈ W) :
    pull h c = 0 := by
  have hr : Set.range h ⊆ Set.range W.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hW y
  rw [← IsOpenImmersion.lift_fac W.ι h hr, pull_comp, H, map_zero]

theorem LocZero.sub {π : Y ⟶ B} {c d : Pic Y} (H : LocZero π c) (H' : LocZero π d) : LocZero π (c - d) := by
  intro p
  obtain ⟨V, hV, t⟩ := H p
  obtain ⟨V', hV', t'⟩ := H' p
  refine ⟨V ⊓ V', ⟨hV, hV'⟩, ?_⟩
  rw [map_sub, pull_eq_zero_of_range t (π ⁻¹ᵁ (V ⊓ V')).ι fun y => y.2.1,
    pull_eq_zero_of_range t' (π ⁻¹ᵁ (V ⊓ V')).ι fun y => y.2.2, sub_zero]

theorem LocZero.pull_over {π : Y ⟶ B} {c : Pic Y} (H : LocZero π c) {π' : Y' ⟶ B} (h : Y' ⟶ Y) (sq : h ≫ π = π') :
    LocZero π' (pull h c) := by
  subst sq
  intro p
  obtain ⟨V, hV, t⟩ := H p
  refine ⟨V, hV, ?_⟩
  rw [← pull_comp]
  exact pull_eq_zero_of_range t _ fun y => y.2

theorem locZero_base (π : Y ⟶ B) (c : Pic B) : LocZero π (pull π c) := by
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  intro p
  obtain ⟨i, hi⟩ := exists_chart hL p
  refine ⟨L.U i, hi, ?_⟩
  rw [← pull_comp]
  exact (cls_eq_zero_iff (pull_isLB hL _)).2
    (BoxKernel.gen_of_chart (pull_isLB hL _) (fun _ => i) fun y => mem_pull.2 y.2)

theorem locZero_iff (π : Y ⟶ B) {N : LB Y} (hN : N.IsLB) :
    (∀ p : B, ∃ V : B.Opens, p ∈ V ∧ ∃ c : LB.Gen (N.pull (π ⁻¹ᵁ V).ι), c.IsGen) ↔ LocZero π (cls N hN) :=
  forall_congr' fun _ => exists_congr fun _ => and_congr_right fun _ =>
    (cls_eq_zero_iff (pull_isLB hN _)).symm

end Local

section Kernel

variable {S : Scheme.{0}} {A G H : Over S} [GrpObj A] [GrpObj G] [GrpObj H]

theorem cls_translDiff {L : LB A.left} (hL : L.IsLB) {T : Over S} (x : T ⟶ A) :
    cls (Out.translDiff A L x) (LB.isLB_linComb hL _ _) =
      pull ((fst T A ≫ x) * snd T A).left (cls L hL) - pull (snd T A).left (cls L hL) := by
  refine (cls_linComb hL _ _ _).trans ?_
  rw [Fin.sum_univ_two]
  show (1 : ℤ) • pull ((fst T A ≫ x) * snd T A).left (cls L hL) + (-1 : ℤ) • pull (snd T A).left (cls L hL) = _
  rw [one_zsmul, neg_one_zsmul, sub_eq_add_neg]

theorem locZero_translDiff_comp {N : LB A.left} {L : LB G.left} (hN : N.IsLB) (hL : L.IsLB) (b : Pic H.left)
    (p : A ⟶ G) (q : A ⟶ H) [IsMonHom p] [IsMonHom q] (u : G ⟶ A) (hp : u ≫ p = 𝟙 G) (hq : u ≫ q = 1)
    (e : cls N hN = pull p.left (cls L hL) + pull q.left b) {T : Over S} (x : T ⟶ A)
    (hx : LocZero (fst T A).left (cls (Out.translDiff A N x) (LB.isLB_linComb hN _ _))) :
    LocZero (fst T G).left (cls (Out.translDiff G L (x ≫ p)) (LB.isLB_linComb hL _ _)) := by
  have H₁ := hx.pull_over (π' := (fst T G).left) (T ◁ u).left (congrArg (fun q => q.left) (whiskerLeft_fst T u))
  have H₂ := (H₁.sub (locZero_base (fst T G).left (pull (x ≫ q).left b))).sub
    (locZero_base (fst T G).left (-pull (1 : T ⟶ H).left b))
  have e₁ : T ◁ u ≫ ((fst T A ≫ x) * snd T A) ≫ p = (fst T G ≫ x ≫ p) * snd T G := by
    rw [MonObj.mul_comp, MonObj.comp_mul, Category.assoc, whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, hp,
      Category.comp_id]
  have e₂ : T ◁ u ≫ ((fst T A ≫ x) * snd T A) ≫ q = fst T G ≫ x ≫ q := by
    rw [MonObj.mul_comp, MonObj.comp_mul, Category.assoc, whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, hq,
      MonObj.comp_one, _root_.mul_one]
  have e₃ : T ◁ u ≫ snd T A ≫ p = snd T G := by rw [whiskerLeft_snd_assoc, hp, Category.comp_id]
  have e₄ : T ◁ u ≫ snd T A ≫ q = fst T G ≫ (1 : T ⟶ H) := by
    rw [whiskerLeft_snd_assoc, hq, MonObj.comp_one, MonObj.comp_one]
  convert H₂ using 1
  rw [cls_translDiff hL, cls_translDiff hN, e]
  simp only [map_sub, map_add (f := _), map_neg, ← pull_comp, ← Over.comp_left, e₁, e₂, e₃, e₄]
  abel

theorem kTriv_prod {N : LB (G ⊗ H).left} {L : LB G.left} {L' : LB H.left} (hN : N.IsLB) (hL : L.IsLB)
    (hL' : L'.IsLB) (e : cls N hN = pull (fst G H).left (cls L hL) + pull (snd G H).left (cls L' hL'))
    (hK : Out.KTriv G L) (hK' : Out.KTriv H L') : Out.KTriv (G ⊗ H) N := by
  intro R _ t x hx
  have hx' := (locZero_iff _ (LB.isLB_linComb hN _ _)).1 hx
  have h₁ : x ≫ fst G H = 1 := hK R t _ ((locZero_iff _ (LB.isLB_linComb hL _ _)).2
    (locZero_translDiff_comp hN hL _ (fst G H) (snd G H) (lift (𝟙 G) 1) (lift_fst _ _) (lift_snd _ _) e x hx'))
  have h₂ : x ≫ snd G H = 1 := hK' R t _ ((locZero_iff _ (LB.isLB_linComb hL' _ _)).2
    (locZero_translDiff_comp hN hL' _ (snd G H) (fst G H) (lift 1 (𝟙 H)) (lift_snd _ _) (lift_fst _ _)
      (e.trans (add_comm _ _)) x hx'))
  show x = 1
  apply CartesianMonoidalCategory.hom_ext
  · rw [h₁, MonObj.one_comp]
  · rw [h₂, MonObj.one_comp]

end Kernel

section Cube

variable {S : Scheme.{0}} {A G : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj G] [IsCommMonObj G] {n : ℕ}

def cubeCls {T : Over S} (x : Fin n → (T ⟶ G)) (c : Pic G.left) : Pic T.left :=
  ∑ I : ULift.{0} (Finset (Fin n)), ((-1 : ℤ) ^ (n - I.down.card)) • pull (psum G x I.down).left c

theorem cls_cubeLB {T : Over S} (x : Fin n → (T ⟶ G)) {L : LB G.left} (hL : L.IsLB) :
    cls (cubeLB G x L) (LB.isLB_linComb hL _ _) = cubeCls x (cls L hL) :=
  cls_linComb hL _ _ _

theorem pull_cubeCls {T T' : Over S} (ρ : T' ⟶ T) (x : Fin n → (T ⟶ G)) (c : Pic G.left)
    (y : Fin n → (T' ⟶ G)) (h : ∀ i, y i = ρ ≫ x i) : cubeCls y c = pull ρ.left (cubeCls x c) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [cubeCls, cubeCls, map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_zsmul, ← pull_comp, PrimNorm.psum_pre ρ x y h]

end Cube

section Triple

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} (t : SAB H S) {T : Over S}

end Triple

end GlobalTheory.TripleProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilEqIffHermFormEqComplex
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.HermWeil

section Unif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem ex_zero : u.ex 0 = 1 := by
  have h := u.ex_add 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem ex_natSmul (n : ℕ) (z : Fin g → ℂ) : u.ex ((n : ℂ) • z) = u.ex z ^ n := by
  induction n with
  | zero => simp [ex_zero]
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, u.ex_add, ih, pow_succ]

theorem ex_div_pow {n : ℕ} (hn : 0 < n) (a : u.Λ) : u.ex ((n : ℂ)⁻¹ • (a : Fin g → ℂ)) ^ n = 1 := by
  rw [← ex_natSmul, smul_inv_smul₀ (Nat.cast_ne_zero.2 hn.ne')]
  exact (u.ker _).2 a.2

theorem exists_eq_ex_div {n : ℕ} (hn : 0 < n) (x : 𝟙_ (Over (Sp ℂ)) ⟶ A) (hx : x ^ n = 1) :
    ∃ a : u.Λ, x = u.ex ((n : ℂ)⁻¹ • (a : Fin g → ℂ)) := by
  obtain ⟨z, rfl⟩ := u.ex_onto x
  refine ⟨⟨(n : ℂ) • z, (u.ker _).1 (by rw [ex_natSmul, hx])⟩, ?_⟩
  rw [inv_smul_smul₀ (Nat.cast_ne_zero.2 hn.ne')]

theorem map_mem {B : Over (Sp ℂ)} [GrpObj B] {M : LB B.left} {g' : ℕ} (v : HolUnif B M g') {f : A ⟶ B}
    {F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)} (hF : ∀ z, v.ex (F z) = u.ex z ≫ f) (a : u.Λ) : F a ∈ v.Λ := by
  rw [← v.ker, hF, (u.ker _).2 a.2, ← ex_zero u, ← hF, map_zero, ex_zero]

end Unif

def rootVal (m : ℤ) (n : ℕ) : ℂˣ :=
  Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / n)) (Complex.exp_ne_zero _)

theorem eq_of_rootVal {m m' : ℤ} (h : ∀ n : ℕ, 0 < n → rootVal m n = rootVal m' n) : m = m' := by
  have key : ∀ n : ℕ, 0 < n → (n : ℤ) ∣ m' - m := by
    intro n hn
    have e := congrArg Units.val (h n hn)
    simp only [rootVal, Units.val_mk0] at e
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.1 e
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    refine ⟨k, ?_⟩
    have : ((m' - m : ℤ) : ℂ) = ((n * k : ℤ) : ℂ) := by
      push_cast
      refine mul_left_cancel₀ Complex.two_pi_I_ne_zero ?_
      field_simp at hk
      linear_combination (2 * Real.pi * Complex.I) * hk
    exact_mod_cast this
  have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (key ((m' - m).natAbs + 1) (Nat.succ_pos _))
    (by rw [Int.natAbs_natCast]; omega)
  omega

theorem hermForm_eq_of_im {p q a b : ℕ} (HA : Matrix (Fin a) (Fin a) ℂ) (HB : Matrix (Fin b) (Fin b) ℂ)
    (F₁ : (Fin p → ℂ) →ₗ[ℂ] (Fin a → ℂ)) (F₂ : (Fin q → ℂ) →ₗ[ℂ] (Fin a → ℂ))
    (G₁ : (Fin p → ℂ) →ₗ[ℂ] (Fin b → ℂ)) (G₂ : (Fin q → ℂ) →ₗ[ℂ] (Fin b → ℂ))
    {S : Set (Fin p → ℂ)} {T : Set (Fin q → ℂ)} (hS : Submodule.span ℝ S = ⊤) (hT : Submodule.span ℝ T = ⊤)
    (h : ∀ z ∈ S, ∀ w ∈ T, (hermForm HA (F₁ z) (F₂ w)).im = (hermForm HB (G₁ z) (G₂ w)).im) (z w) :
    hermForm HA (F₁ z) (F₂ w) = hermForm HB (G₁ z) (G₂ w) := by
  have him : ∀ z w, (hermForm HA (F₁ z) (F₂ w)).im = (hermForm HB (G₁ z) (G₂ w)).im := by
    intro z w
    have hz : z ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    have hw : w ∈ Submodule.span ℝ T := hT ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz =>
      induction hw using Submodule.span_induction with
      | mem w hw => exact h z hz w hw
      | zero => simp [hermForm]
      | add x y _ _ hx hy =>
        simp only [hermForm, map_add (f := _), star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_im] at hx hy ⊢
        rw [hx, hy]
      | smul r x _ hx =>
        rw [← Complex.coe_smul]
        simp only [hermForm, map_smul, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul,
          Complex.star_def, Complex.conj_ofReal, Complex.im_ofReal_mul] at hx ⊢
        rw [hx]
    | zero => simp [hermForm]
    | add x y _ _ hx hy =>
      simp only [hermForm, map_add (f := _), add_dotProduct, Complex.add_im] at hx hy ⊢
      rw [hx, hy]
    | smul r x _ hx =>
      rw [← Complex.coe_smul]
      simp only [hermForm, map_smul, smul_dotProduct, smul_eq_mul, Complex.im_ofReal_mul] at hx ⊢
      rw [hx]
  refine Complex.ext ?_ (him z w)
  have e := him (Complex.I • z) w
  simpa only [hermForm, map_smul, smul_dotProduct, smul_eq_mul, Complex.I_mul_im] using e

theorem weilIs_iff (hU : ThetaUnifAV) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g)
    {Hm : Matrix (Fin P.g) (Fin P.g) ℂ} {χ : u.Λ → ℂ} (h : u.IsAH Hm χ) (a b : u.Λ) :
    ∃ m : ℤ, (m : ℝ) = (hermForm Hm a b).im ∧ ∀ (n : ℕ) (c : ℂˣ), 0 < n →
      (Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • (a : Fin P.g → ℂ))) (u.ex ((n : ℂ)⁻¹ • (b : Fin P.g → ℂ))) (unitOn c) ↔
        c = rootVal m n) := by
  obtain ⟨Ef, hE, -, -, -, -, hW⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hU P P.g u Hm χ h
  refine ⟨Ef a b, hE a b, fun n c hn => ⟨fun hc => ?_, fun hc => hW n a b c hn (by rw [hc]; rfl)⟩⟩
  exact weilIs_unique_fieldPoint (Sp ℂ) P.A P.L P.isLB ℂ (𝟙 _) n _ _ c _ hc (hW n a b (rootVal (Ef a b) n) hn rfl)

end GlobalTheory.CM.HermWeil

namespace GlobalTheory.CM
open HermWeil

theorem weilEq_iff_hermForm_eq : ThetaUnifAV → Out.Laws → ∀ (X Y A B : Out.PolAV (Sp ℂ)) (uX : HolUnif X.A X.L X.g) (uY : HolUnif Y.A Y.L Y.g) (uA : HolUnif A.A A.L A.g) (uB : HolUnif B.A B.L B.g) (HA : Matrix (Fin A.g) (Fin A.g) ℂ) (HB : Matrix (Fin B.g) (Fin B.g) ℂ) (χA : uA.Λ → ℂ) (χB : uB.Λ → ℂ), uA.IsAH HA χA → uB.IsAH HB χB →
  ∀ (f₁ : X.A ⟶ A.A) (f₂ : Y.A ⟶ A.A) (g₁ : X.A ⟶ B.A) (g₂ : Y.A ⟶ B.A) (F₁ : (Fin X.g → ℂ) →ₗ[ℂ] (Fin A.g → ℂ)) (F₂ : (Fin Y.g → ℂ) →ₗ[ℂ] (Fin A.g → ℂ)) (G₁ : (Fin X.g → ℂ) →ₗ[ℂ] (Fin B.g → ℂ)) (G₂ : (Fin Y.g → ℂ) →ₗ[ℂ] (Fin B.g → ℂ)),
  (∀ z, uA.ex (F₁ z) = uX.ex z ≫ f₁) → (∀ z, uA.ex (F₂ z) = uY.ex z ≫ f₂) → (∀ z, uB.ex (G₁ z) = uX.ex z ≫ g₁) → (∀ z, uB.ex (G₂ z) = uY.ex z ≫ g₂) →
  (WeilEq A.L f₁ f₂ B.L g₁ g₂ (𝟙 (Sp ℂ)) ↔ ∀ z w, hermForm HA (F₁ z) (F₂ w) = hermForm HB (G₁ z) (G₂ w)) := by
  intro hU _ X Y A B uX uY uA uB HA HB χA χB hA hB f₁ f₂ g₁ g₂ F₁ F₂ G₁ G₂ h₁ h₂ h₃ h₄
  have key : ∀ (a : uX.Λ) (b : uY.Λ), ∃ m m' : ℤ, (m : ℝ) = (hermForm HA (F₁ a) (F₂ b)).im ∧
      (m' : ℝ) = (hermForm HB (G₁ a) (G₂ b)).im ∧ ∀ (n : ℕ) (c : ℂˣ), 0 < n →
      (Out.WeilIs A.A A.L n (uX.ex ((n : ℂ)⁻¹ • (a : Fin X.g → ℂ)) ≫ f₁)
        (uY.ex ((n : ℂ)⁻¹ • (b : Fin Y.g → ℂ)) ≫ f₂) (unitOn c) ↔ c = rootVal m n) ∧
      (Out.WeilIs B.A B.L n (uX.ex ((n : ℂ)⁻¹ • (a : Fin X.g → ℂ)) ≫ g₁)
        (uY.ex ((n : ℂ)⁻¹ • (b : Fin Y.g → ℂ)) ≫ g₂) (unitOn c) ↔ c = rootVal m' n) := by
    intro a b
    obtain ⟨m, hm, hw⟩ := weilIs_iff hU A uA hA ⟨_, map_mem uX uA h₁ a⟩ ⟨_, map_mem uY uA h₂ b⟩
    obtain ⟨m', hm', hw'⟩ := weilIs_iff hU B uB hB ⟨_, map_mem uX uB h₃ a⟩ ⟨_, map_mem uY uB h₄ b⟩
    refine ⟨m, m', hm, hm', fun n c hn => ?_⟩
    rw [← h₁, ← h₂, ← h₃, ← h₄, map_smul, map_smul, map_smul, map_smul]
    exact ⟨hw n c hn, hw' n c hn⟩
  constructor
  · intro h
    refine hermForm_eq_of_im HA HB F₁ F₂ G₁ G₂ uX.full uY.full fun a ha b hb => ?_
    obtain ⟨m, m', hm, hm', hw⟩ := key ⟨a, ha⟩ ⟨b, hb⟩
    rw [← hm, ← hm', eq_of_rootVal (m := m) (m' := m') fun n hn => ?_]
    exact (hw n _ hn).2.1 ((h n _ _ _ hn (ex_div_pow uX hn ⟨a, ha⟩) (ex_div_pow uY hn ⟨b, hb⟩)).1
      ((hw n _ hn).1.2 rfl))
  · intro h n x y c hn hx hy
    obtain ⟨a, rfl⟩ := exists_eq_ex_div uX hn x hx
    obtain ⟨b, rfl⟩ := exists_eq_ex_div uY hn y hy
    obtain ⟨m, m', hm, hm', hw⟩ := key a b
    obtain rfl : m = m' := by
      have : (m : ℝ) = m' := by rw [hm, hm', h]
      exact_mod_cast this
    exact (hw n c hn).1.trans (hw n c hn).2.symm

end GlobalTheory.CM
end
end

