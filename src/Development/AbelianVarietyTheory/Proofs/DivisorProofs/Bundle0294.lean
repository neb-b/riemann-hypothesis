module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0268
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreservesFilteredColimitsAddCommGrpIffElements
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOneTraceOpenFiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0273
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormMulNormalisedAbsPowHalfEqOne
section
open MeasureTheory Matrix ValuativeRel

noncomputable section
namespace GlobalTheory.CharNormHalf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def normTwist (d : ℕ) (χ : kˣ →* ℂˣ) : kˣ →* ℂˣ where
  toFun x := Units.mk0 (((‖(χ x : ℂ)‖ : ℝ) : ℂ) * GlobalTheory.SplitFlip.apow x (-((d : ℂ) / 2)))
    (mul_ne_zero (by exact_mod_cast (norm_ne_zero_iff.2 (χ x).ne_zero)) (GlobalTheory.SplitFlip.apow_ne_zero _ _))
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    simp only [map_mul, Units.val_mul, norm_mul, Complex.ofReal_mul, Units.val_mk0, GlobalTheory.SplitFlip.apow_mul]
    ring

theorem normTwist_apply (d : ℕ) (χ : kˣ →* ℂˣ) (x : kˣ) :
    (normTwist d χ x : ℂ) = ((‖(χ x : ℂ)‖ : ℝ) : ℂ) * GlobalTheory.SplitFlip.apow x (-((d : ℂ) / 2)) := rfl

theorem norm_mul_apow_eq_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (χ : kˣ →* ℂˣ), (∀ u : kˣ, valuation k (u : k) = 1 → ‖(χ u : ℂ)‖ = 1) →
    ∀ ϖ : kˣ, GlobalTheory.SplitFlip.IsUnif ϖ → ‖(χ ϖ : ℂ)‖ ^ 2 * (GlobalTheory.SplitWeil.resCard k : ℝ) ^ d = 1 →
    ∀ x : kˣ, ‖(χ x : ℂ) * GlobalTheory.SplitFlip.apow x (-((d : ℂ) / 2))‖ = 1 := by
  intro k _ _ _ _ d χ hu ϖ hϖ hn x
  set B := normTwist d χ
  have hunr : ∀ y : kˣ, valuation k (y : k) = 1 → B y = 1 := by
    intro y hy
    ext
    rw [normTwist_apply, hu y hy, GlobalTheory.SplitFlip.apow_of_valuation_eq_one hy]
    simp
  have hq : (1 : ℝ) < (GlobalTheory.SplitWeil.resCard k : ℝ) := by exact_mod_cast GlobalTheory.SplitWeil.one_lt_resCard (k := k)
  set q : ℝ := (GlobalTheory.SplitWeil.resCard k : ℝ) with hqdef
  have hq0 : 0 < q := by linarith
  have hnabs : GlobalTheory.SplitWeil.nabs k ϖ = q⁻¹ := by
    rw [GlobalTheory.LGrp.nabs_eq_zpow, GlobalTheory.SmGL.ord_eq_one (k := k) hϖ]
    simp [hqdef]
  have hap : GlobalTheory.SplitFlip.apow ϖ (-((d : ℂ) / 2)) = ((q ^ ((d : ℝ) / 2) : ℝ) : ℂ) := by
    rw [GlobalTheory.SplitFlip.apow, hnabs, show (-((d : ℂ) / 2)) = ((-((d : ℝ) / 2) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (inv_nonneg.2 hq0.le), Real.inv_rpow hq0.le, ← Real.rpow_neg hq0.le, neg_neg]
  have hBϖ : B ϖ = 1 := by
    ext
    rw [normTwist_apply, hap, Units.val_one, ← Complex.ofReal_mul]
    have hb0 : 0 ≤ ‖(χ ϖ : ℂ)‖ * q ^ ((d : ℝ) / 2) := by positivity
    have hsq : (‖(χ ϖ : ℂ)‖ * q ^ ((d : ℝ) / 2)) ^ 2 = 1 := by
      rw [mul_pow, ← Real.rpow_natCast (q ^ ((d : ℝ) / 2)) 2, ← Real.rpow_mul hq0.le]
      rw [show (d : ℝ) / 2 * ((2 : ℕ) : ℝ) = ((d : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
      exact hn
    have := (pow_eq_one_iff_of_nonneg hb0 two_ne_zero).1 hsq
    rw [this]; simp
  have hB := GlobalTheory.SmGL.eq_unrChar (k := k) (χ := B) hunr hϖ
  have hx : B x = 1 := by
    rw [hB, hBϖ, GlobalTheory.SmGL.unrChar_apply, _root_.one_zpow]
  have hx' : ‖(B x : ℂ)‖ = 1 := by rw [hx]; simp
  rw [normTwist_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm] at hx'
  rw [norm_mul]; exact hx'

end GlobalTheory.CharNormHalf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmAOneApply
section
noncomputable section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil

namespace GlobalTheory.RankFibreKer

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def tw (ν : kˣ →* ℂˣ) (d : ℕ) {a : ℕ} (g : GL (Fin a) k) : ℂ :=
  (ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2)

def minor {a d : ℕ} (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d) : k := (Y.submatrix id J).det

def idx {a d : ℕ} : (Fin a ↪ Fin d) ≃ Fin (Fintype.card (Fin a ↪ Fin d)) := Fintype.equivFin _


variable (k) in
def slice (a d : ℕ) : Set (Matrix (Fin a) (Fin d) k) :=
  {Z | ∃ J : Fin a ↪ Fin d, Z.submatrix id J = 1 ∧ ∀ J' : Fin a ↪ Fin d,
    valuation k (minor Z J') ≤ 1 ∧ (idx J' < idx J → valuation k (minor Z J') < 1)}

def IsFirstMax {a d : ℕ} (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d) : Prop :=
  minor Y J ≠ 0 ∧ ∀ J' : Fin a ↪ Fin d, valuation k (minor Y J') ≤ valuation k (minor Y J) ∧
    (idx J' < idx J → valuation k (minor Y J') < valuation k (minor Y J))


open Classical in
def sec {a d : ℕ} (Y : Matrix (Fin a) (Fin d) k) : GL (Fin a) k := by
  classical
  exact if h : ∃ J, IsFirstMax Y J then
    GeneralLinearGroup.mkOfDetNeZero (Y.submatrix id h.choose) h.choose_spec.1
  else 1

theorem tw_mul (ν : kˣ →* ℂˣ) (d : ℕ) {a : ℕ} (g x : GL (Fin a) k) : tw ν d (g * x) = tw ν d g * tw ν d x := by
  simp only [tw, gdet_mul, map_mul, Units.val_mul, apow_mul]; ring

theorem tw_ne_zero (ν : kˣ →* ℂˣ) (d : ℕ) {a : ℕ} (g : GL (Fin a) k) : tw ν d g ≠ 0 :=
  mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)

theorem omA_one_apply (ν β : kˣ →* ℂˣ) {a b : ℕ} (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin (a + b)) k → ℂ)
    (Y : Matrix (Fin a) (Fin (a + b)) k) : omA ν β g 1 Ψ Y = (tw ν (a + b) g)⁻¹ * Ψ ((g⁻¹).val * Y) := by
  have e : apow (gdet g) (-(((a + b : ℕ)) : ℂ) / 2) = (apow (gdet g) (((a + b : ℕ) : ℂ) / 2))⁻¹ := by
    rw [neg_div, apow_neg]
  simp only [omA, tw, Fintype.card_fin, e, map_one, Units.val_one, apow_one, mul_one, invT_val, inv_one,
    transpose_one, Units.val_inv_eq_inv_val, mul_inv, Matrix.mul_one]

theorem minor_mul {a d : ℕ} (g : Matrix (Fin a) (Fin a) k) (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d) :
    minor (g * Y) J = g.det * minor Y J := by
  rw [minor, minor, ← det_mul]
  congr 1

end GlobalTheory.RankFibreKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairingHarishChandraInductionCharpolyFunctionStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_harishChandraInduction_charpolyFunction : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ), n = a + b → ∀ (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (S : F[X] → ℂ), (Nat.card (GL (Fin a) F) : ℂ) * (Nat.card (GL (Fin b) F) : ℂ) * ∑ᶠ x, hc a b α β n x * star (chG S n x) = (Nat.card (GL (Fin n) F) : ℂ) * ∑ᶠ x : GL (Fin a) F, ∑ᶠ y : GL (Fin b) F, α x * β y * star (S (Matrix.charpoly (x : Matrix (Fin a) (Fin a) F) * Matrix.charpoly (y : Matrix (Fin b) (Fin b) F))) := by
  first | (exact @GlobalTheory.Shin.Mass.mass) | (exact GlobalTheory.Shin.Mass.mass) | (intros; apply GlobalTheory.Shin.Mass.mass <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialOperatorFderivFormula
section
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff

noncomputable section

namespace GlobalTheory.SliceOpDeriv

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁']

theorem pd_padL_add (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (h h' : κ → V) :
    pd (padL (κ' := κ') (h + h')) f = pd (padL h) f + pd (padL h') f := by
  have e : (padL (κ' := κ') (h + h') : κ ⊕ κ' → V) = padL h + padL h' := by
    funext i; cases i <;> simp [padL]
  ext z
  rw [SchwartzMap.add_apply, pd_apply, pd_apply, pd_apply, e, map_add (f := _)]

theorem pd_padL_smul (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (c : ℝ) (h : κ → V) :
    pd (padL (κ' := κ') (c • h)) f = (c : ℂ) • pd (padL h) f := by
  have e : (padL (κ' := κ') (c • h) : κ ⊕ κ' → V) = c • padL h := by
    funext i; cases i <;> simp [padL]
  ext z
  rw [SchwartzMap.smul_apply, pd_apply, pd_apply, e, map_smul, Complex.real_smul, smul_eq_mul]

def xPartL (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ)
    (x : κ → V) (y : κ₁' → V) : (κ → V) →ₗ[ℝ] ℂ where
  toFun h := P (sliceR (pd (padL (κ' := κ') h) f) x) y
  map_add' h h' := by
    simp only [pd_padL_add, ← sliceRL_apply, map_add (f := _), SchwartzMap.add_apply]
  map_smul' c h := by
    simp only [pd_padL_smul, ← sliceRL_apply, map_smul, SchwartzMap.smul_apply, RingHom.id_apply,
      Complex.real_smul, smul_eq_mul]

variable [FiniteDimensional ℝ V]

def xPart (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ)
    (x : κ → V) (y : κ₁' → V) : (κ → V) →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap (xPartL P f x y)

theorem xPart_apply (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ)
    (x : κ → V) (y : κ₁' → V) (h : κ → V) :
    xPart P f x y h = P (sliceR (pd (padL (κ' := κ') h) f) x) y := rfl

end GlobalTheory.SliceOpDeriv

namespace GlobalTheory.SliceOpDeriv
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁']

theorem hasFDerivAt_sliceR_apply (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ)
    (x : κ → V) (y : κ₁' → V) :
    HasFDerivAt (fun x' => P (sliceR f x') y) (xPart P f x y) x := by
  obtain ⟨s', C, hC, hP⟩ := clm_sup_bound P {((0 : ℕ), (0 : ℕ))}
  set M : ℝ := s'.sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ m.1 (m.2 + 2)) f
  have hM : 0 ≤ M := by positivity
  have hb : ∀ h : κ → V, ‖P (sliceR f (x + h)) y - P (sliceR f x) y - xPart P f x y h‖ ≤ C * M * ‖h‖ ^ 2 := by
    intro h
    set D := sliceR f (x + h) - sliceR f x - sliceR (pd (padL (κ' := κ') h) f) x
    have e : P (sliceR f (x + h)) y - P (sliceR f x) y - xPart P f x y h = P D y := by
      simp only [D, xPart_apply, map_sub, SchwartzMap.sub_apply]
    rw [e]
    have h1 : ‖P D y‖ ≤ ({((0 : ℕ), (0 : ℕ))} : Finset (ℕ × ℕ)).sup (schwartzSeminormFamily ℂ (κ₁' → V) ℂ) (P D) := by
      simpa [schwartzSeminormFamily] using SchwartzMap.norm_le_seminorm ℂ (P D) y
    have h2 : s'.sup (schwartzSeminormFamily ℂ (κ' → V) ℂ) D ≤ ‖h‖ ^ 2 * M := by
      refine Seminorm.finset_sup_apply_le (by positivity) fun i hi => ?_
      refine (GlobalTheory.SliceTaylor.seminorm_slice_taylor_le V κ κ' f i.1 i.2 x h).trans ?_
      gcongr
      exact Seminorm.le_finset_sup_apply (p := fun m : ℕ × ℕ => (SchwartzMap.seminorm ℂ m.1 (m.2 + 2) : Seminorm ℂ (SchwartzMap (κ ⊕ κ' → V) ℂ))) (x := f) hi
    calc ‖P D y‖ ≤ C * s'.sup (schwartzSeminormFamily ℂ (κ' → V) ℂ) D := h1.trans (hP D)
      _ ≤ C * (‖h‖ ^ 2 * M) := mul_le_mul_of_nonneg_left h2 hC
      _ = C * M * ‖h‖ ^ 2 := by ring
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.IsBigO.trans_isLittleO ?_ (Asymptotics.isLittleO_norm_pow_id one_lt_two)
  refine Asymptotics.IsBigO.of_bound (C * M) (Filter.Eventually.of_forall fun h => ?_)
  refine (hb h).trans (le_of_eq ?_)
  rw [Real.norm_of_nonneg (by positivity)]

end GlobalTheory.SliceOpDeriv

namespace GlobalTheory.SliceOpDeriv
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁']

theorem continuous_elim_pair :
    Continuous (fun p : (κ → V) × (κ₁' → V) => (Sum.elim p.1 p.2 : κ ⊕ κ₁' → V)) := by
  refine continuous_pi fun i => ?_
  cases i with
  | inl i => simp only [Sum.elim_inl]; fun_prop
  | inr j => simp only [Sum.elim_inr]; fun_prop

theorem qOp_elim (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ)
    (x : κ → V) (y : κ₁' → V) : qOp P f (Sum.elim x y) = P (sliceR f x) y := by
  simp [qOp]

theorem continuous_xPart (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ)
    (f : SchwartzMap (κ ⊕ κ' → V) ℂ) :
    Continuous (fun p : (κ → V) × (κ₁' → V) => xPart P f p.1 p.2) := by
  refine continuous_clm_apply.2 fun h => ?_
  have e : (fun p : (κ → V) × (κ₁' → V) => xPart P f p.1 p.2 h) =
      fun p => qOp P (pd (padL (κ' := κ') h) f) (Sum.elim p.1 p.2) := by
    funext p; rw [qOp_elim, xPart_apply]
  rw [e]
  exact (continuous_qOp V κ κ' κ₁' P _).comp continuous_elim_pair

theorem continuous_yPart (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ)
    (f : SchwartzMap (κ ⊕ κ' → V) ℂ) :
    Continuous (fun p : (κ → V) × (κ₁' → V) => fderiv ℝ (P (sliceR f p.1)) p.2) := by
  refine continuous_clm_apply.2 fun w => ?_
  have e : (fun p : (κ → V) × (κ₁' → V) => fderiv ℝ (P (sliceR f p.1)) p.2 w) =
      fun p => qOp ((pd w).comp P) f (Sum.elim p.1 p.2) := by
    funext p; rw [qOp_elim, ContinuousLinearMap.comp_apply, pd_apply]
  rw [e]
  exact (continuous_qOp V κ κ' κ₁' _ _).comp continuous_elim_pair

def splitL : (κ ⊕ κ₁' → V) →L[ℝ] (κ → V) × (κ₁' → V) :=
  (ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ ⊕ κ₁' => V) (Sum.inl i)).prod
    (ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ ⊕ κ₁' => V) (Sum.inr j))

theorem hasFDerivAt_qOp (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ)
    (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (s : κ ⊕ κ₁' → V) :
    HasFDerivAt (qOp P f)
      (((xPart P f (s ∘ Sum.inl) (s ∘ Sum.inr)).coprod
        (fderiv ℝ (P (sliceR f (s ∘ Sum.inl))) (s ∘ Sum.inr))).comp splitL) s := by
  let F : (κ → V) → (κ₁' → V) → ℂ := fun x y => P (sliceR f x) y
  have key := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := splitL s) (f := F)
    (f₁ := fun x y => xPart P f x y) (f₂ := fun x y => fderiv ℝ (P (sliceR f x)) y)
    (Filter.Eventually.of_forall fun v => hasFDerivAt_sliceR_apply P f v.1 v.2)
    (Filter.Eventually.of_forall fun v => ((P (sliceR f v.1)).differentiableAt).hasFDerivAt)
    (continuous_xPart P f).continuousAt (continuous_yPart P f).continuousAt
  have h2 := key.hasFDerivAt.comp s ((splitL (V := V) (κ := κ) (κ₁' := κ₁')).hasFDerivAt (x := s))
  exact h2

end GlobalTheory.SliceOpDeriv

open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp in
theorem GlobalTheory.SliceOp.differentiable_qOp_and_fderiv : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (κ κ' κ₁' : Type) [Fintype κ] [Fintype κ'] [Fintype κ₁']
    (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ),
    Differentiable ℝ (qOp P f) ∧ ∀ (s v : κ ⊕ κ₁' → V),
      fderiv ℝ (qOp P f) s v = qOp P (pd (padL (κ' := κ') (v ∘ Sum.inl)) f) s + qOp ((pd (v ∘ Sum.inr)).comp P) f s := by
  intro V _ _ _ κ κ' κ₁' _ _ _ P f
  refine ⟨fun s => (GlobalTheory.SliceOpDeriv.hasFDerivAt_qOp P f s).differentiableAt, fun s v => ?_⟩
  rw [(GlobalTheory.SliceOpDeriv.hasFDerivAt_qOp P f s).fderiv]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coprod_apply]
  rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialSystemEventuallySolvableColimit
section
open CategoryTheory Limits TensorProduct

namespace GlobalTheory.TorsorColim

theorem poly_eventually_solvable :
    ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (j : J) (σ ι : Type) [Finite σ] [Finite ι] (p : ι → MvPolynomial σ (F.obj j)) (x : σ → c.pt),
    (∀ i, MvPolynomial.eval₂ (c.ι.app j).hom x (p i) = 0) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k), ∃ y : σ → F.obj k,
      ∀ i, MvPolynomial.eval₂ (F.map (f₀ ≫ f)).hom y (p i) = 0 := by
  classical
  intro J _ _ F c hc j σ ι _ _ p x hx
  haveI := Fintype.ofFinite σ
  haveI := Fintype.ofFinite ι
  have hc' := isColimitOfPreserves (forget _) hc

  choose jx x' hx' using fun s : σ => Types.jointly_surjective_of_isColimit hc' (x s)
  obtain ⟨K, hK⟩ := IsFiltered.sup_objs_exists (insert j (Finset.univ.image jx))
  obtain ⟨h⟩ := hK (Finset.mem_insert_self j _)
  have hm : ∀ s, Nonempty (jx s ⟶ K) := fun s =>
    hK (Finset.mem_insert_of_mem (Finset.mem_image_of_mem jx (Finset.mem_univ s)))
  let u : σ → F.obj K := fun s => (F.map (hm s).some).hom (x' s)
  have hu : ∀ s, (c.ι.app K).hom (u s) = x s := by
    intro s
    have h2 := congr(($(c.w (hm s).some)).hom (x' s))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
    rw [h2]
    exact hx' s

  have hz : ∀ i, (c.ι.app K).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = 0 := by
    intro i
    rw [MvPolynomial.eval₂_comp_left]
    have e1 : (c.ι.app K).hom.comp (F.map h).hom = (c.ι.app j).hom := by
      rw [← CommRingCat.hom_comp, c.w h]
    have e2 : ⇑(c.ι.app K).hom ∘ u = x := funext hu
    rw [e1, e2]; exact hx i

  have one : ∀ i, ∃ (k₀ : J) (f₀ : K ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      (F.map (f₀ ≫ f)).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = 0 := by
    intro i
    have h0 : (c.ι.app K).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = (c.ι.app K).hom 0 := by
      rw [hz i, map_zero]
    obtain ⟨k₀, f₀, e⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc' _ 0).1 (by exact h0)
    refine ⟨k₀, f₀, fun k f => ?_⟩
    have e' : (F.map f₀).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = 0 := by simpa using e
    rw [Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply, e', map_zero]

  have all : ∀ S : Finset ι, ∃ (k₀ : J) (f₀ : K ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      ∀ i ∈ S, (F.map (f₀ ≫ f)).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨K, 𝟙 K, fun _ _ i hi => absurd hi (Finset.notMem_empty i)⟩
    | insert a S _ ih =>
      obtain ⟨k₀, f₀, hh⟩ := eventually_and
        (fun k (g : K ⟶ k) => (F.map g).hom (MvPolynomial.eval₂ (F.map h).hom u (p a)) = 0)
        (fun k (g : K ⟶ k) => ∀ i ∈ S, (F.map g).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = 0)
        (one a) ih
      refine ⟨k₀, f₀, fun k f i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact (hh k f).1
      · exact (hh k f).2 i hi
  obtain ⟨k₀, f₀, h0⟩ := all Finset.univ
  refine ⟨k₀, h ≫ f₀, fun k f => ⟨fun s => (F.map (f₀ ≫ f)).hom (u s), fun i => ?_⟩⟩
  have := h0 k f i (Finset.mem_univ i)
  rw [MvPolynomial.eval₂_comp_left, ← CommRingCat.hom_comp, ← Functor.map_comp] at this
  rw [Category.assoc]
  exact this

end GlobalTheory.TorsorColim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreservesFilteredColimitsAddCommGrpIffElementsStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preservesFilteredColimits_addCommGrp_iff_elements : ∀ (T : Type 1) [Category.{0} T] (N : T ⥤ AddCommGrpCat.{1}), PreservesFilteredColimitsOfSize.{0, 0} N ↔ ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ T) (c : Cocone D), IsColimit c → (∀ x : N.obj c.pt, ∃ j y, N.map (c.ι.app j) y = x) ∧ ∀ j (y : N.obj (D.obj j)), N.map (c.ι.app j) y = 0 → ∃ (k : J) (f : j ⟶ k), N.map (D.map f) y = 0 := by
  first | (exact @GlobalTheory.EtC.FilteredElements.preservesFilteredColimits_iff_elements) | (exact GlobalTheory.EtC.FilteredElements.preservesFilteredColimits_iff_elements) | (intros; apply GlobalTheory.EtC.FilteredElements.preservesFilteredColimits_iff_elements  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdRootPowerSumMapGaloisEqStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_rootPowerSum_map_galois_eq : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (θ : AlgebraicClosure F' →* ℂ) (k : ℕ) (P : F'[X]), ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F')) = ∏ j ∈ Finset.range (Module.finrank F F'), rootSum θ (k * Nat.card F ^ j) P := by
  first | (exact @GlobalTheory.Shin.prod_rootSum_map_algEquiv) | (exact GlobalTheory.Shin.prod_rootSum_map_algEquiv) | (intros; apply GlobalTheory.Shin.prod_rootSum_map_algEquiv  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOneTraceOpenFiniteAdeleRingStatement
section
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternionNormOneTraceOpen_finiteAdeleRing : ∀ (F : Type) [Field F] [NumberField F] (a b : F), (∀ v : HeightOneSpectrum (𝓞 F), TraceOpen (v.adicCompletion F) (algebraMap F (v.adicCompletion F) a) (algebraMap F (v.adicCompletion F) b)) → (∀ᶠ v in (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))), ∀ t ∈ v.adicCompletionIntegers F, ∃ u : ℍ[v.adicCompletion F, algebraMap F (v.adicCompletion F) a, algebraMap F (v.adicCompletion F) b], nrm u = 1 ∧ u.re = t ∧ u.imI ∈ v.adicCompletionIntegers F ∧ u.imJ ∈ v.adicCompletionIntegers F ∧ u.imK ∈ v.adicCompletionIntegers F) → TraceOpen (FiniteAdeleRing (𝓞 F) F) (algebraMap F (FiniteAdeleRing (𝓞 F) F) a) (algebraMap F (FiniteAdeleRing (𝓞 F) F) b) := by
  first | exact @GlobalTheory.QSA.FinAdele.traceOpen_finiteAdele | exact GlobalTheory.QSA.FinAdele.traceOpen_finiteAdele | (intros; apply GlobalTheory.QSA.FinAdele.traceOpen_finiteAdele <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeGenericPointStalkSubsetOfDenseOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.range_genericPoint_stalk_subset_of_denseOpen : ∀ {U S : Scheme.{0}} [GlobalTheory.IsNormalScheme S] [IsLocallyNoetherian S] (j : U ⟶ S) [IsOpenImmersion j], Dense (Set.range j) → ∀ s : S, Set.range (ReciprocityTheory.ChartRestriction.G.Out.jK (S.presheaf.stalk s) ≫ S.fromSpecStalk s) ⊆ Set.range j := by
  first | exact @GlobalTheory.range_jK_fromSpecStalk_subset_of_dense_range | exact GlobalTheory.range_jK_fromSpecStalk_subset_of_dense_range | (intros; apply GlobalTheory.range_jK_fromSpecStalk_subset_of_dense_range <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatLintegralSqNeTop
section
open MeasureTheory Matrix ValuativeRel

namespace GlobalTheory.SBNorm

theorem schwartzBruhat_memL2_inner_self : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}
    (μ : @Measure (Fin n × Fin d → k) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ f ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k),
      ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ ⊤ ∧
      ∫ y, f y * (starRingEnd ℂ) (f y) ∂μ = (((∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ) ∧
      (f ≠ 0 → ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ 0) ∧
      ∀ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), Integrable (fun y => f y * (starRingEnd ℂ) (g y)) μ := by
  intro k _ _ _ _ n d μ hμ f hf
  letI : MeasurableSpace (Fin n × Fin d → k) := borel _
  haveI : BorelSpace (Fin n × Fin d → k) := ⟨rfl⟩
  haveI := hμ
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hfc : Continuous f := hf.1.continuous
  have hint : ∀ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), Integrable (fun y => f y * (starRingEnd ℂ) (g y)) μ := by
    intro g hg
    have hgc : Continuous g := hg.1.continuous
    exact (hfc.mul (Complex.continuous_conj.comp hgc)).integrable_of_hasCompactSupport
      (hf.2.mul_right (f' := fun y => (starRingEnd ℂ) (g y)))
  have hpt : ∀ y, ‖f y * (starRingEnd ℂ) (f y)‖ₑ = ‖f y‖ₑ ^ 2 := by
    intro y
    rw [enorm_mul, pow_two]
    congr 1
    simp [enorm_eq_nnnorm]
  have hfin : ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ ⊤ := by
    have := (hint f hf).2
    unfold HasFiniteIntegral at this
    simp_rw [hpt] at this
    exact this.ne
  refine ⟨hfin, ?_, ?_, hint⟩
  · have h1 : ∀ y, f y * (starRingEnd ℂ) (f y) = (((‖f y‖ ^ 2 : ℝ)) : ℂ) := by
      intro y
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp_rw [h1]
    rw [integral_complex_ofReal]
    congr 1
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun y => ‖f y‖ ^ 2)
      (Filter.Eventually.of_forall fun y => by positivity)
      ((hfc.norm.pow 2).aestronglyMeasurable)]
    congr 1
    apply lintegral_congr
    intro y
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  · intro hne
    obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne (funext h)
    have hmeas : Measurable fun y => ‖f y‖ₑ ^ 2 := (hfc.measurable.enorm).pow_const 2
    rw [← pos_iff_ne_zero, lintegral_pos_iff_support hmeas]
    have hsupp : Function.support (fun y => ‖f y‖ₑ ^ 2) = f ⁻¹' {0}ᶜ := by
      ext y
      simp
    rw [hsupp]
    exact (hf.1 ({0}ᶜ)).measure_pos μ ⟨x, hx⟩

end GlobalTheory.SBNorm
end

