module

public import Development.WeilBound.ThetaLifts.Reductions.Bundle0001
public import Development.WeilBound.ThetaLifts.CartanFactorisation.TensMax

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.Reductions.IsoOfIntegral
section
noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform

namespace PositivityTheory.ThKR.LL

variable {l : Type} [Fintype l]

abbrev Eu (l : Type) : Type := EuclideanSpace ℝ l

def rf (p q : Eu l) (f : Eu l → ℂ) : Eu l → ℂ :=
  fun x => exp (((2 * π * ⟪q, x⟫ + π * ⟪p, q⟫ : ℝ) : ℂ) * I) * f (x + p)

theorem rhoFun_eq (w : l ⊕ l → ℝ) (f : Eu l → ℂ) : rhoFun w f = rf (pPart w) (qPart w) f := rfl

def Intw (S : Sch l →L[ℂ] Sch l) (p q p' q' : Eu l) : Prop :=
  ∀ f g : Sch l, ⇑g = rf p q f → ⇑(S g) = rf p' q' (S f)

def Iso (S : Sch l →L[ℂ] Sch l) : Prop := ∀ f, ‖schwartzToL2 l (S f)‖ = ‖schwartzToL2 l f‖

theorem Intw.mul {S T : Sch l →L[ℂ] Sch l} {p q p' q' p'' q'' : Eu l} (hS : Intw S p' q' p'' q'') (hT : Intw T p q p' q') :
    Intw (S * T) p q p'' q'' := fun f g h => hS _ _ (hT f g h)

theorem Intw.smul {S : Sch l →L[ℂ] Sch l} {p q p' q' : Eu l} (hS : Intw S p q p' q') (c : ℂ) :
    Intw (c • S) p q p' q' := fun f g h => by
  funext x
  have := congrFun (hS f g h) x
  simp only [rf, ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply, smul_eq_mul] at this ⊢
  rw [this]
  ring

theorem Iso.mul {S T : Sch l →L[ℂ] Sch l} (hS : Iso S) (hT : Iso T) : Iso (S * T) := fun f => (hS _).trans (hT f)

theorem iso_of_integral {S : Sch l →L[ℂ] Sch l} (h : ∀ f : Sch l, ∫ x, ‖S f x‖ ^ (2 : ℝ) = ∫ x, ‖f x‖ ^ (2 : ℝ)) : Iso S :=
  fun f => by
    rw [schwartzToL2_apply, schwartzToL2_apply, norm_toLp' (by simp) (by simp), norm_toLp' (by simp) (by simp)]
    simp only [ENNReal.toReal_ofNat, h]

theorem temperate_quad (S : Eu l →L[ℝ] Eu l) : Function.HasTemperateGrowth fun x : Eu l => ⟪x, S x⟫ :=
  (innerSL ℝ).bilinear_hasTemperateGrowth Function.HasTemperateGrowth.id' S.hasTemperateGrowth

def ph (S : Eu l →L[ℝ] Eu l) : Sch l →L[ℂ] Sch l :=
  smulLeftCLM ℂ fun x : Eu l => exp (((-π * ⟪x, S x⟫ : ℝ) : ℂ) * I)

theorem ph_apply (S : Eu l →L[ℝ] Eu l) (f : Sch l) (x : Eu l) :
    ph S f x = exp (((-π * ⟪x, S x⟫ : ℝ) : ℂ) * I) * f x := by
  have h2 : Function.HasTemperateGrowth fun x : Eu l => (-2⁻¹ : ℝ) * ⟪x, S x⟫ :=
    (Function.HasTemperateGrowth.const _).mul (temperate_quad S)
  have h3 : Function.HasTemperateGrowth fun x : Eu l => exp (((-π * ⟪x, S x⟫ : ℝ) : ℂ) * I) := by
    convert GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp h2 using 1
    funext x
    simp only [Function.comp_apply, GlobalTheory.Published.Metaplectic.eChar_apply]
    congr 1
    push_cast
    ring
  rw [ph, smulLeftCLM_apply_apply h3, smul_eq_mul]

theorem ph_mul (S T : Eu l →L[ℝ] Eu l) : ph S * ph T = ph (S + T) := by
  ext f x
  simp only [ContinuousLinearMap.mul_apply, ph_apply, ← mul_assoc, ← Complex.exp_add, ContinuousLinearMap.add_apply,
    inner_add_right]
  congr 2
  push_cast
  ring

theorem ph_zero : ph (0 : Eu l →L[ℝ] Eu l) = 1 := by
  ext f x
  simp [ph_apply]

theorem isUnit_ph (S : Eu l →L[ℝ] Eu l) : IsUnit (ph S) :=
  ⟨⟨ph S, ph (-S), by rw [ph_mul, add_neg_cancel, ph_zero], by rw [ph_mul, neg_add_cancel, ph_zero]⟩, rfl⟩

theorem iso_ph (S : Eu l →L[ℝ] Eu l) : Iso (ph S) := iso_of_integral fun f => by
  simp only [ph_apply, norm_mul, norm_exp_ofReal_mul_I, one_mul]

theorem intw_ph {S : Eu l →L[ℝ] Eu l} (hS : ∀ x y, ⟪x, S y⟫ = ⟪y, S x⟫) (p q : Eu l) : Intw (ph S) p q p (q + S p) :=
  fun f g h => by
    funext x
    simp only [rf, ph_apply, h, ← mul_assoc, ← Complex.exp_add]
    congr 2
    rw [← add_mul, ← add_mul, ← ofReal_add, ← ofReal_add]
    congr 2
    simp only [inner_add_left, inner_add_right, map_add (f := _), hS p x, real_inner_comm x (S p)]
    ring


open Classical in
def dil (B : Eu l →L[ℝ] Eu l) : Sch l →L[ℂ] Sch l :=
  if h : IsUnit B then compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.ofUnit h.unit) else 0

theorem dil_apply {B : Eu l →L[ℝ] Eu l} (h : IsUnit B) (f : Sch l) (x : Eu l) : dil B f x = f (B x) := by
  rw [dil, dite_eq_left h]
  rfl

theorem dil_one : dil (1 : Eu l →L[ℝ] Eu l) = 1 := by
  ext f x
  simp [dil_apply isUnit_one]

theorem dil_mul {A B : Eu l →L[ℝ] Eu l} (hA : IsUnit A) (hB : IsUnit B) : dil A * dil B = dil (B * A) := by
  ext f x
  simp [dil_apply, hA, hB, hB.mul hA]

theorem isUnit_dil {B : Eu l →L[ℝ] Eu l} (h : IsUnit B) : IsUnit (dil B) := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨⟨dil u, dil (u⁻¹ : (Eu l →L[ℝ] Eu l)ˣ), by rw [dil_mul u.isUnit u⁻¹.isUnit, Units.inv_mul, dil_one],
    by rw [dil_mul u⁻¹.isUnit u.isUnit, Units.mul_inv, dil_one]⟩, rfl⟩

theorem intw_dil {B : Eu l →L[ℝ] Eu l} (hB : IsUnit B) {p q p' q' : Eu l} (hp : B p' = p) (hq : ∀ x, ⟪q', x⟫ = ⟪q, B x⟫) :
    Intw (dil B) p q p' q' := fun f g h => by
  funext x
  simp only [rf, dil_apply hB, h, map_add (f := _), hp, real_inner_comm q' p', hq, real_inner_comm q p]

theorem iso_dil {B : Eu l →L[ℝ] Eu l} (hB : IsUnit B) {c : ℝ} (hc : c ^ 2 = |B.det|) : Iso ((c : ℂ) • dil B) :=
  iso_of_integral fun f => by
    have hd : LinearMap.det (B : Eu l →ₗ[ℝ] Eu l) ≠ 0 :=
      ((hB.map ContinuousLinearMap.toLinearMapRingHom).map LinearMap.det).ne_zero
    have h1 := integral_map (μ := volume) (φ := (B : Eu l →ₗ[ℝ] Eu l)) (f := fun x => ‖f x‖ ^ (2 : ℝ))
      B.continuous.aemeasurable (f.continuous.norm.rpow_const fun _ => Or.inr (by norm_num)).aestronglyMeasurable
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ hd, integral_smul_measure,
      ENNReal.toReal_ofReal (abs_nonneg _)] at h1
    simp only [ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply, dil_apply hB, norm_smul, norm_real, Real.rpow_two,
      mul_pow, Real.norm_eq_abs, sq_abs, hc, integral_const_mul] at h1 ⊢
    erw [← h1]
    rw [smul_eq_mul, ← mul_assoc, ← abs_mul, ContinuousLinearMap.det, mul_inv_cancel₀ hd, abs_one, one_mul]

def fou (l : Type) [Fintype l] : Sch l →L[ℂ] Sch l := FourierTransform.fourierCLM ℂ (Sch l)

def fouInv (l : Type) [Fintype l] : Sch l →L[ℂ] Sch l := FourierTransform.fourierInvCLM ℂ (Sch l)

theorem fou_apply (f : Sch l) : fou l f = 𝓕 f := rfl

theorem fouInv_apply (f : Sch l) : fouInv l f = 𝓕⁻ f := rfl

theorem fou_mul_fouInv : fou l * fouInv l = 1 := by
  ext1 f
  rw [ContinuousLinearMap.mul_apply, fou_apply, fouInv_apply, FourierTransform.fourier_fourierInv_eq]
  rfl

theorem fouInv_mul_fou : fouInv l * fou l = 1 := by
  ext1 f
  rw [ContinuousLinearMap.mul_apply, fou_apply, fouInv_apply, FourierTransform.fourierInv_fourier_eq]
  rfl

theorem isUnit_fou : IsUnit (fou l) := ⟨⟨_, _, fou_mul_fouInv, fouInv_mul_fou⟩, rfl⟩

theorem isUnit_fouInv : IsUnit (fouInv l) := ⟨⟨_, _, fouInv_mul_fou, fou_mul_fouInv⟩, rfl⟩

theorem iso_fou : Iso (fou l) := fun f => norm_fourier_toL2_eq f

theorem iso_fouInv : Iso (fouInv l) := fun f => by
  rw [← iso_fou (fouInv l f), ← ContinuousLinearMap.mul_apply, fou_mul_fouInv, ContinuousLinearMap.one_apply]

theorem intw_fou (p q : Eu l) : Intw (fou l) p q (-q) p := fun f g h => by
  funext x
  simp only [fou_apply, fourier_coe, rf, h, Real.fourier_eq', smul_eq_mul]
  rw [← integral_const_mul, ← integral_add_right_eq_self (μ := volume) (fun v => exp (((2 * π * ⟪p, x⟫ + π * ⟪-q, p⟫ : ℝ) : ℂ) * I) *
    (exp (((-2 * π * ⟪v, x + -q⟫ : ℝ) : ℂ) * I) * f v)) p]
  refine integral_congr_ae (.of_forall fun v => ?_)
  simp only [← mul_assoc, ← Complex.exp_add]
  congr 2
  rw [← add_mul, ← add_mul, ← ofReal_add, ← ofReal_add]
  congr 2
  simp only [inner_add_left, inner_add_right, inner_neg_left, inner_neg_right, real_inner_comm q p, real_inner_comm q v]
  ring

theorem intw_fouInv (p q : Eu l) : Intw (fouInv l) p q q (-p) := fun f g h => by
  funext x
  have h1 := congrFun (intw_fou p q f g h) (-x)
  have e : ∀ (u : Sch l) y, fouInv l u y = fou l u (-y) := fun u y => rfl
  rw [e, h1]
  simp only [rf, e, inner_neg_left, inner_neg_right, neg_add]

def big (Ai B C : Eu l →L[ℝ] Eu l) (c : ℝ) : Sch l →L[ℂ] Sch l :=
  ph (C * Ai) * (((c : ℂ) • dil Ai) * (fou l * (ph (-(Ai * B)) * fouInv l)))

theorem isUnit_big {Ai : Eu l →L[ℝ] Eu l} (h : IsUnit Ai) (B C : Eu l →L[ℝ] Eu l) {c : ℝ} (hc : c ≠ 0) :
    IsUnit (big Ai B C c) := by
  refine (isUnit_ph _).mul (IsUnit.mul ?_ (isUnit_fou.mul ((isUnit_ph _).mul isUnit_fouInv)))
  rw [Algebra.smul_def]
  exact ((IsUnit.mk0 (c : ℂ) (by simpa using hc)).map _).mul (isUnit_dil h)

theorem iso_big {Ai : Eu l →L[ℝ] Eu l} (h : IsUnit Ai) (B C : Eu l →L[ℝ] Eu l) {c : ℝ} (hc : c ^ 2 = |Ai.det|) :
    Iso (big Ai B C c) :=
  (iso_ph _).mul ((iso_dil h hc).mul (iso_fou.mul ((iso_ph _).mul iso_fouInv)))

theorem big_one : big (1 : Eu l →L[ℝ] Eu l) 0 0 1 = 1 := by
  simp [big, ph_zero, dil_one, fou_mul_fouInv]

theorem intw_big {A Ai B C D : Eu l →L[ℝ] Eu l} (h : IsUnit Ai) (h1 : ∀ x, A (Ai x) = x) (h2 : ∀ x, Ai (A x) = x)
    (hAC : ∀ y z, ⟪A y, C z⟫ = ⟪C y, A z⟫) (hBD : ∀ y z, ⟪B y, D z⟫ = ⟪D y, B z⟫)
    (hAD : ∀ y z, ⟪A y, D z⟫ - ⟪C y, B z⟫ = ⟪y, z⟫) (c : ℝ) (p q : Eu l) :
    Intw (big Ai B C c) p q (A p + B q) (C p + D q) := by
  have hS : ∀ x y, ⟪x, (C * Ai) y⟫ = ⟪y, (C * Ai) x⟫ := fun x y => by
    have := hAC (Ai x) (Ai y)
    rw [h1, h1] at this
    exact this.trans (real_inner_comm _ _)
  have hr : ∀ q x, ⟪D q - (C * Ai) (B q), x⟫ = ⟪q, Ai x⟫ := fun q x => by
    have := hAD (Ai x) q
    rw [h1] at this
    rw [inner_sub_left, real_inner_comm x, real_inner_comm x, hS, real_inner_comm (Ai x) q, ← this,
      real_inner_comm _ (B q)]
    rfl
  have hT : ∀ x y, ⟪x, (-(Ai * B)) y⟫ = ⟪y, (-(Ai * B)) x⟫ := fun x y => by
    simp only [ContinuousLinearMap.neg_apply, inner_neg_right, ContinuousLinearMap.mul_apply (f := Ai), ← hr,
      inner_sub_left]
    rw [← hBD, real_inner_comm (B x) (D y), real_inner_comm (B y), real_inner_comm (B x), hS]
  have e : C p + D q = D q - (C * Ai) (B q) + (C * Ai) (A p + B q) := by
    simp [h2, add_comm]
  rw [e]
  refine (intw_ph hS _ _).mul (((intw_dil h ?_ (hr q)).smul c).mul
    ((intw_fou _ _).mul ((intw_ph hT _ _).mul (intw_fouInv p q))))
  simp [h2, add_comm]

end PositivityTheory.ThKR.LL
end
end

-- bundled from Development.WeilBound.ThetaLifts.Reductions.TensJoin
section
noncomputable section

open scoped TensorProduct
open PiTensorProduct

namespace PositivityTheory.ThKR.Join

open PositivityTheory.ThKF.Unit

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

theorem upd_comp (u : ∀ j, V j →ₗ[ℂ] V j) (i : ι) (a : V i →ₗ[ℂ] V i) :
    map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i a) ∘ₗ map u = map (Function.update u i (a ∘ₗ u i)) := by
  rw [← map_comp]
  congr 1
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem position_st {A : ι → Type} (act : ∀ i, A i → Module.End ℂ (V i)) (P : Submodule ℂ (⨂[ℂ] i, V i))
    (hP : ∀ i a, ∀ x ∈ P, map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i (act i a)) x ∈ P) (i : ι)
    (u : Module.End ℂ (V i)) (hu : u ∈ Algebra.adjoin ℂ (Set.range (act i))) :
    ∀ x ∈ P, map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i u) x ∈ P := by
  induction hu using Algebra.adjoin_induction with
  | mem u hu => obtain ⟨a, rfl⟩ := hu; exact hP i a
  | algebraMap c =>
    intro x hx
    rw [Algebra.algebraMap_eq_smul_one, PiTensorProduct.map_update_smul, show (1 : Module.End ℂ (V i)) = LinearMap.id from rfl,
      Function.update_eq_self, map_id]
    exact P.smul_mem c hx
  | add a b _ _ ha hb =>
    intro x hx
    rw [PiTensorProduct.map_update_add]
    exact P.add_mem (ha x hx) (hb x hx)
  | mul a b _ _ ha hb =>
    intro x hx
    have := LinearMap.congr_fun (upd_comp (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i b) i a) x
    rw [Function.update_idem, Function.update_self] at this
    exact (show _ = map (Function.update _ i (a * b)) x from this) ▸ ha _ (hb x hx)

theorem map_st {A : ι → Type} (act : ∀ i, A i → Module.End ℂ (V i)) (P : Submodule ℂ (⨂[ℂ] i, V i))
    (hP : ∀ i a, ∀ x ∈ P, map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i (act i a)) x ∈ P)
    (u : ∀ i, Module.End ℂ (V i)) (hu : ∀ i, u i ∈ Algebra.adjoin ℂ (Set.range (act i))) : ∀ x ∈ P, map u x ∈ P := by
  have h : ∀ S : Finset ι, ∀ x ∈ P, map (fun i => if i ∈ S then u i else (LinearMap.id : V i →ₗ[ℂ] V i)) x ∈ P := fun S => by
    induction S using Finset.induction_on with
    | empty => intro x hx; simpa using hx
    | insert j S hj ih =>
      intro x hx
      have h1 := position_st act P hP j (u j) (hu j) _ (ih x hx)
      rw [← LinearMap.comp_apply, upd_comp] at h1
      have e : (fun i => if i ∈ insert j S then u i else (LinearMap.id : V i →ₗ[ℂ] V i)) =
          Function.update (fun i => if i ∈ S then u i else (LinearMap.id : V i →ₗ[ℂ] V i)) j
            (u j ∘ₗ if j ∈ S then u j else LinearMap.id) := by
        funext i
        by_cases h : i = j
        · subst h; simp [hj]
        · simp [h]
      rw [e]
      exact h1
  simpa using h Finset.univ

theorem tens_join {A : ι → Type} (act : ∀ i, A i → Module.End ℂ (V i)) (K Z : ∀ i, Submodule ℂ (V i))
    (hr : ∀ i, Module.rank ℂ (V i) ≤ Cardinal.aleph0) (h1 : ∀ i, K i ≠ ⊤) (h2 : ∀ i a, ∀ x ∈ K i, act i a x ∈ K i)
    (h3 : ∀ i N, K i ≤ N → (∀ a, ∀ x ∈ N, act i a x ∈ N) → N = K i ∨ N = ⊤) (v : ∀ i, V i)
    (h4 : ∀ i (t : List (V i)), (∀ x ∈ t, x ∈ K i) → ∀ y,
      ∃ u ∈ Algebra.adjoin ℂ (Set.range (act i)), u (v i) - y ∈ Z i ∧ ∀ x ∈ t, u x ∈ Z i)
    (P P' : Submodule ℂ (⨂[ℂ] i, V i)) (hZ : ∀ (f : ∀ i, V i) i, f i ∈ Z i → tprod ℂ f ∈ P)
    (hZ' : ∀ (f : ∀ i, V i) i, f i ∈ Z i → tprod ℂ f ∈ P')
    (hP : ∀ i a, ∀ x ∈ P, map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i (act i a)) x ∈ P)
    (hP' : ∀ i a, ∀ x ∈ P', map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i (act i a)) x ∈ P')
    (e : P ⊔ P' = ⊤) : P = ⊤ ∨ P' = ⊤ := by
  let R : Submodule ℂ (⨂[ℂ] i, V i) := Submodule.span ℂ {x | ∃ (f : ∀ i, V i) (i : ι), f i ∈ K i ∧ x = tprod ℂ f}
  have hR : ∀ (f : ∀ i, V i) i, f i ∈ K i → tprod ℂ f ∈ R := fun f i h => Submodule.subset_span ⟨f, i, h, rfl⟩
  have Rst : ∀ i a, R ≤ R.comap (map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i (act i a))) := fun i a =>
    Submodule.span_le.2 (by
      rintro _ ⟨f, j, hj, rfl⟩
      show map _ (tprod ℂ f) ∈ R
      rw [map_tprod]
      refine hR _ j ?_
      by_cases h : j = i
      · subst h; simpa using h2 j a _ hj
      · simpa [Function.update_of_ne h] using hj)
  have nak : ∀ Q : Submodule ℂ (⨂[ℂ] i, V i), (∀ (f : ∀ i, V i) i, f i ∈ Z i → tprod ℂ f ∈ Q) →
      (∀ i a, ∀ x ∈ Q, map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i (act i a)) x ∈ Q) →
      Q ⊔ R = ⊤ → Q = ⊤ := fun Q q1 q2 q3 => by
    have fin : ∀ x ∈ R, ∃ t : ∀ i, List (V i), (∀ i, ∀ y ∈ t i, y ∈ K i) ∧
        ∀ u : ∀ i, Module.End ℂ (V i), (∀ i, ∀ y ∈ t i, u i y ∈ Z i) → map u x ∈ Q := fun x hx => by
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨f, i, hi, rfl⟩ := hx
        refine ⟨Function.update (fun _ => []) i [f i], fun j y hy => ?_, fun u hu => ?_⟩
        · by_cases h : j = i
          · subst h
            rw [Function.update_self, List.mem_singleton] at hy
            exact hy ▸ hi
          · simp [Function.update_of_ne h] at hy
        · rw [map_tprod]
          exact q1 _ i (hu i _ (by simp))
      | zero => exact ⟨fun _ => [], by simp, fun u _ => by simp⟩
      | add a b _ _ ha hb =>
        obtain ⟨s, s1, s2⟩ := ha
        obtain ⟨t, t1, t2⟩ := hb
        refine ⟨fun i => s i ++ t i, fun i y hy => (List.mem_append.1 hy).elim (s1 i y) (t1 i y), fun u hu => ?_⟩
        rw [map_add (f := _)]
        exact Q.add_mem (s2 u fun i y hy => hu i y (List.mem_append_left _ hy))
          (t2 u fun i y hy => hu i y (List.mem_append_right _ hy))
      | smul c a _ ha =>
        obtain ⟨s, s1, s2⟩ := ha
        exact ⟨s, s1, fun u hu => by rw [map_smul]; exact Q.smul_mem c (s2 u hu)⟩
    obtain ⟨p, hp, x, hx, e⟩ := Submodule.mem_sup.1 (q3 ▸ Submodule.mem_top : tprod ℂ v ∈ Q ⊔ R)
    obtain ⟨t, t1, t2⟩ := fin x hx
    refine eq_top_iff.2 fun y _ => ?_
    induction y using PiTensorProduct.induction_on with
    | smul_tprod c f =>
      choose u u1 u2 u3 using fun i => h4 i (t i) (t1 i) (f i)
      have a1 : map u (tprod ℂ v) ∈ Q := by
        rw [← e, map_add (f := _)]
        exact Q.add_mem (map_st act Q q2 u u1 p hp) (t2 u u3)
      have a2 : map u (tprod ℂ v) - tprod ℂ f ∈ Q := ker_le Z Q q1 (by
        rw [LinearMap.mem_ker, map_sub, map_tprod, map_tprod, map_tprod, sub_eq_zero]
        congr 1
        funext i
        exact (Submodule.Quotient.eq _).2 (u2 i))
      exact Q.smul_mem c (by simpa using Q.sub_mem a1 a2)
    | add x y hx hy => exact Q.add_mem (hx trivial) (hy trivial)
  have le : ∀ Q : Submodule ℂ (⨂[ℂ] i, V i), (∀ (f : ∀ i, V i) i, f i ∈ Z i → tprod ℂ f ∈ Q) →
      (∀ i a, ∀ x ∈ Q, map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i (act i a)) x ∈ Q) →
      Q ≤ R ∨ Q = ⊤ := fun Q q1 q2 =>
    (tens_max act K hr h1 h2 h3 R hR (Q ⊔ R) le_sup_right (fun i a x hx => by
      obtain ⟨p, hp, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
      rw [map_add (f := _)]
      exact Submodule.add_mem_sup (q2 i a p hp) (Rst i a hy))).imp (le_sup_left.trans ·) (nak Q q1 q2)
  rcases le P hZ hP with a | a
  · rcases le P' hZ' hP' with b | b
    · exact Or.inl (nak P hZ hP (top_le_iff.1 (e ▸ sup_le le_sup_left (b.trans le_sup_right))))
    · exact Or.inr b
  · exact Or.inl a

end PositivityTheory.ThKR.Join

end
end

