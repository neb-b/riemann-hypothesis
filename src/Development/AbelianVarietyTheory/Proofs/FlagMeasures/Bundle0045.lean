module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0008
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0034
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LinearIndependentRatTupOfDetNeZero
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.FrameGram

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}


open scoped TensorProduct in
variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} in
theorem _root_.GlobalTheory.FrameGram.hE_swap (hσ : ∀ x, σ (σ x) = x)
    (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → E) :
    σ (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J y x) = _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J x y := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE, _root_.Formalism.UG.P.hform_eq_dot, dotProduct, Matrix.mulVec, Function.comp, Finset.mul_sum, map_sum,
    map_mul, AlgHom.coe_toRingHom, RingHom.coe_coe, hσ, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem linearIndependent_ratTup_of_det_ne_zero (R : Type) [CommRing R] [Algebra F R] {m : ℕ}
    (X : Fin m → Fin n → E) (hX : (gramE σ J X).det ≠ 0) :
    LinearIndependent (R ⊗[F] E) (ratTup (F := F) R X) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hcj : ∀ j, ∑ b, c b * inclR (F := F) R (X b j) = 0 := fun j => by
    simpa [Finset.sum_apply, ratTup] using congrFun hc j
  have hu : IsUnit ((gramE σ J X).map (inclR (F := F) R)).det := by
    have := (inclR (F := F) (E := E) R).map_det (gramE σ J X)
    rw [RingHom.mapMatrix_apply] at this
    rw [← this]
    exact (IsUnit.mk0 _ hX).map _
  have h0 : ((gramE σ J X).map (inclR (F := F) R)).mulVec c = 0 := by
    funext a
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, gramE, hE, Formalism.UG.hform, map_sum,
      map_mul, Finset.sum_mul, Pi.zero_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    have := congrArg (fun t => inclR (F := F) R ((σ : E →+* E) (X a i)) * inclR (F := F) R (J i j) * t)
      (hcj j)
    simp only [Finset.mul_sum, mul_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun b _ => by ring
  have hinj := Matrix.mulVec_injective_of_isUnit
    ((Matrix.isUnit_iff_isUnit_det _).2 hu)
  have : c = 0 := hinj (by rw [h0, Matrix.mulVec_zero])
  exact fun b => congrFun this b

theorem det_gram_append_ne_zero (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) {r : ℕ}
    (y : Fin (r + 1) → Fin n → E) (f : Fin r → Fin n → E) (t : E) (ht : t ≠ 0)
    (hy : ∀ i j, gramE σ J y i j = if i = Fin.last r ∧ j = Fin.last r then t else 0)
    (hf : ∀ a b : Fin r, hE σ J (y a.castSucc) (f b) = if a = b then 1 else 0) :
    (gramE σ J (Fin.append y f)).det ≠ 0 := by
  intro h
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  have hy' : ∀ i j, hE σ J (y i) (y j) = if i = Fin.last r ∧ j = Fin.last r then t else 0 := hy
  have hf' : ∀ a b : Fin r, hE σ J (f a) (y b.castSucc) = if a = b then 1 else 0 := fun a b => by
    rw [← hE_swap hσ hJ, hf]
    by_cases hab : a = b
    · simp [hab]
    · simp [hab, Ne.symm hab]
  have row : ∀ k, ∑ b : Fin r, hE σ J (Fin.append y f k) (y b.castSucc) * c (Fin.castAdd r b.castSucc)
      + hE σ J (Fin.append y f k) (y (Fin.last r)) * c (Fin.castAdd r (Fin.last r))
      + ∑ b : Fin r, hE σ J (Fin.append y f k) (f b) * c (Fin.natAdd (r + 1) b) = 0 := fun k => by
    have := congrFun hc k
    simp only [Matrix.mulVec, dotProduct, gramE, Pi.zero_apply] at this
    rw [Fin.sum_univ_add, Fin.sum_univ_castSucc] at this
    simpa only [Fin.append_left, Fin.append_right] using this
  have h1 : ∀ a : Fin r, c (Fin.natAdd (r + 1) a) = 0 := fun a => by
    have := row (Fin.castAdd r a.castSucc)
    simpa [Fin.append_left, hy', hf, Fin.castSucc_ne_last] using this
  have h2 : c (Fin.castAdd r (Fin.last r)) = 0 := by
    have := row (Fin.castAdd r (Fin.last r))
    simpa [Fin.append_left, hy', h1, Fin.castSucc_ne_last, ht] using this
  have h3 : ∀ a : Fin r, c (Fin.castAdd r a.castSucc) = 0 := fun a => by
    have := row (Fin.natAdd (r + 1) a)
    simp only [Fin.append_right, hf', h1, h2] at this
    simpa using this
  apply hc0
  funext k
  refine Fin.addCases (fun i => ?_) (fun a => h1 a) k
  exact Fin.lastCases h2 h3 i

theorem gram_snoc (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) {r : ℕ}
    (e : Fin r → Fin n → E) (z : Fin n → E) (t : E) (he : ∀ a b, hE σ J (e a) (e b) = 0)
    (hez : ∀ a, hE σ J (e a) z = 0) (hz : hE σ J z z = t) (i j : Fin (r + 1)) :
    gramE σ J (Fin.snoc (α := fun _ => Fin n → E) e z) i j =
      if i = Fin.last r ∧ j = Fin.last r then t else 0 := by
  have hze : ∀ a, hE σ J z (e a) = 0 := fun a => by rw [← hE_swap hσ hJ, hez, map_zero]
  refine Fin.lastCases ?_ (fun a => ?_) i <;> refine Fin.lastCases ?_ (fun b => ?_) j <;>
    simp [gramE, he, hez, hze, hz, Fin.castSucc_ne_last]

end Alg


open scoped TensorProduct in
theorem _root_.GlobalTheory.FrameGram.conj_invol {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨-, -, -, hτ⟩ := h
  let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  apply τ.injective
  rw [hτ, hτ, star_star]

theorem frame_gram {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : IsHermND σ J) {r : ℕ} (y : Fin (r + 1) → Fin n → E) (f : Fin r → Fin n → E) (T : F)
    (hT : T ≠ 0)
    (hy : ∀ i j, gramE σ J y i j =
      if i = Fin.last r ∧ j = Fin.last r then algebraMap F E (-T) else 0)
    (hf : ∀ a b : Fin r, hE σ J (y a.castSucc) (f b) = if a = b then 1 else 0) :
    (gramE σ J (Fin.append y f)).det ≠ 0 ∧
      (∀ i j, σ (gramE σ J (Fin.append y f) j i) = gramE σ J (Fin.append y f) i j) ∧
      (∀ i j, σ (gramE σ J y j i) = gramE σ J y i j) ∧
      ∀ (R : Type) [CommRing R] [Algebra F R],
        LinearIndependent (R ⊗[F] E) (ratTup (F := F) R y) := by
  have hd := det_gram_append_ne_zero (conj_invol hσ) hJ.1 y f _
    ((map_ne_zero (algebraMap F E)).2 (neg_ne_zero.2 hT)) hy hf
  refine ⟨hd, fun i j => hE_swap (conj_invol hσ) hJ.1 _ _,
    fun i j => hE_swap (conj_invol hσ) hJ.1 _ _, fun R _ _ => ?_⟩
  have h := (linearIndependent_ratTup_of_det_ne_zero R _ hd).comp (Fin.castAdd r)
    (Fin.castAdd_injective _ _)
  have e : ratTup (F := F) R (Fin.append y f) ∘ Fin.castAdd r = ratTup (F := F) R y := by
    funext a i
    simp [ratTup, Fin.append_left]
  rwa [e] at h

theorem frame_gram_snoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : IsHermND σ J) {r : ℕ} (e f : Fin r → Fin n → E) (z : Fin n → E) (T : F) (hT : T ≠ 0)
    (he : ∀ a b, hE σ J (e a) (e b) = 0) (hez : ∀ a, hE σ J (e a) z = 0)
    (hz : hE σ J z z = algebraMap F E (-T))
    (hf : ∀ a b, hE σ J (e a) (f b) = if a = b then 1 else 0)
    (y : Fin (r + 1) → Fin n → E) (hy : y = Fin.snoc (α := fun _ => Fin n → E) e z)
    (w : Fin (r + 1 + r) → Fin n → E) (hw : w = Fin.append y f) :
    (gramE σ J w).det ≠ 0 ∧ (∀ i j, σ (gramE σ J w j i) = gramE σ J w i j) ∧
      (∀ i j, σ (gramE σ J y j i) = gramE σ J y i j) ∧
      (∀ i j, gramE σ J y i j =
        if i = Fin.last r ∧ j = Fin.last r then algebraMap F E (-T) else 0) ∧
      ∀ (R : Type) [CommRing R] [Algebra F R],
        LinearIndependent (R ⊗[F] E) (ratTup (F := F) R y) := by
  subst hw hy
  have hg := gram_snoc (conj_invol hσ) hJ.1 e z _ he hez hz
  obtain ⟨h1, h2, h3, h4⟩ := frame_gram hσ hJ _ f T hT hg (fun a b => by simpa using hf a b)
  exact ⟨h1, h2, h3, hg, h4⟩

end GlobalTheory.FrameGram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalHeightScaling
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical

namespace GlobalTheory

private theorem rpow_neg_half_height_product_eq (s : Finset ℕ) (r : ℕ) (m : ℕ → ℕ) {a b c : ℝ} {δ : ℕ → ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hδ : ∀ l ∈ s, 0 < δ l) :
    (a * (b⁻¹ ^ (2 * r * (r + 1)) * c / a ^ (2 * (r + 1))) * ∏ l ∈ s, (b⁻¹ ^ m l * δ l) ^ 2) ^ (-(1 / 2 : ℝ)) =
      a ^ ((2 * r + 1 : ℝ) / 2) * b ^ ((r * (r + 1) + ∑ l ∈ s, m l : ℕ) : ℝ) * c ^ (-(1 / 2 : ℝ)) *
        ∏ l ∈ s, (δ l)⁻¹ := by
  have hD : 0 < ∏ l ∈ s, δ l := Finset.prod_pos hδ
  rw [Finset.prod_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_inv_distrib]
  generalize ∏ l ∈ s, δ l = D at hD ⊢
  generalize ∑ l ∈ s, m l = N
  have hY : 0 < a ^ ((2 * r + 1 : ℝ) / 2) * b ^ ((r * (r + 1) + N : ℕ) : ℝ) * c ^ (-(1 / 2 : ℝ)) * D⁻¹ := by
    positivity
  have e1 : (a ^ ((2 * r + 1 : ℝ) / 2)) ^ 2 = a ^ (((2 * r + 1 : ℕ)) : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    congr 1
    push_cast
    ring
  have e2 : (b ^ ((r * (r + 1) + N : ℕ) : ℝ)) ^ 2 = b ^ (2 * r * (r + 1)) * b ^ (2 * N) := by
    rw [Real.rpow_natCast, ← pow_mul, ← pow_add]
    congr 1
    ring
  have e3 : (c ^ (-(1 / 2 : ℝ))) ^ 2 = c⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]
    norm_num [Real.rpow_neg_one]
  have hX : a * (b⁻¹ ^ (2 * r * (r + 1)) * c / a ^ (2 * (r + 1))) * (b⁻¹ ^ N * D) ^ 2 =
      ((a ^ ((2 * r + 1 : ℝ) / 2) * b ^ ((r * (r + 1) + N : ℕ) : ℝ) * c ^ (-(1 / 2 : ℝ)) * D⁻¹) ^ 2)⁻¹ := by
    simp only [mul_pow]
    rw [e1, e2, e3, Real.rpow_natCast]
    have := ha.ne'
    have := hb.ne'
    have := hc.ne'
    have := hD.ne'
    simp only [inv_pow]
    field_simp
    ring
  rw [hX, Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hY.le]
  norm_num [Real.rpow_neg_one]

theorem local_height_scaling : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (P : LocNG.FPair H r), P.Gv ≠ 0 → ∀ (e : F), e ≠ 0 → ∀ (G : E) (d : ℕ → E), P.Gv = algebraMap F E (e⁻¹ ^ (2 * r * (r + 1))) * G → (∀ l ∈ P.ends, P.Dm l = algebraMap F E (e⁻¹ ^ (l * (2 * r + 1 - l))) * d l) → (P.PrimeTo → P.Hp = 1) ∧ P.Hp = M.modK (algebraMap F E (LocNG.theta M)) ^ ((2 * r + 1 : ℝ) / 2) * M.modK (algebraMap F E e) ^ ((r * (r + 1) + ∑ l ∈ P.ends, l * (2 * r + 1 - l) : ℕ) : ℝ) * M.modK G ^ (-(1 / 2 : ℝ)) * ∏ l ∈ P.ends, (M.modK (d l))⁻¹ := by
  intro F _ _ _ E _ _ _ _ M hOK V _ _ H r P hGv0 e he G d hG hD
  obtain ⟨hmul, hpc, hone⟩ := _root_.GlobalTheory.ModuleUnits.modK_units M hOK
  have hA1 : M.modK 1 = 1 := hone 1 M.L.O.one_mem ⟨1, M.L.O.one_mem, one_mul 1⟩
  have hpow : ∀ x : E, IsUnit x → ∀ n : ℕ, M.modK (x ^ n) = M.modK x ^ n := by
    intro x hx n
    induction n with
    | zero => simp [hA1]
    | succ n ih => rw [pow_succ, hmul _ _ (hx.pow n) hx, ih, pow_succ]
  have hneg : ∀ n : ℕ, M.modK ((-1 : E) ^ n) = 1 := fun n =>
    hone _ (pow_mem (neg_mem M.L.O.one_mem) n)
      ⟨(-1) ^ n, pow_mem (neg_mem M.L.O.one_mem) n, by rw [← mul_pow]; simp⟩
  have hGvu : IsUnit P.Gv := by
    have hfix : M.L.cj P.Gv = P.Gv := by
      simp only [LocNG.FPair.Gv, HermSp.Gdet, HermSp.normE, map_sub, map_mul, AlgEquiv.commutes,
        M.L.cj_cj]
      ring
    obtain ⟨a, ha⟩ := (M.L.cj_fix _).1 hfix
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hGv0 (by rw [← ha, map_zero])
    rw [← ha]
    exact (IsUnit.mk0 a ha0).map _
  have hae : IsUnit (algebraMap F E e) := (IsUnit.mk0 e he).map _
  have haei : IsUnit (algebraMap F E e⁻¹) := (IsUnit.mk0 _ (inv_ne_zero he)).map _
  have hAei : M.modK (algebraMap F E e⁻¹) = (M.modK (algebraMap F E e))⁻¹ := by
    have h1 := hmul _ _ haei hae
    have h2 : algebraMap F E e⁻¹ * algebraMap F E e = 1 := by
      rw [← map_mul, inv_mul_cancel₀ he, map_one]
    rw [h2, hA1] at h1
    exact eq_inv_of_mul_eq_one_left h1.symm
  have hθ0 : LocNG.theta M ≠ 0 := by
    unfold LocNG.theta
    split
    · exact one_ne_zero
    · next g _ => simpa using g.q_irr.ne_zero
  have hθu : IsUnit (algebraMap F E (LocNG.theta M)) := (IsUnit.mk0 _ hθ0).map _
  have hdg := det_gram_frame_generators M hOK H r 0 P
  have hdu : IsUnit (H.gram P.MMgen).det := by
    have h1 : IsUnit ((H.gram P.MMgen).det * algebraMap F E (LocNG.theta M) ^ (2 * (r + 1))) := by
      rw [hdg]
      exact (isUnit_one.neg.pow _).mul hGvu
    exact isUnit_of_mul_isUnit_left h1
  have hAdet : M.modK (H.gram P.MMgen).det * M.modK (algebraMap F E (LocNG.theta M)) ^ (2 * (r + 1)) =
      M.modK P.Gv := by
    have h1 := congrArg M.modK hdg
    rw [hmul _ _ hdu (hθu.pow _), hpow _ hθu, hmul _ _ (isUnit_one.neg.pow _) hGvu, hneg, one_mul] at h1
    exact h1
  have hGu : IsUnit G := isUnit_of_mul_isUnit_right (by rw [← hG]; exact hGvu)
  have hAGv : M.modK P.Gv = (M.modK (algebraMap F E e))⁻¹ ^ (2 * r * (r + 1)) * M.modK G := by
    rw [hG, map_pow, hmul _ _ (haei.pow _) hGu, hpow _ haei, hAei]
  have hDu : ∀ l ∈ P.ends, IsUnit (P.Dm l) := by
    intro l hl
    simp only [LocNG.FPair.ends, Finset.mem_filter, Finset.mem_range] at hl
    exact hl.2.2
  have hdu' : ∀ l ∈ P.ends, IsUnit (d l) := fun l hl =>
    isUnit_of_mul_isUnit_right (by rw [← hD l hl]; exact hDu l hl)
  have hAD : ∀ l ∈ P.ends, M.modK (P.Dm l * M.L.cj (P.Dm l)) =
      ((M.modK (algebraMap F E e))⁻¹ ^ (l * (2 * r + 1 - l)) * M.modK (d l)) ^ 2 := by
    intro l hl
    rw [hmul _ _ (hDu l hl) ((hDu l hl).map M.L.cj), (hpc _ (hDu l hl)).2, ← sq, hD l hl, map_pow,
      hmul _ _ (haei.pow _) (hdu' l hl), hpow _ haei, hAei]
  have ha : 0 < M.modK (algebraMap F E (LocNG.theta M)) := (hpc _ hθu).1
  have hb : 0 < M.modK (algebraMap F E e) := (hpc _ hae).1
  have hc : 0 < M.modK G := (hpc _ hGu).1
  have hδ : ∀ l ∈ P.ends, 0 < M.modK (d l) := fun l hl => (hpc _ (hdu' l hl)).1
  have hAdet' : M.modK (H.gram P.MMgen).det = (M.modK (algebraMap F E e))⁻¹ ^ (2 * r * (r + 1)) *
      M.modK G / M.modK (algebraMap F E (LocNG.theta M)) ^ (2 * (r + 1)) := by
    rw [← hAGv, ← hAdet, mul_div_cancel_right₀ _ (pow_ne_zero _ ha.ne')]
  refine ⟨fun hp => ?_, ?_⟩
  · obtain ⟨hs, hGo, hDo⟩ := hp
    have hθ1 : LocNG.theta M = 1 := by
      unfold LocNG.theta
      rw [hs]
    have hAθ : M.modK (algebraMap F E (LocNG.theta M)) = 1 := by rw [hθ1, map_one, hA1]
    have hG1 : M.modK P.Gv = 1 := hone _ hGo.1 hGo.2
    have hdet1 : M.modK (H.gram P.MMgen).det = 1 := by
      have h1 := hAdet
      rw [hAθ, hG1, one_pow, mul_one] at h1
      exact h1
    unfold LocNG.FPair.Hp
    rw [hAθ, hdet1, Finset.prod_eq_one]
    · simp
    · intro l hl
      rw [hmul _ _ (hDu l hl) ((hDu l hl).map M.L.cj), (hpc _ (hDu l hl)).2,
        hone _ (hDo l hl).1 (hDo l hl).2, one_mul]
  · unfold LocNG.FPair.Hp
    rw [hAdet', Finset.prod_congr rfl hAD]
    exact rpow_neg_half_height_product_eq P.ends r (fun l => l * (2 * r + 1 - l)) ha hb hc hδ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LoweringDifferenceOfIsometries
section
open Matrix

namespace GlobalTheory

theorem hform_sub_left_flag {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J : Matrix n n A) (x x' y : n → A) :
    Formalism.UG.hform σ J (x - x') y = Formalism.UG.hform σ J x y - Formalism.UG.hform σ J x' y := by
  unfold Formalism.UG.hform
  simp only [Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem hform_sub_right_flag {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J : Matrix n n A) (x y y' : n → A) :
    Formalism.UG.hform σ J x (y - y') = Formalism.UG.hform σ J x y - Formalism.UG.hform σ J x y' := by
  unfold Formalism.UG.hform
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private theorem hform_eq_dotProduct_mulVec {K : Type} [CommRing K] {n : ℕ} (σ : K →+* K)
    (J : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    Formalism.UG.hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  unfold Formalism.UG.hform
  simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

private theorem hform_mulVec_eq_of_unitary {K : Type} [CommRing K] {n : ℕ} (σ : K →+* K)
    (J γ : Matrix (Fin n) (Fin n) K) (hγ : Formalism.UG.cT σ γ * J * γ = J) (x y : Fin n → K) :
    Formalism.UG.hform σ J (γ *ᵥ x) (γ *ᵥ y) = Formalism.UG.hform σ J x y := by
  rw [hform_eq_dotProduct_mulVec, hform_eq_dotProduct_mulVec]
  have h1 : (fun i => σ ((γ *ᵥ x) i)) = γ.map σ *ᵥ (fun i => σ (x i)) := by
    funext i
    exact RingHom.map_mulVec σ γ x i
  unfold Formalism.UG.cT at hγ
  rw [Matrix.mul_assoc] at hγ
  rw [h1, ← vecMul_transpose (γ.map σ), ← dotProduct_mulVec]
  simp only [mulVec_mulVec, hγ]

theorem lowering_difference_of_isometries :
    ∀ (K R : Type) [Field K] [StarRing K] [CommRing R] [Algebra R K] (n : ℕ) (J : Matrix (Fin n) (Fin n) K), Formalism.UG.IsHerm (starRingEnd K) J → ∀ (a : ℕ) (G : ℕ → Submodule R (Fin n → K)), G 0 = ⊥ → Monotone G → (∀ p ≤ 2 * a + 1, ∀ y, y ∈ G (2 * a + 1 - p) ↔ y ∈ G (2 * a + 1) ∧ ∀ s ∈ G p, Formalism.UG.hform (starRingEnd K) J s y = 0) → ∀ γ γ' : Matrix (Fin n) (Fin n) K, Formalism.UG.cT (starRingEnd K) γ * J * γ = J → Formalism.UG.cT (starRingEnd K) γ' * J * γ' = J → (∀ p ≤ 2 * a, ∀ y ∈ G (p + 1), (γ - 1) *ᵥ y ∈ G p) → (∀ p ≤ 2 * a, ∀ y ∈ G (p + 1), (γ' - 1) *ᵥ y ∈ G p) → ∀ c : ℕ, 1 ≤ c → (∀ q p : ℕ, q < p → q + p ≤ 2 * a → p - q < c → ∀ y ∈ G (p + 1), (γ - γ') *ᵥ y ∈ G q) → (∀ p ≤ 2 * a + 1, ∀ y ∈ G p, (γ - γ') *ᵥ y ∈ G (p - c)) ∧ ∀ p p' : ℕ, p ≤ 2 * a → p' ≤ 2 * a → p + p' ≤ 2 * a + c → ∀ x ∈ G (p + 1), ∀ y ∈ G (p' + 1), Formalism.UG.hform (starRingEnd K) J ((γ - γ') *ᵥ x) y + Formalism.UG.hform (starRingEnd K) J x ((γ - γ') *ᵥ y) = 0 := by
  intro K R _ _ _ _ n J _ a G hG0 hGm hdual γ γ' hγ hγ' hl hl' c hc hlow
  set hf := Formalism.UG.hform (starRingEnd K) J with hhf
  have hL : ∀ x x' y, hf (x - x') y = hf x y - hf x' y := fun x x' y => hform_sub_left_flag _ J x x' y
  have hR : ∀ x y y', hf x (y - y') = hf x y - hf x y' := fun x y y' => hform_sub_right_flag _ J x y y'
  have iso : ∀ x y, hf (γ *ᵥ x) (γ *ᵥ y) = hf x y := hform_mulVec_eq_of_unitary _ J γ hγ
  have iso' : ∀ x y, hf (γ' *ᵥ x) (γ' *ᵥ y) = hf x y := hform_mulVec_eq_of_unitary _ J γ' hγ'
  have h0 : ∀ v, hf 0 v = 0 := fun v => by simp [hhf, Formalism.UG.hform]
  have mem0 : ∀ y ∈ G 0, y = 0 := fun y hy => by
    rw [hG0] at hy
    exact (Submodule.mem_bot R).1 hy
  have orth : ∀ m m', m + m' ≤ 2 * a + 1 → ∀ u ∈ G m, ∀ v ∈ G m', hf u v = 0 := by
    intro m m' hmm u hu v hv
    exact ((hdual m (by omega) v).1 (hGm (by omega) hv)).2 u hu
  have key : ∀ x y, hf ((γ - γ') *ᵥ x) (γ *ᵥ y) + hf (γ' *ᵥ x) ((γ - γ') *ᵥ y) = 0 := by
    intro x y
    rw [sub_mulVec, sub_mulVec, hL, hR, iso, iso']
    ring
  have base : ∀ p ≤ 2 * a + 1, ∀ y ∈ G p, (γ - γ') *ᵥ y ∈ G (p - 1) := by
    intro p hp y hy
    rcases Nat.eq_zero_or_pos p with rfl | hp0
    · rw [mem0 y hy, mulVec_zero]
      exact zero_mem _
    · obtain ⟨p0, rfl⟩ : ∃ p0, p = p0 + 1 := ⟨p - 1, by omega⟩
      have e : (γ - γ') *ᵥ y = (γ - 1) *ᵥ y - (γ' - 1) *ᵥ y := by
        simp only [sub_mulVec, one_mulVec]
        abel
      rw [e, Nat.add_sub_cancel]
      exact sub_mem (hl p0 (by omega) y hy) (hl' p0 (by omega) y hy)
  have main1 : ∀ p, p ≤ 2 * a + 1 → ∀ y ∈ G p, (γ - γ') *ᵥ y ∈ G (p - c) := by
    intro p
    induction p using Nat.strong_induction_on with
    | _ p ih =>
      intro hp y hy
      by_cases hA : c = 1 ∨ p ≤ 1
      · exact hGm (by omega) (base p hp y hy)
      by_cases hB : 2 * p ≤ 2 * a + 1 + c ∨ p < c
      · obtain ⟨p0, rfl⟩ : ∃ p0, p = p0 + 1 := ⟨p - 1, by omega⟩
        exact hlow (p0 + 1 - c) p0 (by omega) (by omega) (by omega) y hy
      have hγy : γ *ᵥ y ∈ G p := by
        have e1 : γ *ᵥ y = (γ - 1) *ᵥ y + y := by
          simp only [sub_mulVec, one_mulVec]
          abel
        rw [e1]
        refine add_mem (hGm (Nat.sub_le p 1) (hl (p - 1) (by omega) y ?_)) hy
        rwa [Nat.sub_add_cancel (by omega : 1 ≤ p)]
      have inner : ∀ j, j ≤ 2 * a + 1 - (p - c) → ∀ s ∈ G j, hf s ((γ - γ') *ᵥ y) = 0 := by
        intro j
        induction j with
        | zero =>
          intro _ s hs
          rw [mem0 s hs, h0]
        | succ j ihj =>
          intro hj s hs
          have k := key s y
          have ha : hf ((γ' - 1) *ᵥ s) ((γ - γ') *ᵥ y) =
              hf (γ' *ᵥ s) ((γ - γ') *ᵥ y) - hf s ((γ - γ') *ᵥ y) := by
            rw [sub_mulVec γ' 1, one_mulVec, hL]
          have hz1 := ihj (by omega) _ (hl' j (by omega) s hs)
          have hz2 := orth (j + 1 - c) p (by omega) _ (ih (j + 1) (by omega) (by omega) s hs) _ hγy
          linear_combination k + ha - hz1 - hz2
      have hd := (hdual (2 * a + 1 - (p - c)) (by omega) ((γ - γ') *ᵥ y)).2
        ⟨hGm (by omega) (base p hp y hy), fun s hs => inner _ le_rfl s hs⟩
      have e2 : 2 * a + 1 - (2 * a + 1 - (p - c)) = p - c := by omega
      rwa [e2] at hd
  refine ⟨main1, ?_⟩
  intro p p' hp hp' hpp x hx y hy
  have e3 : hf ((γ - γ') *ᵥ x) ((γ - 1) *ᵥ y) = 0 :=
    orth (p + 1 - c) p' (by omega) _ (main1 (p + 1) (by omega) x hx) _ (hl p' hp' y hy)
  have e4 : hf ((γ' - 1) *ᵥ x) ((γ - γ') *ᵥ y) = 0 :=
    orth p (p' + 1 - c) (by omega) _ (hl' p hp x hx) _ (main1 (p' + 1) (by omega) y hy)
  rw [sub_mulVec γ 1, one_mulVec, hR] at e3
  rw [sub_mulVec γ' 1, one_mulVec, hL] at e4
  linear_combination key x y - e3 - e4

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelVolMul
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.ContAut

theorem relVol_mul {W : Type} [AddCommGroup W] {X Y B : AddSubgroup W}
    (hYX : Y.relIndex X ≠ 0) (hBY : B.relIndex Y ≠ 0) :
    relVol X B = relVol X Y * relVol Y B := by
  have hCY : (B ⊓ Y).relIndex Y ≠ 0 := by rwa [AddSubgroup.inf_relIndex_right]
  have hCX : (B ⊓ Y).relIndex X ≠ 0 := AddSubgroup.relIndex_ne_zero_trans hCY hYX
  have e1 := ContModel.relVol_of_le (W0 := X) (inf_le_left : B ⊓ Y ≤ B) hCX
  have e2 := ContModel.relVol_of_le (W0 := X) (inf_le_right : B ⊓ Y ≤ Y) hCX
  have e3 := ContModel.relVol_of_le (W0 := Y) (inf_le_left : B ⊓ Y ≤ B) hCY
  have e4 : relVol Y (B ⊓ Y) = 1 / ((B ⊓ Y).relIndex Y : ℝ) := by
    unfold relVol
    rw [AddSubgroup.relIndex_eq_one.2 (inf_le_right : B ⊓ Y ≤ Y)]
    simp
  have c : ((B ⊓ Y).relIndex Y : ℝ) ≠ 0 := by exact_mod_cast hCY
  rw [e1, e2, e3, e4]
  field_simp

theorem image_mk {W : Type} [AddCommGroup W] (A : AddSubgroup W) (φ : W ≃+ W) (S : Set W) :
    ∃ f : W ⧸ A → W ⧸ A.map φ.toAddMonoidHom, Function.Injective f ∧
      (QuotientAddGroup.mk : W → W ⧸ A.map φ.toAddMonoidHom) '' (φ '' S)
        = f '' ((QuotientAddGroup.mk : W → W ⧸ A) '' S) := by
  refine ⟨QuotientAddGroup.map A (A.map φ.toAddMonoidHom) φ.toAddMonoidHom
    (AddSubgroup.le_comap_map _ _), ?_, ?_⟩
  · intro u v
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective u
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective v
    intro h
    rw [QuotientAddGroup.map_mk, QuotientAddGroup.map_mk, QuotientAddGroup.eq] at h
    obtain ⟨a, ha, hh⟩ := h
    rw [QuotientAddGroup.eq]
    have : a = -x + y := φ.injective (by simpa using hh)
    rwa [← this]
  · rw [Set.image_image, Set.image_image]
    rfl

theorem cont_image : ∀ {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) (φ : W ≃+ W), (W0.map φ.toAddMonoidHom).relIndex W0 ≠ 0 → W0.relIndex (W0.map φ.toAddMonoidHom) ≠ 0 → ∀ S, IsCO W0 S → IsCO W0 (φ '' S) ∧ cont W0 (φ '' S) = relVol W0 (W0.map φ.toAddMonoidHom) * cont W0 S := by
  intro W _ W0 φ h1 h2 S ⟨A, hA⟩
  have hi : Function.Injective φ.toAddMonoidHom := φ.injective
  have m1 := AddSubgroup.relIndex_map_map_of_injective A W0 hi
  have m2 := AddSubgroup.relIndex_map_map_of_injective W0 A hi
  obtain ⟨f, hf, him⟩ := image_mk A φ S
  have a1 : (A.map φ.toAddMonoidHom).relIndex (W0.map φ.toAddMonoidHom) ≠ 0 := m1 ▸ hA.1
  have a2 : (W0.map φ.toAddMonoidHom).relIndex (A.map φ.toAddMonoidHom) ≠ 0 := m2 ▸ hA.2.1
  have hG : GoodSub W0 (A.map φ.toAddMonoidHom) (φ '' S) := by
    refine ⟨AddSubgroup.relIndex_ne_zero_trans a1 h1, AddSubgroup.relIndex_ne_zero_trans h2 a2,
      ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨a, ha, rfl⟩
      exact ⟨x + a, hA.2.2.1 x hx a ha, by simp⟩
    · rw [him]; exact hA.2.2.2.image f
  refine ⟨⟨_, hG⟩, ?_⟩
  rw [ContModel.cont_eq hG, ContModel.cont_eq hA, him, Set.ncard_image_of_injective _ hf,
    relVol_mul h1 a1]
  have : relVol (W0.map φ.toAddMonoidHom) (A.map φ.toAddMonoidHom) = relVol W0 A := by
    unfold relVol; rw [m1, m2]
  rw [this]; ring

end GlobalTheory.HL.ContAut
end

