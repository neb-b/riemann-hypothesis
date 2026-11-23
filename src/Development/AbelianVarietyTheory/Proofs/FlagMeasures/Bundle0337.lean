module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0277
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0311
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0332
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0025
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameClassTermCountLeCardAut
section
noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals

namespace GlobalTheory.TypeAsm.FibCard
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Main
variable {D : D7} {X : HidaSetting D}

theorem stab_of_fix' (u : D.what₂.Word) {a : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hi : a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hfix : ∀ c, a ((F0 X u).e c) = (F0 X u).e c) : a ∈ stabF D (X.Fu u) := by
  refine ⟨hi, fun j => ?_, ?_⟩
  · unfold FlagG.Xa
    rw [Submodule.map_span, Set.image_image]
    congr 1
    apply Set.image_congr
    intro i _
    have h' : (F0 X u).e i.castSucc = (X.Fu u).e i := fv_cast (lf D (X.Fu u)).fl i
    have := hfix i.castSucc
    rw [h'] at this
    exact this
  · have h' : (F0 X u).e (Fin.last _) = (X.Fu u).z := fv_last (lf D (X.Fu u)).fl
    have := hfix (Fin.last _)
    rw [h'] at this
    exact this

theorem fix_X (u : D.what₂.Word) {a : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hfix : ∀ c, a ((F0 X u).e c) = (F0 X u).e c) : ∀ x ∈ (X.Fu u).X, a x = x := by
  intro x hx
  have h : Set.EqOn (⇑(a : (VS D).V →ₗ[D.host.E] (VS D).V)) (⇑(LinearMap.id : (VS D).V →ₗ[D.host.E] (VS D).V))
      (Set.range (X.Fu u).e) := by
    rintro _ ⟨i, rfl⟩
    have h' : (F0 X u).e i.castSucc = (X.Fu u).e i := fv_cast (lf D (X.Fu u)).fl i
    have := hfix i.castSucc
    rw [h'] at this
    exact this
  simpa using LinearMap.eqOn_span h hx

theorem perp_pres (u : D.what₂.Word) {a : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hi : a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hfix : ∀ c, a ((F0 X u).e c) = (F0 X u).e c) :
    ∀ y ∈ perpS (VS D) (X.Fu u).X, a y ∈ perpS (VS D) (X.Fu u).X := by
  intro y hy x hx
  rw [← fix_X u hfix x hx, hi x y]
  exact hy x hx

theorem ind_exists (u : D.what₂.Word) {a : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hi : a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hfix : ∀ c, a ((F0 X u).e c) = (F0 X u).e c) :
    ∃ φ : WbQ D (X.Fu u) → WbQ D (X.Fu u), ∀ (x : perpS (VS D) (X.Fu u).X) (hx : a x.1 ∈ perpS (VS D) (X.Fu u).X),
      φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨a x.1, hx⟩ := by
  let f : perpS (VS D) (X.Fu u).X →ₗ[D.host.E] perpS (VS D) (X.Fu u).X :=
    (a : (VS D).V →ₗ[D.host.E] (VS D).V).restrict (perp_pres u hi hfix)
  let q := (X.Fu u).X.comap (perpS (VS D) (X.Fu u).X).subtype
  have hq : q ≤ q.comap f := by
    intro x hx
    simp only [q, Submodule.mem_comap, Submodule.subtype_apply] at hx ⊢
    show a x.1 ∈ (X.Fu u).X
    rw [fix_X u hfix x.1 hx]; exact hx
  refine ⟨Submodule.mapQ q q f hq, fun x hx => ?_⟩
  rw [Submodule.mapQ_apply]
  rfl

end Main
end GlobalTheory.TypeAsm.FibCard

namespace GlobalTheory.TypeAsm.FibCard
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Main2
variable {D : D7} {X : HidaSetting D}

theorem symm_fix (u : D.what₂.Word) {a : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hfix : ∀ c, a ((F0 X u).e c) = (F0 X u).e c) : ∀ x ∈ (X.Fu u).X, a.symm x = x :=
  fun x hx => a.symm_apply_eq.2 (fix_X u hfix x hx).symm

theorem aut_iff {Λ : Submodule (𝓞 D.host.E) (VS D).V} {a : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hga : Formalism.HermitianLatticesTheory.gmap a Λ = Λ) (y : (VS D).V) : a.symm y ∈ Λ ↔ y ∈ Λ := by
  rw [← GlobalTheory.LoopC.FrEqv.mem_gmap (Λ := Λ) a y, hga]

theorem nlam_of_same (u : D.what₂.Word) {Λ : Submodule (𝓞 D.host.E) (VS D).V} {a b : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hia : a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hib : b ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hga : Formalism.HermitianLatticesTheory.gmap a Λ = Λ) (hgb : Formalism.HermitianLatticesTheory.gmap b Λ = Λ)
    (hfa : ∀ c, a ((F0 X u).e c) = (F0 X u).e c) (hfb : ∀ c, b ((F0 X u).e c) = (F0 X u).e c)
    (hsame : ∀ x ∈ perpS (VS D) (X.Fu u).X, b x - a x ∈ (X.Fu u).X) :
    a⁻¹ * b ∈ NLam Λ (lf D (X.Fu u)) := by
  have happ : ∀ x, (a⁻¹ * b) x = a.symm (b x) := fun x => rfl
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hia) hib, ?_⟩,
    fun j x hx => ?_, fun x hx => ?_⟩
  · ext y
    rw [GlobalTheory.LoopC.FrEqv.mem_gmap]
    have : (a⁻¹ * b).symm y = b.symm (a y) := by
      apply (a⁻¹ * b).injective
      rw [LinearEquiv.apply_symm_apply, happ, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
    rw [this, aut_iff hgb]
    have h2 := aut_iff hga (a y)
    rw [LinearEquiv.symm_apply_apply] at h2
    exact h2.symm
  · have hX : x ∈ (X.Fu u).X := by
      have hle : Xflag (lf D (X.Fu u)) (j + 1) ≤ (X.Fu u).X :=
        Submodule.span_mono (by rintro _ ⟨i, -, rfl⟩; exact ⟨i, rfl⟩)
      exact hle hx
    rw [happ, fix_X u hfb x hX, symm_fix u hfa x hX, sub_self]
    exact zero_mem _
  · have hp : x ∈ perpS (VS D) (X.Fu u).X := by
      simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx
      exact fun y hy => hx y hy
    have e : (a⁻¹ * b) x - x = a.symm (b x - a x) := by
      rw [happ, map_sub, LinearEquiv.symm_apply_apply]
    rw [e, symm_fix u hfa _ (hsame x hp)]
    exact hsame x hp

end Main2
end GlobalTheory.TypeAsm.FibCard

namespace GlobalTheory.TypeAsm.FibCard
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem fibCardC : FibCardC := by
  intro D large₂ X Y u hStd t₀ s hs
  show (s.card : ℝ) * ((Nat.card (autLz D (X.Fu u) t₀.lam') : ℝ))⁻¹ ≤ 1
  by_cases hfin : Finite (autLz D (X.Fu u) t₀.lam')
  swap
  · have : Infinite (autLz D (X.Fu u) t₀.lam') := not_finite_iff_infinite.1 hfin
    rw [Nat.card_eq_zero_of_infinite]; simp
  have H : ∀ t : s, ∃ a : (VS D).V ≃ₗ[D.host.E] (VS D).V, a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧
      Formalism.HermitianLatticesTheory.gmap a t₀.lam' = t₀.lam' ∧ (∀ c, a ((F0 X u).e c) = (F0 X u).e c) ∧ t₀.lam' = t.1.lam' ∧
      ∃ n ∈ NLam t₀.lam (lf D (X.Fu u)), ∃ n' ∈ NLam t₀.lam' (lf D (X.Fu u)), t.1.lin = n * t₀.lin * a * n' := by
    intro t
    obtain ⟨hl, n, a, hn, ha, hga, hfa, n', hn', he⟩ :=
      _root_.GlobalTheory.TypeAsm.FibProof.fibC D large₂ X Y u hStd t₀ t.1 (hs t.1 t.2).1 (hs t.1 t.2).2
    exact ⟨a, ha, hga, hfa, hl, n, hn, n', hn', he⟩
  choose A hA using H
  have Hφ : ∀ t : s, ∃ φ : WbQ D (X.Fu u) → WbQ D (X.Fu u), ∀ (x : perpS (VS D) (X.Fu u).X)
      (hx : A t x.1 ∈ perpS (VS D) (X.Fu u).X), φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨A t x.1, hx⟩ :=
    fun t => ind_exists u (hA t).1 (hA t).2.2.1
  choose Φ hΦ using Hφ
  have hmem : ∀ t, Φ t ∈ autLz D (X.Fu u) t₀.lam' :=
    fun t => ⟨A t, stab_of_fix' u (hA t).1 (hA t).2.2.1, (hA t).2.1, hΦ t⟩
  let f : s → autLz D (X.Fu u) t₀.lam' := fun t => ⟨Φ t, hmem t⟩
  have hinj : Function.Injective f := by
    intro t₁ t₂ h12
    have hΦe : Φ t₁ = Φ t₂ := congrArg Subtype.val h12
    obtain ⟨hi1, hg1, hf1, hl1, n₁, hn₁, n₁', hn₁', he1⟩ := hA t₁
    obtain ⟨hi2, hg2, hf2, hl2, n₂, hn₂, n₂', hn₂', he2⟩ := hA t₂
    have hsame : ∀ x ∈ perpS (VS D) (X.Fu u).X, A t₂ x - A t₁ x ∈ (X.Fu u).X := by
      intro x hx
      have p1 := perp_pres u hi1 hf1 x hx
      have p2 := perp_pres u hi2 hf2 x hx
      have k1 := hΦ t₁ ⟨x, hx⟩ p1
      have k2 := hΦ t₂ ⟨x, hx⟩ p2
      rw [hΦe, k2] at k1
      have := (Submodule.Quotient.eq _).1 k1
      rw [Submodule.mem_comap] at this
      simpa using this
    have hm := nlam_of_same u hi1 hi2 hg1 hg2 hf1 hf2 hsame
    apply Subtype.ext
    apply GlobalTheory.TypeAsm.eqC_holds D X Y u t₁.1 t₂.1
    · rw [← (hs t₁.1 t₁.2).1, ← (hs t₂.1 t₂.2).1]
    · rw [← hl1, ← hl2]
    · refine ⟨n₂ * n₁⁻¹, ?_, n₁'⁻¹ * ((A t₁)⁻¹ * A t₂) * n₂', ?_, ?_⟩
      · rw [← (hs t₁.1 t₁.2).1]; exact Formalism.L2.SG.Pf.nlam_mul hn₂ (Formalism.L2.SG.Pf.nlam_inv hn₁)
      · rw [← hl1]; exact Formalism.L2.SG.Pf.nlam_mul (Formalism.L2.SG.Pf.nlam_mul (Formalism.L2.SG.Pf.nlam_inv hn₁') hm) hn₂'
      · rw [he1, he2]; group
  have hcard : Nat.card s ≤ Nat.card (autLz D (X.Fu u) t₀.lam') := Nat.card_le_card_of_injective f hinj
  have hs' : Nat.card s = s.card := by simp
  rw [hs'] at hcard
  rcases Nat.eq_zero_or_pos (Nat.card (autLz D (X.Fu u) t₀.lam')) with h0 | hpos
  · rw [h0]; simp
  · have hp : (0 : ℝ) < Nat.card (autLz D (X.Fu u) t₀.lam') := by exact_mod_cast hpos
    rw [← div_eq_mul_inv, div_le_one hp]; exact_mod_cast hcard

end GlobalTheory.TypeAsm.FibCard
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LebesgueRootCoordinatesMapBesselTorusConj
section
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

namespace GlobalTheory.ThA.TorusJac

variable {k r : ℕ}

noncomputable def dT (k r : ℕ) (α : ℂ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r then α ^ (r - i.val) else if i.val ≤ r + k then 1 else ((star α) ^ (i.val - (r + k)))⁻¹

theorem aT_eq (α : ℂ) : aT k r α = Matrix.diagonal (dT k r α) := rfl

theorem dT_mul (α β : ℂ) (i : Fin (2 * r + k + 1)) : dT k r α i * dT k r β i = dT k r (α * β) i := by
  unfold dT
  split_ifs
  · rw [mul_pow]
  · simp
  · rw [star_mul', mul_pow, mul_inv]

theorem dT_one (i : Fin (2 * r + k + 1)) : dT k r 1 i = 1 := by
  unfold dT
  split_ifs <;> simp

theorem aT_mul (α β : ℂ) : aT k r α * aT k r β = aT k r (α * β) := by
  rw [aT_eq, aT_eq, aT_eq, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact dT_mul α β i

theorem aT_one : aT k r 1 = 1 := by
  rw [aT_eq, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact dT_one i

theorem aT_inv {α : ℂ} (h : α ≠ 0) : (aT k r α)⁻¹ = aT k r α⁻¹ :=
  Matrix.inv_eq_right_inv (by rw [aT_mul, mul_inv_cancel₀ h, aT_one])

theorem aT_unit {α : ℂ} (h : α ≠ 0) : IsUnit (aT k r α).det :=
  Matrix.isUnit_det_of_right_inverse (B := aT k r α⁻¹) (by rw [aT_mul, mul_inv_cancel₀ h, aT_one])

theorem aT_real (t : ℝ) : aT k r (t : ℂ) = B.aDil k r t := by
  unfold aT B.aDil
  congr 1
  funext i
  split_ifs <;> simp

theorem aT_mem {α : ℂ} (h : α ≠ 0) : aT k r α ∈ UH (Hpk k r) := by
  show (aT k r α)ᴴ * Hpk k r * aT k r α = Hpk k r
  rw [aT_eq, Matrix.diagonal_conjTranspose]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hs : star α ≠ 0 := star_ne_zero.2 h
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, Pi.star_apply]
  by_cases h1 : i.val < r ∧ i.val + j.val = 2 * r + k
  · rw [if_pos h1]
    unfold dT
    rw [if_pos h1.1, if_neg (by omega), if_neg (by omega), show j.val - (r + k) = r - i.val by omega, star_pow,
      mul_one, mul_inv_cancel₀ (pow_ne_zero _ hs)]
  rw [if_neg h1]
  by_cases h2 : j.val < r ∧ i.val + j.val = 2 * r + k
  · rw [if_pos h2]
    unfold dT
    rw [if_pos h2.1, if_neg (by omega), if_neg (by omega), show i.val - (r + k) = r - j.val by omega, star_inv₀,
      star_pow, star_star, mul_one, inv_mul_cancel₀ (pow_ne_zero _ h)]
  rw [if_neg h2]
  by_cases h3 : r ≤ i.val ∧ i.val ≤ r + k ∧ i = j
  · rw [if_pos h3]
    obtain ⟨h3, h4, rfl⟩ := h3
    unfold dT
    rw [if_neg (show ¬ i.val < r by omega), if_pos h4, star_one, one_mul, mul_one]
  rw [if_neg h3, mul_zero, zero_mul]

theorem conj_entry {α : ℂ} (h : α ≠ 0) (g : B.Mat k r) (i j : Fin (2 * r + k + 1))
    (hg : g i j = if i = j then 1 else 0) :
    (aT k r α * g * (aT k r α)⁻¹) i j = if i = j then 1 else 0 := by
  rw [aT_inv h, aT_eq, aT_eq, Matrix.mul_diagonal, Matrix.diagonal_mul, hg]
  split_ifs with e
  · subst e
    rw [mul_one, dT_mul, mul_inv_cancel₀ h, dT_one]
  · simp

theorem conj_mem {α : ℂ} (h : α ≠ 0) {n : B.Mat k r} (hn : n ∈ Nset k r) :
    aT k r α * n * (aT k r α)⁻¹ ∈ Nset k r := by
  have hG := Formalism.FourierDecayAlt.Final.closed_subgroup_general_linear k r
  obtain ⟨h1, h2, h3⟩ := hn
  refine ⟨hG.mul_mem _ (hG.mul_mem _ (aT_mem h) _ h1) _ (hG.inv_mem _ (aT_mem h)), fun a i hi => ?_,
    fun i j a b c => ?_⟩
  · exact conj_entry h n _ _ (h2 a i hi)
  · exact conj_entry h n _ _ (h3 i j a b c)

theorem contOn : ContinuousOn (aT k r) (Metric.sphere (0 : ℂ) 1) := by
  have : ContinuousOn (dT k r) (Metric.sphere (0 : ℂ) 1) := by
    refine continuousOn_pi.2 fun i => ?_
    unfold dT
    split_ifs
    · fun_prop
    · fun_prop
    · refine ContinuousOn.inv₀ (by fun_prop) fun x hx => pow_ne_zero _ (star_ne_zero.2 ?_)
      exact ne_zero_of_mem_unit_sphere ⟨x, hx⟩
  exact (Continuous.matrix_diagonal continuous_id).comp_continuousOn this

theorem circle_compact : IsCompact (aT k r '' Metric.sphere (0 : ℂ) 1) :=
  (isCompact_sphere _ _).image_of_continuousOn contOn

theorem circle_subgroup : B2.IsClosedSubgroup (aT k r '' Metric.sphere (0 : ℂ) 1) := by
  refine ⟨⟨1, by simp, aT_one⟩, ?_, ?_, ?_, circle_compact.isClosed⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    refine ⟨a * b, ?_, (aT_mul a b).symm⟩
    simp only [mem_sphere_zero_iff_norm] at *
    rw [norm_mul, ha, hb, mul_one]
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨a⁻¹, ?_, (aT_inv (ne_zero_of_mem_unit_sphere ⟨a, ha⟩)).symm⟩
    simp only [mem_sphere_zero_iff_norm] at *
    rw [norm_inv, ha, inv_one]
  · rintro _ ⟨a, ha, rfl⟩
    exact aT_unit (ne_zero_of_mem_unit_sphere ⟨a, ha⟩)

theorem conj_cont (a : B.Mat k r) : Continuous (conjM a : Mt k r → Mt k r) :=
  (continuous_const.matrix_mul (continuous_id (X := B.Mat k r))).matrix_mul continuous_const

theorem conj_conj (a b : B.Mat k r) : (conjM a : Mt k r → Mt k r) ∘ conjM b = conjM (a * b) := by
  funext x
  show (a * (b * Matrix.of x * b⁻¹) * a⁻¹ : B.Mat k r) = a * b * Matrix.of x * (a * b)⁻¹
  simp only [Matrix.mul_inv_rev, Matrix.mul_assoc]

theorem haar_map_conj (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Nset k r) μ) (α : ℂ) (h : α ≠ 0) :
    μ.map (conjM (aT k r α)) = ENNReal.ofReal ((‖α‖ ^ B.kap k r)⁻¹) • μ := by
  have hp : 0 < ‖α‖ := norm_pos_iff.2 h
  have hc : (‖α‖ : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hu : α / (‖α‖ : ℂ) ∈ Metric.sphere (0 : ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, norm_norm, div_self hp.ne']
  have e : aT k r α = B.aDil k r ‖α‖ * aT k r (α / (‖α‖ : ℂ)) := by
    rw [← aT_real, aT_mul, mul_div_cancel₀ _ hc]
  have h1 : μ.map (conjM (aT k r (α / (‖α‖ : ℂ)))) = μ := by
    refine Formalism.FourierDecayAlt.Final.compact_conjugation k r _ _ μ (Formalism.FourierDecayAlt.Final.closed_subgroup_unipotent_radical k r) circle_subgroup circle_compact
      ?_ hμ _ ⟨_, hu, rfl⟩
    rintro _ ⟨a, ha, rfl⟩ u hu
    exact conj_mem (ne_zero_of_mem_unit_sphere ⟨a, ha⟩) hu
  rw [e, ← conj_conj, ← Measure.map_map (conj_cont _).measurable (conj_cont _).measurable, h1]
  exact Formalism.FourierDecayAlt.Final.dilation_jacobian_formula k r μ hμ _ hp

theorem muN_map_conj : ∀ (k r : ℕ) (α : ℂ), α ≠ 0 →
    (D.muN k r).map (conjM (aT k r α)) = ENNReal.ofReal ((‖α‖ ^ B.kap k r)⁻¹) • D.muN k r :=
  fun k r α h => haar_map_conj _ (Formalism.FourierDecayAlt.Final.d_muNHaar k r) α h

end GlobalTheory.ThA.TorusJac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableFlagGramNumberNormalizedIndicator
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.YMeas

theorem exists_matrix_ker {n : ℕ} (Q : Submodule ℂ (Fin n → ℂ)) :
    ∃ M : Matrix (Fin n) (Fin n) ℂ, ∀ v, M *ᵥ v = 0 ↔ v ∈ Q := by
  obtain ⟨P, hP⟩ := Q.exists_isCompl
  refine ⟨LinearMap.toMatrix' (P.subtype ∘ₗ P.projectionOnto Q hP.symm), fun v => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  simp

theorem measurable_proj {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (Q : Submodule ℂ (Fin n → ℂ)) (g : X → Matrix (Fin n) (Fin n) ℂ)
    (v : X → EuclideanSpace ℂ (Fin n)) (hg : Continuous g) (hv : Continuous v) :
    Measurable fun x => ((LinearMap.ker (Matrix.toLin' A) ⊓ Q.comap (Matrix.toLin' (g x))).comap
      (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).toLinearMap).starProjection (v x) := by
  obtain ⟨M, hM⟩ := exists_matrix_ker Q
  let Φ : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ →ₗ[ℂ]
      (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n ⊕ Fin n)) :=
    (LinearMap.toContinuousLinearMap.toLinearMap).comp Matrix.toEuclideanLin.toLinearMap
  have hΦ : Continuous Φ := Φ.continuous_of_finiteDimensional
  have hMg : Continuous fun x => M * g x := continuous_const.matrix_mul hg
  have hL : Continuous fun x => Matrix.fromRows A (M * g x) := by
    refine continuous_matrix fun i j => ?_
    rcases i with i | i
    · simpa using continuous_const
    · simpa using hMg.matrix_elem i j
  have h := GlobalTheory.measurable_starProjection_ker_clm (fun x => Φ (Matrix.fromRows A (M * g x))) v (hΦ.comp hL) hv
  have e : ∀ x, ((LinearMap.ker (Matrix.toLin' A) ⊓ Q.comap (Matrix.toLin' (g x))).comap
      (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).toLinearMap) =
      LinearMap.ker (Φ (Matrix.fromRows A (M * g x)) :
        EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n ⊕ Fin n)) := by
    intro x
    ext p
    have h1 : Φ (Matrix.fromRows A (M * g x)) p =
        WithLp.toLp 2 (Matrix.fromRows A (M * g x) *ᵥ p.ofLp) := rfl
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, h1, WithLp.toLp_eq_zero, Matrix.fromRows_mulVec,
      ← Matrix.mulVec_mulVec]
    simp only [Submodule.mem_comap, Submodule.mem_inf, LinearMap.mem_ker, Matrix.toLin'_apply, ← hM]
    constructor
    · rintro ⟨h2, h3⟩
      funext i
      rcases i with i | i
      · exact congrFun h2 i
      · exact congrFun h3 i
    · intro h2
      exact ⟨funext fun i => congrFun h2 (Sum.inl i), funext fun i => congrFun h2 (Sum.inr i)⟩
  simp only [e]
  exact h

theorem measurableSet_GG (k r : ℕ) : MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r} := by
  refine IsClosed.measurableSet ?_
  have hc : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := continuous_id
  exact isClosed_eq ((hc.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hc) continuous_const

theorem measurable_gramProj (k r j : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r)
    (w : Fin j → Fin (2 * r + k + 1) → ℂ) :
    Measurable fun x : {x : Mt k r | Matrix.of x ∈ GG k r} =>
      gramProj (Ppos k r z z' γ (Matrix.of x.1)) (fun a : Fin j => (Matrix.of x.1 : Mat k r)⁻¹ *ᵥ w a) := by
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  have hc : Continuous fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => (Matrix.of x.1 : Mat k r) :=
    continuous_subtype_val
  have hinv : Continuous fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => (Matrix.of x.1 : Mat k r)⁻¹ := by
    rw [continuous_iff_continuousAt]
    intro x
    have hx : IsUnit (Matrix.of x.1 : Mat k r).det := ((uHGroup _ _ hH).2.2 _ x.2).1
    have h1 : ContinuousAt (Inv.inv : Mat k r → _) (Matrix.of x.1) := by
      refine continuousAt_matrix_inv _ ?_
      obtain ⟨u, hu⟩ := hx
      rw [← hu]
      exact NormedRing.inverse_continuousAt u
    exact ContinuousAt.comp (f := fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => (Matrix.of x.1 : Mat k r))
      h1 hc.continuousAt
  have hp : ∀ a : Fin j, Measurable fun x : {x : Mt k r | Matrix.of x ∈ GG k r} =>
      (Ppos k r z z' γ (Matrix.of x.1)).starProjection
        (WithLp.toLp 2 ((Matrix.of x.1 : Mat k r)⁻¹ *ᵥ w a)) := fun a =>
    measurable_proj (Hpk k r - 1) (Hcom k r z z' γ ⊔ Xsp k r) _ _ hc
      ((PiLp.continuous_toLp 2 _).comp (hinv.matrix_mulVec continuous_const))
  have hG : Continuous fun u : Fin j → EuclideanSpace ℂ (Fin (2 * r + k + 1)) =>
      Real.sqrt ‖(Matrix.gram ℂ u).det‖ := by
    refine Real.continuous_sqrt.comp (continuous_norm.comp (Continuous.matrix_det ?_))
    refine continuous_matrix fun a b => ?_
    simp only [Matrix.gram_apply]
    exact (continuous_apply a).inner (continuous_apply b)
  exact hG.measurable.comp (Measurable.of_eval hp)

theorem yj_measurable : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ γ : Mat k r, inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → γ ∈ GG k r → Measurable (Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r} fun x => Yj k r hj z z' γ (Matrix.of x)) ∧ ∀ R₀ y : ℝ, MeasurableSet (Eset0 k r hj z z' γ R₀ y) := by
  intro k r j hj z z' γ hz hz' hT hT' hγ
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  have hS := measurableSet_GG k r
  have hY : Measurable fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => Yj k r hj z z' γ (Matrix.of x.1) :=
    (measurable_gramProj k r j z z' γ _).div_const _
  have hc : Continuous fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => (Matrix.of x.1 : Mat k r) :=
    continuous_subtype_val
  have h1 : Continuous fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => Sg2 k r z' (Matrix.of x.1) :=
    (TwoSided.Sg2_invariant_continuousOn_one_le_bounds k r z' hz' hT').2.2.1.comp_continuous hc fun x => x.2
  have h2 : Continuous fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => Sg2 k r z (γ * Matrix.of x.1) :=
    (TwoSided.Sg2_invariant_continuousOn_one_le_bounds k r z hz hT).2.2.1.comp_continuous (continuous_const.matrix_mul hc)
      fun x => (uHGroup _ _ hH).2.1 _ hγ _ x.2
  refine ⟨?_, fun R₀ y => ?_⟩
  · refine measurable_of_restrict_of_restrict_compl hS ?_ ?_
    · convert hY using 1
      funext x
      exact Set.indicator_of_mem x.2 _
    · convert (measurable_const (a := (0 : ℝ))) using 1
      funext x
      exact Set.indicator_of_notMem x.2 _
  have e : Eset0 k r hj z z' γ R₀ y = Subtype.val '' {x : {x : Mt k r | Matrix.of x ∈ GG k r} |
      Sg2 k r z' (Matrix.of x.1) ≤ R₀ ∧ Sg2 k r z (γ * Matrix.of x.1) ≤ R₀ ∧
        y < Yj k r hj z z' γ (Matrix.of x.1) ∧ Yj k r hj z z' γ (Matrix.of x.1) ≤ 2 * y} := by
    ext x
    constructor
    · rintro ⟨hx, h⟩
      exact ⟨⟨x, hx⟩, h, rfl⟩
    · rintro ⟨⟨x, hx⟩, h, rfl⟩
      exact ⟨hx, h⟩
  rw [e]
  refine hS.subtype_image ?_
  exact (measurableSet_le h1.measurable measurable_const).inter
    ((measurableSet_le h2.measurable measurable_const).inter
      ((measurableSet_lt measurable_const hY).inter (measurableSet_le hY measurable_const)))

end GlobalTheory.Amp.YMeas
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowSplitFiniteArchimedeanPartsOfStepsStatement
section
open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowSplitFiniteArchimedeanParts_of_steps : StepAnalyticConstantsP → StepSizes → StepClass → StepNormals → StepPoints → StepHeight → NGCut2P := by
  first | exact @GlobalTheory.NGRow.ngCut2P_of_steps | exact GlobalTheory.NGRow.ngCut2P_of_steps | (intros; apply GlobalTheory.NGRow.ngCut2P_of_steps <;> assumption)
end

