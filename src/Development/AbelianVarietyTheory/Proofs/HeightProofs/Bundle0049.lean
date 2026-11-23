module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsSmoothAutomorphicFunctionCompactFamilyAverage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryCoordFunMulEqSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFourier

open MeasureTheory

variable {n : ℕ}

theorem integral_conjK (ε : Fin n → Bool) (f : KG ε → ℂ) (a : KG ε) :
    ∫ k, f (a * k * a⁻¹) ∂(muK ε) = ∫ k, f k ∂(muK ε) := by
  haveI : Measure.IsMulRightInvariant (muK ε) := ⟨(compact_haar_holds n ε).2.2.1⟩
  have h1 := integral_mul_right_eq_self (μ := muK ε) (fun k => f (a * k)) a⁻¹
  have h2 := integral_mul_left_eq_self (μ := muK ε) f a
  simp only [mul_assoc] at h1 ⊢
  exact h1.trans h2

theorem integrable_of_continuousK {ε : Fin n → Bool} {f : KG ε → ℂ} (hf : Continuous f) :
    Integrable f (muK ε) := by
  haveI : IsFiniteMeasure (muK ε) := ⟨isCompact_univ.measure_lt_top⟩
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem lowV_le (ε : Fin n → Bool) (i : ℕ) : lowV ε i ≤ polyV ε i := by
  cases i with
  | zero => exact bot_le
  | succ j => exact polyV_mono ε (Nat.le_succ j)

theorem integral_sub_mulK {ε : Fin n → Bool} {f g h : KG ε → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hh : Continuous h) :
    ∫ k, (f - g) k * h k ∂(muK ε) = ∫ k, f k * h k ∂(muK ε) - ∫ k, g k * h k ∂(muK ε) := by
  rw [← integral_sub (integrable_of_continuousK (f := fun k => f k * h k) (hf.mul hh))
    (integrable_of_continuousK (f := fun k => g k * h k) (hg.mul hh))]
  congr 1; funext k; simp [sub_mul]

theorem isKer_unique {ε : Fin n → Bool} {i : ℕ} {e e' : KG ε → ℂ} (he : IsKer ε i e) (he' : IsKer ε i e') :
    e = e' := by
  have hdmem : (e - e') ∈ polyV ε i := sub_mem he.1 he'.1
  have hc : Continuous (e - e') := continuous_of_mem hdmem
  have hce : Continuous e := continuous_of_mem he.1
  have hce' : Continuous e' := continuous_of_mem he'.1
  have hp : (fun k => star ((e - e') k)) ∈ polyV ε i := star_mem hdmem
  have horth : ∀ q ∈ lowV ε i, ∫ k, star (q k) * star ((e - e') k) ∂(muK ε) = 0 := by
    intro q hq
    have hqc : Continuous q := continuous_of_mem (lowV_le ε i hq)
    have h1 := he.2.1 q hq
    have h2 := he'.2.1 q hq
    have h3 : ∫ k, (e - e') k * q k ∂(muK ε) = 0 := by
      rw [integral_sub_mulK hce hce' hqc, h1, h2, sub_self]
    calc ∫ k, star (q k) * star ((e - e') k) ∂(muK ε)
        = ∫ k, (starRingEnd ℂ) ((e - e') k * q k) ∂(muK ε) := by
          congr 1; funext k; rw [map_mul, mul_comm]; rfl
      _ = (starRingEnd ℂ) (∫ k, (e - e') k * q k ∂(muK ε)) := integral_conj
      _ = 0 := by rw [h3, map_zero]
  have h0 : ∫ k, (e - e') k * star ((e - e') k) ∂(muK ε) = 0 := by
    have a1 := he.2.2 _ hp horth
    have a2 := he'.2.2 _ hp horth
    have hs : Continuous (fun k => star ((e - e') k)) := continuous_star.comp hc
    rw [integral_sub_mulK hce hce' hs, a1, a2, sub_self]
  have hns : Continuous (fun k => Complex.normSq ((e - e') k)) := Complex.continuous_normSq.comp hc
  have h1 : ∫ k, Complex.normSq ((e - e') k) ∂(muK ε) = 0 := by
    have : (fun k => (e - e') k * star ((e - e') k)) = fun k => ((Complex.normSq ((e - e') k) : ℝ) : ℂ) :=
      funext fun k => Complex.mul_conj _
    rw [this, integral_complex_ofReal] at h0
    exact_mod_cast h0
  have h2 : (fun k => Complex.normSq ((e - e') k)) =ᵐ[muK ε] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun k => Complex.normSq_nonneg _)
      ((integrable_of_continuousK (Complex.continuous_ofReal.comp hns)).re)).1 h1
  have h3 : (fun k => Complex.normSq ((e - e') k)) = 0 :=
    (Continuous.ae_eq_iff_eq (muK ε) hns continuous_const).1 h2
  funext k
  have := congrFun h3 k
  simp only [Pi.zero_apply, map_eq_zero, Pi.sub_apply] at this
  exact sub_eq_zero.1 this

theorem conj_mem {ε : Fin n → Bool} (a : KG ε) {d : ℕ} {φ : KG ε → ℂ} (h : φ ∈ polyV ε d) :
    (fun k => φ (a * k * a⁻¹)) ∈ polyV ε d := by
  have := mul_right_mem a⁻¹ (mul_left_mem a h)
  simpa only [mul_assoc] using this

theorem conj_mem_low {ε : Fin n → Bool} (a : KG ε) {i : ℕ} {φ : KG ε → ℂ} (h : φ ∈ lowV ε i) :
    (fun k => φ (a * k * a⁻¹)) ∈ lowV ε i := by
  cases i with
  | zero =>
    rw [lowV, Submodule.mem_bot] at h ⊢
    subst h
    rfl
  | succ j => exact conj_mem a h

theorem isKer_conj {ε : Fin n → Bool} {i : ℕ} {e : KG ε → ℂ} (he : IsKer ε i e) (a : KG ε) :
    IsKer ε i (fun k => e (a * k * a⁻¹)) := by
  have key : ∀ f g : KG ε → ℂ, ∫ k, f (a * k * a⁻¹) * g k ∂(muK ε) = ∫ k, f k * g (a⁻¹ * k * a) ∂(muK ε) := by
    intro f g
    rw [← integral_conjK ε (fun k => f k * g (a⁻¹ * k * a)) a]
    congr 1; funext k
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  refine ⟨conj_mem a he.1, ?_, ?_⟩
  · intro q hq
    rw [key]
    have := conj_mem_low a⁻¹ hq
    simpa only [inv_inv] using he.2.1 _ this
  · intro p hp horth
    rw [key]
    have hp' : (fun k => p (a⁻¹ * k * a)) ∈ polyV ε i := by simpa only [inv_inv] using conj_mem a⁻¹ hp
    have horth' : ∀ q ∈ lowV ε i, ∫ k, star (q k) * p (a⁻¹ * k * a) ∂(muK ε) = 0 := by
      intro q hq
      rw [← integral_conjK ε (fun k => star (q k) * p (a⁻¹ * k * a)) a]
      have := horth _ (conj_mem_low a hq)
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using this
    rw [he.2.2 _ hp' horth']
    simp

theorem isKer_class : ∀ {n : ℕ} (ε : Fin n → Bool) (i : ℕ) (e : KG ε → ℂ), IsKer ε i e →
    ∀ a k : KG ε, e (a * k * a⁻¹) = e k := by
  intro n ε i e he a k
  have := isKer_unique (isKer_conj he a) he
  exact congrFun this k

end GlobalTheory.KFourier

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryIntegralConjInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFourier

open MeasureTheory

variable {n : ℕ}

theorem integrable_of_continuous' {ε : Fin n → Bool} {E : Type*} [NormedAddCommGroup E] {f : KG ε → E} (hf : Continuous f) :
    Integrable f (muK ε) :=
  integrableOn_univ.1 (hf.continuousOn.integrableOn_compact isCompact_univ)

theorem eq_zero_of_integral_mul_star {ε : Fin n → Bool} {φ : KG ε → ℂ} (hc : Continuous φ)
    (h : ∫ k, φ k * star (φ k) ∂(muK ε) = 0) : φ = 0 := by
  have e : (fun k => φ k * star (φ k)) = fun k => ((Complex.normSq (φ k) : ℝ) : ℂ) := by
    funext k; exact Complex.mul_conj (φ k)
  rw [e, integral_complex_ofReal, Complex.ofReal_eq_zero] at h
  have hcs : Continuous fun k => Complex.normSq (φ k) := Complex.continuous_normSq.comp hc
  have hae := (integral_eq_zero_iff_of_nonneg (fun k => Complex.normSq_nonneg (φ k))
    (integrable_of_continuous' hcs)).1 h
  have h2 : (fun k => Complex.normSq (φ k)) = 0 := (Continuous.ae_eq_iff_eq (muK ε) hcs continuous_const).1 hae
  funext k
  have := congrFun h2 k
  simpa using this

theorem exists_isKer (ε : Fin n → Bool) (i : ℕ) : ∃ e, IsKer ε i e := by
  classical
  have hlow : lowV ε i ≤ polyV ε i := by
    cases i with
    | zero => simp [lowV]
    | succ j => simpa [lowV] using polyV_mono ε (Nat.le_succ j)
  let W : Submodule ℂ (KG ε → ℂ) :=
    { carrier := {p | p ∈ polyV ε i ∧ ∀ q ∈ lowV ε i, ∫ k, star (q k) * p k ∂(muK ε) = 0}
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨add_mem ha hb, fun q hq => ?_⟩
        have hq' := continuous_of_mem (hlow hq)
        have h1 := integral_add (μ := muK ε) (f := fun k => star (q k) * a k) (g := fun k => star (q k) * b k)
          (integrable_of_continuous' (hq'.star.mul (continuous_of_mem ha)))
          (integrable_of_continuous' (hq'.star.mul (continuous_of_mem hb)))
        simp only [Pi.add_apply, mul_add]
        rw [h1, ha' q hq, hb' q hq, add_zero]
      zero_mem' := ⟨Submodule.zero_mem _, fun q _ => by simp⟩
      smul_mem' := by
        rintro c a ⟨ha, ha'⟩
        refine ⟨Submodule.smul_mem _ c ha, fun q hq => ?_⟩
        simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
        rw [integral_const_mul, ha' q hq, mul_zero] }
  have hW : ∀ p, p ∈ W ↔ p ∈ polyV ε i ∧ ∀ q ∈ lowV ε i, ∫ k, star (q k) * p k ∂(muK ε) = 0 :=
    fun p => Iff.rfl

  let B : polyV ε i →ₗ[ℂ] Module.Dual ℂ (polyV ε i) :=
    LinearMap.mk₂ ℂ (fun e p : polyV ε i => ∫ k, (e : KG ε → ℂ) k * (p : KG ε → ℂ) k ∂(muK ε))
      (fun e e' p => by
        have h1 := integral_add (μ := muK ε) (f := fun k => (e : KG ε → ℂ) k * (p : KG ε → ℂ) k)
          (g := fun k => (e' : KG ε → ℂ) k * (p : KG ε → ℂ) k)
          (integrable_of_continuous' ((continuous_of_mem e.2).mul (continuous_of_mem p.2)))
          (integrable_of_continuous' ((continuous_of_mem e'.2).mul (continuous_of_mem p.2)))
        simp only [Submodule.coe_add, Pi.add_apply, add_mul]
        exact h1)
      (fun c e p => by
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
        exact integral_const_mul c _)
      (fun e p p' => by
        have h1 := integral_add (μ := muK ε) (f := fun k => (e : KG ε → ℂ) k * (p : KG ε → ℂ) k)
          (g := fun k => (e : KG ε → ℂ) k * (p' : KG ε → ℂ) k)
          (integrable_of_continuous' ((continuous_of_mem e.2).mul (continuous_of_mem p.2)))
          (integrable_of_continuous' ((continuous_of_mem e.2).mul (continuous_of_mem p'.2)))
        simp only [Submodule.coe_add, Pi.add_apply, mul_add]
        exact h1)
      (fun c e p => by
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
        exact integral_const_mul c _)
  have hB : ∀ e p : polyV ε i, B e p = ∫ k, (e : KG ε → ℂ) k * (p : KG ε → ℂ) k ∂(muK ε) := fun _ _ => rfl
  have hinj : Function.Injective B := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro e he
    have h0 := hB e ⟨_, star_mem e.2⟩
    rw [he] at h0
    have hz : (e : KG ε → ℂ) = 0 := eq_zero_of_integral_mul_star (continuous_of_mem e.2) h0.symm
    exact Subtype.ext hz
  have hsurj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank Subspace.dual_finrank_eq.symm).1 hinj

  let f : W →ₗ[ℂ] (KG ε → ℂ) ⧸ lowV ε i := (lowV ε i).mkQ ∘ₗ W.subtype
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    have hwl : (w : KG ε → ℂ) ∈ lowV ε i := (Submodule.Quotient.mk_eq_zero _).1 hw
    have h0 := ((hW w).1 w.2).2 _ hwl
    have hc : (fun k => star ((w : KG ε → ℂ) k) * (w : KG ε → ℂ) k) =
        fun k => (w : KG ε → ℂ) k * star ((w : KG ε → ℂ) k) := funext fun k => mul_comm _ _
    rw [hc] at h0
    exact Subtype.ext (eq_zero_of_integral_mul_star (continuous_of_mem ((hW w).1 w.2).1) h0)
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective f hker
  let g : (KG ε → ℂ) →ₗ[ℂ] ℂ := (LinearMap.proj 1 : (KG ε → ℂ) →ₗ[ℂ] ℂ) ∘ₗ W.subtype ∘ₗ r ∘ₗ (lowV ε i).mkQ
  have hgW : ∀ w ∈ W, g w = w 1 := by
    intro w hw
    have := LinearMap.congr_fun hr ⟨w, hw⟩
    simp only [LinearMap.comp_apply, LinearMap.id_apply, f, Submodule.subtype_apply] at this
    simp only [g, LinearMap.comp_apply, Submodule.subtype_apply, this, LinearMap.proj_apply]
  have hgU : ∀ q ∈ lowV ε i, g q = 0 := by
    intro q hq
    simp only [g, LinearMap.comp_apply, (Submodule.Quotient.mk_eq_zero _).2 hq, Submodule.mkQ_apply, map_zero,
      LinearMap.proj_apply]
  obtain ⟨e, he⟩ := hsurj (g ∘ₗ (polyV ε i).subtype)
  refine ⟨e, e.2, fun q hq => ?_, fun p hp hpo => ?_⟩
  · have := LinearMap.congr_fun he ⟨q, hlow hq⟩
    rw [hB] at this
    rw [this]
    exact hgU q hq
  · have := LinearMap.congr_fun he ⟨p, hp⟩
    rw [hB] at this
    rw [this]
    exact hgW p ⟨hp, hpo⟩

end GlobalTheory.KFourier
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryRightDerivConjInvariantAverageEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KAvgDeriv

open MeasureTheory Filter Topology GlobalTheory.KFourier

variable {n : ℕ}

theorem toMK_expK_real {ε : Fin n → Bool} {X : Mx n} (hX : inK ε X) (t : ℝ) :
    toMK (expK ε X t) = NormedSpace.exp (t • X) := by
  rw [toMK_expK hX t, Complex.coe_smul]

theorem toMK_mem_UJ {ε : Fin n → Bool} (k : KG ε) : toMK k ∈ UJset ε := K_le_UJ (toMK_mem_K k)

theorem integral_conj_swap {ε : Fin n → Bool} (e : KG ε → ℂ) (he : ∀ a k : KG ε, e (a * k * a⁻¹) = e k)
    (φ : Mx n → ℂ) (g : Mx n) (κ : KG ε) :
    ∫ k, e k * φ (g * toMK κ * toMK k) ∂(muK ε) = ∫ k, e k * φ (g * toMK k * toMK κ) ∂(muK ε) := by
  have h1 := integral_mul_left_eq_self (μ := muK ε) (fun k => e k * φ (g * toMK κ * toMK k)) κ⁻¹
  have h2 := integral_mul_right_eq_self (μ := muK ε) (fun k => e (κ⁻¹ * k) * φ (g * toMK k)) κ
  have ea : ∀ k, g * toMK κ * toMK (κ⁻¹ * k) = g * toMK k := fun k => by
    rw [mul_assoc, ← toMK_mul, mul_inv_cancel_left]
  have eb : ∀ k, e (κ⁻¹ * (k * κ)) = e k := fun k => by
    have := he κ⁻¹ k
    rwa [inv_inv, mul_assoc] at this
  calc ∫ k, e k * φ (g * toMK κ * toMK k) ∂(muK ε)
      = ∫ k, e (κ⁻¹ * k) * φ (g * toMK κ * toMK (κ⁻¹ * k)) ∂(muK ε) := h1.symm
    _ = ∫ k, e (κ⁻¹ * k) * φ (g * toMK k) ∂(muK ε) := by simp only [ea]
    _ = ∫ k, e (κ⁻¹ * (k * κ)) * φ (g * toMK (k * κ)) ∂(muK ε) := h2.symm
    _ = _ := by simp only [eb, toMK_mul, mul_assoc]

variable {ε : Fin n → Bool} {F : List (Mx n) → Mx n → ℂ}

theorem measurable_fam (hD : IsDerFam ε F) {f : Mx n → ℂ} (hf : ContinuousOn f (UJset ε))
    (hF0 : ∀ g ∈ UJset ε, F [] g = f g) :
    ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ a ∈ UJset ε, ∀ b ∈ UJset ε,
      Measurable fun k : KG ε => F l (a * toMK k * b) := by
  intro l
  induction l with
  | nil =>
    intro _ a ha b hb
    have hm : ∀ k : KG ε, a * toMK k * b ∈ UJset ε := fun k => mul_mem_UJ (mul_mem_UJ ha (toMK_mem_UJ k)) hb
    have e1 : (fun k : KG ε => F [] (a * toMK k * b)) = fun k => f (a * toMK k * b) :=
      funext fun k => hF0 _ (hm k)
    rw [e1]
    exact (hf.comp_continuous ((continuous_const.mul (continuous_toMK ε)).mul continuous_const) hm).measurable
  | cons X l ih =>
    intro hl a ha b hb
    have hX : X ∈ lieSet ε := hl X List.mem_cons_self
    have hl' : ∀ Y ∈ l, Y ∈ lieSet ε := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
    let s : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
    have hs0 : Tendsto s atTop (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall fun m => by simp only [Set.mem_compl_iff, Set.mem_singleton_iff, s]; positivity⟩
    have hmeas : ∀ m : ℕ, Measurable fun k : KG ε =>
        (s m)⁻¹ • (F l (a * toMK k * (b * NormedSpace.exp (s m • X))) - F l (a * toMK k * b)) := fun m => by
      have := ((ih hl' a ha _ (mul_mem_UJ hb (exp_mem_UJ hX (s m)))).sub (ih hl' a ha b hb)).const_smul (s m)⁻¹
      exact this
    refine measurable_of_tendsto_metrizable hmeas (tendsto_pi_nhds.2 fun k => ?_)
    have hg : a * toMK k * b ∈ UJset ε := mul_mem_UJ (mul_mem_UJ ha (toMK_mem_UJ k)) hb
    have hd := (hasDerivAt_iff_tendsto_slope.1 (hD l hl' X hX _ hg)).comp hs0
    refine hd.congr fun m => ?_
    simp only [Function.comp_apply, slope_def_module, sub_zero, zero_smul, NormedSpace.exp_zero, mul_one,
      mul_assoc]

theorem hasDerivAt_avg (hD : IsDerFam ε F) {N : ℕ} (hG : FamGrowth ε N F) {f : Mx n → ℂ}
    (hf : ContinuousOn f (UJset ε)) (hF0 : ∀ g ∈ UJset ε, F [] g = f g) {e : KG ε → ℂ} (hec : Continuous e)
    (he : ∀ a k : KG ε, e (a * k * a⁻¹) = e k) {l : List (Mx n)} (hl : ∀ Y ∈ l, Y ∈ lieSet ε) {X : Mx n}
    (hX : inK ε X) {g : Mx n} (hg : g ∈ UJset ε) :
    HasDerivAt (fun t : ℝ => ∫ k, e k * F l (g * toMK (expK ε X t) * toMK k) ∂(muK ε))
      (∫ k, e k * F (X :: l) (g * toMK k) ∂(muK ε)) 0 := by
  have hXl : X ∈ lieSet ε := hX.1
  have hl' : ∀ Y ∈ X :: l, Y ∈ lieSet ε := by
    intro Y hY
    rcases List.mem_cons.1 hY with rfl | h
    exacts [hXl, hl Y h]
  have hre : (fun t : ℝ => ∫ k, e k * F l (g * toMK (expK ε X t) * toMK k) ∂(muK ε)) =
      fun t => ∫ k, e k * F l (g * toMK k * NormedSpace.exp (t • X)) ∂(muK ε) := by
    funext t
    rw [integral_conj_swap e he, toMK_expK_real hX]
  rw [hre]
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hec.continuousOn
  obtain ⟨C, hC⟩ := hG (X :: l) hl'
  obtain ⟨C0, hC0⟩ := hG l hl
  have hmem : ∀ (k : KG ε) (s : ℝ), g * toMK k * NormedSpace.exp (s • X) ∈ UJset ε := fun k s =>
    mul_mem_UJ (mul_mem_UJ hg (toMK_mem_UJ k)) (exp_mem_UJ hXl s)
  have hhs : ∀ (k : KG ε) (s : ℝ), hs (g * toMK k * NormedSpace.exp (s • X)) = hs g := fun k s => by
    rw [← toMK_expK_real hX, mul_assoc, ← toMK_mul]
    exact ((hermitian_small_ball n ε).2 _ _ (toMK_mem_K _)).1
  have hem : Measurable e := hec.measurable
  have hbd : ∀ (l' : List (Mx n)) (C' : ℝ), (∀ h ∈ UJset ε, ‖F l' h‖ ≤ C' * (1 + hs h) ^ N) →
      ∀ (k : KG ε) (s : ℝ), ‖e k * F l' (g * toMK k * NormedSpace.exp (s • X))‖ ≤ M * (C' * (1 + hs g) ^ N) :=
    fun l' C' hC' k s => by
      rw [norm_mul]
      refine mul_le_mul (hM k trivial) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hM k trivial))
      rw [← hhs k s]
      exact hC' _ (hmem k s)
  have hmeasF : ∀ t : ℝ, AEStronglyMeasurable (fun k => e k * F l (g * toMK k * NormedSpace.exp (t • X))) (muK ε) :=
    fun t => (hem.mul (measurable_fam hD hf hF0 l hl g hg _ (exp_mem_UJ hXl t))).aestronglyMeasurable
  have hmeasF' : AEStronglyMeasurable (fun k => e k * F (X :: l) (g * toMK k * NormedSpace.exp ((0 : ℝ) • X)))
      (muK ε) := (hem.mul (measurable_fam hD hf hF0 (X :: l) hl' g hg _ (exp_mem_UJ hXl 0))).aestronglyMeasurable
  have hint : Integrable (fun k => e k * F l (g * toMK k * NormedSpace.exp ((0 : ℝ) • X))) (muK ε) :=
    Integrable.mono' (integrable_const (M * (C0 * (1 + hs g) ^ N))) (hmeasF 0) (ae_of_all _ fun k => hbd l C0 hC0 k 0)
  have hdif : ∀ (k : KG ε) (s : ℝ), HasDerivAt (fun t : ℝ => e k * F l (g * toMK k * NormedSpace.exp (t • X)))
      (e k * F (X :: l) (g * toMK k * NormedSpace.exp (s • X))) s := fun k s => by
    have h1 := hD l hl X hXl _ (hmem k s)
    have h2 : HasDerivAt (fun t : ℝ => F l (g * toMK k * NormedSpace.exp (s • X) * NormedSpace.exp ((t - s) • X)))
        (F (X :: l) (g * toMK k * NormedSpace.exp (s • X))) s :=
      HasDerivAt.comp_sub_const (f := fun t : ℝ => F l (g * toMK k * NormedSpace.exp (s • X) * NormedSpace.exp (t • X)))
        s s (by rw [sub_self]; exact h1)
    have e2 : (fun t : ℝ => F l (g * toMK k * NormedSpace.exp (s • X) * NormedSpace.exp ((t - s) • X))) =
        fun t => F l (g * toMK k * NormedSpace.exp (t • X)) := by
      funext t
      rw [mul_assoc (g * toMK k), ← exp_add_smul, add_sub_cancel]
    rw [e2] at h2
    exact h2.const_mul (e k)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := muK ε) (x₀ := (0 : ℝ))
    (F := fun t k => e k * F l (g * toMK k * NormedSpace.exp (t • X)))
    (F' := fun t k => e k * F (X :: l) (g * toMK k * NormedSpace.exp (t • X)))
    (bound := fun _ => M * (C * (1 + hs g) ^ N)) (s := Set.univ) Filter.univ_mem (Eventually.of_forall hmeasF) hint hmeasF'
    (ae_of_all _ fun k t _ => hbd (X :: l) C hC k t) (integrable_const _) (ae_of_all _ fun k s _ => hdif k s)
  have e3 : (fun k => e k * F (X :: l) (g * toMK k * NormedSpace.exp ((0 : ℝ) • X))) =
      fun k => e k * F (X :: l) (g * toMK k) := by
    funext k
    rw [zero_smul, NormedSpace.exp_zero, mul_one]
  simpa only [e3] using key.2

theorem rder_avgK_all (hD : IsDerFam ε F) {N : ℕ} (hG : FamGrowth ε N F) {f : Mx n → ℂ}
    (hf : ContinuousOn f (UJset ε)) (hF0 : ∀ g ∈ UJset ε, F [] g = f g) {e : KG ε → ℂ} (hec : Continuous e)
    (he : ∀ a k : KG ε, e (a * k * a⁻¹) = e k) {y : Mx n} (hy : y ∈ UJset ε) :
    ∀ u : List (Mx n), (∀ X ∈ u, inK ε X) → ∀ k' : KG ε,
      rder ε u (avgK ε e f y) k' = ∫ k, e k * F u (y * toMK k' * toMK k) ∂(muK ε) := by
  intro u
  induction u with
  | nil =>
    intro _ k'
    rw [rder_nil]
    refine integral_congr_ae (ae_of_all _ fun k => ?_)
    simp only
    rw [hF0 _ (mul_mem_UJ (mul_mem_UJ hy (toMK_mem_UJ k')) (toMK_mem_UJ k))]
  | cons X l ih =>
    intro hu k'
    have hX : inK ε X := hu X List.mem_cons_self
    have hlK : ∀ Y ∈ l, inK ε Y := fun Y hY => hu Y (List.mem_cons_of_mem _ hY)
    have hl : ∀ Y ∈ l, Y ∈ lieSet ε := fun Y hY => (hlK Y hY).1
    rw [rder_cons]
    have e1 : (fun t : ℝ => rder ε l (avgK ε e f y) (k' * expK ε X t)) =
        fun t => ∫ k, e k * F l (y * toMK k' * toMK (expK ε X t) * toMK k) ∂(muK ε) := by
      funext t
      rw [ih hlK, toMK_mul, mul_assoc y]
    rw [e1]
    exact (hasDerivAt_avg hD hG hf hF0 hec he hl hX (mul_mem_UJ hy (toMK_mem_UJ k'))).deriv

theorem rder_avgK_one (ε : Fin n → Bool) (N : ℕ) (F : List (Mx n) → Mx n → ℂ) (hD : IsDerFam ε F)
    (hG : FamGrowth ε N F) (f : Mx n → ℂ) (hf : ContinuousOn f (UJset ε)) (hF0 : ∀ g ∈ UJset ε, F [] g = f g)
    (e : KG ε → ℂ) (hec : Continuous e) (he : ∀ a k : KG ε, e (a * k * a⁻¹) = e k) (u : List (Mx n))
    (hu : ∀ X ∈ u, inK ε X) (y : Mx n) (hy : y ∈ UJset ε) :
    GlobalTheory.KFourier.rder ε u (GlobalTheory.KFourier.avgK ε e f y) 1 = ∫ k, e k * F u (y * toMK k) ∂(muK ε) := by
  rw [rder_avgK_all hD hG hf hF0 hec he hy u hu 1, toMK_one, mul_one]

end GlobalTheory.KAvgDeriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.IsSmoothAutomorphicFunctionCompactFamilyAverageStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSmoothAutomorphicFunction_compactFamily_average : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam (D := D) θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (K : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (κ : K → Matrix (Fin V.rank) (Fin V.rank) ℂ), Continuous κ → (∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) → ∀ e : K → ℂ, Continuous e → ∀ φ : GA D V → ℂ, IsAutFunSm θ V φ → IsAutFunSm θ V (fun x => ∫ k, e k * φ (x * atTau θ V τ (κ k)) ∂μ) := by
  first | exact @GlobalTheory.RealAverage.isAutFunSm_average | exact GlobalTheory.RealAverage.isAutFunSm_average | (intros; apply GlobalTheory.RealAverage.isAutFunSm_average <;> assumption)
end

