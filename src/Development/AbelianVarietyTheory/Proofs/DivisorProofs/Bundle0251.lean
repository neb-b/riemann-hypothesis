module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0042
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0133

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeMapPrimeMap
section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.FixNormCls

variable {E : Type} [Field E] [NumberField E]

def ord (P : HeightOneSpectrum (𝓞 E)) (x : E) : ℤ :=
  FractionalIdeal.count E P (FractionalIdeal.spanSingleton (𝓞 E)⁰ x)

def primeMap (τ : E ≃+* E) (P : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) where
  asIdeal := P.asIdeal.comap (RingOfIntegers.mapRingEquiv τ.symm : 𝓞 E →+* 𝓞 E)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    apply P.ne_bot
    rw [eq_bot_iff] at h ⊢
    intro x hx
    have : (RingOfIntegers.mapRingEquiv τ) x ∈
        P.asIdeal.comap (RingOfIntegers.mapRingEquiv τ.symm : 𝓞 E →+* 𝓞 E) := by
      rw [Ideal.mem_comap]
      convert hx using 1
      exact (RingOfIntegers.mapRingEquiv τ).symm_apply_apply x
    have h2 := h this
    rw [Submodule.mem_bot, map_eq_zero_iff _ (RingOfIntegers.mapRingEquiv τ).injective] at h2
    rw [Submodule.mem_bot]; exact h2

theorem mem_primeMap (τ : E ≃+* E) (P : HeightOneSpectrum (𝓞 E)) (a : 𝓞 E) :
    a ∈ (primeMap τ P).asIdeal ↔ RingOfIntegers.mapRingEquiv τ.symm a ∈ P.asIdeal :=
  Ideal.mem_comap

theorem ord_zero (P : HeightOneSpectrum (𝓞 E)) : ord P (0 : E) = 0 := by
  simp [ord, FractionalIdeal.count_zero]

theorem ord_mul (P : HeightOneSpectrum (𝓞 E)) {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    ord P (x * y) = ord P x + ord P y := by
  unfold ord
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton]
  exact FractionalIdeal.count_mul E P (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy)

theorem ord_inv (P : HeightOneSpectrum (𝓞 E)) (x : E) : ord P x⁻¹ = - ord P x := by
  unfold ord
  rw [← FractionalIdeal.spanSingleton_inv, FractionalIdeal.count_inv]

theorem ord_div (P : HeightOneSpectrum (𝓞 E)) {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    ord P (x / y) = ord P x - ord P y := by
  rw [div_eq_mul_inv, ord_mul P hx (inv_ne_zero hy), ord_inv, sub_eq_add_neg]

theorem ord_one (P : HeightOneSpectrum (𝓞 E)) : ord P (1 : E) = 0 := by
  simp [ord, FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]

theorem ord_primeMap (τ : E ≃+* E) (P : HeightOneSpectrum (𝓞 E)) (x : E) :
    ord (primeMap τ P) (τ x) = ord P x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [ord_zero]
  exact GlobalTheory.OrdTransport.count_spanSingleton_ringEquiv (𝓞 E) E (RingOfIntegers.mapRingEquiv τ) τ
    (fun a => rfl) P (primeMap τ P)
    (fun a => by
      rw [mem_primeMap]
      have : RingOfIntegers.mapRingEquiv τ.symm (RingOfIntegers.mapRingEquiv τ a) = a :=
        RingOfIntegers.ext (by change τ.symm (τ (a : E)) = (a : E); exact τ.symm_apply_apply _)
      rw [this]) x hx

theorem primeMap_primeMap (τ : E ≃+* E) (hτ : ∀ x, τ (τ x) = x) (P : HeightOneSpectrum (𝓞 E)) :
    primeMap τ (primeMap τ P) = P := by
  ext a
  rw [mem_primeMap, mem_primeMap]
  have : RingOfIntegers.mapRingEquiv τ.symm (RingOfIntegers.mapRingEquiv τ.symm a) = a := by
    apply RingOfIntegers.ext
    change τ.symm (τ.symm (a : E)) = (a : E)
    rw [RingEquiv.symm_apply_eq, RingEquiv.symm_apply_eq, hτ]
  rw [this]

end GlobalTheory.FixNormCls
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdImIteratedWirtingerDerivWordDifferentiableOn
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwo.ProdImWirt
variable {Φ : Type} [Fintype Φ]

noncomputable def mono (c : ℂ → ℂ) (a : ℂ → Φ → ℂ) (σ : ℂ) (z : Φ → ℂ) : ℂ :=
  c σ * Complex.exp (∑ τ, a σ τ * ((Real.log (z τ).im : ℝ) : ℂ))

theorem hasFDerivAt_logIm (τ : Φ) {z : Φ → ℂ} (hz : (z τ).im ≠ 0) :
    HasFDerivAt (fun z : Φ → ℂ => ((Real.log (z τ).im : ℝ) : ℂ))
      (ofRealCLM.comp (((z τ).im)⁻¹ • (imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Φ => ℂ) τ)))) z := by
  have h1 : HasFDerivAt (fun z : Φ → ℂ => (z τ).im) (imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Φ => ℂ) τ)) z :=
    (imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Φ => ℂ) τ)).hasFDerivAt
  have h2 := h1.log hz
  exact ofRealCLM.hasFDerivAt.comp z h2

theorem hasFDerivAt_expo (A : Φ → ℂ) {z : Φ → ℂ} (hz : ∀ τ, (z τ).im ≠ 0) :
    HasFDerivAt (fun z : Φ → ℂ => ∑ τ, A τ * ((Real.log (z τ).im : ℝ) : ℂ))
      (∑ τ, A τ • (ofRealCLM.comp (((z τ).im)⁻¹ • (imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Φ => ℂ) τ))))) z := by
  have := HasFDerivAt.sum (u := Finset.univ) (fun τ _ => (hasFDerivAt_logIm τ (hz τ)).const_mul (A τ))
  have e : (∑ τ, fun y : Φ → ℂ => A τ * ((Real.log (y τ).im : ℝ) : ℂ)) = fun y => ∑ τ, A τ * ((Real.log (y τ).im : ℝ) : ℂ) := by
    ext y; simp [Finset.sum_apply]
  rw [e] at this; exact this

theorem hasFDerivAt_mono (c : ℂ → ℂ) (a : ℂ → Φ → ℂ) (σ : ℂ) {z : Φ → ℂ} (hz : ∀ τ, (z τ).im ≠ 0) :
    HasFDerivAt (mono c a σ)
      (c σ • (Complex.exp (∑ τ, a σ τ * ((Real.log (z τ).im : ℝ) : ℂ)) • ∑ τ, a σ τ • (ofRealCLM.comp (((z τ).im)⁻¹ • (imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Φ => ℂ) τ)))))) z :=
  ((hasFDerivAt_expo (a σ) hz).cexp).const_mul (c σ)

open Classical in
theorem wirt_mono (c : ℂ → ℂ) (a : ℂ → Φ → ℂ) (σ : ℂ) {z : Φ → ℂ} (hz : ∀ τ, 0 < (z τ).im) (τ₀ : Φ) (b : Bool) :
    wirt τ₀ b (mono c a σ) z =
      mono (fun σ => (if b then I else -I) / 2 * c σ * a σ τ₀) (fun σ => a σ - Pi.single τ₀ 1) σ z := by
  have hz' : ∀ τ, (z τ).im ≠ 0 := fun τ => (hz τ).ne'
  rw [wirt, (hasFDerivAt_mono c a σ hz').fderiv]
  simp [mono, Pi.single_apply]
  have hy := hz τ₀
  have e1 : ∀ x, ((if x = τ₀ then (1:ℂ) else 0).im) = 0 := fun x => by split_ifs <;> simp
  have e2 : ∀ x, ((if x = τ₀ then I else 0).im) = if x = τ₀ then 1 else 0 := fun x => by split_ifs <;> simp
  simp only [e1, e2, ofReal_zero, mul_zero, Finset.sum_const_zero, zero_add, apply_ite (fun r : ℝ => (r : ℂ)), ofReal_one, ofReal_zero,
    mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have he : ∑ x, (a σ x - if x = τ₀ then 1 else 0) * ((Real.log (z x).im : ℝ) : ℂ) =
      ∑ x, a σ x * ((Real.log (z x).im : ℝ) : ℂ) - ((Real.log (z τ₀).im : ℝ) : ℂ) := by
    simp [sub_mul, Finset.sum_sub_distrib, ite_mul]
  rw [he, Complex.exp_sub, ← Complex.ofReal_exp, Real.exp_log hy]
  have hy' : ((z τ₀).im : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  cases b <;> simp <;> field_simp <;> ring

theorem wirtWord_mono (U : Set (Φ → ℂ)) (hU : IsOpen U) (hUpos : ∀ z ∈ U, ∀ τ, 0 < (z τ).im) (w : List (Φ × Bool)) :
    ∀ (c : ℂ → ℂ) (a : ℂ → Φ → ℂ), Differentiable ℂ c → (∀ τ, Differentiable ℂ (fun σ => a σ τ)) →
      ∃ (c' : ℂ → ℂ) (a' : ℂ → Φ → ℂ), Differentiable ℂ c' ∧ (∀ τ, Differentiable ℂ (fun σ => a' σ τ)) ∧
        ∀ σ, Set.EqOn (wirtWord w (mono c a σ)) (mono c' a' σ) U := by
  induction w with
  | nil => exact fun c a hc ha => ⟨c, a, hc, ha, fun σ z _ => rfl⟩
  | cons l w ih =>
    intro c a hc ha
    obtain ⟨c₁, a₁, hc₁, ha₁, h₁⟩ := ih c a hc ha
    classical
    refine ⟨fun σ => (if l.2 then I else -I) / 2 * c₁ σ * a₁ σ l.1, fun σ => a₁ σ - Pi.single l.1 1,
      ((differentiable_const _).mul hc₁).mul (ha₁ l.1), fun τ => ?_, fun σ z hz => ?_⟩
    · simp only [Pi.sub_apply]
      exact (ha₁ τ).sub (differentiable_const _)
    · rw [wirtWord_cons, GoodAdd.wirt_congr hU (h₁ σ) _ _ hz]
      convert wirt_mono c₁ a₁ σ (hUpos z hz) l.1 l.2

theorem mono_differentiable {c : ℂ → ℂ} {a : ℂ → Φ → ℂ} (hc : Differentiable ℂ c)
    (ha : ∀ τ, Differentiable ℂ (fun σ => a σ τ)) (z : Φ → ℂ) : Differentiable ℂ (fun σ => mono c a σ z) := by
  unfold mono
  refine hc.mul (Differentiable.cexp ?_)
  exact Differentiable.fun_sum fun τ _ => (ha τ).mul (differentiable_const _)

theorem wirtWord_congr {U : Set (Φ → ℂ)} (hU : IsOpen U) {f g : (Φ → ℂ) → ℂ} (h : Set.EqOn f g U)
    (w : List (Φ × Bool)) : Set.EqOn (wirtWord w f) (wirtWord w g) U := by
  induction w with
  | nil => exact h
  | cons l w ih => intro y hy; rw [wirtWord_cons, wirtWord_cons]; exact GoodAdd.wirt_congr hU ih _ _ hy

end GlobalTheory.HeckeTwo.ProdImWirt

theorem GlobalTheory.HeckeTwo.prodIm_wirtWord_differentiableOn : ∀ (F : Type) [Field F] [NumberField F] (w : List (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F × Bool)) (z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ), z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F → DifferentiableOn ℂ (fun σ : ℂ => GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.wirtWord w (fun z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ => ∏ τ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ)) z) GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane := by
  intro F _ _ w z hz
  have hU := GoodAdd.upperHalf_isOpen F
  obtain ⟨c', a', hc', ha', h⟩ := ProdImWirt.wirtWord_mono (upperHalf F) hU (fun z hz => hz) w (fun _ => 1)
    (fun σ _ => -1 - 2 * σ) (differentiable_const _)
    (fun _ => (differentiable_const _).sub ((differentiable_const _).mul differentiable_id))
  have hw : ∀ σ, Set.EqOn (wirtWord w (fun z : Emb F → ℂ => ∏ τ : Emb F, (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ)))
      (wirtWord w (ProdImWirt.mono (fun _ => 1) (fun σ _ => -1 - 2 * σ) σ)) (upperHalf F) := by
    intro σ
    have h0 : Set.EqOn (fun z : Emb F → ℂ => ∏ τ : Emb F, (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ))
        (ProdImWirt.mono (fun _ => 1) (fun σ _ => -1 - 2 * σ) σ) (upperHalf F) := by
      intro y hy
      simp only [ProdImWirt.mono, one_mul, Complex.exp_sum]
      refine Finset.prod_congr rfl fun τ _ => ?_
      have hpos : 0 < (y τ).im := hy τ
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), ← Complex.ofReal_log hpos.le, mul_comm]
    exact ProdImWirt.wirtWord_congr hU h0 w
  refine ((ProdImWirt.mono_differentiable hc' ha' z).differentiableOn).congr fun σ _ => ?_
  rw [hw σ hz, h σ hz]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerProductEuclideanModelsAgree
section
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

theorem GlobalTheory.Proof.schrodinger_models_agree : ∀ (l : Type) [Fintype l] [DecidableEq l] (w : (l → ℝ) × (l → ℝ)) (φ : 𝓢(l → ℝ, ℂ)) (f f₁ : Sch l), (∀ x : EuclideanSpace ℝ l, f x = φ x.ofLp) → (∀ x : EuclideanSpace ℝ l, f₁ x = GlobalTheory.Published.Metaplectic.rho w φ x.ofLp) → f₁.toLp 2 = rho (Sum.elim w.1 w.2) (f.toLp 2) := by
  intro l _ _ w φ f f₁ hf hf₁
  obtain ⟨p, q⟩ := w
  have h : ⇑f₁ = rhoFun (Sum.elim p q) ⇑f := by
    funext x
    rw [hf₁, GlobalTheory.Published.Metaplectic.rho_apply, rhoFun, hf]
    simp only [phase, pPart, qPart, Sum.elim_inl, Sum.elim_inr, PiLp.inner_apply, WithLp.ofLp_add]
    congr 1
    · congr 1
      push_cast
      simp only [dotProduct, RCLike.inner_apply, conj_trivial, Finset.sum_div]
      push_cast
      ring_nf
      rw [Finset.sum_congr rfl fun i _ => mul_comm ((q i : ℝ) : ℂ) ((p i : ℝ) : ℂ)]
      ring
  refine Lp.ext ((f₁.coeFn_toLp 2 volume).trans ?_)
  rw [h]
  exact ((coeFn_rho _ _).trans (rhoFun_congr _ (f.coeFn_toLp 2 volume))).symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatVectorIrreducibleTranslationsChara
section
open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.IrredSBVec

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem norm_char_eq_one (ψ0 : AddChar k ℂ) (h1 : ∀ y ∈ 𝒪[k], ψ0 y = 1) (x : k) : ‖ψ0 x‖ = 1 := by
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨n, hn, hxn⟩ := GlobalTheory.SBUnif.exists_nat_mem_mul_integer x⁻¹ (inv_ne_zero hx)
  rw [inv_inv] at hxn
  have hp : ψ0 x ^ n = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_comm]
    exact h1 _ hxn
  have := congrArg norm hp
  rw [norm_pow, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this

def toCircle (ψ0 : AddChar k ℂ) (h1 : ∀ y ∈ 𝒪[k], ψ0 y = 1) : AddChar k Circle where
  toFun x := ⟨ψ0 x, mem_sphere_zero_iff_norm.2 (norm_char_eq_one ψ0 h1 x)⟩
  map_zero_eq_one' := Circle.ext (by simp)
  map_add_eq_mul' a b := Circle.ext (AddChar.map_add_eq_mul ψ0 a b)

theorem coe_toCircle (ψ0 : AddChar k ℂ) (h1 : ∀ y ∈ 𝒪[k], ψ0 y = 1) (x : k) :
    ((toCircle ψ0 h1 x : Circle) : ℂ) = ψ0 x := rfl

theorem continuous_toCircle (ψ0 : AddChar k ℂ) (h1 : ∀ y ∈ 𝒪[k], ψ0 y = 1) (hψ : Continuous ψ0) :
    Continuous (toCircle ψ0 h1) :=
  hψ.subtype_mk _

theorem sb_irreducible_vec : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    {κ : Type} [Fintype κ] (ψ0 : AddChar k ℂ), Continuous ψ0 →
    (∀ x : k, (∀ y ∈ 𝒪[k], ψ0 (x * y) = 1) ↔ x ∈ 𝒪[k]) →
    ∀ W : Submodule ℂ ((κ → k) → ℂ), W ≤ GlobalTheory.WeilM.SB (κ → k) →
    (∀ φ ∈ W, ∀ v : κ → k, (fun x => φ (x + v)) ∈ W) →
    (∀ φ ∈ W, ∀ y : κ → k, (fun x => ψ0 (x ⬝ᵥ y) * φ x) ∈ W) →
    ∀ φ₀ ∈ W, φ₀ ≠ 0 → W = GlobalTheory.WeilM.SB (κ → k) := by
  intro k _ _ _ _ _ κ _ ψ0 hψ hcond W hW hT hM φ₀ h0 hne
  classical
  have h1 : ∀ y ∈ 𝒪[k], ψ0 y = 1 := fun y hy => by
    simpa using (hcond 1).2 (one_mem _) y hy
  set ψ := toCircle ψ0 h1 with hψdef
  have hψc : Continuous ψ := continuous_toCircle ψ0 h1 hψ
  have hψ1 : ψ ≠ 1 := by
    obtain ⟨w, hw0, hw1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
    have hno : w⁻¹ ∉ 𝒪[k] := by
      intro h
      have h' : valuation k w⁻¹ ≤ 1 := h
      rw [map_inv₀] at h'
      have hv0 : valuation k w ≠ 0 := (Valuation.ne_zero_iff _).2 hw0
      have := (one_lt_inv₀ (zero_lt_iff.2 hv0)).2 hw1
      exact absurd h' (not_le.2 this)
    have := mt (hcond w⁻¹).1 hno
    push_neg at this
    obtain ⟨y, -, hy⟩ := this
    intro he
    apply hy
    have := congrArg (fun χ : AddChar k Circle => ((χ (w⁻¹ * y) : Circle) : ℂ)) he
    simpa [hψdef, coe_toCircle] using this

  let toM : (κ → k) → Matrix κ Unit k := fun x i _ => x i
  let frM : Matrix κ Unit k → (κ → k) := fun t i => t i ()
  have hto : Continuous toM := by fun_prop
  have hfr : Continuous frM := by fun_prop
  have hft : ∀ t, toM (frM t) = t := fun t => by funext i j; rfl
  let e : Matrix κ Unit k ≃ₜ (κ → k) :=
    { toFun := frM, invFun := toM, left_inv := hft, right_inv := fun x => rfl,
      continuous_toFun := hfr, continuous_invFun := hto }
  have SBto : ∀ φ : (κ → k) → ℂ, φ ∈ GlobalTheory.WeilM.SB (κ → k) → (fun t => φ (frM t)) ∈ GlobalTheory.SplitWeil.SB (Matrix κ Unit k) :=
    fun φ hφ => ⟨hφ.1.comp_continuous hfr, hφ.2.comp_homeomorph e⟩
  let W' : Submodule ℂ (Matrix κ Unit k → ℂ) := W.comap (LinearMap.funLeft ℂ ℂ toM)
  have mem' : ∀ Φ, Φ ∈ W' ↔ (fun x => Φ (toM x)) ∈ W := fun Φ => Iff.rfl
  have hW' : W' ≤ GlobalTheory.SplitWeil.SB (Matrix κ Unit k) := by
    intro Φ hΦ
    have := SBto _ (hW ((mem' Φ).1 hΦ))
    simpa only [hft] using this
  have key := GlobalTheory.IrredSB.sb_irreducible k κ Unit ψ hψc hψ1 W' hW'
    (fun Φ hΦ x _ => by
      rw [mem']
      have := hT _ ((mem' Φ).1 hΦ) (frM x)
      have hv : ∀ v, toM (v + frM x) = toM v + x := fun v => by
        funext i j
        cases j
        rfl
      show (fun v => Φ (toM v + x)) ∈ W
      simpa only [hv] using this)
    (fun Φ hΦ b _ => by
      rw [mem']
      have := hM _ ((mem' Φ).1 hΦ) (fun i => b i ())
      have hs : ∀ v, (∑ r, ∑ q, b r q * toM v r q) = v ⬝ᵥ (fun i => b i ()) := fun v => by
        rw [dotProduct]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Fintype.sum_unique]
        exact mul_comm _ _
      show (fun v => ((ψ (∑ r, ∑ q, b r q * toM v r q) : Circle) : ℂ) * Φ (toM v)) ∈ W
      simp only [hs]
      exact this)
    (fun t => φ₀ (frM t)) ((mem' _).2 h0) (by
      intro h
      apply hne
      funext x
      exact congrFun h (toM x))
  refine le_antisymm hW fun φ hφ => ?_
  · have : (fun t => φ (frM t)) ∈ W' := key ▸ SBto φ hφ
    exact (mem' _).1 this

end GlobalTheory.IrredSBVec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzEqGaussianOfFderivEqMulVec
section
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

namespace GlobalTheory

theorem schwartz_eq_gaussian_of_fderiv_eq_mulVec :
    ∀ (l : Type) [Fintype l] [DecidableEq l] (τ : Matrix l l ℂ) (f : Sch l), τ.IsSymm →
      (∀ (a : l) (x : EuclideanSpace ℝ l),
        fderiv ℝ f x (EuclideanSpace.single a 1) = 2 * π * I * (τ *ᵥ fun i => (x i : ℂ)) a * f x) →
      ∀ x : EuclideanSpace ℝ l,
        f x = f 0 * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (x i : ℂ))) := by
  intro l _ _ τ f _hτ H x
  set v : l → ℂ := fun i => (x i : ℂ) with hv
  set c : ℂ := v ⬝ᵥ τ *ᵥ v with hc
  have hx : x = ∑ a, x a • EuclideanSpace.single a (1 : ℝ) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun l ℝ).toBasis.sum_repr x]
    simp
  have hD : ∀ t : ℝ, fderiv ℝ f (t • x) x = 2 * π * I * (t * c) * f (t • x) := by
    intro t
    rw [show fderiv ℝ f (t • x) x = fderiv ℝ f (t • x) (∑ a, x a • EuclideanSpace.single a (1 : ℝ)) from
      congrArg _ hx]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, H, Complex.real_smul]
    have hvt : (fun i => ((t • x) i : ℂ)) = (t : ℂ) • v := by
      funext i; simp [hv]
    rw [hvt, Matrix.mulVec_smul, hc, dotProduct]
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul, hv]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  set φ : ℝ → ℂ := fun t => f (t • x) * cexp (-(π * I * c) * ((t ^ 2 : ℝ) : ℂ)) with hφ
  have hφd : ∀ t : ℝ, HasDerivAt φ 0 t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => f (t • x)) (fderiv ℝ f (t • x) ((1 : ℝ) • x)) t :=
      (f.differentiableAt (x := t • x)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const x)
    have h2 : HasDerivAt (fun t : ℝ => cexp (-(π * I * c) * ((t ^ 2 : ℝ) : ℂ)))
        (cexp (-(π * I * c) * ((t ^ 2 : ℝ) : ℂ)) * (-(π * I * c) * (((2 : ℕ) * t ^ (2 - 1) : ℝ) : ℂ))) t :=
      (((hasDerivAt_pow 2 t).ofReal_comp).const_mul _).cexp
    refine (h1.mul h2).congr_deriv ?_
    rw [one_smul, hD]
    push_cast
    ring
  have hconst := is_const_of_deriv_eq_zero (fun t => (hφd t).differentiableAt) (fun t => (hφd t).deriv) 1 0
  simp only [hφ, one_smul, zero_smul, one_pow, ofReal_one, mul_one] at hconst
  norm_num at hconst
  rw [← hconst, mul_assoc, ← Complex.exp_add]
  simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzL2EuclideanIdentification
section
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

noncomputable section

namespace GlobalTheory.EuclidTransport

variable (l : Type) [Fintype l]

theorem volume_preserving_ofLp' : MeasurePreserving (@WithLp.ofLp 2 (l → ℝ)) volume volume :=
  PiLp.volume_preserving_ofLp l

theorem volume_preserving_toLp' : MeasurePreserving (@WithLp.toLp 2 (l → ℝ)) volume volume :=
  PiLp.volume_preserving_toLp l

def schwartzTransport : 𝓢(l → ℝ, ℂ) ≃L[ℂ] Sch l :=
  ContinuousLinearEquiv.equivOfInverse
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (EuclideanSpace.equiv l ℝ))
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (EuclideanSpace.equiv l ℝ).symm)
    (fun φ => by ext x; rfl) (fun φ => by ext x; rfl)

variable {l}

theorem schwartzTransport_apply (φ : 𝓢(l → ℝ, ℂ)) (x : EuclideanSpace ℝ l) :
    schwartzTransport l φ x = φ x.ofLp := rfl

variable (l)

def l2TransportIsometry : Lp ℂ 2 (volume : Measure (l → ℝ)) →ₗᵢ[ℂ] L2 l :=
  Lp.compMeasurePreservingₗᵢ ℂ (@WithLp.ofLp 2 (l → ℝ)) (volume_preserving_ofLp' l)

theorem l2TransportIso_apply (f : Lp ℂ 2 (volume : Measure (l → ℝ))) :
    l2TransportIsometry l f = Lp.compMeasurePreserving _ (volume_preserving_ofLp' l) f := rfl

theorem l2TransportIso_surjective : Function.Surjective (l2TransportIsometry l) := by
  intro h
  refine ⟨Lp.compMeasurePreserving (@WithLp.toLp 2 (l → ℝ)) (volume_preserving_toLp' l) h, ?_⟩
  rw [l2TransportIso_apply]
  ext1
  refine (Lp.coeFn_compMeasurePreserving _ (volume_preserving_ofLp' l)).trans ?_
  refine ((volume_preserving_ofLp' l).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_compMeasurePreserving h (volume_preserving_toLp' l))).trans ?_
  exact Filter.Eventually.of_forall fun x => rfl

def l2Transport : Lp ℂ 2 (volume : Measure (l → ℝ)) ≃ₗᵢ[ℂ] L2 l :=
  LinearIsometryEquiv.ofSurjective (l2TransportIsometry l) (l2TransportIso_surjective l)

variable {l}

theorem l2Transport_apply (f : Lp ℂ 2 (volume : Measure (l → ℝ))) :
    l2Transport l f = Lp.compMeasurePreserving _ (volume_preserving_ofLp' l) f := rfl

theorem l2Transport_toLp (φ : 𝓢(l → ℝ, ℂ)) : l2Transport l (φ.toLp 2) = (schwartzTransport l φ).toLp 2 := by
  rw [l2Transport_apply]
  have h4 : ((φ.toLp 2 : Lp ℂ 2 (volume : Measure (l → ℝ))) : (l → ℝ) → ℂ) =ᵐ[volume] (φ : (l → ℝ) → ℂ) :=
    φ.coeFn_toLp 2 volume
  have h5 : (((schwartzTransport l φ).toLp 2 : L2 l) : EuclideanSpace ℝ l → ℂ) =ᵐ[volume]
      (schwartzTransport l φ : EuclideanSpace ℝ l → ℂ) :=
    (schwartzTransport l φ).coeFn_toLp 2 volume
  refine Lp.ext (Filter.EventuallyEq.trans ?_ h5.symm)
  refine (Lp.coeFn_compMeasurePreserving _ (volume_preserving_ofLp' l)).trans ?_
  refine ((volume_preserving_ofLp' l).quasiMeasurePreserving.ae_eq_comp h4).trans ?_
  exact Filter.Eventually.of_forall fun x => (schwartzTransport_apply φ x).symm

theorem exists_schwartz_L2_transport (l : Type) [Fintype l] [DecidableEq l] :
    ∃ (e : 𝓢(l → ℝ, ℂ) ≃L[ℂ] Sch l) (u : Lp ℂ 2 (volume : Measure (l → ℝ)) ≃ₗᵢ[ℂ] L2 l),
      (∀ φ (x : EuclideanSpace ℝ l), e φ x = φ x.ofLp) ∧ ∀ φ : 𝓢(l → ℝ, ℂ), u (φ.toLp 2) = (e φ).toLp 2 :=
  ⟨schwartzTransport l, l2Transport l, schwartzTransport_apply, l2Transport_toLp⟩

end GlobalTheory.EuclidTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorBasisCriterion
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_basis_criterion : ∀ (A B R S : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing R] [Algebra A R] [CommRing S] (κ : R ⊗[A] B →+* S) {r : ℕ} (v : Fin r → B), Function.Bijective (fun c : Fin r → R => κ (∑ k, c k ⊗ₜ[A] v k)) ↔ (Function.Surjective κ ∧ LinearIndependent R (fun k => Ideal.Quotient.mk (RingHom.ker κ) ((1 : R) ⊗ₜ[A] v k)) ∧ Submodule.span R (Set.range (fun k => Ideal.Quotient.mk (RingHom.ker κ) ((1 : R) ⊗ₜ[A] v k))) = ⊤) := by
  first | (exact @GlobalTheory.tensorSum_bijective_iff) | (exact GlobalTheory.tensorSum_bijective_iff) | (intros; apply GlobalTheory.tensorSum_bijective_iff <;> assumption)
end

