module

public import ReciprocityTheory.SemistableReduction.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CoveringRadiusStatement
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Matrix ReciprocityTheory.MultiplicativeHeights

noncomputable def d5mu (f r : ℕ) (d laStar : ℝ) : ℝ := 4 * ((f : ℝ) * r) ^ 3 * d / laStar

def CoveringRadiusStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (ι : Type) [Fintype ι] [Nonempty ι]
    (r p : ℕ) (S : HermForm K r) (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ)
    (L : Submodule (𝓞 K) (Fin r → K)) (laStar : ℝ),
    Function.Injective σ →
    (∀ τ : K →+* ℂ, (∃ i, σ i = τ) ↔ ¬ ∃ i, σ i = ComplexEmbedding.conjugate τ) →
    p ≤ r → 0 < laStar → (∀ i, (Q i).det ≠ 0) →
    (∀ i x y, σ i (S.h x y) = jForm p (Q i *ᵥ embVec (σ i) x) (Q i *ᵥ embVec (σ i) y)) →
    IsLattice L → IsSelfDual S L →
    (∀ v ∈ L, v ≠ 0 → ∃ i, laStar ^ 2 ≤ normSq (Q i *ᵥ embVec (σ i) v)) →
    let μ := d5mu (Fintype.card ι) r |(NumberField.discr K : ℝ)| laStar
    (∀ w : ι → Fin r → ℂ, ∃ l ∈ L, ∑ i, normSq (Q i *ᵥ embVec (σ i) l - w i) ≤ μ ^ 2) ∧
    ∃ v : Fin r → Fin r → K, (∀ j, v j ∈ L) ∧ LinearIndependent K v ∧ ∀ j, majSq σ Q (v j) ≤ μ ^ 2

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsIntegralCc
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma cc_cc (x : E) : cc (cc x) = x := by
  simp [cc]

lemma cc_sub (x y : E) : cc (x - y) = cc x - cc y := by
  simp [cc]

lemma cc_mul (x y : E) : cc (x * y) = cc x * cc y := by
  simp [cc]

lemma cc_one : cc (1 : E) = 1 := by
  simp [cc]

lemma cc_zero : cc (0 : E) = 0 := by
  simp [cc]

lemma emb_cc (τ : E →+* ℂ) (x : E) : τ (cc x) = conj (τ x) := by
  rw [cc]
  exact IsCMField.complexEmbedding_complexConj E τ x

lemma cc_eq_zero {x : E} (h : cc x = 0) : x = 0 := by
  have := congrArg cc h
  rwa [cc_cc, cc_zero] at this

lemma isIntegral_cc {x : E} (hx : IsIntegral ℤ x) : IsIntegral ℤ (cc x) := by
  have := hx.map (IsCMField.complexConj E).toAlgHom.toRatAlgHom
  exact this

lemma exists_imag : ∃ κ : E, cc κ = -κ ∧ κ ≠ 0 := by
  obtain ⟨x, hx⟩ : ∃ x : E, cc x ≠ x := by
    by_contra hne
    push_neg at hne
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    apply InfinitePlace.isComplex_iff.mp (IsTotallyComplex.isComplex w)
    refine RingHom.ext fun y => ?_
    rw [ComplexEmbedding.conjugate_coe_eq, ← emb_cc, hne y]
  refine ⟨x - cc x, ?_, ?_⟩
  · rw [cc_sub, cc_cc, neg_sub]
  · exact sub_ne_zero.mpr (Ne.symm hx)

lemma im_ne_zero {κ : E} (hκ : cc κ = -κ) (h0 : κ ≠ 0) (τ : E →+* ℂ) : (τ κ).im ≠ 0 := by
  intro him
  have h1 : conj (τ κ) = -(τ κ) := by rw [← emb_cc, hκ, map_neg]
  have h2 : conj (τ κ) = τ κ := Complex.conj_eq_iff_im.mpr him
  have h3 : τ κ = 0 := by
    have h4 : τ κ = -(τ κ) := h2.symm.trans h1
    linear_combination (1 / 2 : ℂ) * h4
  exact h0 ((map_eq_zero_iff τ τ.injective).mp h3)

def e1 : Fin 1 → E := fun _ => 1

lemma herm_one (x y : Fin 1 → E) : herm (1 : Matrix (Fin 1) (Fin 1) E) x y = x 0 * cc (y 0) := by
  simp [herm]

lemma stab_finite :
    {γ : GL (Fin 1) E | IsIntegral ℤ ((γ : Matrix (Fin 1) (Fin 1) E) 0 0) ∧
      ∀ φ : E →+* ℂ, ‖φ ((γ : Matrix (Fin 1) (Fin 1) E) 0 0)‖ ≤ 1}.Finite := by
  have hfin := NumberField.Embeddings.finite_of_norm_le E ℂ (1 : ℝ)
  refine (hfin.preimage (f := fun γ : GL (Fin 1) E => (γ : Matrix (Fin 1) (Fin 1) E) 0 0) ?_).subset ?_
  · intro γ₁ _ γ₂ _ h
    apply Units.ext
    ext i j
    fin_cases i
    fin_cases j
    exact h
  · intro γ hγ
    exact hγ

noncomputable def inhab : Data E 1 := by
  classical
  let κ : E := (exists_imag (E := E)).choose
  have hκ : cc κ = -κ := (exists_imag (E := E)).choose_spec.1
  have hκ0 : κ ≠ 0 := (exists_imag (E := E)).choose_spec.2
  let Λ : Submodule (𝓞 E) (Fin 1 → E) := Submodule.span (𝓞 E) {(e1 : Fin 1 → E)}
  have memΛ : ∀ x, x ∈ Λ ↔ ∃ a : 𝓞 E, (a : E) = x 0 := by
    intro x
    rw [Submodule.mem_span_singleton]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, by simp [e1, Algebra.smul_def]⟩
    · rintro ⟨a, ha⟩
      refine ⟨a, ?_⟩
      funext i
      fin_cases i
      simp [e1, Algebra.smul_def, ha]
  have hfin := stab_finite (E := E)
  exact
  { Ψ := Finset.univ.filter fun τ : E →+* ℂ => 0 < (τ κ).im
    cmType := by
      intro τ
      have h1 := im_ne_zero hκ hκ0 τ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, ComplexEmbedding.conjugate_coe_eq,
        Complex.conj_im, not_lt, neg_nonpos]
      constructor
      · intro h; exact h.le
      · intro h; exact lt_of_le_of_ne h (Ne.symm h1)
    Gm := 1
    Gm_herm := by
      intro a b
      fin_cases a; fin_cases b
      simp [cc_one]
    Gm_det := by simp
    p0 := 1
    p0_le := le_rfl
    signature := by
      intro τ
      refine ⟨1, by simp, ?_⟩
      ext a b
      fin_cases a; fin_cases b
      simp [gram, hermC, col, sgn, Matrix.one_apply]
    Λ := Λ
    Λ_fg := Submodule.fg_span_singleton _
    Λ_span := by
      rw [eq_top_iff]
      intro x _
      have hx : x = x 0 • (e1 : Fin 1 → E) := by
        funext i; fin_cases i; simp [e1]
      rw [hx]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      exact Submodule.subset_span (Set.mem_singleton _)
    den := 1
    den_ne := one_ne_zero
    Λ_int := by
      intro x hx y hy
      obtain ⟨a, ha⟩ := (memΛ x).mp hx
      obtain ⟨b, hb⟩ := (memΛ y).mp hy
      rw [herm_one, ← ha, ← hb]
      rw [show ((1 : 𝓞 E) : E) = 1 by simp, one_mul]
      exact a.isIntegral_coe.mul (isIntegral_cc b.isIntegral_coe)
    Γ := ⊥
    Γ_stab := by
      intro γ hγ
      rw [Subgroup.mem_bot] at hγ
      subst hγ
      simp [IsUStab]
    Γ_index := by
      refine ⟨hfin.toFinset, ?_⟩
      intro γ hγ
      refine ⟨γ, ?_, by simp⟩
      rw [Set.Finite.mem_toFinset]
      obtain ⟨hh, hl⟩ := hγ
      have hmem : Matrix.mulVec (γ : Matrix (Fin 1) (Fin 1) E) e1 ∈ Λ :=
        (hl e1).mp (Submodule.subset_span (Set.mem_singleton _))
      have hv : Matrix.mulVec (γ : Matrix (Fin 1) (Fin 1) E) e1 0 = (γ : Matrix (Fin 1) (Fin 1) E) 0 0 := by
        simp [Matrix.mulVec, dotProduct, e1]
      obtain ⟨a, ha⟩ := (memΛ _).mp hmem
      rw [hv] at ha
      refine ⟨ha ▸ a.isIntegral_coe, ?_⟩
      intro φ
      have h1 := hh e1 e1
      rw [herm_one, herm_one, hv] at h1
      simp only [e1, cc_one, mul_one] at h1
      have h2 := congrArg φ h1
      rw [map_mul, emb_cc, map_one, Complex.mul_conj] at h2
      have h3 : ‖φ ((γ : Matrix (Fin 1) (Fin 1) E) 0 0)‖ ^ 2 = 1 := by
        rw [← Complex.normSq_eq_norm_sq]; exact_mod_cast h2
      nlinarith [norm_nonneg (φ ((γ : Matrix (Fin 1) (Fin 1) E) 0 0))]
    Γ_free := by
      intro γ hγ _ _ _ _ _
      exact (Subgroup.mem_bot.mp hγ)
    χ := fun _ _ => 1
    χ_mul := by intros; simp
    χ_add := by intros; simp
    χ_fin := fun _ => ⟨1, one_pos, by intros; simp⟩
    ξ0 := κ
    ξ0_im := hκ
    ξ0_ne := hκ0
    κ0 := -(2 * κ)
    κ0_xi := Or.inr rfl
    κ0_sign := by
      rintro ⟨τ, hτ⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ
      simp only [map_neg, map_mul, map_ofNat, Complex.neg_im, Complex.mul_im]
      norm_num
      exact hτ
    m := 1
    m_pos := one_pos
    transv := by
      intro ξ _ hiso s _ _
      rw [herm_one] at hiso
      have hξ : ξ 0 = 0 := by
        rcases mul_eq_zero.mp hiso with h | h
        · exact h
        · exact cc_eq_zero h
      refine ⟨1, Subgroup.one_mem _, ?_⟩
      ext a b
      fin_cases a; fin_cases b
      simp [transvMat, hξ] }

theorem nonempty_data : Nonempty (Data E 1) :=
  ⟨inhab⟩

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex MeasureTheory
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace Data

variable {r : ℕ} (X : Data E r)

def flowMatV (e : Fin r → ℂ) (τ : X.Ψ) (s : ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => (if a = b then 1 else 0) -
    I * X.c τ * s * e a * ∑ k, τ.1 (X.Gm b k) * conj (e k)

def flowV (e : X.Ψ → Fin r → ℂ) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) : Frame X.Ψ r :=
  fun τ => (X.flowMatV (e τ) τ (s τ) * mat x τ : Matrix (Fin r) (Fin r) ℂ)

def ttV (e : X.Ψ → Fin r → ℂ) (x : Frame X.Ψ r) (τ : X.Ψ) : ℝ := 1 / (X.c τ * X.maj x τ (e τ))

def IsIsoV (e : X.Ψ → Fin r → ℂ) : Prop := ∀ τ : X.Ψ, hermC τ.1 X.Gm (e τ) (e τ) = 0 ∧ e τ ≠ 0

def IsIso (ξ : Fin r → E) : Prop := ξ ∈ X.Λ ∧ herm X.Gm ξ ξ = 0 ∧ ξ ≠ 0

def nfac (la : Wt X.Ψ r) (x : Frame X.Ψ r) : ℝ :=
  ∏ τ, ∏ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2)

def spread (la : Wt X.Ψ r) (τ : X.Ψ) : ℝ :=
  ((⨆ i, (la τ i : ℝ)) - ⨅ i, (la τ i : ℝ))

def chiOrd (la : Wt X.Ψ r) : ℕ := (X.χ_fin la).choose

def periods (la : Wt X.Ψ r) : AddSubgroup (X.Ψ → ℝ) :=
  AddSubgroup.closure {p | ∃ a : E, cc a = a ∧ IsIntegral ℤ a ∧
    p = fun τ => ((X.m * X.chiOrd la : ℕ) : ℝ) * (τ.1 a).re}


open Classical in
def fj (la : Wt X.Ψ r) (ξ : Fin r → E) (ν : X.Ψ → ℝ) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : ℂ :=
  if (∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, ν τ * p τ = k) then
  if h : ∃ D : Set (X.Ψ → ℝ), MeasurableSet D ∧ IsAddFundamentalDomain (X.periods la) D volume ∧
      0 < volume D ∧ volume D < ⊤ then
    ((volume h.choose).toReal : ℂ)⁻¹ * ∫ s in h.choose,
      P (X.flow ξ (fun τ => (s τ : ℂ)) x) * cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ)
  else 0
  else 0

def IsModerate (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) : Prop :=
  ∃ C A : ℝ, ∀ x ∈ X.dom, X.pnorm la P x ≤ C * X.la1 x ^ (-A)

def IsBddSec (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) : Prop :=
  X.IsSec la P ∧ ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm la P x ≤ C

def SS (la : Wt X.Ψ r) : Set (Frame X.Ψ r → ℂ) :=
  {P | X.IsBddSec la P ∧ ∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom, X.fj la ξ 0 P x = 0}

def SSgt (la : Wt X.Ψ r) (c : ℝ) : Set (Frame X.Ψ r → ℂ) :=
  {P | P ∈ X.SS la ∧ ∀ ξ, X.IsIso ξ → ∀ ν : X.Ψ → ℝ, ∑ τ, ν τ ≤ c → ∀ x ∈ X.dom, X.fj la ξ ν P x = 0}

end Data

def FlowDomainCriterion : Prop :=
  ∀ (r : ℕ) (X : Data E r) (e : X.Ψ → Fin r → ℂ), X.IsIsoV e → ∀ x ∈ X.dom, ∀ s : X.Ψ → ℂ,
    (X.flowV e s x ∈ X.dom ↔ ∀ τ, 0 < 1 + (s τ).im / X.ttV e x τ) ∧
    (X.flowV e s x ∈ X.dom → ∀ τ, X.ttV e (X.flowV e s x) τ = X.ttV e x τ + (s τ).im)

def FlowNormRatio : Prop :=
  ∀ (r : ℕ) (X : Data E r) (e : X.Ψ → Fin r → ℂ), X.IsIsoV e → ∀ (la : Wt X.Ψ r), ∀ x ∈ X.dom,
    ∀ s : X.Ψ → ℂ, X.flowV e s x ∈ X.dom →
    let q := fun τ => 1 + (s τ).im / X.ttV e x τ
    (∏ τ, min (q τ) (q τ)⁻¹ ^ (X.spread la τ / 2) ≤ X.nfac la x / X.nfac la (X.flowV e s x)) ∧
    X.nfac la x / X.nfac la (X.flowV e s x) ≤ ∏ τ, max (q τ) (q τ)⁻¹ ^ (X.spread la τ / 2)

def FourierJacobiExpansion : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), X.IsSec la P →
    ∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom, ∀ s : X.Ψ → ℂ, X.flow ξ s x ∈ X.dom →
      HasSum (fun ν : X.Ψ → ℝ => X.fj la ξ ν P x * cexp (4 * Real.pi * I * ∑ τ, (ν τ : ℂ) * s τ))
        (P (X.flow ξ s x))

def ModerateCoefficientPositivity : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (C A : ℝ), X.IsSec la P →
    (∀ x ∈ X.dom, X.pnorm la P x ≤ C * X.la1 x ^ (-A)) →
    (∀ ξ, X.IsIso ξ → ∀ (ν : X.Ψ → ℝ), ∀ x ∈ X.dom, X.fj la ξ ν P x ≠ 0 → ∀ τ, 0 ≤ ν τ) ∧
    ∀ η : ℝ, 0 < η → η < 1 → ∃ Cη : ℝ, ∀ ξ, X.IsIso ξ → ∀ (ν : X.Ψ → ℝ), ∀ x ∈ X.dom,
      (∀ τ, X.c τ * X.maj x τ (Data.emb τ.1 ξ) ≤ 1) →
      ‖X.fj la ξ ν P x‖ * X.nfac la x ≤
        Cη * X.la1 x ^ (-A) * Real.exp (-4 * Real.pi * (1 - η) * ∑ τ, ν τ * X.tt ξ x τ)

def CoefficientConvolution : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la la' : Wt X.Ψ r) (P Q : Frame X.Ψ r → ℂ),
    X.IsSec la P → X.IsSec la' Q → X.IsModerate la P → X.IsModerate la' Q →
    ∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom, ∀ ν : X.Ψ → ℝ,
      HasSum (fun ν' : X.Ψ → ℝ => X.fj la ξ ν' P x * X.fj la' ξ (ν - ν') Q x)
        (X.fj (la + la') ξ ν (P * Q) x)

def SiegelSpaceAlgebra : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la la' : Wt X.Ψ r) (c : ℝ),
    (0 ∈ X.SS la ∧ (∀ P ∈ X.SS la, ∀ Q ∈ X.SS la, P + Q ∈ X.SS la) ∧
      ∀ (a : ℂ), ∀ P ∈ X.SS la, a • P ∈ X.SS la) ∧
    (∀ P ∈ X.SS la, ∀ Q, X.IsBddSec la' Q → P * Q ∈ X.SS (la + la')) ∧
    (0 ∈ X.SSgt la c ∧ (∀ P ∈ X.SSgt la c, ∀ Q ∈ X.SSgt la c, P + Q ∈ X.SSgt la c) ∧
      ∀ (a : ℂ), ∀ P ∈ X.SSgt la c, a • P ∈ X.SSgt la c) ∧
    ∀ P ∈ X.SSgt la c, ∀ Q, X.IsBddSec la' Q → P * Q ∈ X.SSgt (la + la') c

end

end ReciprocityTheory.ChartRestriction.G.FD
end

