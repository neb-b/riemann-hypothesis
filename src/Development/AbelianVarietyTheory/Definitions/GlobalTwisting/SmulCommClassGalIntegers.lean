module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0002
public import Formalism.GL3MeanSquares.Bundle0001
public import Formalism.CyclotomicNorms.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008

@[expose] public section

noncomputable section

namespace GlobalTheory.NT

open Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory NumberField IsDedekindDomain

def mult {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ

def NormOne (d M p : ℕ) : Prop :=
  ∃ u v : ℤ, (p : ℤ) = (1 + M * u) ^ 2 + (1 + M * u) * (M * v) + (M * v) ^ 2 * (((d + 1) / 4 : ℕ) : ℤ)

theorem normOne_iff {d : ℕ} (hd : d % 4 = 3) (M p : ℕ) : NormOne d M p ↔ GlobalTheory.Mem.An.NormOne d M p := by
  obtain ⟨k, hk, rfl⟩ : ∃ k : ℕ, (d + 1) / 4 = k + 1 ∧ d = 4 * k + 3 := ⟨d / 4, by omega, by omega⟩
  unfold NormOne GlobalTheory.Mem.An.NormOne
  rw [hk]
  push_cast
  constructor
  · rintro ⟨u, v, h⟩
    exact ⟨2 * (1 + M * u) + M * v, M * v, by rw [h]; ring, ⟨v, rfl⟩, ⟨u, by ring⟩⟩
  · rintro ⟨A, B, h, ⟨v, rfl⟩, ⟨u, hu⟩⟩
    obtain rfl : A = 2 * (1 + M * u) + M * v := by linarith
    exact ⟨u, v, by nlinarith [h]⟩

section Hecke

variable {K : Type} (L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def IsFrob (𝔭 : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L) : Prop :=
  ∃ P : Ideal (𝓞 L), P.IsPrime ∧ P.LiesOver 𝔭.asIdeal ∧ ∀ x : 𝓞 L, σ • x - x ^ Ideal.absNorm 𝔭.asIdeal ∈ P

def InInertia (𝔭 : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L) : Prop :=
  ∃ P : Ideal (𝓞 L), P.IsPrime ∧ P.LiesOver 𝔭.asIdeal ∧ ∀ x : 𝓞 L, σ • x - x ∈ P

def UnramIn (𝔭 : HeightOneSpectrum (𝓞 K)) : Prop := ∀ σ : L ≃ₐ[K] L, InInertia L 𝔭 σ → σ = 1


open Classical in
def heckeVal (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔭 : HeightOneSpectrum (𝓞 K)) : ℂ :=
  if h : (∀ σ, InInertia L 𝔭 σ → χ σ = 1) ∧ ∃ σ, IsFrob L 𝔭 σ then ((χ h.2.choose : ℂˣ) : ℂ) else 0


open Classical in
def heckeIdeal (χ : (L ≃ₐ[K] L) →* ℂˣ) (I : Ideal (𝓞 K)) : ℂ :=
  ∏ᶠ 𝔭 : HeightOneSpectrum (𝓞 K), heckeVal L χ 𝔭 ^ (Associates.mk 𝔭.asIdeal).count (Associates.mk I).factors

def RayPair (𝔪 : Ideal (𝓞 K)) (α β : 𝓞 K) : Prop :=
  α ≠ 0 ∧ β ≠ 0 ∧ IsCoprime (Ideal.span {α}) 𝔪 ∧ IsCoprime (Ideal.span {β}) 𝔪 ∧ α - β ∈ 𝔪 ∧
    ∀ φ : K →+* ℝ, 0 < φ (α : K) * φ (β : K)

def IsModulus (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔪 : Ideal (𝓞 K)) : Prop :=
  𝔪 ≠ ⊥ ∧ (∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔪 → heckeVal L χ 𝔭 ≠ 0) ∧
    ∀ α β : 𝓞 K, RayPair 𝔪 α β → heckeIdeal L χ (Ideal.span {α}) = heckeIdeal L χ (Ideal.span {β})

def condNorm (χ : (L ≃ₐ[K] L) →* ℂˣ) : ℕ :=
  sInf {n | ∃ 𝔪 : Ideal (𝓞 K), IsModulus L χ 𝔪 ∧ Ideal.absNorm 𝔪 = n}


variable (K) in
def bigQ : ℝ :=
  |(discr K : ℝ)| * ((⨆ χ : (L ≃ₐ[K] L) →* ℂˣ, condNorm L χ : ℕ) : ℝ) *
    (Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K

def HeckeZero (χ : (L ≃ₐ[K] L) →* ℂˣ) (β : ℂ) : Prop :=
  β ≠ 1 ∧ ∃ F : ℂ → ℂ, DifferentiableOn ℂ F {1}ᶜ ∧
    (∀ s : ℂ, 1 < s.re → HasProd (fun 𝔭 : HeightOneSpectrum (𝓞 K) =>
      (1 - heckeVal L χ 𝔭 * ((Ideal.absNorm 𝔭.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) (F s)) ∧ F β = 0


omit [NumberField K] [NumberField L] in
instance smulCommClass_gal_integers : SMulCommClass (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) where
  smul_comm s a x := by
    apply RingOfIntegers.ext
    rw [Algebra.smul_def, Algebra.smul_def]
    change s (algebraMap K L a * x) = algebraMap K L a * s x
    rw [map_mul, AlgEquiv.commutes]

theorem isFrob_iff (𝔭 : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L) :
    IsFrob L 𝔭 σ ↔ ∃ P : Ideal (𝓞 L), P.IsPrime ∧ P.LiesOver 𝔭.asIdeal ∧ IsArithFrobAt (𝓞 K) σ P := by
  refine exists_congr fun P => and_congr_right fun _ => and_congr_right fun hP => ?_
  have h : P.under (𝓞 K) = 𝔭.asIdeal := hP.over.symm
  unfold IsArithFrobAt AlgHom.IsArithFrobAt
  rw [h, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rfl

theorem inInertia_iff (𝔭 : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L) :
    InInertia L 𝔭 σ ↔ ∃ P : Ideal (𝓞 L), P.IsPrime ∧ P.LiesOver 𝔭.asIdeal ∧ σ ∈ P.inertia (L ≃ₐ[K] L) :=
  Iff.rfl

theorem exists_isFrob [IsGalois K L] (𝔭 : HeightOneSpectrum (𝓞 K)) : ∃ σ : L ≃ₐ[K] L, IsFrob L 𝔭 σ := by
  have := 𝔭.isPrime
  obtain ⟨P, hP, hP'⟩ := (inferInstance : Nonempty (𝔭.asIdeal.primesOver (𝓞 L)))
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
  have : Finite (𝓞 L ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 K) (L ≃ₐ[K] L) P
  exact ⟨σ, (isFrob_iff L 𝔭 σ).2 ⟨P, hP, hP', hσ⟩⟩

theorem heckeVal_eq [IsGalois K L] (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔭 : HeightOneSpectrum (𝓞 K))
    (hχ : ∀ τ, InInertia L 𝔭 τ → χ τ = 1) {σ : L ≃ₐ[K] L} (hσ : IsFrob L 𝔭 σ) :
    heckeVal L χ 𝔭 = (χ σ : ℂˣ) := by
  have h : (∀ σ, InInertia L 𝔭 σ → χ σ = 1) ∧ ∃ σ, IsFrob L 𝔭 σ := ⟨hχ, σ, hσ⟩
  unfold heckeVal
  rw [dite_eq_left h]
  obtain ⟨P, hP, hPo, h1⟩ := (isFrob_iff L 𝔭 _).1 h.2.choose_spec
  obtain ⟨P', hP', hPo', h2⟩ := (isFrob_iff L 𝔭 _).1 hσ
  have := 𝔭.isPrime
  obtain ⟨τ, hτ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 K) (𝓞 L) (L ≃ₐ[K] L) P' P
    (hPo'.over.symm.trans hPo.over)
  have h3 := h2.conj τ
  rw [← hτ] at h3
  have h4 := hχ _ ((inInertia_iff L 𝔭 _).2 ⟨P, hP, hPo, h1.mul_inv_mem_inertia h3⟩)
  simp only [map_mul, map_inv, mul_inv_eq_one] at h4
  rw [h4, mul_inv_cancel_comm]

theorem heckeVal_eq_zero (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔭 : HeightOneSpectrum (𝓞 K))
    (hχ : ¬ ∀ τ, InInertia L 𝔭 τ → χ τ = 1) : heckeVal L χ 𝔭 = 0 := by
  unfold heckeVal
  rw [dite_eq_right fun h => hχ h.1]

theorem heckeVal_of_unramIn [IsGalois K L] (χ : (L ≃ₐ[K] L) →* ℂˣ) {𝔭 : HeightOneSpectrum (𝓞 K)}
    (hu : UnramIn L 𝔭) {σ : L ≃ₐ[K] L} (hσ : IsFrob L 𝔭 σ) : heckeVal L χ 𝔭 = (χ σ : ℂˣ) :=
  heckeVal_eq L χ 𝔭 (fun τ hτ => by rw [hu τ hτ, map_one]) hσ

theorem heckeVal_one [IsGalois K L] (𝔭 : HeightOneSpectrum (𝓞 K)) :
    heckeVal L (1 : (L ≃ₐ[K] L) →* ℂˣ) 𝔭 = 1 := by
  obtain ⟨σ, hσ⟩ := exists_isFrob L 𝔭
  rw [heckeVal_eq L 1 𝔭 (fun _ _ => rfl) hσ]
  simp

theorem condNorm_one [IsGalois K L] : condNorm L (1 : (L ≃ₐ[K] L) →* ℂˣ) = 1 := by
  have hm : IsModulus L (1 : (L ≃ₐ[K] L) →* ℂˣ) ⊤ :=
    ⟨top_ne_bot, fun p _ => by simp [heckeVal_one], fun a b _ => by simp [heckeIdeal, heckeVal_one]⟩
  apply le_antisymm
  · exact Nat.sInf_le ⟨⊤, hm, by simp⟩
  · unfold condNorm
    refine le_csInf ⟨1, ⊤, hm, by simp⟩ ?_
    rintro n ⟨m, hm, rfl⟩
    exact Nat.one_le_iff_ne_zero.2 (by simpa [Ideal.absNorm_eq_zero_iff] using hm.1)

theorem heckeZero_iff (χ : (L ≃ₐ[K] L) →* ℂˣ) {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G {1}ᶜ)
    (hp : ∀ s : ℂ, 1 < s.re → HasProd (fun 𝔭 : HeightOneSpectrum (𝓞 K) =>
      (1 - heckeVal L χ 𝔭 * ((Ideal.absNorm 𝔭.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) (G s)) (β : ℂ) :
    HeckeZero L χ β ↔ β ≠ 1 ∧ G β = 0 := by
  refine and_congr_right fun hβ => ⟨?_, fun h => ⟨G, hG, hp, h⟩⟩
  rintro ⟨F, hF, hFp, h0⟩
  have ho : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have he : F =ᶠ[nhds (2 : ℂ)] G := by
    have : {s : ℂ | 1 < s.re} ∈ nhds (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
    filter_upwards [this] with s hs using (hFp s hs).unique (hp s hs)
  have := (hF.analyticOnNhd ho).eqOn_of_preconnected_of_eventuallyEq (hG.analyticOnNhd ho) hc
    (z₀ := 2) (by norm_num) he hβ
  rw [← this, h0]

end Hecke

theorem absNorm_rat (p : HeightOneSpectrum (𝓞 ℚ)) :
    Ideal.absNorm p.asIdeal = (Rat.HeightOneSpectrum.primesEquiv p : ℕ) := by
  have e := Ideal.quotientEquiv p.asIdeal _ (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) (Rat.HeightOneSpectrum.span_natGenerator p)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_congr e.toEquiv]
  have := Ideal.absNorm_span_singleton ((Rat.HeightOneSpectrum.natGenerator p : ℕ) : ℤ)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this
  rw [this]
  simp only [Algebra.norm_self, MonoidHom.id_apply, Int.natAbs_natCast]
  rfl

theorem heckeZero_rat_one_iff (L : Type) [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L] (β : ℂ) :
    HeckeZero L (1 : (L ≃ₐ[ℚ] L) →* ℂˣ) β ↔ riemannZeta β = 0 := by
  rw [heckeZero_iff L 1 (G := riemannZeta)
    (fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt) ?_ β]
  · exact ⟨fun h => h.2, fun h => ⟨fun h1 => riemannZeta_one_ne_zero (h1 ▸ h), h⟩⟩
  · intro s hs
    have := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).hasProd_iff.2 (riemannZeta_eulerProduct_hasProd hs)
    convert this using 2 with p
    simp [heckeVal_one, absNorm_rat]

end GlobalTheory.NT

end
