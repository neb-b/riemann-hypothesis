module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StageData
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

def vec {K : Type} [Zero K] {M n : ℕ} (α : K) (c : Fin n → K) (X : Fin n → Fin M → K) :
    Fin (n + 1) → Fin (M + 1) → K :=
  Fin.cons (Fin.cons α (fun _ => 0)) (fun j => Fin.cons (c j) (X j))

def scl {K : Type} [Mul K] {N n : ℕ} (u : K) (y : Fin n → Fin N → K) : Fin n → Fin N → K :=
  fun a i => y a i * u

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def s0 {n : ℕ} (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) : R :=
  algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (S 0 0)

def cvec {n : ℕ} (t : F) (a : R → Rˣ) (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) :
    Fin n → R ⊗[F] E :=
  fun j => ((((a (s0 R S))⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * S 0 j.succ

def schurM (σ : E →ₐ[F] E) {n : ℕ} (t : F) (a : R → Rˣ)
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  fun i j => S i.succ j.succ -
    sigR R σ (cvec R t a S i) * inclR R (algebraMap F E t) * cvec R t a S j


open scoped Classical in
open Classical in
def schur (σ : E →ₐ[F] E) {n : ℕ} (t : F) (a : R → Rˣ) (S : HermR R σ (n + 1)) : HermR R σ n :=
  if h : schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ HermR R σ n then ⟨_, h⟩ else 0

theorem schur_coe (σ : E →ₐ[F] E) {n : ℕ} (t : F) (a : R → Rˣ) (S : HermR R σ (n + 1))
    (h : schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ HermR R σ n) :
    (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = schurM R σ t a S := by
  simp [schur, h]

def Bset (σ : E →ₐ[F] E) {n : ℕ} (t : F) (a : R → Rˣ) (B₀ : Set R) : Set (HermR R σ (n + 1)) :=
  {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀ ∧
    IsUnit (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}

end Alg

section Meas

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : F) {n : ℕ}
  {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
  (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E))
  (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
  (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J))
  (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0)

def fibS (S : HermR R σ (n + 1)) : Measure (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) :=
  (Bset R σ t a B₀).indicator (fun S : HermR R σ (n + 1) =>
    (κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) *
        cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) ^ n) •
      ((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (schur R σ t a S))).map (fun p =>
        actW R σ (blockOne (algebraMap F E t) J) (s p.1)
          (vec (((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) : Rˣ) : R) ⊗ₜ[F] (1 : E))
            (cvec R t a S) p.2))) S

def Pint (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞) (α : R) (c : Fin n → R ⊗[F] E)
    (S' : HermR R σ n) : ℝ≥0∞ :=
  ∫⁻ y₀, ∫⁻ X, φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (α ⊗ₜ[F] (1 : E)) c X)) ∂(m' S')
    ∂(m₁ (hermScal R σ (algebraMap F R t)))

def Preal (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ) (α : R) (c : Fin n → R ⊗[F] E)
    (S' : HermR R σ n) : ℝ :=
  ∫ y₀, ∫ X, φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (α ⊗ₜ[F] (1 : E)) c X)) ∂(m' S')
    ∂(m₁ (hermScal R σ (algebraMap F R t)))

def sTil (y : Fin 1 → Fin (M + 1) → R ⊗[F] E) : HA R σ (blockOne (algebraMap F E t) J) :=
  s (scl ((((a (s0 R (gramR R σ (blockOne (algebraMap F E t) J) y)))⁻¹ : Rˣ) : R) ⊗ₜ[F] (1 : E)) y)

def chi {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞) (y : Fin 1 → Fin (M + 1) → R ⊗[F] E) : ℝ≥0∞ :=
  ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ X : Fin n → Fin M → R ⊗[F] E,
    φ (Fin.cons (y 0) (actW R σ (blockOne (algebraMap F E t) J) (sTil σ J t s a y)
      (fun j => Fin.cons (c j) (X j)))) ∂(coordW R b lam n M) ∂(Measure.pi fun _ => coordK R b lam)

def Uset (B₀ : Set R) (a : R → Rˣ) : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) :=
  gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' (Subtype.val '' Bset R σ t a B₀)

def Unt (R : Type) [CommRing R] [Algebra F R] (n : ℕ) : Set (HermR R σ n) :=
  {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}

def Mid {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ x in B₀, (κ₁ (a x) : ℝ≥0∞) * ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ S' in Unt σ R n,
    Pint σ J t m₁ m' s φ ((a x : Rˣ) : R) c S' ∂(coordHerm R σ b lam n)
    ∂(Measure.pi fun _ => coordK R b lam) ∂lam

end Meas

section Data

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

structure StageData (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ)
    {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E))
    (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J))
    (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0) : Prop where
  hCM : IsCMExt F E σ
  hJ : IsHermND σ J
  ht : t ≠ 0
  hR : IsLocR R
  hlam : lam.IsAddHaarMeasure
  hm₁ : IsGramFib R σ (blockOne (algebraMap F E t) J) 1 (coordW R b lam 1 (M + 1)) (coordHerm R σ b lam 1) m₁
  hm' : IsGramFib R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m'
  hs : Measurable s
  hsec : ∀ y, gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) →
    actW R σ _ (s y) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) = y
  hcpt : ∀ C : Set (Fin 1 → Fin (M + 1) → R ⊗[F] E), IsCompact C →
    ∃ C' : Set (HA R σ (blockOne (algebraMap F E t) J)), IsCompact C' ∧ ∀ y ∈ C,
      gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → s y ∈ C'
  hB₀ : IsOpen B₀
  htB : algebraMap F R t ∈ B₀
  hac : ContinuousOn a B₀
  hoff : ∀ x, x ∉ B₀ → a x = 1
  hsq : ∀ x ∈ B₀, x = ((a x : Rˣ) : R) ^ 2 * algebraMap F R t
  ha1 : a (algebraMap F R t) = 1
  hκc : Continuous κ₁
  hκ1 : κ₁ 1 = 1
  hscale : ∀ u : Rˣ, m₁ (hermScal R σ ((u : R) ^ 2 * algebraMap F R t)) =
    κ₁ u • (m₁ (hermScal R σ (algebraMap F R t))).map (scl ((u : R) ⊗ₜ[F] (1 : E)))
  hcmc : Continuous cm
  hmod : ∀ u : Rˣ, (coordK R b lam).map (fun y => ((u : R) ⊗ₜ[F] (algebraMap F E t)) * y) = cm u • coordK R b lam

end Data

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorInvolutionAlgebraProperties
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.KAlg

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem exists_basis_one_delta (σ : E →ₐ[F] E) {δ : E} (hδ : σ δ = -δ) (h0 : δ ≠ 0)
    (hfr : Module.finrank F E = 2) (h2 : (2 : F) ≠ 0) :
    ∃ b : Module.Basis (Fin 2) F E, b 0 = 1 ∧ b 1 = δ := by
  have li : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : s • (1 : E) + t • (-δ) = 0 := by
      have := congrArg σ hst
      simpa [map_add (f := _), map_smul, hδ] using this
    have hs : (2 * s) • (1 : E) = 0 := by
      have : (2 * s) • (1 : E) = (s • (1 : E) + t • δ) + (s • (1 : E) + t • (-δ)) := by module
      rw [this, hst, h1, add_zero]
    have hs0 : s = 0 := by
      rcases smul_eq_zero.1 hs with h | h
      · exact (mul_eq_zero.1 h).resolve_left h2
      · exact absurd h one_ne_zero
    subst hs0
    refine ⟨rfl, ?_⟩
    rcases smul_eq_zero.1 (by simpa using hst : t • δ = 0) with h | h
    · exact h
    · exact absurd h h0
  refine ⟨basisOfLinearIndependentOfCardEqFinrank li (by simp [hfr]), ?_, ?_⟩
  · simp
  · simp

variable {R : Type} [CommRing R] [Algebra F R]

theorem exists_coord (b : Module.Basis (Fin 2) F E) {δ : E} (hb0 : b 0 = 1) (hb1 : b 1 = δ)
    (y : R ⊗[F] E) : ∃ a c : R, y = a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] δ := by
  let B := Algebra.TensorProduct.basis R b
  refine ⟨B.repr y 0, B.repr y 1, ?_⟩
  have h := (B.sum_repr y).symm
  rw [Fin.sum_univ_two] at h
  have e0 : B 0 = (1 : R) ⊗ₜ[F] (1 : E) := by simp [B, hb0]
  have e1 : B 1 = (1 : R) ⊗ₜ[F] δ := by simp [B, hb1]
  rw [e0, e1, TensorProduct.smul_tmul', TensorProduct.smul_tmul'] at h
  simpa using h

theorem coord_inj (b : Module.Basis (Fin 2) F E) {δ : E} (hb0 : b 0 = 1) (hb1 : b 1 = δ)
    {a c a' c' : R} (h : a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] δ = a' ⊗ₜ[F] (1 : E) + c' ⊗ₜ[F] δ) :
    a = a' ∧ c = c' := by
  let B := Algebra.TensorProduct.basis R b
  have e : ∀ p q : R, p ⊗ₜ[F] (1 : E) + q ⊗ₜ[F] δ = p • B 0 + q • B 1 := by
    intro p q
    have e0 : B 0 = (1 : R) ⊗ₜ[F] (1 : E) := by simp [B, hb0]
    have e1 : B 1 = (1 : R) ⊗ₜ[F] δ := by simp [B, hb1]
    rw [e0, e1, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    simp
  rw [e, e] at h
  have h0 := congrArg (fun y => B.repr y 0) h
  have h1 := congrArg (fun y => B.repr y 1) h
  simp at h0 h1
  exact ⟨h0, h1⟩

theorem tmul_one_injective (b : Module.Basis (Fin 2) F E) {δ : E} (hb0 : b 0 = 1) (hb1 : b 1 = δ) :
    Function.Injective (Algebra.TensorProduct.includeLeft : R →ₐ[F] R ⊗[F] E) := by
  intro p q h
  have h' : p ⊗ₜ[F] (1 : E) + (0 : R) ⊗ₜ[F] δ = q ⊗ₜ[F] (1 : E) + (0 : R) ⊗ₜ[F] δ := by
    simpa using h
  exact (coord_inj b hb0 hb1 h').1

end Coord

theorem algebra_tensor_invol : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [IsArtinianRing R] [IsReduced R],
    IsArtinianRing (R ⊗[F] E) ∧ IsReduced (R ⊗[F] E) ∧ IsUnit (2 : R ⊗[F] E) ∧
      (∀ y, sigR R σ (sigR R σ y) = y) ∧ (∃ δ : R ⊗[F] E, IsUnit δ ∧ sigR R σ δ = -δ) ∧
      (∀ y : R ⊗[F] E, sigR R σ y = y → ∃ r : R, y = r ⊗ₜ[F] (1 : E)) ∧
      ∀ r : R, IsUnit (r ⊗ₜ[F] (1 : E) : R ⊗[F] E) ↔ IsUnit r := by
  intro F E _ _ _ _ _ σ h R _ _ _ _
  have hσσ : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  have hne : ∃ x, σ x ≠ x := by
    by_contra hc
    push Not at hc
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have := h.2.1
    apply IsTotallyComplex.complexEmbedding_not_isReal τ
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have h' := h.2.2.2 τ x
    rw [hc] at h'
    simpa [ComplexEmbedding.conjugate_coe_eq] using h'.symm
  obtain ⟨x₀, hx₀⟩ := hne
  set δ : E := x₀ - σ x₀ with hδdef
  have hδ : σ δ = -δ := by simp [hδdef, hσσ]
  have hδ0 : δ ≠ 0 := fun e => hx₀ (sub_eq_zero.1 e).symm
  have h2F : (2 : F) ≠ 0 := two_ne_zero
  obtain ⟨b, hb0, hb1⟩ := exists_basis_one_delta σ hδ hδ0 h.2.2.1 h2F
  have : Module.Finite F E := Module.Finite.of_basis b
  have hsig : ∀ (a : R) (e : E), sigR R σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := fun _ _ => rfl
  have h2R : IsUnit (2 : R) := by
    have := (IsUnit.mk0 (2 : F) h2F).map (algebraMap F R)
    rwa [map_ofNat] at this
  have half : ∀ a : R, a + a = 0 → a = 0 := fun a ha =>
    (h2R.mul_right_eq_zero).1 (by rw [two_mul, ha])
  have hnil : ∀ a : R, IsNilpotent (a ⊗ₜ[F] (1 : E) : R ⊗[F] E) → a = 0 := fun a ha =>
    ((IsNilpotent.map_iff (tmul_one_injective (R := R) b hb0 hb1)).1 ha).eq_zero
  have hδu : IsUnit ((1 : R) ⊗ₜ[F] δ : R ⊗[F] E) :=
    (IsUnit.mk0 δ hδ0).map (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E)
  refine ⟨IsArtinianRing.of_finite R _, ⟨fun x hx => ?_⟩, ?_, fun y => ?_, ⟨_, hδu, ?_⟩, fun y hy => ?_, fun r => ⟨?_, ?_⟩⟩
  · obtain ⟨a, c, rfl⟩ := exists_coord b hb0 hb1 x
    have hs := hx.map (sigR R σ)
    have hadd := (Commute.all _ _).isNilpotent_add hx hs
    have e1 : (a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] δ) + sigR R σ (a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] δ) =
        (a + a) ⊗ₜ[F] (1 : E) := by
      rw [map_add (f := _), hsig, hsig, map_one, hδ, TensorProduct.tmul_neg, TensorProduct.add_tmul]
      abel
    rw [e1] at hadd
    have ha : a = 0 := half a (hnil _ hadd)
    subst ha
    rw [TensorProduct.zero_tmul, zero_add] at hx ⊢
    have hm : IsNilpotent ((c ⊗ₜ[F] δ) * ((1 : R) ⊗ₜ[F] δ⁻¹) : R ⊗[F] E) :=
      (Commute.all _ _).isNilpotent_mul_right (show IsNilpotent (c ⊗ₜ[F] δ : R ⊗[F] E) from hx)
    have e2 : ((c ⊗ₜ[F] δ) * ((1 : R) ⊗ₜ[F] δ⁻¹) : R ⊗[F] E) = c ⊗ₜ[F] (1 : E) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hδ0]
    rw [e2] at hm
    rw [hnil c hm, TensorProduct.zero_tmul]
  · have := (IsUnit.mk0 (2 : F) h2F).map (algebraMap F (R ⊗[F] E))
    rwa [map_ofNat] at this
  · induction y using TensorProduct.induction_on with
    | zero => simp
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | tmul a e => rw [hsig, hsig, hσσ]
  · rw [hsig, hδ, TensorProduct.tmul_neg]
  · obtain ⟨a, c, rfl⟩ := exists_coord b hb0 hb1 y
    rw [map_add (f := _), hsig, hsig, map_one, hδ, TensorProduct.tmul_neg, ← TensorProduct.neg_tmul] at hy
    have hc := (coord_inj b hb0 hb1 hy).2
    have : c = 0 := half c (by nth_rewrite 1 [← hc]; simp)
    exact ⟨a, by rw [this, TensorProduct.zero_tmul, add_zero]⟩
  · rintro ⟨u, hu⟩
    obtain ⟨a, c, hac⟩ := exists_coord b hb0 hb1 (u⁻¹ : (R ⊗[F] E)ˣ).val
    have e : (r * a) ⊗ₜ[F] (1 : E) + (r * c) ⊗ₜ[F] δ =
        (1 : R) ⊗ₜ[F] (1 : E) + (0 : R) ⊗ₜ[F] δ := by
      have : (u : R ⊗[F] E) * (u⁻¹ : (R ⊗[F] E)ˣ).val = 1 := u.mul_inv
      rw [hu, hac, mul_add, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, one_mul, Algebra.TensorProduct.one_def] at this
      rw [this, TensorProduct.zero_tmul, add_zero]
    exact IsUnit.of_mul_eq_one a (coord_inj b hb0 hb1 e).1
  · intro hr
    exact hr.map (Algebra.TensorProduct.includeLeft : R →ₐ[F] R ⊗[F] E)

end GlobalTheory.CompanionTheory.SW.KAlg
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitProductClosureProperties
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.UnitProdAlg

variable {F : Type} [Field F] [NumberField F]

theorem mulSupport_finite {a : ℝ≥0} {c : HeightOneSpectrum (𝓞 F) → ℝ≥0} (h : IsUnitProd a c) :
    (Function.mulSupport c).Finite := by
  have := h.1
  rw [Filter.eventually_cofinite] at this
  exact this

theorem map_hom (f : ℝ≥0 →* ℝ≥0) {a : ℝ≥0} {c : HeightOneSpectrum (𝓞 F) → ℝ≥0}
    (h : IsUnitProd a c) : IsUnitProd (f a) (fun v => f (c v)) := by
  have hfin := mulSupport_finite h
  refine ⟨h.1.mono fun v hv => by simp [hv], ?_⟩
  have hsub : Function.mulSupport (fun v => f (c v)) ⊆ (hfin.toFinset : Set _) := by
    intro v hv
    simp only [Function.mem_mulSupport] at hv
    simp only [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h1
    exact hv (by simp [h1])
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub, ← map_prod, ← map_mul,
    ← finprod_eq_prod_of_mulSupport_subset c (by simp), h.2, map_one]

def sqrtHom : ℝ≥0 →* ℝ≥0 where
  toFun := NNReal.sqrt
  map_one' := NNReal.sqrt_one
  map_mul' := NNReal.sqrt_mul

theorem mul {a b : ℝ≥0} {c e : HeightOneSpectrum (𝓞 F) → ℝ≥0}
    (h : IsUnitProd a c) (k : IsUnitProd b e) : IsUnitProd (a * b) (fun v => c v * e v) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [h.1, k.1] with v h1 h2
    simp [h1, h2]
  · rw [finprod_mul_distrib (mulSupport_finite h) (mulSupport_finite k), mul_mul_mul_comm,
      h.2, k.2, one_mul]

theorem ne_zero {a : ℝ≥0} {c : HeightOneSpectrum (𝓞 F) → ℝ≥0} (h : IsUnitProd a c) : a ≠ 0 := by
  rintro rfl
  simpa using h.2

theorem family_ne_zero {a : ℝ≥0} {c : HeightOneSpectrum (𝓞 F) → ℝ≥0} (h : IsUnitProd a c)
    (v : HeightOneSpectrum (𝓞 F)) : c v ≠ 0 := by
  intro hv
  have h2 := h.2
  rw [finprod_eq_zero c v hv (mulSupport_finite h)] at h2
  simp at h2

theorem inv {a : ℝ≥0} {c : HeightOneSpectrum (𝓞 F) → ℝ≥0} (h : IsUnitProd a c) :
    IsUnitProd a⁻¹ (fun v => (c v)⁻¹) :=
  map_hom (invMonoidWithZeroHom (G₀ := ℝ≥0) : ℝ≥0 →* ℝ≥0) h

theorem main : ∀ (F : Type) [Field F] [NumberField F] (a b : ℝ≥0)
    (c e : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd a c → IsUnitProd b e →
    a ≠ 0 ∧ (∀ v, c v ≠ 0) ∧ IsUnitProd (a * b) (fun v => c v * e v) ∧
    IsUnitProd a⁻¹ (fun v => (c v)⁻¹) ∧ IsUnitProd (a / b) (fun v => c v / e v) ∧
    IsUnitProd (NNReal.sqrt a) (fun v => NNReal.sqrt (c v)) ∧
    (∀ n : ℕ, IsUnitProd (a ^ n) (fun v => c v ^ n)) ∧
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S →
      (∀ v, v ∉ S → c v = 1) ∧ a * ∏ v ∈ S, c v = 1 := by
  intro F _ _ a b c e h k
  refine ⟨ne_zero h, family_ne_zero h, mul h k, inv h, ?_, map_hom sqrtHom h,
    fun n => map_hom (powMonoidHom n) h, (mulSupport_finite h).toFinset, fun S hS => ?_⟩
  · simpa only [div_eq_mul_inv] using mul h (inv k)
  · have hsub : Function.mulSupport c ⊆ (S : Set _) := by
      intro v hv
      exact hS ((mulSupport_finite h).mem_toFinset.2 hv)
    refine ⟨fun v hv => ?_, ?_⟩
    · by_contra hne
      exact hv (hsub hne)
    · rw [← finprod_eq_prod_of_mulSupport_subset c hsub]
      exact h.2

end GlobalTheory.CompanionTheory.SW.UnitProdAlg
end
end

