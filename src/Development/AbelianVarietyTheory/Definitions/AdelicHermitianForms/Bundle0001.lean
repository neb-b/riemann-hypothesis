module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
section
namespace GlobalTheory.ClassFin

open Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def ev {R : Type} [CommRing R] [Algebra ℚ R] (f : MvPolynomial (ι × ι) ℚ) (g : Matrix ι ι R) : R :=
  MvPolynomial.aeval (fun ij : ι × ι => g ij.1 ij.2) f

noncomputable def evC (f : MvPolynomial (ι × ι) ℂ) (g : Matrix ι ι ℂ) : ℂ :=
  MvPolynomial.eval (fun ij : ι × ι => g ij.1 ij.2) f

def vanI (Γ : Set (Matrix ι ι ℂ)) : Set (MvPolynomial (ι × ι) ℚ) := {f | ∀ g ∈ Γ, ev f g = 0}

def pts (Γ : Set (Matrix ι ι ℂ)) (R : Type) [CommRing R] [Algebra ℚ R] : Set (Matrix ι ι R) :=
  {g | ∀ f ∈ vanI Γ, ev f g = 0}

structure IsPre (Γ : Set (Matrix ι ι ℂ)) : Prop where
  one_mem : (1 : Matrix ι ι ℂ) ∈ Γ
  mul_mem : ∀ g ∈ Γ, ∀ h ∈ Γ, g * h ∈ Γ
  adj_mem : ∀ g ∈ Γ, g.adjugate ∈ Γ
  det_eq : ∀ g ∈ Γ, g.det = 1
  aut_mem : ∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ

structure IsQGroup (Γ : Set (Matrix ι ι ℂ)) : Prop extends IsPre Γ where
  closed : pts Γ ℂ ⊆ Γ

def SS (Γ : Set (Matrix ι ι ℂ)) : Prop :=
  ∀ W : Submodule ℂ (ι → ℂ), (∀ g ∈ Γ, ∀ v ∈ W, g *ᵥ v ∈ W) →
    ∃ W' : Submodule ℂ (ι → ℂ), (∀ g ∈ Γ, ∀ v ∈ W', g *ᵥ v ∈ W') ∧ IsCompl W W'

structure AdelicPair (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R) : Prop where
  int_of_mem : ∀ q : ℚ, algebraMap ℚ R q ∈ R₀ → ∃ z : ℤ, q = z
  approx : ∀ M : ℕ, 0 < M → ∀ r : R, ∃ q : ℚ, ∃ a ∈ R₀, r = algebraMap ℚ R q + (M : R) * a

def CF (Γ : Set (Matrix ι ι ℂ)) (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R) : Prop :=
  ∃ T : Finset (Matrix ι ι R), (∀ s ∈ T, s ∈ pts Γ R) ∧ ∀ x ∈ pts Γ R, ∃ γ ∈ pts Γ ℚ, ∃ s ∈ T, ∃ u ∈ pts Γ R,
    (∀ i j, u i j ∈ R₀) ∧ x = γ.map (algebraMap ℚ R) * s * u

noncomputable def blk {R : Type} [CommRing R] [Algebra ℚ R] (e : Matrix ι ι ℚ) (g : Matrix ι ι R) : Matrix ι ι R :=
  e.map (algebraMap ℚ R) * g * e.map (algebraMap ℚ R) +
    (1 - e.map (algebraMap ℚ R)) * g * (1 - e.map (algebraMap ℚ R))

noncomputable def linExt {R : Type} [CommRing R] [Algebra ℚ R] (c : ι × ι → ι × ι → ℚ) (X : Matrix ι ι R) :
    Matrix ι ι R :=
  Matrix.of fun i j => ∑ kl : ι × ι, algebraMap ℚ R (c (i, j) kl) * X kl.1 kl.2

def IsLog (H A : Matrix ι ι ℂ) : Prop :=
  ∃ (U : Matrix ι ι ℂ) (d : ι → ℝ), U * Uᴴ = 1 ∧ H = U * diagonal (fun i => (d i : ℂ)) * Uᴴ ∧
    A = U * diagonal (fun i => (Real.exp (d i) : ℂ)) * Uᴴ

def Harm {σ : Type} [Fintype σ] (g : σ → Matrix ι ι ℂ) : Prop :=
  ∃ H : σ → Matrix ι ι ℂ, (∀ s, IsLog (H s) ((g s)ᴴ * g s)) ∧ ∑ s, H s = 0

def tpow {R : Type} [CommRing R] (d : ℕ) (y : Matrix ι ι R) : Matrix (Fin d → ι) (Fin d → ι) R :=
  Matrix.of fun a b => ∏ k, y (a k) (b k)

abbrev TIdx (ι : Type) {m : ℕ} (d : Fin m → ℕ) : Type := Σ i : Fin m, (Fin (d i) → ι)

def act {R : Type} [CommRing R] {m : ℕ} (d : Fin m → ℕ) (t : TIdx ι d → R) (y : Matrix ι ι R) : TIdx ι d → R :=
  fun k => ((fun a => t ⟨k.1, a⟩) ᵥ* tpow (d k.1) y) k.2

noncomputable def nsq {κ : Type} [Fintype κ] (v : κ → ℂ) : ℝ := ∑ k, ‖v k‖ ^ 2

def orb {m : ℕ} (d : Fin m → ℕ) (v : TIdx ι d → ℂ) : Set (TIdx ι d → ℂ) :=
  {w | ∃ y : Matrix ι ι ℂ, y.det = 1 ∧ w = act d v y}

def IsMinVec {m : ℕ} (d : Fin m → ℕ) (v : TIdx ι d → ℂ) : Prop := ∀ w ∈ orb d v, nsq v ≤ nsq w

def IsInv (Γ : Set (Matrix ι ι ℂ)) (f : MvPolynomial (ι × ι) ℂ) : Prop :=
  ∀ g ∈ Γ, ∀ y : Matrix ι ι ℂ, evC f (g * y) = evC f y

noncomputable def ltr (g : Matrix ι ι ℂ) : MvPolynomial (ι × ι) ℂ →ₐ[ℂ] MvPolynomial (ι × ι) ℂ :=
  MvPolynomial.aeval fun ij : ι × ι => ∑ k, MvPolynomial.C (g ij.1 k) * MvPolynomial.X (k, ij.2)

structure IsReynolds (Γ : Set (Matrix ι ι ℂ)) (Rey : MvPolynomial (ι × ι) ℂ →ₗ[ℂ] MvPolynomial (ι × ι) ℂ) : Prop where
  inv : ∀ f, IsInv Γ (Rey f)
  fix : ∀ f, IsInv Γ f → Rey f = f
  mul : ∀ a f, IsInv Γ a → Rey (a * f) = a * Rey f
  stable : ∀ U : Submodule ℂ (MvPolynomial (ι × ι) ℂ), (∀ g ∈ Γ, ∀ f ∈ U, ltr g f ∈ U) → ∀ f ∈ U, Rey f ∈ U

structure IsSiegel [LinearOrder ι] (C : ℝ) (k : Matrix ι ι ℝ) (a : ι → ℝ) (n : Matrix ι ι ℝ) : Prop where
  orth : kᵀ * k = 1
  det_k : k.det = 1
  pos : ∀ i, 0 < a i
  prod_eq : ∏ i, a i = 1
  le : ∀ i j, i < j → a i ≤ C * a j
  diag : ∀ i, n i i = 1
  lower : ∀ i j, j < i → n i j = 0
  bdd : ∀ i j, |n i j| ≤ C

noncomputable def res {R A β κ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β]
    (b : Module.Basis β R A) (g : Matrix κ κ A) : Matrix (κ × β) (κ × β) R :=
  Matrix.of fun p q => Algebra.leftMulMatrix b (g p.1 q.1) p.2 q.2

noncomputable def emb {R A β κ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β]
    [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A) (g : GL κ A) :
    Matrix ((κ × β) ⊕ Unit) ((κ × β) ⊕ Unit) R :=
  Matrix.fromBlocks (res b (g : Matrix κ κ A)) 0 0
    (Matrix.of fun _ _ => (res b ((g⁻¹ : GL κ A) : Matrix κ κ A)).det)

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermHyperbolic
section
noncomputable section

namespace GlobalTheory.UTrans

variable {R : Type} [CommRing R] {n : ℕ}

def hf (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) (x y : Fin n → R) : R :=
  ∑ a, ∑ b, x a * G a b * σ (y b)

def IsU (σ : R →+* R) (G γ : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ x y, hf σ G (γ.mulVec x) (γ.mulVec y) = hf σ G x y

def tv (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) (x : Fin n → R) (t : R) : Matrix (Fin n) (Fin n) R :=
  1 + Matrix.of fun a b => t * x a * ∑ e, G b e * σ (x e)

def TvGen (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) : Submonoid (Matrix (Fin n) (Fin n) R) :=
  Submonoid.closure {m | ∃ x t, hf σ G x x = 0 ∧ t + σ t = 0 ∧ m = tv σ G x t}

structure IsHerm {E : Type} [Field E] (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) : Prop where
  invol : ∀ a, σ (σ a) = a
  ne_id : ∃ a, σ a ≠ a
  herm : ∀ a b, σ (G a b) = G b a
  det_ne : G.det ≠ 0

end GlobalTheory.UTrans
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
section
open NumberField IsDedekindDomain
open scoped WithZero

noncomputable section

namespace GlobalTheory.QNorm

def sqSub {F L : Type} [Field F] [Field L] (φ : F →+* L) : Subgroup Fˣ where
  carrier := {x | IsSquare (φ (x : F))}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simpa using IsSquare.mul ha hb
  inv_mem' := by
    intro a ha
    simpa using IsSquare.inv ha

def normSub {F L : Type} [Field F] [Field L] (φ : F →+* L) (δ : F) : Subgroup Fˣ where
  carrier := {x | ∃ a b : L, φ (x : F) = a ^ 2 - φ δ * b ^ 2}
  one_mem' := ⟨1, 0, by simp⟩
  mul_mem' := by
    rintro x y ⟨a, b, h⟩ ⟨c, d, h'⟩
    refine ⟨a * c + φ δ * b * d, a * d + b * c, ?_⟩
    rw [Units.val_mul, map_mul, h, h']; ring
  inv_mem' := by
    rintro x ⟨a, b, h⟩
    have hx : φ (x : F) ≠ 0 := by simp
    refine ⟨a / φ (x : F), b / φ (x : F), ?_⟩
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    field_simp
    rw [← h]

theorem mem_sqSub {F L : Type} [Field F] [Field L] (φ : F →+* L) (x : Fˣ) :
    x ∈ sqSub φ ↔ IsSquare (φ (x : F)) := Iff.rfl

theorem mem_normSub {F L : Type} [Field F] [Field L] (φ : F →+* L) (δ : F) (x : Fˣ) :
    x ∈ normSub φ δ ↔ ∃ a b : L, φ (x : F) = a ^ 2 - φ δ * b ^ 2 := Iff.rfl

theorem sqSub_le_normSub {F L : Type} [Field F] [Field L] (φ : F →+* L) (δ : F) :
    sqSub φ ≤ normSub φ δ := by
  rintro x ⟨r, hr⟩
  exact ⟨r, 0, by rw [hr]; ring⟩

def sqs {G : Type} [CommGroup G] (U : Subgroup G) : Subgroup G := U.map (powMonoidHom 2)

def hiUnits {K : Type} [Field K] (w : Valuation K ℤᵐ⁰) (n : ℕ) : Subgroup Kˣ where
  carrier := {x | w (x : K) = 1 ∧ w ((x : K) - 1) ≤ WithZero.exp (-(n : ℤ))}
  one_mem' := by simp
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨by simp [hx, hy], ?_⟩
    have : ((x * y : Kˣ) : K) - 1 = (x : K) * ((y : K) - 1) + ((x : K) - 1) := by
      rw [Units.val_mul]; ring
    rw [this]
    refine le_trans (w.map_add _ _) (max_le ?_ hx')
    rw [map_mul, hx, one_mul]; exact hy'
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨by simp [hx], ?_⟩
    have : ((x⁻¹ : Kˣ) : K) - 1 = -((x : K)⁻¹ * ((x : K) - 1)) := by
      rw [Units.val_inv_eq_inv_val]; field_simp; ring
    rw [this, Valuation.map_neg, map_mul, map_inv₀, hx, inv_one, one_mul]; exact hx'

def EvenNorms {K : Type} [Field K] (w : Valuation K ℤᵐ⁰) (Δ : K) : Prop :=
  ∀ a b : K, (a ≠ 0 ∨ b ≠ 0) → ∃ n : ℤ, w (a ^ 2 - Δ * b ^ 2) = WithZero.exp (2 * n)

variable (F : Type) [Field F] [NumberField F]

def sUnits (S : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup Fˣ :=
  (S : Set (HeightOneSpectrum (𝓞 F))).unit F

theorem mem_sUnits (S : Finset (HeightOneSpectrum (𝓞 F))) (x : Fˣ) :
    x ∈ sUnits F S ↔ ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → v.valuation F (x : F) = 1 :=
  Iff.rfl

def finSq (S : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup Fˣ :=
  ⨅ v ∈ S, sqSub (algebraMap F (v.adicCompletion F))

def locSq (S : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup Fˣ :=
  finSq F S ⊓ ⨅ σ : F →+* ℝ, sqSub σ

def locNorm (δ : F) (S : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup Fˣ :=
  (⨅ v ∈ S, normSub (algebraMap F (v.adicCompletion F)) δ) ⊓ ⨅ σ : F →+* ℝ, normSub σ δ

def tFin (δ : F) (S : Finset (HeightOneSpectrum (𝓞 F))) : ℕ :=
  Set.ncard {v : HeightOneSpectrum (𝓞 F) |
    v ∈ S ∧ ¬ IsSquare (algebraMap F (v.adicCompletion F) δ)}

def tReal (δ : F) : ℕ := Set.ncard {σ : F →+* ℝ | σ δ < 0}

def admitted (S : Finset (HeightOneSpectrum (𝓞 F))) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → v.valuation F 2 = 1 ∧
    ∃ π : F, v.valuation F π = WithZero.exp (-1) ∧
      ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → w ≠ v → w.valuation F π = 1

theorem admitted.mono {F : Type} [Field F] [NumberField F] {S T : Finset (HeightOneSpectrum (𝓞 F))}
    (h : admitted F S) (hST : S ⊆ T) : admitted F T := by
  intro v hv
  obtain ⟨h2, π, hπ, hw⟩ := h v (fun a => hv (hST a))
  exact ⟨h2, π, hπ, fun w hwT hne => hw w (fun a => hwT (hST a)) hne⟩

structure IsQuad {F E : Type} [Field F] [Field E] [Algebra F E] (δ : F) (θ : E)
    (σ : E ≃ₐ[F] E) : Prop where
  nonsq : ¬ IsSquare δ
  sq : θ ^ 2 = algebraMap F E δ
  conj : σ θ = -θ
  span : ∀ x : E, ∃ a b : F, x = algebraMap F E a + algebraMap F E b * θ

end GlobalTheory.QNorm

end
end

