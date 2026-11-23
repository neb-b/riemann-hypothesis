module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
public import Formalism.PairingDivisors.StatementH
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0220

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.InertSign

abbrev Lat (D : D7) (n : ℕ) : Type := Submodule (𝓞 D.host.E) (Fin n → D.host.E)

def hE (D : D7) {n : ℕ} (x y : Fin n → D.host.E) : D.host.E := ∑ i, x i * D.host.conj (y i)

def IntE (D : D7) (e : D.host.E) : Prop := e ∈ (algebraMap (𝓞 D.host.E) D.host.E).range

def sgO (D : D7) : 𝓞 D.host.E →+* 𝓞 D.host.E :=
  MulSemiringAction.toRingHom (D.host.E ≃ₐ[ℚ] D.host.E) (𝓞 D.host.E) D.host.conj

theorem sgO_coe (D : D7) (a : 𝓞 D.host.E) : ((sgO D a : 𝓞 D.host.E) : D.host.E) = D.host.conj a := rfl

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  letI := D.host.cmStar
  rw [← AdLattice.star_eq_conj, ← AdLattice.star_eq_conj]
  exact star_star x

theorem sgO_sgO (D : D7) (a : 𝓞 D.host.E) : sgO D (sgO D a) = a :=
  Subtype.ext (conj_conj D a)

theorem embT_conj (D : D7) (τ : D.what₂.Tau) (x : D.host.E) :
    embT D τ (D.host.conj x) = (starRingEnd ℂ) (embT D τ x) := by
  letI := D.host.isCMField_hostE
  rw [← AdLattice.star_eq_conj]
  exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E (embT D τ) x

theorem conj_hE (D : D7) {n : ℕ} (x y : Fin n → D.host.E) : D.host.conj (hE D x y) = hE D y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hE, map_sum, map_mul, conj_conj, mul_comm]

theorem hE_add_left (D : D7) {n : ℕ} (x x' y : Fin n → D.host.E) : hE D (x + x') y = hE D x y + hE D x' y := by
  simp only [hE, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem hE_add_right (D : D7) {n : ℕ} (x y y' : Fin n → D.host.E) : hE D x (y + y') = hE D x y + hE D x y' := by
  simp only [hE, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem hE_smul_left (D : D7) {n : ℕ} (a : D.host.E) (x y : Fin n → D.host.E) : hE D (a • x) y = a * hE D x y := by
  simp only [hE, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem hE_smul_right (D : D7) {n : ℕ} (a : D.host.E) (x y : Fin n → D.host.E) :
    hE D x (a • y) = D.host.conj a * hE D x y := by
  simp only [hE, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem IntE.conj {D : D7} {e : D.host.E} (h : IntE D e) : IntE D (D.host.conj e) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨sgO D a, rfl⟩

theorem sd_iff (D : D7) {n : ℕ} (L : Lat D n) : SD D L ↔
    L.FG ∧ Submodule.span D.host.E (L : Set (Fin n → D.host.E)) = ⊤ ∧ ∀ y, y ∈ L ↔ ∀ x ∈ L, IntE D (hE D y x) := by
  unfold SD IsSDLat
  simp only [stdH, AdLattice.star_eq_conj, IntE, hE, mul_comm]

def nbM (D : D7) {n : ℕ} (B : Lat D n) (x : Fin n → D.host.E) : Lat D n where
  carrier := {y | y ∈ B ∧ IntE D (hE D y x)}
  add_mem' := fun {a b} ha hb => ⟨B.add_mem ha.1 hb.1, by rw [hE_add_left]; exact add_mem ha.2 hb.2⟩
  zero_mem' := ⟨B.zero_mem, by simp only [hE, Pi.zero_apply, zero_mul, Finset.sum_const_zero]; exact zero_mem _⟩
  smul_mem' := fun c a ha => ⟨B.smul_mem c ha.1, by
    rw [← algebraMap_smul D.host.E c a, hE_smul_left]; exact mul_mem ⟨c, rfl⟩ ha.2⟩

theorem mem_nbM {D : D7} {n : ℕ} {B : Lat D n} {x y : Fin n → D.host.E} :
    y ∈ nbM D B x ↔ y ∈ B ∧ IntE D (hE D y x) := Iff.rfl

def nbr (D : D7) {n : ℕ} (B : Lat D n) (x : Fin n → D.host.E) : Lat D n :=
  nbM D B x ⊔ Submodule.span (𝓞 D.host.E) {x}

def NbD (D : D7) {n : ℕ} (P : Ideal (𝓞 D.host.E)) (B : Lat D n) (x : Fin n → D.host.E) : Prop :=
  x ∉ B ∧ (∀ p ∈ P, p • x ∈ B) ∧ IntE D (hE D x x)

def Tri (D : D7) {n : ℕ} (P : Ideal (𝓞 D.host.E)) (A B C : Lat D n) : Prop :=
  SD D A ∧ SD D B ∧ SD D C ∧ ∃ (M : Lat D n) (b x : Fin n → D.host.E),
    A = M ⊔ Submodule.span (𝓞 D.host.E) {b + x} ∧ B = M ⊔ Submodule.span (𝓞 D.host.E) {b} ∧
    C = M ⊔ Submodule.span (𝓞 D.host.E) {x} ∧ (∀ p ∈ P, p • b ∈ M ∧ p • x ∈ M) ∧ ¬ IntE D (hE D b x)

def Bet (D : D7) {n : ℕ} (L₁ L₂ L₃ : Lat D n) : Prop := L₂ ≤ (L₁ ⊓ L₂) ⊔ (L₂ ⊓ L₃) ∧ L₁ ⊓ L₃ ≤ L₂

def cT (D : D7) {m n : ℕ} (s : Matrix (Fin m) (Fin n) D.host.E) : Matrix (Fin n) (Fin m) D.host.E :=
  (s.map D.host.conj).transpose

def SAt (D : D7) {n : ℕ} (q : ℕ) (s : Matrix (Fin n) (Fin n) D.host.E) (L L₁ : Lat D n) : Prop :=
  ∃ m : ℕ, Nat.Coprime m q ∧ (∀ v ∈ L, (m : D.host.E) • s.mulVec v ∈ L₁) ∧
    ∀ v ∈ L₁, (m : D.host.E) • (cT D s).mulVec v ∈ L

def Iid (D : D7) (cc : Ideal (𝓞 D.host.K)) : Submodule (𝓞 D.host.E) D.host.E :=
  Submodule.span (𝓞 D.host.E) {t | ∃ c ∈ cc, ∃ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E),
    t = ((c : D.host.K) : D.host.E) * a}

def RL (D : D7) (cc : Ideal (𝓞 D.host.K)) {N N' : ℕ} (L : Lat D N) (L' : Lat D N') :
    Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E) :=
  Submodule.span (𝓞 D.host.E) {z | ∃ t ∈ Iid D cc, ∃ A ∈ homL D L L', z = t • A}

def bc (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') : ℂ :=
  Complex.exp (-(Real.pi : ℂ) * Complex.I *
    ((Real.sqrt D.host.d * (Hf D T x y).re + (Hf D T x y).im : ℝ) : ℂ))

theorem Hf_add_left (D : D7) (T : Tor D) {N N' : ℕ} (x x' y : VC D N N') :
    Hf D T (x + x') y = Hf D T x y + Hf D T x' y := by
  simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]

theorem Hf_add_right (D : D7) (T : Tor D) {N N' : ℕ} (x y y' : VC D N N') :
    Hf D T x (y + y') = Hf D T x y + Hf D T x y' := by
  simp only [Hf, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib, add_div]

theorem Hf_conj (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') :
    (starRingEnd ℂ) (Hf D T x y) = Hf D T y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal, mul_comm]

theorem bc_ne_zero (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') : bc D T x y ≠ 0 := Complex.exp_ne_zero _

theorem bc_add_left (D : D7) (T : Tor D) {N N' : ℕ} (x x' y : VC D N N') :
    bc D T (x + x') y = bc D T x y * bc D T x' y := by
  rw [bc, bc, bc, ← Complex.exp_add, Hf_add_left, Complex.add_re, Complex.add_im]
  congr 1; push_cast; ring

theorem bc_add_right (D : D7) (T : Tor D) {N N' : ℕ} (x y y' : VC D N N') :
    bc D T x (y + y') = bc D T x y * bc D T x y' := by
  rw [bc, bc, bc, ← Complex.exp_add, Hf_add_right, Complex.add_re, Complex.add_im]
  congr 1; push_cast; ring

theorem bc_zero_left (D : D7) (T : Tor D) {N N' : ℕ} (y : VC D N N') : bc D T 0 y = 1 := by
  have h := bc_add_left D T 0 0 y
  rw [add_zero] at h
  exact (mul_eq_left₀ (bc_ne_zero D T 0 y)).1 h.symm

theorem bc_zero_right (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') : bc D T x 0 = 1 := by
  have h := bc_add_right D T x 0 0
  rw [add_zero] at h
  exact (mul_eq_left₀ (bc_ne_zero D T x 0)).1 h.symm

theorem bc_comm (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') :
    bc D T x y = Complex.exp (-(2 * Real.pi * Complex.I) * ((Hf D T x y).im : ℂ)) * bc D T y x := by
  rw [bc, bc, ← Complex.exp_add, ← Hf_conj D T x y, Complex.conj_re, Complex.conj_im]
  congr 1; push_cast; ring

theorem Wd_Wd (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') (F : VC D N N' → ℂ) :
    Wd D T x (Wd D T y F) = bc D T x y • Wd D T (x + y) F := by
  funext z
  have hc := Hf_conj D T x y
  have hre : (Hf D T y x).re = (Hf D T x y).re := by rw [← hc, Complex.conj_re]
  have h2 : Hf D T y x = Hf D T x y - 2 * Complex.I * ((Hf D T x y).im : ℂ) := by
    rw [← hc]; apply Complex.ext <;> simp <;> ring
  simp only [Wd, U, wdPh, ee, bc, qH, Pi.smul_apply, smul_eq_mul, Hf_add_left, Hf_add_right, Complex.add_re, hre,
    add_assoc]
  rw [h2]
  have key : ∀ a b c d' e f g' : ℂ, ∀ v : ℂ, a + b + c + d' = e + f + g' →
      Complex.exp a * (Complex.exp b * (v * Complex.exp c) * Complex.exp d') =
        Complex.exp e * (Complex.exp f * (v * Complex.exp g')) := by
    intro a b c d' e f g' v h
    have := congrArg Complex.exp h
    simp only [Complex.exp_add] at this
    linear_combination v * this
  apply key
  push_cast; ring

theorem Wd_add (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') (F G : VC D N N' → ℂ) :
    Wd D T x (F + G) = Wd D T x F + Wd D T x G := by
  funext z; simp only [Wd, U, Pi.add_apply]; ring

theorem Wd_smul (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') (a : ℂ) (F : VC D N N' → ℂ) :
    Wd D T x (a • F) = a • Wd D T x F := by
  funext z; simp only [Wd, U, Pi.smul_apply, smul_eq_mul]; ring

def Nice (D : D7) (T : Tor D) {N N' : ℕ} (A : AddSubgroup (VC D N N')) : Prop :=
  (∀ x ∈ A, ∀ F, Wd D T x F = fun z => al D T x * U D T x F z) ∧ (∀ x ∈ A, ∀ y ∈ A, bc D T x y = 1) ∧
    ∀ x, (∀ y ∈ A, bc D T x y = bc D T y x) → x ∈ A

theorem Nice.mem_ThSp {D : D7} {T : Tor D} {N N' : ℕ} {A : AddSubgroup (VC D N N')} (h : Nice D T A)
    (F : VC D N N' → ℂ) : F ∈ ThSp D T A ↔ Differentiable ℂ F ∧ ∀ x ∈ A, Wd D T x F = F := by
  refine and_congr_right fun _ => forall₂_congr fun x hx => ?_
  rw [h.1 x hx, funext_iff]

theorem Nice.Iop_eq {D : D7} {T : Tor D} {N N' : ℕ} (A : AddSubgroup (VC D N N')) {B : AddSubgroup (VC D N N')}
    (h : Nice D T B) (F : VC D N N' → ℂ) :
    Iop D T A B F = fun z => ((Real.sqrt ((A.addSubgroupOf B).index : ℝ))⁻¹ : ℂ) *
      ∑ᶠ q : B ⧸ A.addSubgroupOf B, Wd D T ((Quotient.out q : B) : VC D N N') F z := by
  funext z
  simp only [Iop]
  congr 1
  exact finsum_congr fun q => by rw [h.1 _ (Quotient.out q : B).2]

def Trip (D : D7) (T : Tor D) {N N' : ℕ} (A₁ A₂ A₃ : AddSubgroup (VC D N N')) (e : VC D N N' → ℂ) (μ : ℂ) : Prop :=
  Nice D T A₁ ∧ Nice D T A₂ ∧ Nice D T A₃ ∧ (A₁.addSubgroupOf A₂).index ≠ 0 ∧ (A₂.addSubgroupOf A₃).index ≠ 0 ∧
    (A₁.addSubgroupOf A₃).index ≠ 0 ∧ e ∈ ThSp D T A₁ ∧ e ≠ 0 ∧ μ ^ 8 = 1 ∧
    Iop D T A₂ A₃ (Iop D T A₁ A₂ e) = fun z => μ * Iop D T A₁ A₃ e z

def Dist {V : Type} [AddCommGroup V] (A₁ A₂ A₃ : AddSubgroup V) : Prop :=
  ∀ x ∈ A₂, ∀ y ∈ A₃, x + y ∈ A₁ → x ∈ (A₁ ⊓ A₂) ⊔ (A₂ ⊓ A₃)

def TriDat (D : D7) (T : Tor D) {N N' : ℕ} (A₁ A₂ A₃ : AddSubgroup (VC D N N')) (P : Ideal (𝓞 D.host.E)) (r : ℕ) : Prop :=
  ∃ (X Y : Fin r → 𝓞 D.host.E →+ VC D N N') (φ : Fin r → 𝓞 D.host.E →+ ℂ),
    (∀ i j a a', Hf D T (Y i a') (X j a) = if i = j then φ i (a' * sgO D a) else 0) ∧
    (∀ i a, X i a ∈ A₂ ∧ Y i a ∈ A₃ ∧ X i a + Y i a ∈ A₁) ∧
    (∀ i, ∀ p ∈ P, X i p ∈ A₁ ⊓ A₃ ∧ Y i p ∈ A₁ ⊓ A₂) ∧
    (∀ z ∈ A₂, ∃ a : Fin r → 𝓞 D.host.E, z - ∑ i, X i (a i) ∈ A₁ ⊓ A₃) ∧
    (∀ z ∈ A₃, ∃ a : Fin r → 𝓞 D.host.E, z - ∑ i, Y i (a i) ∈ A₁ ⊓ A₂) ∧
    (∀ a : Fin r → 𝓞 D.host.E, ∑ i, X i (a i) ∈ A₁ → ∀ i, a i ∈ P) ∧
    (∀ a : Fin r → 𝓞 D.host.E, ∑ i, Y i (a i) ∈ A₂ → ∀ i, a i ∈ P)

end GlobalTheory.InertSign
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeriodThetaDifferentiableAndSignedTranslateI
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.HalfPeriodTheta

theorem parity_mod_two : ∀ a b c d s₁ s₂ x₁ x₂ : ZMod 2,
    a * a + b * c = a → a * b + b * d = b → c * a + d * c = c → c * b + d * d = d →
    ¬ (a * s₁ + c * s₂ = 0 ∧ b * s₁ + d * s₂ = 0) →
    ¬ (s₁ - (a * s₁ + c * s₂) = 0 ∧ s₂ - (b * s₁ + d * s₂) = 0) →
    (((a * x₁ + c * x₂) * x₂ - (b * x₁ + d * x₂) * x₁) + (x₁ * s₂ - x₂ * s₁) = 0 ↔ x₁ = 0 ∧ x₂ = 0) := by
  decide

theorem exists_orthonormal_basis_family (Λ : AddSubgroup ℂ) (ω t : ℂ) (G : ℂ → ℂ) (z : ℂ) :
    U1 Λ ω (U1 Λ t G) z =
      Complex.exp (-(Real.pi : ℂ) * Complex.I * (gl3FieldFirst Λ ω (2 * t) : ℂ)) * U1 Λ t (U1 Λ ω G) z := by
  have h : ((gl3FieldFirst Λ ω (2 * t) : ℝ) : ℂ) * Complex.I =
      (ω * (starRingEnd ℂ) t - t * (starRingEnd ℂ) ω) / (area Λ : ℂ) := by
    have h2 := Complex.sub_conj (ω * (starRingEnd ℂ) t)
    rw [map_mul, Complex.conj_conj, mul_comm ((starRingEnd ℂ) ω) t] at h2
    have h3 : (ω * (starRingEnd ℂ) (2 * t)).im = 2 * (ω * (starRingEnd ℂ) t).im := by
      simp; ring
    rw [h2, gl3FieldFirst, h3]
    push_cast
    ring
  have h' : -(Real.pi : ℂ) * Complex.I * (gl3FieldFirst Λ ω (2 * t) : ℂ) =
      -(Real.pi : ℂ) * ((ω * (starRingEnd ℂ) t - t * (starRingEnd ℂ) ω) / (area Λ : ℂ)) := by
    rw [← h]; ring
  rw [h']
  simp only [U1]
  rw [add_right_comm z t ω, mul_assoc (G _), mul_assoc (G _), ← Complex.exp_add, ← Complex.exp_add,
    mul_left_comm _ (G _), ← Complex.exp_add]
  congr 2
  ring

theorem even_im_hermitian_sub (Λ : AddSubgroup ℂ) (w₁ w₂ : ℂ) (hi : LinearIndependent ℝ ![w₁, w₂])
    (hΛ : Λ = AddSubgroup.closure {w₁, w₂})
    (hsd : ∀ z : ℂ, z ∈ Λ ↔ ∀ w ∈ Λ, ∃ m : ℤ, gl3FieldFirst Λ z w = m)
    (θ : ℂ) (N : ℤ) (hN : Even N) (hθ : θ * θ = θ - N) (hst : ∀ w ∈ Λ, θ * w ∈ Λ)
    (t : ℂ) (ht : 2 * t ∈ Λ) (h1 : θ * t ∉ Λ) (h2 : (1 - θ) * t ∉ Λ) (ω : ℂ) (hω : ω ∈ Λ) :
    ∃ m n : ℤ, gl3FieldFirst Λ (θ * ω) ω = m ∧ gl3FieldFirst Λ ω (2 * t) = n ∧ (Even (m + n) ↔ ω / 2 ∈ Λ) := by
  have mem : ∀ z, z ∈ Λ ↔ ∃ x y : ℤ, z = x * w₁ + y * w₂ := by
    intro z
    rw [hΛ, AddSubgroup.mem_closure_pair]
    simp only [zsmul_eq_mul, eq_comm]
  have uniq : ∀ x y : ℤ, (x : ℂ) * w₁ + y * w₂ = 0 → x = 0 ∧ y = 0 := by
    intro x y h
    have := LinearIndependent.pair_iff.1 hi (x : ℝ) (y : ℝ) (by simpa using h)
    exact_mod_cast this
  have half : ∀ x y : ℤ, ((x : ℂ) * w₁ + y * w₂) / 2 ∈ Λ ↔ (x : ZMod 2) = 0 ∧ (y : ZMod 2) = 0 := by
    intro x y
    rw [mem, ZMod.intCast_eq_zero_iff_even, ZMod.intCast_eq_zero_iff_even]
    constructor
    · rintro ⟨u, v, h⟩
      obtain ⟨e1, e2⟩ := uniq (x - 2 * u) (y - 2 * v) (by push_cast; linear_combination 2 * h)
      exact ⟨⟨u, by omega⟩, ⟨v, by omega⟩⟩
    · rintro ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
      exact ⟨u, v, by push_cast; ring⟩
  have hw₁ : w₁ ∈ Λ := (mem _).2 ⟨1, 0, by simp⟩
  have hw₂ : w₂ ∈ Λ := (mem _).2 ⟨0, 1, by simp⟩
  obtain ⟨e, he⟩ := (hsd w₁).1 hw₁ w₂ hw₂
  have EFr : ∀ x y u v : ℝ, gl3FieldFirst Λ (x * w₁ + y * w₂) (u * w₁ + v * w₂) = (x * v - y * u) * e := by
    intro x y u v
    rw [← he]
    simp only [gl3FieldFirst]
    simp
    ring
  have EFi : ∀ x y u v : ℤ, gl3FieldFirst Λ (x * w₁ + y * w₂) (u * w₁ + v * w₂) = (((x * v - y * u) * e : ℤ) : ℝ) := by
    intro x y u v
    have := EFr x y u v
    push_cast at this ⊢
    exact this
  have hodd : (e : ZMod 2) = 1 := by
    rw [ZMod.intCast_eq_one_iff_odd, ← Int.not_even_iff_odd]
    rintro ⟨k, hk⟩
    have : (((1 : ℤ) : ℂ) * w₁ + ((0 : ℤ) : ℂ) * w₂) / 2 ∈ Λ := by
      rw [hsd]
      intro w hw
      obtain ⟨u, v, rfl⟩ := (mem _).1 hw
      refine ⟨v * k, ?_⟩
      have := EFr (1 / 2) 0 u v
      rw [hk] at this
      push_cast at this ⊢
      rw [show (1 * w₁ + 0 * w₂) / 2 = 1 / 2 * w₁ + 0 * w₂ by ring, this]
      ring
    rw [half] at this
    exact absurd this.1 (by decide)
  obtain ⟨a, b, hab⟩ := (mem _).1 (hst _ hw₁)
  obtain ⟨c, d, hcd⟩ := (mem _).1 (hst _ hw₂)
  obtain ⟨s₁, s₂, hs⟩ := (mem _).1 ht
  obtain ⟨x₁, x₂, rfl⟩ := (mem _).1 hω
  have mul : ∀ x y : ℤ, θ * ((x : ℂ) * w₁ + y * w₂) =
      ((a * x + c * y : ℤ) : ℂ) * w₁ + ((b * x + d * y : ℤ) : ℂ) * w₂ := by
    intro x y
    push_cast
    linear_combination (x : ℂ) * hab + (y : ℂ) * hcd
  obtain ⟨r1, r2⟩ := uniq (a * a + b * c - a + N) (a * b + b * d - b) (by
    push_cast
    linear_combination w₁ * hθ - (θ + a - 1) * hab - (b : ℂ) * hcd)
  obtain ⟨r3, r4⟩ := uniq (c * a + d * c - c) (c * b + d * d - d + N) (by
    push_cast
    linear_combination w₂ * hθ - (θ + d - 1) * hcd - (c : ℂ) * hab)
  have hN2 : (N : ZMod 2) = 0 := ZMod.intCast_eq_zero_iff_even.2 hN
  have q1 := congrArg (Int.cast : ℤ → ZMod 2) r1
  have q2 := congrArg (Int.cast : ℤ → ZMod 2) r2
  have q3 := congrArg (Int.cast : ℤ → ZMod 2) r3
  have q4 := congrArg (Int.cast : ℤ → ZMod 2) r4
  push_cast at q1 q2 q3 q4
  have e1 : θ * t = (((a * s₁ + c * s₂ : ℤ) : ℂ) * w₁ + ((b * s₁ + d * s₂ : ℤ) : ℂ) * w₂) / 2 := by
    rw [← mul, ← hs]; ring
  have e2 : (1 - θ) * t = (((s₁ - (a * s₁ + c * s₂) : ℤ) : ℂ) * w₁ + ((s₂ - (b * s₁ + d * s₂) : ℤ) : ℂ) * w₂) / 2 := by
    push_cast at e1 ⊢
    linear_combination (1 / 2) * hs - e1
  rw [e1, half] at h1
  rw [e2, half] at h2
  push_cast at h1 h2
  refine ⟨_, _, by rw [mul, EFi], by rw [hs, EFi], ?_⟩
  rw [half, ← ZMod.intCast_eq_zero_iff_even]
  push_cast
  rw [hodd, mul_one, mul_one]
  exact parity_mod_two _ _ _ _ _ _ _ _ (by linear_combination q1 - hN2) (by linear_combination q2)
    (by linear_combination q3) (by linear_combination q4 - hN2) h1 h2

theorem theta_signed_translation : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Differentiable ℂ (GL3Theta.th0 (lamOf D cc δ) t0) ∧ ∀ ω ∈ lamOf D cc δ, ∃ m : ℤ, q1 D (lamOf D cc δ) ω = (m : ℝ) ∧ ∀ z, (-1 : ℂ) ^ m * U1 (lamOf D cc δ) ω (GL3Theta.th0 (lamOf D cc δ) t0) z = GL3Theta.th0 (lamOf D cc δ) t0 z := by
  intro D hG cc δ hC t0 ht
  obtain ⟨hb, -, -, -, hst⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hC
  set Λ := lamOf D cc δ
  obtain ⟨⟨hdiff, -, -, hlaw⟩, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ hb
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ hb
  obtain ⟨-, hsd⟩ := GlobalTheory.PlaneLattice.area_pos_and_selfDual L Λ hL
  obtain ⟨w₁, w₂, hi, hΛ⟩ := hb
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  have hd : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  obtain ⟨k, hk⟩ : ∃ k : ℕ, D.host.d = 16 * k + 7 := ⟨D.host.d / 16, by omega⟩
  have hsq : ((Real.sqrt D.host.d : ℝ) : ℂ) * (Real.sqrt D.host.d : ℝ) = 16 * (k : ℂ) + 7 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), hk]
    push_cast; ring
  refine ⟨?_, fun ω hω => ?_⟩
  · unfold GL3Theta.th0 U1
    refine Differentiable.div_const (Differentiable.mul (hdiff.comp (differentiable_id.add_const _)) ?_) _
    fun_prop
  obtain ⟨m, n, hm, hn, hpar⟩ := even_im_hermitian_sub Λ w₁ w₂ hi hΛ hsd (w0 D) (4 * k + 2) ⟨2 * k + 1, by ring⟩
    (by
      unfold w0
      push_cast
      linear_combination (((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 / 4) * Complex.I_mul_I - (1 / 4) * hsq)
    (fun w hw => ha ▸ hst a w hw) t0 ht.1 ht.2.1
    (by
      have := ht.2.2
      convert this using 3
      unfold w0; ring) ω hω
  refine ⟨m, ?_, fun z => ?_⟩
  · rw [← hm, q1, gl3FieldFirst, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, w0]
    rw [mul_comm ((1 + _) / 2 : ℂ), Complex.im_ofReal_mul]
    simp
    ring
  · have e1 : U1 Λ ω (GL3Theta.th0 Λ t0) z = U1 Λ ω (U1 Λ t0 (sgStar Λ)) z / U1 Λ t0 (sgStar Λ) 0 := by
      conv_lhs => rw [U1]
      conv_rhs => rw [U1]
      simp only [GL3Theta.th0]
      ring
    have e2 : U1 Λ t0 (U1 Λ ω (sgStar Λ)) z = (if ω / 2 ∈ Λ then 1 else -1) * U1 Λ t0 (sgStar Λ) z := by
      conv_lhs => rw [U1]
      rw [hlaw ω hω, mul_assoc]
      rfl
    have e3 : Complex.exp (-(Real.pi : ℂ) * Complex.I * ((n : ℝ) : ℂ)) = (-1) ^ n := by
      rw [show -(Real.pi : ℂ) * Complex.I * ((n : ℝ) : ℂ) = (n : ℂ) * (-(Real.pi * Complex.I)) by push_cast; ring,
        Complex.exp_int_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num
    have e4 : (-1 : ℂ) ^ m * (-1) ^ n * (if ω / 2 ∈ Λ then 1 else -1) = 1 := by
      rw [← zpow_add₀ (by norm_num)]
      split_ifs with h
      · rw [(hpar.2 h).neg_one_zpow]; simp
      · rw [(Int.not_even_iff_odd.1 (mt hpar.1 h)).neg_one_zpow]; simp
    rw [e1, exists_orthonormal_basis_family, hn, e2, e3]
    simp only [GL3Theta.th0]
    linear_combination (U1 Λ t0 (sgStar Λ) z / U1 Λ t0 (sgStar Λ) 0) * e4

end GlobalTheory.HalfPeriodTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImConjMulEqIntMulArea
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.TransInv

theorem im_conj_mul_ne_zero {w₁ w₂ : ℂ} (h : LinearIndependent ℝ ![w₁, w₂]) :
    ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 := by
  intro h0
  rw [LinearIndependent.pair_iff] at h
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at h0
  have h1 := h w₂.im (-w₁.im) (by
    apply Complex.ext <;> simp <;> linarith)
  have h2 := h w₂.re (-w₁.re) (by
    apply Complex.ext <;> simp <;> linarith)
  have h3 := h 1 0 (by
    apply Complex.ext <;> simp <;> linarith [h1.2, h2.2])
  exact one_ne_zero h3.1

theorem im_conj_mul_mem {w₁ w₂ u v : ℂ} (hu : u ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ))
    (hv : v ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ)) :
    ∃ k : ℤ, ((starRingEnd ℂ) u * v).im = k * ((starRingEnd ℂ) w₁ * w₂).im := by
  obtain ⟨a, b, rfl⟩ := AddSubgroup.mem_closure_pair.1 hu
  obtain ⟨c, d, rfl⟩ := AddSubgroup.mem_closure_pair.1 hv
  refine ⟨a * d - b * c, ?_⟩
  simp
  ring

theorem area_closure_pair {w₁ w₂ : ℂ} (h : LinearIndependent ℝ ![w₁, w₂]) :
    area (AddSubgroup.closure ({w₁, w₂} : Set ℂ)) = |((starRingEnd ℂ) w₁ * w₂).im| := by
  have h0 := im_conj_mul_ne_zero h
  unfold area
  apply IsLeast.csInf_eq
  refine ⟨⟨abs_pos.2 h0, w₁, AddSubgroup.subset_closure (by simp), w₂,
    AddSubgroup.subset_closure (by simp), rfl⟩, ?_⟩
  rintro a ⟨ha, u, hu, v, hv, rfl⟩
  obtain ⟨k, hk⟩ := im_conj_mul_mem hu hv
  rw [hk] at ha ⊢
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at ha
  have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
  rw [abs_mul]
  nlinarith [abs_nonneg ((starRingEnd ℂ) w₁ * w₂).im]

end GlobalTheory.TransInv
end

