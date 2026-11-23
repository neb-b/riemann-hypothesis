module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.HasSumLocallyUniformlyWeierstrassZetaExcept
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsTrSelf
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeGal

namespace GlobalTheory.WpFam

def Tr {K : Type} [Field K] [NumberField K] (t : (Af K)ˣ) (x x' : K) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x) v) ≤ 1

structure IsTr {K : Type} [Field K] (ι : K →+* ℂ) (Λ₀ Λ₁ : PeriodPair) (T : K → K → Prop) : Prop where

  sub : ∀ x x' y y', T x x' → T y y' → T (x - y) (x' - y')

  mem_iff : ∀ x x', T x x' → (ι x ∈ Λ₀.lattice ↔ ι x' ∈ Λ₁.lattice)

  triv : ∀ x x', ι x ∈ Λ₀.lattice → ι x' ∈ Λ₁.lattice → T x x'

  left : ∀ x, ∃ x', T x x'

  right : ∀ x', ∃ x, T x x'

  rat₀ : ∀ z ∈ Λ₀.lattice, ∃ k, ι k = z

  rat₁ : ∀ z ∈ Λ₁.lattice, ∃ k, ι k = z

end GlobalTheory.WpFam
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.MemPass
section
set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.CMVal

namespace GlobalTheory.RoadE

variable {E : Type} [Field E] [NumberField E]

def ptE (t : E) (x : Fin 2 → maximalRealSubfield E) : E := ((x 0 : maximalRealSubfield E) : E) * t + ((x 1 : maximalRealSubfield E) : E)

theorem ptE_smul (t : E) (a : OF E) (x : Fin 2 → maximalRealSubfield E) :
    ptE t (a • x) = algebraMap (OF E) E a * ptE t x := by
  simp only [ptE, Pi.smul_apply]
  rw [Algebra.smul_def, Algebra.smul_def]
  push_cast
  have h : (((algebraMap (OF E) (maximalRealSubfield E) a) : maximalRealSubfield E) : E) = algebraMap (OF E) E a := rfl
  rw [h]; ring

end GlobalTheory.RoadE
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransportPrinc
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (betaBound_vp c_vp cE_vp a0 n_vp)
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (IsConjWt upIdele IsInvIdealOf IsLatOf)
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

namespace GlobalTheory.LatVal.Model

variable {K : Type} [Field K] [NumberField K]

theorem exists_isLatOf (d : ℕ) (δ : K) (ι : K →+* ℂ) (h2 : Module.finrank ℚ K = 2) (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) :
    ∃ Λ : PeriodPair, IsLatOf ι 1 Λ := by
  have hc : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = Fintype.card (Fin 2) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, h2]; simp
  let e := Fintype.equivOfCardEq hc
  let b := (RingOfIntegers.basis K).reindex e
  let B := (integralBasis K).reindex e
  have hB : ∀ i, B i = algebraMap (𝓞 K) K (b i) := fun i => by simp [B, b]
  have hrep : ∀ x : K, ∃ p q : ℚ, ι x = p * ι (B 0) + q * ι (B 1) := fun x => by
    refine ⟨B.repr x 0, B.repr x 1, ?_⟩
    conv_lhs => rw [← B.sum_repr x]
    simp [Fin.sum_univ_two, Rat.smul_def]
  have hδ' : ι δ ^ 2 = -(d : ℂ) := by rw [← map_pow, hδ]; simp
  have hind : LinearIndependent ℝ ![ι (B 0), ι (B 1)] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    simp only [Complex.real_smul] at h
    obtain ⟨p, q, h1⟩ := hrep 1
    obtain ⟨p', q', h3⟩ := hrep δ
    rw [map_one] at h1
    have key : ∀ u w : ℝ, (u : ℂ) * ι δ = w → u = 0 := fun u w huw => by
      have : ((u : ℂ) * ι δ) ^ 2 = (w : ℂ) ^ 2 := by rw [huw]
      rw [mul_pow, hδ'] at this
      have h' : u ^ 2 * (-(d : ℝ)) = w ^ 2 := by exact_mod_cast this
      have hd' : (0 : ℝ) < d := by exact_mod_cast hd
      have : u ^ 2 ≤ 0 := by nlinarith [sq_nonneg w, sq_nonneg u]
      exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm this (sq_nonneg u))
    have k1 := key (s * q - t * p) (s * q' - t * p') (by
      push_cast
      have : ((s : ℂ) * q' - t * p') = ((s : ℂ) * q' - t * p') * 1 := by ring
      rw [this, h1, h3]
      linear_combination (q * p' - p * q' : ℂ) * h)
    have k1' : (s : ℂ) * q - t * p = 0 := by exact_mod_cast k1
    have hb0 : ι (B 0) ≠ 0 := by simpa using B.ne_zero 0
    have hb1 : ι (B 1) ≠ 0 := by simpa using B.ne_zero 1
    have hs : (s : ℂ) = 0 := by linear_combination (s : ℂ) * h1 + (p : ℂ) * h + ι (B 1) * k1'
    have ht : (t : ℂ) = 0 := by linear_combination (t : ℂ) * h1 + (q : ℂ) * h - ι (B 0) * k1'
    exact ⟨by exact_mod_cast hs, by exact_mod_cast ht⟩
  refine ⟨⟨ι (B 0), ι (B 1), hind⟩, ?_⟩
  ext z
  simp only [SetLike.mem_coe, PeriodPair.mem_lattice, Set.mem_image, FractionalIdeal.mem_coe, FractionalIdeal.mem_one_iff]
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨_, ⟨m * b 0 + n * b 1, rfl⟩, by simp [hB]⟩
  · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
    refine ⟨b.repr r 0, b.repr r 1, ?_⟩
    conv_rhs => rw [← b.sum_repr r]
    simp [Fin.sum_univ_two, hB]

end GlobalTheory.LatVal.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
section
set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace GlobalTheory

namespace PDivGroup

open PDiv

variable {p : ℕ} {k : Type} [CommRing k]

def IsConn (G : PDivGroup p k) : Prop := ∀ n, ∀ a ∈ augIdeal k (G.A n), IsNilpotent a

def IsEt (G : PDivGroup p k) : Prop := ∀ n, IsReduced (G.A n)

end PDivGroup

end GlobalTheory
end
end

