module

public import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalRingCardinality.SpanPowerMembership.GatTies
public import Formalism.SharpRestriction.InertJacobiLevels.ExtraGat
public import Formalism.SharpRestriction.InertJacobiLevels.Bundle0002
public import Formalism.CyclotomicNorms.IrreducibilityOfGoodTuple

@[expose] public section

-- bundled from Formalism.SharpRestriction.InertJacobiLevels.ExtraGatC
section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LevelValuationRings Formalism.MainNotions.G Formalism.FrobeniusOrbits NumberField

theorem two_ne_Kn (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) (n : ℕ) : (2 : Kn p n) ≠ 0 := by
  intro h
  have h1 : ((algebraMap (On p n) (Kn p n)).comp (algebraMap (Wn p n) (On p n))) 2 =
      ((algebraMap (On p n) (Kn p n)).comp (algebraMap (Wn p n) (On p n))) 0 := by
    rw [map_ofNat, map_zero, h]
  have h2 : (2 : Wn p n) = 0 := inj_WK p n h1
  have h3 : ((2 : ℕ) : GaloisField p n) = 0 := by
    have := congrArg (WittVector.constantCoeff (p := p) (R := GaloisField p n)) h2
    rw [map_ofNat, map_zero] at this
    exact_mod_cast this
  have h4 := (CharP.cast_eq_zero_iff (GaloisField p n) p 2).1 h3
  have := Nat.le_of_dvd (by norm_num) h4
  omega

section One

variable {R : Ranks} {H : Host R} {p : ℕ}

def gatOfC (S : Served H p) (T : Set ↥(R.Psi)) (r : ℕ) (lam : ↥(R.Psi) → DomWeight (R.N 0))
    (comp : Type) [Fintype comp] (e : ℕ) : GAtP p :=
  haveI : Fact p.Prime := ⟨S.prime⟩
  { O := On p (orderOf (gPsi S))
    Kf := Kn p (orderOf (gPsi S))
    P := placesOf S T r lam
    comp := comp
    lev := fun _ => levAll _
    e := e }

theorem gatOfC_M (S : Served H p) (T : Set ↥(R.Psi)) (r : ℕ) (lam : ↥(R.Psi) → DomWeight (R.N 0))
    (comp : Type) [Fintype comp] (e : ℕ) : (gatOfC S T r lam comp e).M = ⊥ :=
  haveI : Fact p.Prime := ⟨S.prime⟩
  gat_M_bot _ fun _ => levAll_M _ (two_ne_Kn p S.five_le _)

end One

variable (D : D7) (h0 : ∀ u, Module.finrank ℂ (D.mem u).A.Mu0 = 0)
  (rOf : D.what₂.Word → ℕ → ℕ) (eOf : ℕ → ℕ) (bs : D.what₂.Word → ℕ → Set ↥(D.R.Psi))

def withGatC : D7 :=
  { D with
    gat := fun u w h => gatOfC (served_of h) (bs u (D.what₂.places.resChar w))
      (rOf u (D.what₂.places.resChar w)) (fun ψ => (D.fm u).lam 0 (D.eTau.symm ψ)) ((D.mem u).C.cls 0)
      (eOf (D.what₂.places.resChar w))
    gat_d := fun u _ _ => (gat_d_zero _ (gatOfC_M _ _ _ _ _ _)).trans (h0 u).symm }

def gatTiesC : GatTies (withGatC D h0 rOf eOf bs) where
  gat_k := fun _ _ _ => k_pos D.R
  gat_n := fun _ _ h _ P hP hL σ hσ => @orderOf_frobenius_image_eq _ D.host _ (served_of h) P hP hL σ hσ
  gat_pos := fun u w h => (posPsi (served_of h) (bs u (D.what₂.places.resChar w))).trans D.eTau.symm
  gat_step := fun u w h v s P hP hL σ hσ =>
    @position_succ_eq_mul_frobenius _ D.host _ (served_of h) (bs u (D.what₂.places.resChar w)) _ D.eTau v s P hP hL σ hσ
  gat_lam := fun _ _ _ _ _ _ => rfl

variable (B : D.what₂.Word → ℕ → Set (HH D))

variable (u : D.what₂.Word) (w : D.what₂.places.Pl)
  (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))

end Formalism.MainNotions.Inhab

end
end

-- bundled from Formalism.SharpRestriction.InertJacobiLevels.TwoPrimeFieldMemLevelOfCoprime
section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition NumberField IsDedekindDomain
open scoped Pointwise

section General

variable {R : Ranks} (H : Host R)

theorem primesOver_ncard (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime) :
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = (placesOver E p).ncard := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  have hpM : (Ideal.span {(p : ℤ)}).IsMaximal :=
    hpI.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpZ.ne_zero)
  have himg : (fun v : HeightOneSpectrum (𝓞 E) => v.asIdeal) '' placesOver E p =
      (Ideal.span {(p : ℤ)}).primesOver (𝓞 E) := by
    ext I
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨v.isPrime, ⟨?_⟩⟩
      have hle : Ideal.span {(p : ℤ)} ≤ v.asIdeal.under ℤ := by
        rw [Ideal.span_le, Set.singleton_subset_iff]
        change algebraMap ℤ (𝓞 E) p ∈ v.asIdeal
        have hv' : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal := hv
        simpa using hv'
      exact hpM.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top hle
    · rintro ⟨hI, hIl⟩
      have hmem : ((p : ℕ) : 𝓞 E) ∈ I := by
        have : (p : ℤ) ∈ I.under ℤ := by rw [← hIl.over]; exact Ideal.mem_span_singleton_self _
        simpa using this
      have hne : I ≠ ⊥ := by
        rintro rfl
        have h0 : ((p : ℕ) : 𝓞 E) = 0 := by simpa using hmem
        exact hp.ne_zero (by exact_mod_cast h0)
      exact ⟨⟨I, hI, hne⟩, hmem, rfl⟩
  rw [← himg, Set.ncard_image_of_injective _ (fun v w h => HeightOneSpectrum.ext h)]

end General

def Yof (R : Ranks) (x eps : ℝ) : ℝ := ((R.k : ℝ) * Real.exp (x ^ eps)) ^ 8

structure Fld (R : Ranks) (x eps : ℝ) extends Formalism.HC.HostAx R.toFrame where
  flPS : toHostRaw.PsQ
  sqq : E
  sqq_sq : sqq ^ 2 = -(q : E)
  gal_sqq : ∀ σ : E ≃ₐ[ℚ] E, σ sqq = ((((gal σ).1.1 : ℤˣ) : ℤ) : E) * sqq
  QS_exact : toHostRaw.Exact
  QS_le : QS ≤ R.n ^ 2
  o_pow : R.toFrame.o ^ 64 ≤ 2 ^ R.e
  small_le : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ QS → 4 * l ≤ ⌊x ^ (eps / 5)⌋₊
  good : QDGood x eps q d
  o_tie : (R.o : ℝ) ≤ x ^ (eps / 1000)
  QS_tie : (QS : ℝ) ≤ 4 * R.n * x ^ (eps / 1000)

structure Base (R : Ranks) (x eps Cp CT : ℝ) extends Fld R x eps where
  q_big : 4 * R.t * R.r + 1 < q
  d_big : 4 * R.t * R.r + 1 < d
  g0 : ℕ
  g1 : ℕ
  first_prime_isPrime : g0.Prime
  second_prime_isPrime : g1.Prime
  g_ne : g0 ≠ g1
  first_prime_in_window : Yof R x eps ≤ g0 ∧ (g0 : ℝ) ≤ 2 * Yof R x eps
  second_prime_in_window : Yof R x eps ≤ g1 ∧ (g1 : ℝ) ≤ 2 * Yof R x eps
  first_prime_norm_form : ∃ u v : ℤ, (g0 : ℤ) = (1 + (QS * q * d : ℕ) * u) ^ 2 + d * ((QS * q * d : ℕ) * v) ^ 2
  second_prime_norm_form : ∃ u v : ℤ, (g1 : ℤ) = (1 + (QS * q * d : ℕ) * u) ^ 2 + d * ((QS * q * d : ℕ) * v) ^ 2
  bb : Disjoint (Formalism.CyclotomicNorms.BB R.r g0) (Formalism.CyclotomicNorms.BB R.r g1)
  pde : ℕ
  pde' : ℕ
  pde_prime : pde.Prime
  pde'_prime : pde'.Prime
  pde_ne : pde ≠ pde'
  pde_mod : pde ≡ 1 [MOD 15 * (QS * q * d)]
  pde'_mod : pde' ≡ 1 [MOD 15 * (QS * q * d)]
  pde_ne_g : pde ≠ g0 ∧ pde ≠ g1 ∧ pde' ≠ g0 ∧ pde' ≠ g1
  pde_log : Real.log pde < x ^ (eps / 3) ∧ Real.log pde' < x ^ (eps / 3)
  Cp_pos : 0 < Cp
  Lw : ℕ
  two_le_Lw : 2 ≤ Lw
  T2 : Finset ℕ
  second_set_range : ∀ s ∈ T2, 4 * Lw * s < R.n0
  second_set_no_relation : NoRel T2 Lw
  T2_card : (R.n0 : ℝ) * Real.exp (-(CT * Real.sqrt (Real.log (R.n0 : ℝ) * Real.log Lw))) / Lw ≤ T2.card
  TT : Finset (R.A)

variable {R : Ranks} {x eps Cp CT : ℝ} (B : Base R x eps Cp CT)

namespace Base

end Base

end Formalism.MainNotions.Inhab

end
end

