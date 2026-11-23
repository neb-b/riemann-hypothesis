module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.PolarLatticePairs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0234
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0218
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0225
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0238

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdelicHermitianCharacterPairingProperties
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.GamAlg

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [D.host.toHostAx.conjE_apply, D.host.toHostAx.conjE_apply]
  simp

theorem sgA_sgA (D : D7) (y : AE D) : sgA D (sgA D y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sgA, Formalism.UG.sigR, conj_conj]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem sum_eq_trace {R : Type} [CommRing R] (s : R →+* R) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) R) :
    ∑ i, ∑ j, x i j * s (y i j) = Matrix.trace (x * (y.map s).transpose) := by
  simp [Matrix.trace, Matrix.mul_apply]

theorem trace_inv {R : Type} [CommRing R] (s : R →+* R) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) R)
    (p : Matrix (Fin a) (Fin a) R) (q : Matrix (Fin b) (Fin b) R)
    (hp : (p.map s).transpose * p = 1) (hq : (q.map s).transpose * q = 1) :
    Matrix.trace (p * x * q * ((p * y * q).map s).transpose) = Matrix.trace (x * (y.map s).transpose) := by
  have hq' : q * (q.map s).transpose = 1 := mul_eq_one_comm.1 hq
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul]
  have h : p * x * q * ((q.map s).transpose * ((y.map s).transpose * (p.map s).transpose)) =
      p * (x * (q * (q.map s).transpose) * (y.map s).transpose * (p.map s).transpose) := by
    simp only [Matrix.mul_assoc]
  rw [h, hq', Matrix.mul_one, Matrix.trace_mul_comm, Matrix.mul_assoc, hp, Matrix.mul_one]

end GlobalTheory.FinWeil.GamAlg


open GlobalTheory.FinWeil.GamAlg GlobalTheory.NormSum.PtsMem in
theorem GlobalTheory.FinWeil.gamA_alg : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ ψ : AE D → ℂ, IsPsi D cc δ ψ → ∀ (N N' : ℕ), (∀ u ζ η, gamA ψ (actA D N N' u ζ) (actA D N N' u η) = gamA ψ ζ η) ∧ (∀ ζ : XA D N N', gamA ψ ζ ζ = 1) ∧ (∀ (r : 𝓞 D.host.E) (ζ η : XA D N N'), gamA ψ (r • ζ) η = gamA ψ ζ (sgO D r • η)) ∧ (∀ ζ η ξ : XA D N N', gamA ψ (ζ + η) ξ = gamA ψ ζ ξ * gamA ψ η ξ) ∧ (∀ ζ η ξ : XA D N N', gamA ψ ζ (η + ξ) = gamA ψ ζ η * gamA ψ ζ ξ) := by
  intro D _ cc δ _ ψ hψ N N'
  obtain ⟨hadd, -, -, hsg, -⟩ := hψ
  refine ⟨?_, fun ζ => ?_, fun r ζ η => ?_, fun ζ η ξ => ?_, fun ζ η ξ => ?_⟩
  · rintro ⟨g, g'⟩ ζ η
    unfold gamA
    rw [sum_eq_trace, sum_eq_trace, actA_apply, actA_apply,
      trace_inv _ _ _ _ _ ((mem_GA D _).1 g'.2) ((mem_GA D _).1 (inv_mem g.2))]
  · unfold gamA
    set t := ∑ i, ∑ j, ζ i j * sgA D (ζ i j) with ht
    have h1 : sgA D t = t := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [ht, map_sum, map_mul, sgA_sgA]
      simp only [mul_comm]
    have h2 : t = inc D (1 / 2) * t + sgA D (inc D (1 / 2) * t) := by
      rw [map_mul, sgA_inc, h1, ← add_mul, ← map_add (f := _), map_div₀, map_one, map_ofNat, add_halves, map_one, one_mul]
    rw [h2]
    exact hsg _
  · unfold gamA
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.smul_apply, Matrix.smul_apply, smul_AE, smul_AE, map_mul, sgA_inc, coe_sgO, conj_conj]
    ring
  · unfold gamA
    rw [← hadd]
    simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]
  · unfold gamA
    rw [← hadd]
    simp only [Matrix.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleAtOfIrreducibleTame
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.WdCocycle

section General

variable {D : D7} {T : Tor D} {N N' : ℕ}

theorem hf_add_left (x y z : VC D N N') : Hf D T (x + y) z = Hf D T x z + Hf D T y z := by
  simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]

theorem hf_add_right (x y z : VC D N N') : Hf D T x (y + z) = Hf D T x y + Hf D T x z := by
  simp only [Hf, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib, add_div]

theorem hf_conj (x z : VC D N N') : Hf D T z x = (starRingEnd ℂ) (Hf D T x z) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  congr 1
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem wd_wd (x y : VC D N N') (F : VC D N N' → ℂ) :
    Wd D T x (Wd D T y F) = ee (-(w0 D * Hf D T x y).im) • Wd D T (x + y) F := by
  funext z
  have h1 : Hf D T x y = ((Hf D T x y).re : ℂ) + ((Hf D T x y).im : ℂ) * Complex.I := (Complex.re_add_im _).symm
  have h2 : Hf D T y x = ((Hf D T x y).re : ℂ) - ((Hf D T x y).im : ℂ) * Complex.I := by
    rw [hf_conj x y]
    apply Complex.ext <;> simp
  have h3 : (Hf D T y x).re = (Hf D T x y).re := by
    rw [hf_conj x y, Complex.conj_re]
  have h4 : (w0 D * Hf D T x y).im = ((Hf D T x y).im + Real.sqrt D.host.d * (Hf D T x y).re) / 2 := by
    have : w0 D = ((1 / 2 : ℝ) : ℂ) + ((Real.sqrt D.host.d / 2 : ℝ) : ℂ) * Complex.I := by
      rw [w0]; push_cast; ring
    rw [this]
    simp only [Complex.mul_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have key : ee (qH D T x / 2) * ee (qH D T y / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T (z + x) y - (Real.pi : ℂ) * Hf D T y y / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z x - (Real.pi : ℂ) * Hf D T x x / 2) =
      ee (-(w0 D * Hf D T x y).im) * ee (qH D T (x + y) / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z (x + y) - (Real.pi : ℂ) * Hf D T (x + y) (x + y) / 2) := by
    simp only [ee, ← Complex.exp_add, qH]
    congr 1
    rw [h4]
    simp only [hf_add_left, hf_add_right, Complex.add_re, h3]
    rw [h2]
    generalize (Hf D T x y).re = a at h1 ⊢
    generalize (Hf D T x y).im = b at h1 ⊢
    rw [h1]
    push_cast
    ring
  simp only [Wd, U, wdPh, Pi.smul_apply, smul_eq_mul]
  rw [add_assoc z x y]
  linear_combination F (z + (x + y)) * key

end General

variable {D : D7}

theorem emb_conj (φ : D.host.E →+* ℂ) (x : D.host.E) : φ (D.host.conj x) = starRingEnd ℂ (φ x) :=
  D.host.conjE_apply φ x

theorem hf_pt (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (z y : Matrix (Fin N') (Fin N) D.host.E) :
    Hf D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (pt D (tor0 D cc δ) δ y) =
      ((‖δ‖ ^ 2 / area (lamOf D cc δ) : ℝ) : ℂ) * ∑ τ, embT D τ (∑ i, ∑ j, z i j * D.host.conj (y i j)) := by
  have h : δ * starRingEnd ℂ δ = (‖δ‖ : ℂ) ^ 2 := Complex.mul_conj' δ
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Hf, pt, embV, tor0, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, emb_conj]
  push_cast
  rw [← h, div_mul_eq_mul_div]
  congr 1
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem pt_add (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (z y : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (z + y) = pt D (tor0 D cc δ) δ z + pt D (tor0 D cc δ) δ y := by
  funext τ i j
  simp only [pt, embV, tor0, Pi.smul_apply, Pi.add_apply, Matrix.add_apply, smul_eq_mul, map_add (f := _), mul_add]

theorem wd_cocycle : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∃ w : 𝓞 D.host.E, w + sgO D w = 1 ∧ ∀ (N N' : ℕ) (z y : Matrix (Fin N') (Fin N) D.host.E), ee (-(Hf D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (pt D (tor0 D cc δ) δ y)).im) = psi0 D cc δ (∑ i, ∑ j, z i j * D.host.conj (y i j)) ∧ pt D (tor0 D cc δ) δ (z + y) = pt D (tor0 D cc δ) δ z + pt D (tor0 D cc δ) δ y ∧ ∀ F, Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ y) F) = psi0 D cc δ (∑ i, ∑ j, (w : D.host.E) * z i j * D.host.conj (y i j)) • Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z + y)) F := by
  intro D hg cc δ _
  obtain ⟨a, ha⟩ := exists_integer_map_eq_w0 D
  let w : 𝓞 D.host.E := algebraMap (𝓞 D.host.K) (𝓞 D.host.E) a
  have hw : (w : D.host.E) = ((a : D.host.K) : D.host.E) := rfl
  have hτ : ∀ τ, embT D τ (w : D.host.E) = w0 D := fun τ => by
    rw [hw, ← ha]
    exact hg.1 τ _
  refine ⟨w, ?_, fun N N' z y => ⟨?_, pt_add cc δ z y, fun F => ?_⟩⟩
  · apply RingOfIntegers.ext
    apply D.host.φ₀.injective
    change D.host.φ₀ ((w : D.host.E) + D.host.conj (w : D.host.E)) = D.host.φ₀ 1
    rw [map_add (f := _), emb_conj, hw, ha, map_one, w0]
    simp only [map_div₀, map_add (f := _), map_mul, map_one, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    ring
  · rw [hf_pt, psi0, Complex.im_ofReal_mul]
  · rw [wd_wd, pt_add, hf_pt, psi0]
    congr 3
    rw [mul_left_comm, Complex.im_ofReal_mul, Finset.mul_sum]
    congr 2
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← hτ τ, ← map_mul]
    simp only [Finset.mul_sum, mul_assoc]

end GlobalTheory.FinWeil.WdCocycle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicTaylorTorsionTranslateEvenTheta
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.EvenThetaTorsion

variable {Λ : AddSubgroup ℂ}

def phase (Λ : AddSubgroup ℂ) (x y : ℂ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * (y * (starRingEnd ℂ) x - x * (starRingEnd ℂ) y) / (2 * (area Λ : ℂ)))

theorem phase_ne_zero (x y : ℂ) : phase Λ x y ≠ 0 := Complex.exp_ne_zero _

theorem thetaTranslate_comp_eq_phase_mul_add (x y : ℂ) (G : ℂ → ℂ) (z : ℂ) :
    U1 Λ x (U1 Λ y G) z = phase Λ x y * U1 Λ (x + y) G z := by
  simp only [U1, phase]
  rw [mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add, add_assoc]
  congr 2
  simp only [map_add (f := _)]
  ring

theorem rationalLatticePoint_add {x y : ℂ} (hx : InRationalLattice Λ x) (hy : InRationalLattice Λ y) : InRationalLattice Λ (x + y) := by
  obtain ⟨m, hm, hx⟩ := hx
  obtain ⟨n, hn, hy⟩ := hy
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  have := Λ.add_mem (Λ.nsmul_mem hx n) (Λ.nsmul_mem hy m)
  convert this using 1
  simp only [nsmul_eq_mul]
  push_cast
  ring

theorem rationalLatticePoint_of_mem_lattice {x : ℂ} (hx : x ∈ Λ) : InRationalLattice Λ x := ⟨1, one_pos, by simpa using hx⟩

theorem phase_mem (h : IsLat Λ) {x y : ℂ} (hx : InRationalLattice Λ x) (hy : InRationalLattice Λ y) :
    phase Λ x y ∈ Qbar := by
  obtain ⟨m, hm, hx⟩ := hx
  obtain ⟨n, hn, hy⟩ := hy
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  obtain ⟨k, hk⟩ := GlobalTheory.exists_int_im_latticeForm L ((hL _).1 hy) ((hL _).1 hx)
  have hA := GlobalTheory.latticeArea_pos L
  rw [GlobalTheory.latticeForm, Complex.div_ofReal_im, div_eq_iff hA.ne', ← GlobalTheory.OddTheta.area_eq L Λ hL] at hk
  rw [← GlobalTheory.OddTheta.area_eq L Λ hL] at hA
  have hA' : (area Λ : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have e := Complex.sub_conj ((n : ℂ) * y * (starRingEnd ℂ) ((m : ℂ) * x))
  rw [hk] at e
  simp only [map_mul, map_natCast, Complex.conj_conj] at e
  push_cast at e
  have hp : phase Λ x y ^ (2 * m * n) = 1 := by
    rw [phase, ← Complex.exp_nat_mul, ← Complex.exp_int_mul_two_pi_mul_I k]
    congr 1
    push_cast
    field_simp
    linear_combination e
  rw [mem_algebraicClosure_iff]
  refine IsAlgebraic.of_pow (n := 2 * m * n) (by positivity) ?_
  rw [hp]
  exact isAlgebraic_one

theorem algEnt_const_mul {F : ℂ → ℂ} (hF : AlgEnt F) {κ : ℂ} (hκ : κ ∈ Qbar) :
    AlgEnt fun z => κ * F z := by
  refine ⟨hF.1.const_mul κ, fun n => ?_⟩
  have : coef1 (fun z => κ * F z) n = κ * coef1 F n := by
    rw [coef1, coef1, iteratedDeriv_const_mul_field, mul_div_assoc]
  rw [this]
  exact Qbar.mul_mem hκ (hF.2 n)

theorem thetaTranslate_evenTheta_eq_sigmaStar_translate (t x z : ℂ) : U1 Λ x (GL3Theta.th0 Λ t) z =
    (phase Λ x t / U1 Λ t (sgStar Λ) 0) * U1 Λ (x + t) (sgStar Λ) z := by
  rw [div_mul_eq_mul_div, ← thetaTranslate_comp_eq_phase_mul_add]
  simp only [U1, GL3Theta.th0]
  ring

theorem sigmaStarTranslate_add_lattice_sign_phase (h : IsLat Λ) {ω : ℂ} (hω : ω ∈ Λ) (y z : ℂ) :
    U1 Λ (y + ω) (sgStar Λ) z =
      ((if ω / 2 ∈ Λ then 1 else -1) / phase Λ y ω) * U1 Λ y (sgStar Λ) z := by
  have e := thetaTranslate_comp_eq_phase_mul_add (Λ := Λ) y ω (sgStar Λ) z
  rw [funext (h.sg_law hω)] at e
  rw [div_mul_eq_mul_div, eq_div_iff (phase_ne_zero _ _), mul_comm, ← e]
  simp only [U1]
  ring

theorem algebraicTaylor_torsionTranslate_evenTheta_alt : ∀ Λ : AddSubgroup ℂ, IsLat Λ → (∀ x, InRationalLattice Λ x → AlgEnt (U1 Λ x (sgStar Λ))) → ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → ∀ x, InRationalLattice Λ x → AlgEnt (U1 Λ x (GL3Theta.th0 Λ t₀)) ∧ ∀ ω ∈ Λ, ∃ κ ∈ Qbar, κ ≠ 0 ∧ ∀ z, U1 Λ (x + ω) (GL3Theta.th0 Λ t₀) z = κ * U1 Λ x (GL3Theta.th0 Λ t₀) z := by
  intro Λ h halg t _ h2 x hx
  have ht : InRationalLattice Λ t := ⟨2, two_pos, by simpa using h2⟩
  have hc : U1 Λ t (sgStar Λ) 0 ∈ Qbar := by
    simpa [coef1] using (halg t ht).2 0
  refine ⟨?_, fun ω hω => ?_⟩
  · rw [funext (thetaTranslate_evenTheta_eq_sigmaStar_translate t x)]
    exact algEnt_const_mul (halg _ (rationalLatticePoint_add hx ht)) (Qbar.div_mem (phase_mem h hx ht) hc)
  · have hω' := rationalLatticePoint_of_mem_lattice hω
    have hs : (if ω / 2 ∈ Λ then 1 else -1 : ℂ) ∈ Qbar := by
      split_ifs
      · exact Qbar.one_mem
      · exact Qbar.neg_mem Qbar.one_mem
    have hs0 : (if ω / 2 ∈ Λ then 1 else -1 : ℂ) ≠ 0 := by
      split_ifs <;> norm_num
    refine ⟨phase Λ (x + ω) t / phase Λ x t * ((if ω / 2 ∈ Λ then 1 else -1) / phase Λ (x + t) ω),
      Qbar.mul_mem (Qbar.div_mem (phase_mem h (rationalLatticePoint_add hx hω') ht) (phase_mem h hx ht))
        (Qbar.div_mem hs (phase_mem h (rationalLatticePoint_add hx ht) hω')),
      mul_ne_zero (div_ne_zero (phase_ne_zero _ _) (phase_ne_zero _ _))
        (div_ne_zero hs0 (phase_ne_zero _ _)), fun z => ?_⟩
    rw [thetaTranslate_evenTheta_eq_sigmaStar_translate, thetaTranslate_evenTheta_eq_sigmaStar_translate, add_right_comm, sigmaStarTranslate_add_lattice_sign_phase h hω]
    have := phase_ne_zero (Λ := Λ) x t
    generalize (if ω / 2 ∈ Λ then 1 else -1 : ℂ) / phase Λ (x + t) ω = s
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    generalize (U1 Λ t (sgStar Λ) 0)⁻¹ = c
    field_simp

end GlobalTheory.EvenThetaTorsion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardLatticeQuotIdeal
section
open NumberField IsDedekindDomain Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.IndefiniteRowSideFullHecke.PolarLatticePairs
open scoped Pointwise

noncomputable section

namespace GlobalTheory.MatrixLatticeIndex

theorem card_matIn (D : D7) (a d : ℕ) (A B : Submodule (𝓞 D.host.E) D.host.E) :
    Nat.card (matIn D a d A ⧸ (matIn D a d B).addSubgroupOf (matIn D a d A)) =
      (B.toAddSubgroup.relIndex A.toAddSubgroup) ^ (a * d) := by
  let Q := A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup
  let f : matIn D a d A →+ (Fin d → Fin a → Q) :=
    { toFun := fun z i j => QuotientAddGroup.mk (⟨z.1 i j, z.2 i j⟩ : A.toAddSubgroup)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : Function.Surjective f := by
    intro y
    refine ⟨⟨fun i j => ((y i j).out : A.toAddSubgroup), fun i j => (y i j).out.2⟩, ?_⟩
    funext i j
    exact QuotientAddGroup.out_eq' (y i j)
  have hker : f.ker = (matIn D a d B).addSubgroupOf (matIn D a d A) := by
    ext z
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
    constructor
    · intro h i j
      exact (QuotientAddGroup.eq_zero_iff _).1 (congrFun (congrFun h i) j)
    · intro h
      funext i j
      exact (QuotientAddGroup.eq_zero_iff _).2 (h i j)
  rw [← hker, Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hf).toEquiv,
    Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin a), Nat.card_eq_fintype_card (α := Fin d),
    Fintype.card_fin, Fintype.card_fin, ← pow_mul]
  rfl

theorem relIndex_smul {K : Type} [Field K] [NumberField K]
    (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hJ : J ≠ 0) (q : Ideal (𝓞 K)) (hq : q ≠ ⊥) :
    (q • (J : Submodule (𝓞 K) K)).toAddSubgroup.relIndex (J : Submodule (𝓞 K) K).toAddSubgroup =
      Ideal.absNorm q := by
  have hq' : (q : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 hq
  have hle : (q : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) * J ≤ J := by
    calc (q : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) * J ≤ 1 * J :=
          mul_le_mul' FractionalIdeal.coeIdeal_le_one le_rfl
      _ = J := one_mul J
  have h := Formalism.L2.LamCM.Dx.absNorm_eq_relIndex_mul J _ (mul_ne_zero hq' hJ) hle
  have he : (((q : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) * J :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) = q • (J : Submodule (𝓞 K) K) := by
    apply le_antisymm
    · rw [FractionalIdeal.coe_mul]
      refine Submodule.mul_le.2 fun x hx y hy => ?_
      obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem_smul hb hy
    · refine Submodule.smul_le.2 fun b hb y hy => ?_
      rw [Algebra.smul_def]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hb) hy
  rw [he, map_mul, FractionalIdeal.coeIdeal_absNorm] at h
  have h0 : FractionalIdeal.absNorm J ≠ 0 := fun h' => hJ (FractionalIdeal.absNorm_eq_zero_iff.1 h')
  exact_mod_cast (mul_right_cancel₀ h0 h).symm


open GlobalTheory.NormSum.MovedLattice in
theorem coefLat_eq (D : D7) (cc : Ideal (𝓞 D.host.K)) :
    coefLat D cc = ((ext D cc * D.host.AA0 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
      Submodule (𝓞 D.host.E) D.host.E) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro t ⟨c, hc, m, hm, rfl⟩
    exact FractionalIdeal.mul_mem_mul (mem_ext D hc) hm
  · rw [FractionalIdeal.coe_mul]
    refine Submodule.mul_le.2 fun x hx y hy => ?_
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
    clear hx
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨c, hc, rfl⟩ := hb
      exact Submodule.subset_span ⟨c, hc, y, hy, rfl⟩
    | zero => rw [map_zero, zero_mul]; exact zero_mem _
    | add b b' _ _ hb hb' => rw [map_add (f := _), add_mul]; exact add_mem hb hb'
    | smul r b _ hb =>
      rw [smul_eq_mul, map_mul, mul_assoc, ← Algebra.smul_def]
      exact Submodule.smul_mem _ r hb

end GlobalTheory.MatrixLatticeIndex

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualWeylEqEvalAtOneSmulExtremalOfRowWeightStatement
section
open GlobalTheory.DualWeyl MvPolynomial NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeyl_eq_evalAt_one_smul_extremal_of_rowWeight : ∀ (K : Type) [Field K] [Infinite K] (N : ℕ) (la : Fin N → ℕ), Antitone la → ∀ f ∈ nabla la K, IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW N N) f la → f = evalAt 1 f • extremal la K := by
  first | exact @GlobalTheory.DualWeyl.eq_evalAt_one_smul_extremal_of_rowWeight | exact GlobalTheory.DualWeyl.eq_evalAt_one_smul_extremal_of_rowWeight | (intros; apply GlobalTheory.DualWeyl.eq_evalAt_one_smul_extremal_of_rowWeight <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsComplexEndomorphismEqOnCountableStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complexEndomorphism_eq_on_countable : ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (S : Set ℂ), S.Countable → ∃ σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ, ∀ x ∈ S, x ∈ M → cj ⊤ σ x = cj M ρ x := by
  first | exact @GlobalTheory.GalTheta.exists_top_embedding_eq_on_countable | exact GlobalTheory.GalTheta.exists_top_embedding_eq_on_countable | (intros; apply GlobalTheory.GalTheta.exists_top_embedding_eq_on_countable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHomLatticeCommensurableOrthonormalStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homLattice_commensurable_orthonormal : ∀ (D : D7) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), OnB D b → SD D L → SD D L' → ∃ k : ℕ, 0 < k ∧ Comm D b k (YYl D L L' : Set (Matrix (Fin N') (Fin N) D.host.E)) := by
  first | exact @GlobalTheory.ThetaConj.exists_comm_YYl | exact GlobalTheory.ThetaConj.exists_comm_YYl | (intros; apply GlobalTheory.ThetaConj.exists_comm_YYl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOrthonormalBasisEigenOfInnerMap
section
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

noncomputable section

namespace GlobalTheory.UnitaryTheta

theorem exists_eigenbasis_of_isPosHerm {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Sesq V) (hH : IsPosHerm H) (a : V →ₗ[ℂ] V) (ha : ∀ z w, H (a z) (a w) = H z w) :
    ∃ (n : ℕ) (e : Module.Basis (Fin n) ℂ V) (l : Fin n → ℂ),
      (∀ i j, H (e i) (e j) = if i = j then 1 else 0) ∧ ∀ i, ‖l i‖ = 1 ∧ a (e i) = l i • e i := by
  first
  | exact @_root_.GlobalTheory.OrthonormalEigenbasis.exists_orthonormal_eigenbasis
  | exact _root_.GlobalTheory.OrthonormalEigenbasis.exists_orthonormal_eigenbasis
  | (apply _root_.GlobalTheory.OrthonormalEigenbasis.exists_orthonormal_eigenbasis <;> assumption)
  | (intros; apply _root_.GlobalTheory.OrthonormalEigenbasis.exists_orthonormal_eigenbasis <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OrthonormalEigenbasis.exists_orthonormal_eigenbasis <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OrthonormalEigenbasis.exists_orthonormal_eigenbasis ..)

theorem unitary_exists_orthonormal_eigenbasis :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V), IsPosHerm H →
      ∀ a : V ≃ₗ[ℂ] V, (∀ z w, H (a z) (a w) = H z w) →
        ∃ (n : ℕ) (e : Module.Basis (Fin n) ℂ V) (l : Fin n → ℂ),
          (∀ i j, H (e i) (e j) = if i = j then 1 else 0) ∧ ∀ i, ‖l i‖ = 1 ∧ a (e i) = l i • e i :=
  fun _ _ _ _ H hH a ha => exists_eigenbasis_of_isPosHerm H hH a.toLinearMap ha

end GlobalTheory.UnitaryTheta
end
end

