module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MkLeContinuumOfDenseRange
section
set_option autoImplicit false

open Cardinal

namespace GlobalTheory.PadicComplexIso

theorem exists_ringEquiv_over (R K L : Type) [Field R] [Field K] [Field L] [IsAlgClosed K]
    [IsAlgClosed L] [Algebra R K] [Algebra R L] (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K) (hKL : #K = #L) :
    ∃ e : K ≃+* L, ∀ x : R, e (algebraMap R K x) = algebraMap R L x := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis R L
  have hL : ℵ₀ < #L := hKL ▸ hK
  have hsK : #K = #s := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs hR hK
  have htL : #L = #t := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hR hL
  obtain ⟨e⟩ : Nonempty (s ≃ t) := Cardinal.eq.1 (hsK.symm.trans (hKL.trans htL))
  let _ := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  let _ := IsAlgClosed.isAlgClosure_of_transcendence_basis _ ht
  let e0 : Algebra.adjoin R (Set.range ((↑) : s → K)) ≃ₐ[R] Algebra.adjoin R (Set.range ((↑) : t → L)) :=
    hs.1.aevalEquiv.symm.trans ((MvPolynomial.renameEquiv R e).trans ht.1.aevalEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv K L e0.toRingEquiv, fun x => ?_⟩
  rw [IsScalarTower.algebraMap_apply R (Algebra.adjoin R (Set.range ((↑) : s → K))) K,
    IsAlgClosure.equivOfEquiv_algebraMap, AlgEquiv.coe_ringEquiv,
    AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]

theorem mk_le_continuum_of_denseRange {X Y : Type} [MetricSpace Y] (f : X → Y)
    (hf : DenseRange f) (hX : #X ≤ 𝔠) : #Y ≤ 𝔠 := by
  have hex : ∀ (y : Y) (n : ℕ), ∃ x, dist (f x) y < 1 / ((n : ℝ) + 1) := by
    intro y n
    obtain ⟨x, hx⟩ := Metric.denseRange_iff.1 hf y (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat
    exact ⟨x, by rw [dist_comm]; exact hx⟩
  choose g hg using hex
  have hlim : ∀ y, Filter.Tendsto (fun n => f (g y n)) Filter.atTop (nhds y) := by
    intro y
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => (hg y n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hinj : Function.Injective g := by
    intro y y' h
    have h2 := hlim y'
    rw [← h] at h2
    exact tendsto_nhds_unique (hlim y) h2
  calc #Y ≤ #(ℕ → X) := Cardinal.mk_le_of_injective hinj
    _ = #X ^ ℵ₀ := by rw [← Cardinal.mk_nat, Cardinal.power_def]
    _ ≤ 𝔠 ^ ℵ₀ := Cardinal.power_le_power_right hX
    _ = 𝔠 := Cardinal.continuum_power_aleph0

theorem mk_padicComplex (q : ℕ) [Fact q.Prime] : #ℂ_[q] = 𝔠 := by
  apply le_antisymm
  · have hQp : #ℚ_[q] ≤ 𝔠 :=
      mk_le_continuum_of_denseRange _ (Padic.denseRange_ratCast q)
        (by rw [Cardinal.mkRat]; exact Cardinal.aleph0_le_continuum)
    have hAl : #(PadicAlgCl q) ≤ 𝔠 :=
      (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[q] (PadicAlgCl q)).trans
        (max_le hQp Cardinal.aleph0_le_continuum)
    exact mk_le_continuum_of_denseRange _ (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl q)) hAl
  · obtain ⟨g, -, -, hg⟩ :=
      (PerfectSpace.univ_perfect (α := ℂ_[q])).exists_nat_bool_injection Set.univ_nonempty
    calc 𝔠 = #(ℕ → Bool) := by
          rw [← Cardinal.power_def, Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.two_power_aleph0]
      _ ≤ #ℂ_[q] := Cardinal.mk_le_of_injective hg

theorem exists_ringEquiv_extending : ∀ (q : ℕ) [Fact q.Prime]
    (lam : algebraicClosure ℚ ℂ →+* ℂ_[q]),
    ∃ ι : ℂ ≃+* ℂ_[q], ∀ x : algebraicClosure ℚ ℂ, ι (x : ℂ) = lam x := by
  intro q _ lam
  let _ : Algebra (algebraicClosure ℚ ℂ) ℂ_[q] := lam.toAlgebra
  have _ : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  have hR : #(algebraicClosure ℚ ℂ) ≤ ℵ₀ :=
    (Algebra.IsAlgebraic.cardinalMk_le_max ℚ (algebraicClosure ℚ ℂ)).trans
      (by rw [Cardinal.mkRat, max_self])
  have hK : ℵ₀ < #ℂ := by
    rw [Cardinal.mk_complex]
    exact Cardinal.aleph0_lt_continuum
  obtain ⟨e, he⟩ := exists_ringEquiv_over (algebraicClosure ℚ ℂ) ℂ ℂ_[q] hR hK
    (by rw [Cardinal.mk_complex, mk_padicComplex])
  exact ⟨e, fun x => he x⟩

end GlobalTheory.PadicComplexIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormLeOfDistinct
section
noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.Triang

variable {q : ℕ} [Fact q.Prime]

theorem bd_one_mul {f g : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (hg : Bd 1 g) : Bd 1 (f * g) := by
  intro n
  rw [PowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun p _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hf _) (norm_nonneg _) (hg _)

theorem bd_one_pow {f : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (n : ℕ) : Bd 1 (f ^ n) := by
  induction n with
  | zero =>
    intro m
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs <;> simp
  | succ n ih =>
    rw [pow_succ]
    exact bd_one_mul ih hf

theorem norm_le_of_distinct {ι : Type*} (s : Finset ι) (e : ι → ℕ) (u : ι → ℂ_[q]⟦X⟧) (c : ι → ℂ_[q]) (B : ℝ)
    (he : Set.InjOn e s) (hu : ∀ j ∈ s, Bd 1 (u j)) (h0 : ∀ j ∈ s, ‖constantCoeff (u j)‖ = 1)
    (hB : Bd B (∑ j ∈ s, C (c j) * (X ^ e j * u j))) : ∀ j ∈ s, ‖c j‖ ≤ B := by
  classical
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hcoeff : ∀ N, coeff N (∑ j ∈ s, C (c j) * (X ^ e j * u j)) =
      ∑ j ∈ s, c j * (if e j ≤ N then coeff (N - e j) (u j) else 0) := by
    intro N
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  have key : ∀ N, ∀ j ∈ s, e j = N → ‖c j‖ ≤ B := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    intro j hj hjN
    have hsplit := (hcoeff N).trans (Finset.add_sum_erase s _ hj).symm
    beta_reduce at hsplit
    have hjterm : c j * (if e j ≤ N then coeff (N - e j) (u j) else 0) = c j * constantCoeff (u j) := by
      rw [if_pos hjN.le, hjN, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    have hrest : ‖∑ i ∈ s.erase j, c i * (if e i ≤ N then coeff (N - e i) (u i) else 0)‖ ≤ B := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB0 fun i hi => ?_
      obtain ⟨hij, his⟩ := Finset.mem_erase.mp hi
      split_ifs with hle
      · have hlt : e i < N := lt_of_le_of_ne hle fun h => hij (he his hj (h.trans hjN.symm))
        rw [norm_mul]
        calc ‖c i‖ * ‖coeff (N - e i) (u i)‖ ≤ B * 1 :=
              mul_le_mul (ih _ hlt i his rfl) (hu i his _) (norm_nonneg _) hB0
          _ = B := mul_one B
      · simpa using hB0
    have hmain : c j * constantCoeff (u j) = coeff N (∑ j ∈ s, C (c j) * (X ^ e j * u j)) -
        ∑ i ∈ s.erase j, c i * (if e i ≤ N then coeff (N - e i) (u i) else 0) := by
      linear_combination -hsplit - hjterm
    have hnorm : ‖c j‖ = ‖c j * constantCoeff (u j)‖ := by rw [norm_mul, h0 j hj, mul_one]
    rw [hnorm, hmain, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hB N) ?_)
    rwa [norm_neg]
  exact fun j hj => key (e j) j hj rfl

theorem coeff_norm_le : ∀ (q : ℕ) [Fact q.Prime] (xs ys : ℂ_[q]⟦X⟧) (k : ℕ) (a b : ℕ → ℂ_[q]) (B : ℝ), Bd 1 xs → Bd 1 ys → ‖constantCoeff xs‖ = 1 → ‖constantCoeff ys‖ = 1 → Bd B (∑ i ∈ Finset.range (k + 1), (C (a i) * X ^ (2 * (k - i) + 3) * xs ^ i + C (b i) * X ^ (2 * (k - i)) * xs ^ i * ys)) → ∀ i ≤ k, ‖a i‖ ≤ B ∧ ‖b i‖ ≤ B := by
  intro q _ xs ys k a b B hxs hys hx0 hy0 hB
  classical
  let s : Finset (Bool × ℕ) := Finset.univ ×ˢ Finset.range (k + 1)
  let e : Bool × ℕ → ℕ := fun j => bif j.1 then 2 * (k - j.2) + 3 else 2 * (k - j.2)
  let u : Bool × ℕ → ℂ_[q]⟦X⟧ := fun j => bif j.1 then xs ^ j.2 else xs ^ j.2 * ys
  let c : Bool × ℕ → ℂ_[q] := fun j => bif j.1 then a j.2 else b j.2
  have hmem : ∀ {j : Bool × ℕ}, j ∈ s → j.2 < k + 1 := fun hj =>
    Finset.mem_range.mp (Finset.mem_product.mp hj).2
  have he : Set.InjOn e s := by
    rintro ⟨b₁, i₁⟩ h₁ ⟨b₂, i₂⟩ h₂ heq
    have hi₁ := hmem (Finset.mem_coe.mp h₁)
    have hi₂ := hmem (Finset.mem_coe.mp h₂)
    cases b₁ <;> cases b₂ <;> simp only [e, cond_true, cond_false] at heq hi₁ hi₂ <;>
      first | (exfalso; omega) | (congr 1; omega)
  have hu : ∀ j ∈ s, Bd 1 (u j) := by
    rintro ⟨_ | _, i⟩ _
    · exact bd_one_mul (bd_one_pow hxs i) hys
    · exact bd_one_pow hxs i
  have h0 : ∀ j ∈ s, ‖constantCoeff (u j)‖ = 1 := by
    rintro ⟨_ | _, i⟩ _
    · show ‖constantCoeff (xs ^ i * ys)‖ = 1
      rw [map_mul, map_pow, norm_mul, norm_pow, hx0, hy0, one_pow, one_mul]
    · show ‖constantCoeff (xs ^ i)‖ = 1
      rw [map_pow, norm_pow, hx0, one_pow]
  have hsum : (∑ j ∈ s, C (c j) * (X ^ e j * u j)) = ∑ i ∈ Finset.range (k + 1),
      (C (a i) * X ^ (2 * (k - i) + 3) * xs ^ i + C (b i) * X ^ (2 * (k - i)) * xs ^ i * ys) := by
    simp only [s]
    rw [Finset.sum_product, Fintype.sum_bool, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [e, u, c, cond_true, cond_false]
    ring
  have hB' : Bd B (∑ j ∈ s, C (c j) * (X ^ e j * u j)) := by
    rw [hsum]
    exact hB
  have key := norm_le_of_distinct s e u c B he hu h0 hB'
  intro i hi
  have hi' : i ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
  exact ⟨key (true, i) (Finset.mem_product.mpr ⟨Finset.mem_univ _, hi'⟩),
    key (false, i) (Finset.mem_product.mpr ⟨Finset.mem_univ _, hi'⟩)⟩

end GlobalTheory.MomOne.Triang
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormSumProdLeOfCoord
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

theorem norm_sum_prod_le_of_coord {K : Type*} [NormedCommRing K] {g m : ℕ} (F G : Fin m → Fin g → ℕ → K)
    (c : Fin m → K) (B : ℝ)
    (step : ∀ (i : Fin g) (c' : Fin m → K), (∀ n, ‖∑ j, c' j * F j i n‖ ≤ B) → ∀ n, ‖∑ j, c' j * G j i n‖ ≤ B)
    (h : ∀ ν : Fin g → ℕ, ‖∑ j, c j * ∏ i, F j i (ν i)‖ ≤ B) (ν : Fin g → ℕ) :
    ‖∑ j, c j * ∏ i, G j i (ν i)‖ ≤ B := by
  classical
  have key : ∀ I : Finset (Fin g), ∀ ν : Fin g → ℕ,
      ‖∑ j, c j * ∏ i, (if i ∈ I then G j i (ν i) else F j i (ν i))‖ ≤ B := by
    intro I
    induction I using Finset.induction_on with
    | empty => simpa using h
    | insert i₀ I hi ih =>
      intro ν
      have hs := step i₀
        (fun j => c j * ∏ i ∈ Finset.univ.erase i₀, (if i ∈ I then G j i (ν i) else F j i (ν i))) ?_ (ν i₀)
      · convert hs using 3 with j _
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i₀), mul_assoc]
        congr 2
        · refine Finset.prod_congr rfl fun i hi' => ?_
          simp [Finset.mem_insert, Finset.ne_of_mem_erase hi']
        · simp
      · intro n
        convert ih (Function.update ν i₀ n) using 3 with j _
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i₀), mul_assoc]
        congr 2
        · refine Finset.prod_congr rfl fun i hi' => ?_
          simp [Function.update_of_ne (Finset.ne_of_mem_erase hi')]
        · simp [hi]
  simpa using key Finset.univ ν

theorem translate_norm_prod_le : ∀ (d q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (θ : ℂ → ℂ), ThetaLaws ι d ω θ → ∀ (g m : ℕ) (a : Fin g → ℕ) (c : Fin m → ℂ_[q]) (t : Fin m → Fin g → ℂ) (τ : Fin g → ℂ) (B : ℝ), (∀ j i, PrimeTo d q (t j i)) → (∀ i, PrimeTo d q (τ i)) → (∀ ν : Fin g → ℕ, ‖∑ j, c j * ∏ i, coeff (ν i) (hat ι (C ω * logS) (U1 d (t j i) θ) ^ a i)‖ ≤ B) → ∀ ν : Fin g → ℕ, ‖∑ j, c j * ∏ i, coeff (ν i) (hat ι (C ω * logS) (U1 d (τ i) (U1 d (t j i) θ)) ^ a i)‖ ≤ B := by
  intro d q _ ι ω θ hθ g m a c t τ B ht hτ h
  refine norm_sum_prod_le_of_coord
    (fun j i n => coeff n (hat ι (C ω * logS) (U1 d (t j i) θ) ^ a i))
    (fun j i n => coeff n (hat ι (C ω * logS) (U1 d (τ i) (U1 d (t j i) θ)) ^ a i)) c B ?_ h
  intro i c' hc n
  have := hθ.2.2 (a i) m c' (fun j => t j i) (τ i) B (fun j => ht j i) (hτ i) (fun k => by
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [map_sum, coeff_C_mul] using hc k) n
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [map_sum, coeff_C_mul] using this

end GlobalTheory.MomOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.OpUConstMul
section
open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators

namespace GlobalTheory.HeisOps

variable {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}

theorem hf_add_left (x y z : Fin g → ℂ) : hf Hm (x + y) z = hf Hm x z + hf Hm y z := by
  simp only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem hf_add_right (x y z : Fin g → ℂ) : hf Hm x (y + z) = hf Hm x y + hf Hm x z := by
  simp only [hf, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem hf_zero_right (x : Fin g → ℂ) : hf Hm x 0 = 0 := by simp [hf]

theorem hf_swap (h : Hm.IsHermitian) (x y : Fin g → ℂ) : hf Hm y x = conj (hf Hm x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hf, map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have e : conj (Hm i j) = Hm j i := h.apply j i
  rw [e]; ring

theorem opU_opU (h : Hm.IsHermitian) (x y : Fin g → ℂ) (F : (Fin g → ℂ) → ℂ) :
    opU Hm x (opU Hm y F) = fun z =>
      Complex.exp (-(Real.pi : ℂ) * Complex.I * (((hf Hm x y).im : ℝ) : ℂ)) * opU Hm (x + y) F z := by
  funext z
  simp only [opU]
  rw [add_assoc z x y, mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add]
  congr 2
  simp only [hf_add_left, hf_add_right]
  have e := Complex.sub_conj (hf Hm x y)
  rw [hf_swap h x y]
  push_cast at e
  linear_combination (-(Real.pi : ℂ) / 2) * e

theorem opU_comm (h : Hm.IsHermitian) (x y : Fin g → ℂ) (F : (Fin g → ℂ) → ℂ) :
    opU Hm x (opU Hm y F) = fun z => kap Hm x y * opU Hm y (opU Hm x F) z := by
  funext z
  rw [opU_opU h x y, opU_opU h y x, add_comm y x, kap, ← mul_assoc, ← Complex.exp_add, hf_swap h x y,
    Complex.conj_im]
  push_cast
  ring_nf

theorem im_eq {d : ℕ} (hd : 0 < d) (x y : Fin g → ℂ) (u v : ℤ) (h : beta d Hm x y = u + v * w0 d) :
    (hf Hm x y).im = v := by
  have hs : Real.sqrt d ≠ 0 := by positivity
  have e := congrArg Complex.im h
  rw [beta, Complex.im_ofReal_mul] at e
  have e2 : ((u : ℂ) + v * w0 d).im = Real.sqrt d / 2 * v := by
    simp [w0, rtd]; ring
  rw [e2] at e
  exact mul_left_cancel₀ (div_ne_zero hs two_ne_zero) e

theorem opU_const_mul (c : ℂ) (x : Fin g → ℂ) (F : (Fin g → ℂ) → ℂ) (z : Fin g → ℂ) :
    opU Hm x (fun w => c * F w) z = c * opU Hm x F z := by
  simp only [opU]; ring

theorem opW_opW {d : ℕ} (hd : 0 < d) (h : Hm.IsHermitian) (x y : Fin g → ℂ) (F : (Fin g → ℂ) → ℂ)
    (hb : beta d Hm x y ∈ OK d) : opW d Hm x (opW d Hm y F) = opW d Hm (x + y) F := by
  obtain ⟨u, v, huv⟩ := hb
  have him := im_eq hd x y u v huv
  have hre : (beta d Hm x y).re = u + v / 2 := by
    rw [huv]; simp [w0, rtd]; ring
  have hq : (beta d Hm (x + y) (x + y)).re = (beta d Hm x x).re + (beta d Hm y y).re + (2 * u + v) := by
    simp only [beta, Complex.re_ofReal_mul, hf_add_left, hf_add_right, Complex.add_re] at hre ⊢
    rw [hf_swap h x y, Complex.conj_re]
    linear_combination 2 * hre
  funext z
  have e : opW d Hm x (opW d Hm y F) z = Complex.exp ((Real.pi : ℂ) * Complex.I * ((beta d Hm x x).re : ℂ)) *
      (Complex.exp ((Real.pi : ℂ) * Complex.I * ((beta d Hm y y).re : ℂ)) * opU Hm x (opU Hm y F) z) := by
    rw [← opU_const_mul]; rfl
  rw [e, opU_opU h, him]
  simp only [opW]
  rw [hq, ← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-(u + v), ?_⟩
  push_cast
  ring

theorem contDiff_opU (x : Fin g → ℂ) {F : (Fin g → ℂ) → ℂ} (hF : ContDiff ℂ ⊤ F) : ContDiff ℂ ⊤ (opU Hm x F) := by
  unfold opU hf
  refine (hF.comp (contDiff_id.add contDiff_const)).mul (ContDiff.cexp ?_)
  fun_prop

theorem contDiff_opW (d : ℕ) (x : Fin g → ℂ) {F : (Fin g → ℂ) → ℂ} (hF : ContDiff ℂ ⊤ F) :
    ContDiff ℂ ⊤ (opW d Hm x F) :=
  contDiff_const.mul (contDiff_opU x hF)

theorem heisenberg : ∀ (g d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), 0 < d → Hm.IsHermitian → (∀ (x y : Fin g → ℂ) (F : (Fin g → ℂ) → ℂ), opU Hm x (opU Hm y F) = (fun z => Complex.exp (-(Real.pi : ℂ) * Complex.I * (((hf Hm x y).im : ℝ) : ℂ)) * opU Hm (x + y) F z) ∧ opU Hm x (opU Hm y F) = (fun z => kap Hm x y * opU Hm y (opU Hm x F) z) ∧ (beta d Hm x y ∈ OK d → opW d Hm x (opW d Hm y F) = opW d Hm (x + y) F)) ∧ (∀ F, opU Hm 0 F = F ∧ opW d Hm 0 F = F) ∧ (∀ (x : Fin g → ℂ) (F : (Fin g → ℂ) → ℂ), ContDiff ℂ ⊤ F → ContDiff ℂ ⊤ (opU Hm x F) ∧ ContDiff ℂ ⊤ (opW d Hm x F)) ∧ (∀ x y : Fin g → ℂ, hf Hm y x = conj (hf Hm x y)) ∧ (∀ (x y : Fin g → ℂ) (u v : ℤ), beta d Hm x y = u + v * w0 d → (hf Hm x y).im = v) ∧ ∀ x y z : Fin g → ℂ, kap Hm x (y + z) = kap Hm x y * kap Hm x z ∧ kap Hm (x + y) z = kap Hm x z * kap Hm y z := by
  intro g d Hm hd h
  refine ⟨fun x y F => ⟨opU_opU h x y F, opU_comm h x y F, opW_opW hd h x y F⟩, fun F => ?_,
    fun x F hF => ⟨contDiff_opU x hF, contDiff_opW d x hF⟩, hf_swap h, im_eq hd, fun x y z => ⟨?_, ?_⟩⟩
  · constructor <;> funext z <;> simp [opW, opU, beta, hf_zero_right]
  · simp only [kap, hf_add_right, ← Complex.exp_add]; congr 1; push_cast [Complex.add_im]; ring
  · simp only [kap, hf_add_left, ← Complex.exp_add]; congr 1; push_cast [Complex.add_im]; ring

end GlobalTheory.HeisOps
end

