module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0011

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ADensStC
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory Filter Topology
open scoped ComplexOrder

section Poly

variable {J : Type} [Fintype J]

theorem adens_hasFDerivAt_eval (F : MvPolynomial J ℂ) (z : J → ℂ) :
    HasFDerivAt (fun w => eval w F)
      (∑ i, eval z (pderiv i F) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : J => ℂ) i) z := by
  induction F using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C, pderiv_C, map_zero, zero_smul, Finset.sum_const_zero]
    exact hasFDerivAt_const a z
  | add p q hp hq =>
    simp only [map_add (f := _), add_smul, Finset.sum_add_distrib]
    exact hp.add hq
  | mul_X p n hp =>
    classical
    have h := hp.mul (hasFDerivAt_apply n z)
    have hf : (fun w : J → ℂ => eval w (p * X n)) = fun w => eval w p * w n := by
      funext w
      simp
    rw [hf]
    refine h.congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    have h1 : ∀ x, eval z (pderiv x (X n : MvPolynomial J ℂ)) = if x = n then 1 else 0 := by
      intro x
      rw [pderiv_X]
      by_cases hx : x = n
      · subst hx
        simp
      · simp [hx]
    have h2 : ∀ x, eval z (pderiv x (p * X n)) =
        eval z p * (if x = n then 1 else 0) + z n * eval z (pderiv x p) := by
      intro x
      rw [Derivation.leibniz, map_add (f := _), smul_eq_mul, smul_eq_mul, map_mul, map_mul, h1, eval_X]
    have h3 : ∑ x, eval z (pderiv x (p * X n)) * v x =
        eval z p * v n + z n * ∑ x, eval z (pderiv x p) * v x := by
      simp only [h2, add_mul, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.mul_sum, mul_assoc]
    simpa [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using h3.symm

end Poly

variable {J : Type} [Fintype J] {D : ℕ}

theorem adens_contDiffAt_logρ_id {m : ConeMetric (C := ℂ) (ι := J)}
    (hsm : IsSmoothMetric m) {z : J → ℂ}
    (hne : z ≠ 0) : ContDiffAt ℝ 2 (fun w => Real.log (m.ρ w)) z := by
  have hρ : ContDiffAt ℝ 2 m.ρ z :=
    (hsm.contDiffAt (isOpen_ne.mem_nhds hne)).of_le (WithTop.coe_le_coe.2 le_top)
  exact hρ.log (m.pos _ hne).ne'

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AInterpSt
section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Topology

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem interp_rho (m₀ m₁ : ConeMetric (C := ℂ) (ι := Ix κ)) (t : ℝ) (z : Ix κ → ℂ) :
    (interp m₀ m₁ t).ρ z = m₀.ρ z ^ (1 - t) * m₁.ρ z ^ t := rfl

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MultAtEqCount
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem le_colon_chain {J : Ideal (MRing ι)} {N : ℕ} {F : Fin (N + 1) → Ideal (MRing ι)}
    {f : Fin N → MRing ι} {q : Fin N → Ideal (MRing ι)} (h0 : F 0 = J)
    (hj : ∀ j : Fin N, F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧
      ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc) (j : Fin N) : J ≤ q j := by

  have mono : ∀ k : ℕ, ∀ hk : k ≤ N, J ≤ F ⟨k, Nat.lt_succ_of_le hk⟩ := by
    intro k
    induction k with
    | zero =>
      intro hk
      have e : (⟨0, Nat.lt_succ_of_le hk⟩ : Fin (N + 1)) = 0 := Fin.ext (by simp)
      rw [e, h0]
    | succ k ih =>
      intro hk
      have hk' : k < N := hk
      have step := (hj ⟨k, hk'⟩).1
      calc J ≤ F (Fin.castSucc ⟨k, hk'⟩) := ih hk'.le
        _ ≤ F (Fin.castSucc ⟨k, hk'⟩) ⊔ Ideal.span {f ⟨k, hk'⟩} := le_sup_left
        _ = F (Fin.succ ⟨k, hk'⟩) := step.symm
  intro g hg
  exact ((hj j).2 g).2 (Ideal.mul_mem_right _ _ (mono j.val j.isLt.le hg))

theorem multAt_eq_count {J : Ideal (MRing ι)} {N : ℕ} {F : Fin (N + 1) → Ideal (MRing ι)}
    {f : Fin N → MRing ι} {q : Fin N → Ideal (MRing ι)} (h0 : F 0 = J) (hlast : F (Fin.last N) = ⊤)
    (hj : ∀ j : Fin N, F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧ (q j).IsPrime ∧
      ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc)
    {W' : Ideal (MRing ι)} (hW' : W' ∈ J.minimalPrimes) :
    multAt J W' = ∑ j, if q j = W' then 1 else 0 := by
  classical
  have hp : W'.IsPrime := hW'.1.1
  have hJq : ∀ j, J ≤ q j := le_colon_chain h0 fun j => ⟨(hj j).1, (hj j).2.2⟩
  have hmin : ∀ j, q j ≤ W' → q j = W' := fun j h => le_antisymm h (hW'.2 ⟨(hj j).2.1, hJq j⟩ h)
  have := length_loc_chain W' N F f q hlast hj hmin
  rw [h0] at this
  unfold multAt
  rw [dite_eq_left hp, this]
  simp

theorem block_step {L : ℝ} {m p : ℕ} (hp : p.Prime) {W : Ideal (MRing ι)} (hW : IsMultiProjPrime W)
    (hpW : (p : MRing ι) ∈ W)
    (hdim : ringKrullDim (MRing ι ⧸ W) = ((m + 1 + Fintype.card K : ℕ) : WithBot ℕ∞))
    (hR4W : ∀ (a : Fin (m + 1) → K → ℤ) (k : K) (i : ι k), (X ⟨k, i⟩ : MRing ι) ∉ W →
      (a (Fin.last m) = fun k' => if k' = k then 1 else 0) →
      geoNum (m + 1) W a = ∑ᶠ W' ∈ divSupp W (X ⟨k, i⟩),
        (multAt (W ⊔ Ideal.span {(X ⟨k, i⟩ : MRing ι)}) W' : ℤ) * geoNum m W' (Fin.init a))
    (IH : ∀ W' : Ideal (MRing ι), IsMultiProjPrime W' → (p : MRing ι) ∈ W' →
      ringKrullDim (MRing ι ⧸ W') = ((m + Fintype.card K : ℕ) : WithBot ℕ∞) →
      HAsymp L m W' ∧ SymmAt m W')
    (b : K) :
    ∃ (a₀ : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      |lg W a - lg W (a - Pi.single b 1) -
          L * (geoNum (m + 1) W (Fin.snoc (fun _ k => (a k : ℤ)) (uv b)) : ℝ) / m.factorial| ≤
        C * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := by
  classical
  obtain ⟨hWp, hWm, hWr⟩ := hW
  obtain ⟨i, hi⟩ := hWr b
  set s : MRing ι := X ⟨b, i⟩ with hsdef
  have hs : IsMultiHomog s (Pi.single b 1) := isMultiHomog_X' b i
  set J := W ⊔ Ideal.span {s} with hJdef
  have hJ : IsMultiHomogIdeal J := isMultiHomogIdeal_sup_span hWm hs
  obtain ⟨N, F, f, c, q, h0, hlast, hj⟩ := exists_primeFiltration_of_isMultiHomogIdeal J hJ
  have hJq : ∀ j, J ≤ q j := le_colon_chain h0 fun j => ⟨(hj j).2.1, (hj j).2.2.2.2⟩
  have hFm : IsMultiHomogIdeal (F 0) := h0 ▸ hJ
  choose a0 C hC hb using fun j => per_factor (L := L) hp hWm hpW hdim hs hi IH (hj j).2.2.1
    (hj j).2.2.2.1 (hJq j) (c j)
  refine ⟨1 + ∑ j, a0 j + ∑ j, tdeg (c j), ∑ j, C j, Finset.sum_nonneg fun j _ => hC j,
    fun a ha => ?_⟩
  have ha0 : ∀ j k, a0 j ≤ a k := fun j k => by
    have h1 : a0 j ≤ ∑ j, a0 j := Finset.single_le_sum (f := a0) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
    have := ha k
    omega
  have hca : ∀ j k, c j k ≤ a k := fun j k => by
    have h1 : c j k ≤ tdeg (c j) := Finset.single_le_sum (f := c j) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ k)
    have h2 : tdeg (c j) ≤ ∑ j, tdeg (c j) := Finset.single_le_sum (f := fun j => tdeg (c j))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have := ha k
    omega
  have hb1 : ∀ k, (Pi.single b 1 : K → ℕ) k ≤ a k := fun k => by
    have := ha k
    by_cases hk : k = b
    · subst hk; simp; omega
    · simp [Pi.single_apply, hk]
  have hstep := lg_step hWm hs (q := W)
    (fun g => ⟨fun h => W.mul_mem_right _ h, fun h => (hWp.mem_or_mem h).resolve_right hi⟩)
    hb1 hp.pos hpW
  have hch := lg_chain a hFm hlast (fun j => ⟨(hj j).1, (hj j).2.1, (hj j).2.2.2.2⟩) hca hp.pos
    (fun j => hJq j (Ideal.mem_sup_left hpW))
  rw [h0] at hch
  have hfin := divSupp_finite W s
  have hsum : L * (geoNum (m + 1) W (Fin.snoc (fun _ k => (a k : ℤ)) (uv b)) : ℝ) / m.factorial =
      ∑ j, (if q j ∈ divSupp W s then appr L m (q j) a else 0) := by
    rw [hR4W _ b i hi (by funext k'; simp [uv, Pi.single_apply]), Fin.init_snoc,
      finsum_mem_eq_finite_toFinset_sum _ hfin]
    have hcount : ∀ W' ∈ hfin.toFinset, multAt J W' = ∑ j, if q j = W' then 1 else 0 :=
      fun W' hW' => multAt_eq_count h0 hlast (fun j => ⟨(hj j).2.1, (hj j).2.2.1, (hj j).2.2.2.2⟩)
        ((Set.Finite.mem_toFinset hfin).mp hW').1
    rw [Finset.sum_congr rfl fun W' hW' => by rw [hcount W' hW']]
    push_cast
    simp_rw [Finset.sum_mul, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_comm, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_ite_eq]
    simp only [Set.Finite.mem_toFinset, appr]
    split_ifs <;> simp
  rw [hsum, hstep, hch, add_sub_cancel_right, ← Finset.sum_sub_distrib, Finset.sum_mul,
    Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hb j a fun k => ha0 j k)

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

