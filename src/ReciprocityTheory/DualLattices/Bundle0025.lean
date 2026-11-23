module

public import ReciprocityTheory.DualLattices.Bundle0021
public import ReciprocityTheory.DualLattices.Bundle0011
public import ReciprocityTheory.DualLattices.Bundle0013
public import ReciprocityTheory.DualLattices.Bundle0009
public import ReciprocityTheory.DualLattices.Bundle0022

@[expose] public section

-- bundled from ReciprocityTheory.DualLattices.RestrictHopfOrderLength
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up.PullbackHopfOrder

private theorem red_surj {p : ℕ} [Fact p.Prime] {g : ℕ} (n : Nb p g) : ∃ t, red p g t = n := by
  refine ⟨fun i => ((n i).val : ℤ_[p]), funext fun i => ?_⟩
  simp [red]

private theorem red_mulVec {p : ℕ} [Fact p.Prime] {g : ℕ} (M : Matrix (Ix g) (Ix g) ℤ_[p])
    (t : TT p g) : red p g (M *ᵥ t) = M.map PadicInt.toZMod *ᵥ red p g t := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [red, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem restrict_hopfOrder_length : RestrictedHopfOrderStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H a ha r Bw hrange hkerB d hd
  have hE : H.ρ a * H.ρ a = H.ρ a := by rw [← map_mul, ha]
  have hcol : ∀ j : Ix g, ∃ k : Fin r → ℤ_[p], Bw *ᵥ k = H.ρ a *ᵥ Pi.single j 1 := by
    intro j
    have hm : H.ρ a *ᵥ Pi.single j 1 ∈ LinearMap.range (Matrix.mulVecLin Bw) := by
      rw [hrange]
      exact ⟨Pi.single j 1, rfl⟩
    obtain ⟨k, hk⟩ := hm
    exact ⟨k, hk⟩
  choose kk hkk using hcol
  let K : Matrix (Fin r) (Ix g) ℤ_[p] := Matrix.of fun i j => kk j i
  have hBK : Bw * K = H.ρ a := by
    ext i j
    have h1 : (Bw * K) i j = (Bw *ᵥ kk j) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, K]
    rw [h1, hkk j]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hKB : K * Bw = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun x => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.one_mulVec]
    apply LinearMap.ker_eq_bot.mp hkerB
    show Bw *ᵥ ((K * Bw) *ᵥ x) = Bw *ᵥ x
    obtain ⟨y, hy⟩ : Bw *ᵥ x ∈ LinearMap.range (Matrix.mulVecLin (H.ρ a)) := by
      rw [← hrange]
      exact ⟨x, rfl⟩
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hBK, ← hy]
    show H.ρ a *ᵥ (H.ρ a *ᵥ y) = H.ρ a *ᵥ y
    rw [Matrix.mulVec_mulVec, hE]
  let ψ := psiW Bw
  let χ : Nb p g →+ (Fin r → ZMod p) := (Matrix.mulVecLin (K.map PadicInt.toZMod)).toAddMonoidHom
  have hχψ : ∀ x, χ (ψ x) = x := by
    intro x
    show K.map PadicInt.toZMod *ᵥ (Bw.map PadicInt.toZMod *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hKB, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.one_mulVec]
  have hred : ∀ t, ψ (χ (red p g t)) = red p g (H.ρ a *ᵥ t) := by
    intro t
    show Bw.map PadicInt.toZMod *ᵥ (K.map PadicInt.toZMod *ᵥ red p g t) = _
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hBK, ← red_mulVec]
  have hA : ∀ f ∈ H.AA.carrier, (fun n => f (ψ (χ n))) ∈ H.AA.carrier := by
    intro f hf
    obtain ⟨f', hf', hff⟩ := H.h3 a f hf
    convert hf' using 1
    funext n
    obtain ⟨t, rfl⟩ := red_surj n
    rw [hff, hred]
  have hinj : Function.Injective ψ := fun x y h => by rw [← hχψ x, ← hχψ y, h]
  have hEE : H.ρL a * H.ρL a = H.ρL a := by rw [← map_mul, ha]
  let e := hd.some
  let Q1 : Matrix (Fin g) (Fin d) R :=
    LinearMap.toMatrix' ((LinearMap.range (H.ρL a).mulVecLin).subtype ∘ₗ e.symm.toLinearMap)
  let Q2 : Matrix (Fin d) (Fin g) R :=
    LinearMap.toMatrix' (e.toLinearMap ∘ₗ (H.ρL a).mulVecLin.rangeRestrict)
  have hQ12 : Q1 * Q2 = H.ρL a := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
    refine LinearMap.ext fun x => ?_
    simp [Matrix.toLin'_apply]
  have hQ21 : Q2 * Q1 = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix', Matrix.toLin'_one]
    refine LinearMap.ext fun y => ?_
    have hz : (H.ρL a).mulVecLin.rangeRestrict ((e.symm y : LinearMap.range (H.ρL a).mulVecLin) : Fin g → R) =
        e.symm y := by
      apply Subtype.ext
      obtain ⟨w, hw⟩ := (e.symm y).2
      show H.ρL a *ᵥ ((e.symm y : LinearMap.range (H.ρL a).mulVecLin) : Fin g → R) = e.symm y
      rw [← hw]
      show H.ρL a *ᵥ (H.ρL a *ᵥ w) = H.ρL a *ᵥ w
      rw [Matrix.mulVec_mulVec, hEE]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply, LinearMap.id_apply]
    rw [hz, LinearEquiv.apply_symm_apply]
  have hF : Q2ᵀ * Q1ᵀ = (H.ρL a)ᵀ := by rw [← Matrix.transpose_mul, hQ12]
  have h21 : Q1ᵀ * Q2ᵀ = 1 := by rw [← Matrix.transpose_mul, hQ21, Matrix.transpose_one]
  obtain ⟨eO⟩ := omega_pull p ψ χ hχψ H.AA.carrier hA H.φ H.cotangent_surjective H.cotangent_ker_eq (H.ρL a)ᵀ Q2ᵀ Q1ᵀ hF h21
    (fun f f' l hff hl => H.cotangent_linear a f f' l (fun t => by rw [hff, hred]) hl)
  refine ⟨pullHopf ψ H.AA (isLat_pull v hS.integers ψ hinj H.AA), pullHopf_carrier _ _ _, ?_⟩
  rw [pullHopf_carrier]
  exact ⟨d, fun _ => (p : R), ⟨eO.trans (qPi p d)⟩, by simp [Finset.prod_const]⟩

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.StdJForm
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

private lemma stdJ_form' {D : Type} [CommRing D] {g : ℕ}
    (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D) (i j : Fin g ⊕ Fin g) :
    (Mᵀ * stdJ D g * M) i j =
      ∑ a, (M (Sum.inr a) i * M (Sum.inl a) j - M (Sum.inl a) i * M (Sum.inr a) j) := by
  simp [stdJ, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Finset.sum_sub_distrib,
    sub_eq_add_neg, add_comm]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  ring

private lemma stdJ_eq (D : Type) [CommRing D] (g : ℕ) :
    stdJ D g = fromBlocks 1 (-1) 0 1 * fromBlocks 1 0 1 1 * fromBlocks 1 (-1) 0 1 := by
  rw [stdJ]
  simp [Matrix.fromBlocks_multiply]

private lemma det_stdJ (D : Type) [CommRing D] (g : ℕ) : (stdJ D g).det = 1 := by
  rw [stdJ_eq, Matrix.det_mul, Matrix.det_mul]
  simp [Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂]

theorem u1 : IsotypicAveragingStatement := by
  intro S _ g m Ht Bt E cp εT εL π hπ hT hT1 hL hL1 hHt hE hBH
  intro Bt'
  have hBt' : Bt' = ∑ i, εL i * Bt * εT i := rfl
  have hLt : ∀ i, (εL i)ᵀ * Ht = Ht * εT (π i) := by
    intro i
    have h := hHt (π i)
    rw [hπ] at h
    exact h.symm
  have hHtL : ∀ i, Htᵀ * εL i = (εT (π i))ᵀ * Htᵀ := by
    intro i
    have h := congrArg Matrix.transpose (hLt i)
    simpa [Matrix.transpose_mul] using h
  have part2 : ∀ i, Bt' * εT i = εL i * Bt' := by
    intro i
    have l : ∀ j, εL j * Bt * εT j * εT i = if j = i then εL j * Bt * εT j else 0 := by
      intro j
      rw [Matrix.mul_assoc (εL j * Bt), hT j i]
      split_ifs with h
      · subst h; rfl
      · simp
    have r : ∀ j, εL i * (εL j * Bt * εT j) = if j = i then εL j * Bt * εT j else 0 := by
      intro j
      by_cases h : j = i
      · subst h
        rw [if_pos rfl, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hL, if_pos rfl]
      · rw [if_neg h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hL, if_neg (Ne.symm h),
          Matrix.zero_mul, Matrix.zero_mul]
    rw [hBt', Matrix.sum_mul, Matrix.mul_sum]
    simp only [l, r]
  have hA : Bt'ᵀ * Ht = ∑ i, (εT i)ᵀ * Btᵀ * Ht * εT (π i) := by
    rw [hBt', Matrix.transpose_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.transpose_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
    rw [hLt i]
  have hB : Htᵀ * Bt' = ∑ i, (εT i)ᵀ * Htᵀ * Bt * εT (π i) := by
    rw [hBt', Matrix.mul_sum, ← Equiv.sum_comp π (fun i => Htᵀ * (εL i * Bt * εT i))]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [← Matrix.mul_assoc]
    rw [hHtL (π i), hπ]
  have part1 : Bt'ᵀ * Ht - Htᵀ * Bt' = cp • E := by
    rw [hA, hB, ← Finset.sum_sub_distrib]
    have h : ∀ i, (εT i)ᵀ * Btᵀ * Ht * εT (π i) - (εT i)ᵀ * Htᵀ * Bt * εT (π i) =
        cp • (E * εT (π i)) := by
      intro i
      rw [Matrix.mul_assoc ((εT i)ᵀ) Btᵀ Ht, Matrix.mul_assoc ((εT i)ᵀ) Htᵀ Bt, ← Matrix.sub_mul,
        ← Matrix.mul_sub, hBH, Matrix.mul_smul, hE i, Matrix.smul_mul, Matrix.mul_assoc, hT,
        if_pos rfl]
    simp only [h]
    rw [← Finset.smul_sum, ← Matrix.mul_sum, Equiv.sum_comp π εT, hT1, Matrix.mul_one]
  have hJ : (Matrix.fromRows Ht Bt')ᵀ * stdJ S g * Matrix.fromRows Ht Bt' = cp • E := by
    rw [← part1]
    ext i j
    rw [stdJ_form']
    simp [Matrix.sub_apply, Matrix.mul_apply, Finset.sum_sub_distrib]
  refine ⟨part1, part2, ?_⟩
  rw [det_sq_eq E _ cp hJ, det_stdJ, mul_one]

end ReciprocityTheory.PGsh.Up
end
end

