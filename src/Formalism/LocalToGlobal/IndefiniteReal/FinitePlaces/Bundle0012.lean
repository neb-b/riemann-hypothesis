module

public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSplit
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0011
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0002

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemFin
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem pin_eq {P Q : HeightOneSpectrum (𝓞 D.host.E)} {x : AE D} (hP : Formalism.L2.NTheta.IsIdemAt x P)
    (hQ : Formalism.L2.NTheta.IsIdemAt x Q) : P = Q := by
  have h : P.asIdeal = Q.asIdeal := by
    ext x
    by_cases hx : x = 0
    · subst hx
      exact ⟨fun _ => Q.asIdeal.zero_mem, fun _ => P.asIdeal.zero_mem⟩
    · rw [hP.2 x hx, hQ.2 x hx]
  exact HeightOneSpectrum.ext h

theorem conj_idem_eq {P Q : HeightOneSpectrum (𝓞 D.host.E)} {x y : AE D} (hx : Formalism.L2.NTheta.IsIdemAt x P)
    (hy : Formalism.L2.NTheta.IsIdemAt y Q) (hc : Lev.IsConjPl (D := D) P Q) : y = cA D x := by
  have hsp := idemAt_split hx
  obtain ⟨e₀, ι, he₀, -, hs₀, hz, hκ⟩ := idem_data P hsp (belowPl P) rfl
  have hx0 : x = e₀ := idemAt_eq_split hsp hx he₀
  have hle : (belowPl P).asIdeal ≤ (belowPl Q).asIdeal := by
    intro f hf
    obtain ⟨c, hc', hce⟩ := hc _ hf
    have : c = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) f := by
      apply FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E
      show (c : D.host.E) = ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) f : 𝓞 D.host.E) : D.host.E)
      rw [hce, algebraMap_O]
      exact (D.sp.cm.fixed _).2 ⟨_, rfl⟩
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) f ∈ Q.asIdeal
    rw [← this]; exact hc'
  have hbel : belowPl Q = belowPl P :=
    (HeightOneSpectrum.ext ((belowPl P).isMaximal.eq_of_le (belowPl Q).isPrime.ne_top hle)).symm
  have hs' := below_of_idemAt hy
  rw [hbel] at hs'
  rcases idem_class P hsp e₀ ι hs₀ hz hκ he₀.1.1 he₀.1.2.1 y hy.1.1 hy.1.2.1 hs' with h | h
  · exfalso
    rw [← hx0] at h
    have hPQ : P = Q := pin_eq hx (h ▸ hy)
    subst hPQ
    exact hsp hc
  · rw [h, hx0]

private theorem ne_zero_of_isIdemAt' {P : HeightOneSpectrum (𝓞 D.host.E)} {e : AE D}
    (he : Formalism.L2.NTheta.IsIdemAt e P) : e ≠ 0 := by
  intro h0
  obtain ⟨c, hcP, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  have h := (he.2 c hc0).1 hcP
  rw [h0, zero_mul] at h
  first
  | exact h (by simp)
  | simp at h
  | exact h (map_zero (finPart D) ▸ (intAE D).zero_mem)

private theorem not_isConjPl_of_isIdemAt {P : HeightOneSpectrum (𝓞 D.host.E)} {e : AE D}
    (he : Formalism.L2.NTheta.IsIdemAt e P) : ¬ Lev.IsConjPl (D := D) P P := by
  intro hc
  have h1 : e = cA D e := conj_idem_eq he he hc
  have h2 : e * cA D e = 0 := he.1.2.1
  rw [← h1, he.1.1] at h2
  exact ne_zero_of_isIdemAt' he h2

theorem idemSum_orth (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D) (he : Formalism.IndefR.Datum.IsIdemSum e P) :
    ∃ es : Formalism.L2.DIV.Pl D.host.E → AE D, (∀ PP ∈ P, IsSplitIdem D (es PP)) ∧ e = ∑ PP ∈ P, es PP ∧
      ∀ PP ∈ P, ∀ PP' ∈ P, PP ≠ PP' → es PP * es PP' = 0 ∧ es PP * cA D (es PP') = 0 := by
  obtain ⟨⟨es, hes, hsum⟩, hc⟩ := he
  refine ⟨es, fun PP hPP => (hes PP hPP).1, hsum, fun PP hPP PP' hPP' hne => ⟨?_, ?_⟩⟩
  · exact idem_orth (not_isConjPl_of_isIdemAt (hes PP hPP)) (hes PP hPP) (hes PP' hPP') hne
  · by_cases hcj : Lev.IsConjPl (D := D) PP PP'
    · exfalso
      have hy : es PP' = cA D (es PP) := conj_idem_eq (hes PP hPP) (hes PP' hPP') hcj
      have hL : es PP * e = es PP := by
        rw [hsum, Finset.mul_sum, Finset.sum_eq_single PP]
        · exact (hes PP hPP).1.1
        · intro b hb hbne
          exact idem_orth (not_isConjPl_of_isIdemAt (hes PP hPP)) (hes PP hPP) (hes b hb) (Ne.symm hbne)
        · intro h; exact absurd hPP h
      have hR : es PP * cA D e = es PP := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hsum, map_sum, Finset.mul_sum, Finset.sum_eq_single PP']
        · rw [hy, cA_cA]; exact (hes PP hPP).1.1
        · intro b hb hbne
          by_cases hb0 : b = PP
          · rw [hb0]; exact (hes PP hPP).1.2.1
          · refine idem_orth_conj (not_isConjPl_of_isIdemAt (hes PP hPP)) (hes PP hPP) (hes b hb) (fun hcb => hbne ?_)
            have hyb : es b = cA D (es PP) := conj_idem_eq (hes PP hPP) (hes b hb) hcb
            rw [← hy] at hyb
            have hb' := hes b hb
            rw [hyb] at hb'
            exact pin_eq hb' (hes PP' hPP')
        · intro h; exact absurd hPP' h
      have h0 : es PP * (e * cA D e) = 0 := by rw [hc, mul_zero]
      rw [← mul_assoc, hL, hR] at h0
      exact ne_zero_of_isIdemAt' (hes PP hPP) h0
    · exact idem_orth_conj (not_isConjPl_of_isIdemAt (hes PP hPP)) (hes PP hPP) (hes PP' hPP') hcj

end Formalism.IndefR.Fin

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SplitLem
section
set_option synthInstance.maxHeartbeats 100000

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (S T : HSp D)

theorem suppAt_inv_fp {e : AE D} {V : HSp D} {g : GA D V} (hg : SuppAt e V g) : SuppAt e V g⁻¹ := by
  have hinv : HMul.hMul (mt V g⁻¹) (mt V g) = (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
    rw [← Formalism.IndefR.Eqv.mt_mul, inv_mul_cancel, Formalism.IndefR.Eqv.mt_one]
  have hd : (mt V g⁻¹ : Matrix (Fin V.rank) (Fin V.rank) (AE D)) - 1 =
      -(HMul.hMul (mt V g⁻¹) ((mt V g : Matrix (Fin V.rank) (Fin V.rank) (AE D)) - 1)) := by
    rw [Matrix.mul_sub, hinv, Matrix.mul_one, neg_sub]
  intro i j
  rw [hd, Matrix.neg_apply, mul_neg, Matrix.mul_apply, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, hg k j]

theorem actO_nsmul (g : GA D S) (h : GA D T) (k : ℕ) (t : WO S T) : actO S T g h (k • t) = k • actO S T g h t := by
  induction k with
  | zero =>
    rw [zero_smul, zero_smul]
    unfold actO
    rw [Matrix.mul_zero, Matrix.zero_mul]
  | succ n ih => rw [succ_nsmul, succ_nsmul, Formalism.IndefR.Eqv.actO_add, ih]

theorem isHalf_actO_fp {e : AE D} (g : GA D S) (h : GA D T) {t : WO S T} (ht : IsHalf e t) :
    IsHalf e (actO S T g h t) := by
  intro i j
  unfold actO
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← ht l k]
  ring

theorem isHalf_nsmul_fp {e : AE D} {v : WO S T} (hv : IsHalf e v) (m : ℕ) : IsHalf e (m • v) := fun i j => by
  rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hv i j]

theorem isHalf_actO_iff {e : AE D} (g : GA D S) (h : GA D T) (t : WO S T) :
    IsHalf e (actO S T g h t) ↔ IsHalf e t := by
  refine ⟨fun h' => ?_, isHalf_actO_fp S T g h⟩
  have := isHalf_actO_fp S T g⁻¹ h⁻¹ h'
  rwa [Formalism.IndefR.Eqv.actO_actO_inv] at this

open Classical in
theorem halfInd_add {e : AE D} {Λ : AddSubgroup (WO S T)} {u : WO S T} (hu : u ∈ Λ) (hue : IsHalf e u)
    (s : WO S T) : halfInd e Λ (s + u) = halfInd e Λ s := by
  unfold halfInd
  have h1 : s + u ∈ Λ ↔ s ∈ Λ := ⟨fun h => by simpa using Λ.sub_mem h hu, fun h => Λ.add_mem h hu⟩
  have h2 : IsHalf e (s + u) ↔ IsHalf e s := by
    constructor
    · intro h i j
      have := h i j
      rw [Matrix.add_apply, mul_add, hue i j] at this
      exact add_right_cancel this
    · intro h i j
      rw [Matrix.add_apply, mul_add, h i j, hue i j]
  simp only [h1, h2]

theorem sb_comp {e : AE D} {Λ : AddSubgroup (WO S T)} (g : GA D S) (h : GA D T)
    {k₁ : ℕ} (hk₁ : 0 < k₁) (h₁ : ∀ t ∈ Λ, k₁ • actO S T g h t ∈ Λ)
    {k₂ : ℕ} (hk₂ : 0 < k₂) (h₂ : ∀ t ∈ Λ, k₂ • actO S T g⁻¹ h⁻¹ t ∈ Λ)
    {Φ : WO S T → ℂ} (hΦ : IsSBHalf e Λ Φ) : IsSBHalf e Λ (fun t => Φ (actO S T g h t)) := by
  obtain ⟨hs, k, hk, hi, hl⟩ := hΦ
  refine ⟨fun t ht => (isHalf_actO_iff S T g h t).1 (hs _ ht), k * k₁ * k₂, by positivity,
    fun u hu hue t => ?_, fun t ht => ?_⟩
  · show Φ (actO S T g h (t + (k * k₁ * k₂) • u)) = Φ (actO S T g h t)
    rw [Formalism.IndefR.Eqv.actO_add, actO_nsmul, show (k * k₁ * k₂) • actO S T g h u =
      k • (k₂ • (k₁ • actO S T g h u)) by rw [smul_smul, smul_smul]; ring_nf]
    exact hi _ (Λ.nsmul_mem (h₁ u hu) k₂)
      (isHalf_nsmul_fp S T (isHalf_nsmul_fp S T (isHalf_actO_fp S T g h hue) k₁) k₂) _
  · have h1 := hl _ ht
    have h2 := h₂ _ h1
    rw [actO_nsmul, Formalism.IndefR.Eqv.actO_actO_inv, smul_smul] at h2
    rw [show k * k₁ * k₂ = k₁ * (k₂ * k) by ring, ← smul_smul]
    exact Λ.nsmul_mem h2 k₁

end Formalism.IndefR.Fin

end
end

