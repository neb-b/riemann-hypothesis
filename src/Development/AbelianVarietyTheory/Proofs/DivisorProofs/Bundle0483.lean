module

public import Mathlib
public import Formalism.PairingDivisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0459
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0472
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisAutMemAdelicCompletionIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharUnramifiedInverseSplitPair
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.Euler.SplitPair

variable {E : Type} [Field E] [NumberField E]

theorem eq_exp_of_le {x : WithZero (Multiplicative ℤ)} {m : ℤ} (h : x ≤ WithZero.exp m) (h' : ¬ x ≤ WithZero.exp (m - 1)) :
    x = WithZero.exp m := by
  refine le_antisymm h (not_lt.1 fun h1 => h' ?_)
  rw [← WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero, ← WithZero.exp_add, sub_add_cancel]
  exact h1

theorem exists_int_cong (P : HeightOneSpectrum (𝓞 E)) (z : P.adicCompletion E) (hz : Valued.v z ≤ 1) :
    ∃ b : 𝓞 E, Valued.v (algebraMap E (Af E) (algebraMap (𝓞 E) E b) P - z) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap E P).mem_nhds (OrderUnits.ball_mem_nhds P 1 z)
  have hk' : Valued.v (algebraMap E (P.adicCompletion E) k - z) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := hk
  have hval : ∀ x : E, Valued.v (algebraMap E (P.adicCompletion E) x) = P.valuation E x := fun x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P x
  have h1 : P.valuation E k ≤ 1 := by
    have h2 : WithZero.exp (-((1 : ℕ) : ℤ)) ≤ 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
    have := Valuation.map_add_le _ (hk'.trans h2) hz
    rwa [sub_add_cancel, hval] at this
  obtain ⟨b, hb⟩ := P.exists_valuation_sub_lt_of_integer h1 (Units.mk0 (WithZero.exp (-((1 : ℕ) : ℤ))) WithZero.exp_ne_zero)
  refine ⟨b, ?_⟩
  rw [← hval, map_sub] at hb
  have := Valuation.map_add_le _ hb.le hk'
  rw [sub_add_sub_cancel] at this
  exact this

def unitF (a : OF E) (ha : a ≠ 0) : (maximalRealSubfield E)ˣ :=
  Units.mk0 (a : maximalRealSubfield E) (fun h => ha (RingOfIntegers.ext h))

def locF (P : HeightOneSpectrum (𝓞 E)) (a : OF E) (ha : a ≠ 0) : (P.adicCompletion E)ˣ :=
  Formalism.L2.Host.atFin P (Formalism.L2.Host.upF (maximalRealSubfield E) (unitF a ha))

theorem coe_locF (P : HeightOneSpectrum (𝓞 E)) (a : OF E) (ha : a ≠ 0) : (locF P a ha : P.adicCompletion E) = iota a P := rfl

theorem loc_mul_loc {χ : HChar E} (hF : TrivOnF χ) {v : HeightOneSpectrum (OF E)} {P P' : HeightOneSpectrum (𝓞 E)}
    (hP : Over P v) (hP' : Over P' v) (hne : P ≠ P') (h2 : ∀ R, Over R v → R = P ∨ R = P') (a : OF E) (ha : a ≠ 0) :
    χ.loc P (locF P a ha) * χ.loc P' (locF P' a ha) = 1 := by
  classical
  have hS : Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v = {P, P'} := by
    ext R
    rw [mem_aboveF, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨h2 R, ?_⟩
    rintro (rfl | rfl)
    · exact hP
    · exact hP'
  have h := hF.1 v (unitF a ha)
  unfold Formalism.L2.Host.HChar.resFin at h
  rw [MonoidHom.finsetProd_apply, hS, Finset.prod_pair hne] at h
  exact h

theorem unrAt_and_val : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar E) (v : HeightOneSpectrum (OF E))
    (P P' : HeightOneSpectrum (𝓞 E)), TrivOnF χ → Splits v → Over P v → Over P' v → P ≠ P' → LevelLe χ P' 1 → UnrAt χ P →
    UnrAt χ P' ∧ val χ P' = (val χ P)⁻¹ := by
  intro E _ _ _ χ v P P' hF hs hP hP' hne hlev hun
  obtain ⟨h2, hef⟩ := GlobalTheory.CMVal.Euler.SplitPlace.split_place E v hs
  have hmul := loc_mul_loc hF hP hP' hne (h2 P P' hP hP' hne)
  have hval : ∀ R, Over R v → ∀ (n : ℕ) (a : OF E), a ∈ v.asIdeal ^ n → a ∉ v.asIdeal ^ (n + 1) →
      Valued.v (iota a R) = WithZero.exp (-(n : ℤ)) := fun R hR n a h h' => by
    refine eq_exp_of_le (val_iota_le_of_mem hR n h) fun h3 => h' ?_
    rw [← (hef R hR).2.1, ← val_iota_le_iff]
    convert h3 using 2
    push_cast; ring
  have hun' : UnrAt χ P' := by
    intro u hu
    have hu1 : Valued.v (u : P'.adicCompletion E) = 1 := hu
    obtain ⟨b, hb⟩ := exists_int_cong P' u hu1.le
    obtain ⟨a, ha⟩ := (hef P' hP').2.2 b
    have h3 := OrderUnits.val_int_le P' 1 _ (by simpa using ha)
    have h4 : Valued.v (iota a P' - u) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
      rw [map_sub (algebraMap (𝓞 E) E), map_sub (algebraMap E (Af E)), sub_coord] at h3
      have := Valuation.map_sub_le _ hb h3
      rw [sub_sub_sub_cancel_left] at this
      exact this
    have hlt : WithZero.exp (-((1 : ℕ) : ℤ)) < 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    have h5 : Valued.v (iota a P') = 1 := by
      rw [Valuation.map_eq_of_sub_lt _ (hu1 ▸ h4.trans_lt hlt), hu1]
    have hav : a ∉ v.asIdeal ^ (0 + 1) := fun h => (h5 ▸ val_iota_le_of_mem hP' 1 h).not_gt hlt
    have ha0 : a ≠ 0 := fun h => hav (h ▸ zero_mem _)
    have h6 : χ.loc P (locF P a ha0) = 1 := hun _ (by
      show Valued.v (iota a P) = 1
      simpa using hval P hP 0 a (by simp) hav)
    have h7 := hmul a ha0
    rw [h6, one_mul] at h7
    have h8 : χ.loc P' (locF P' a ha0 / u) = 1 := by
      refine hlev _ ?_ ?_
      · show Valued.v ((locF P' a ha0 / u : (P'.adicCompletion E)ˣ) : P'.adicCompletion E) = 1
        rw [Units.val_div_eq_div_val, map_div₀, coe_locF, h5, hu1, div_one]
      · rw [Units.val_div_eq_div_val, div_sub_one u.ne_zero, map_div₀, hu1, div_one, coe_locF]
        exact h4
    rw [map_div, div_eq_one, h7] at h8
    exact h8.symm
  refine ⟨hun', ?_⟩
  obtain ⟨a, ha, ha'⟩ := Ideal.exists_mem_pow_notMem_pow_succ v.asIdeal v.ne_bot v.isPrime.ne_top 1
  have ha0 : a ≠ 0 := fun h => ha' (h ▸ zero_mem _)
  have h7 := hmul a ha0
  have hunif : ∀ R, Over R v → Formalism.L2.Host.IsUnifAt R (locF R a ha0) := fun R hR => by
    show Valued.v (iota a R) = WithZero.exp (-1 : ℤ)
    simpa using hval R hR 1 a ha ha'
  rw [χ.val_eq hun _ (hunif P hP), χ.val_eq hun' _ (hunif P' hP')] at h7
  exact eq_inv_of_mul_eq_one_right h7

end GlobalTheory.CMVal.Euler.SplitPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdjointMemEndLattice
section
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc

noncomputable section

namespace GlobalTheory.LieDisc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_eq_dotProduct (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    herm G x y = x ⬝ᵥ (G *ᵥ fun b => cc (y b)) := by
  simp only [herm, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem cc_map_mulVec (M : Matrix (Fin r) (Fin r) E) (y : Fin r → E) :
    (fun b => cc ((M.map cc *ᵥ y) b)) = M *ᵥ fun b => cc (y b) := by
  funext b
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mulVec, dotProduct, map_apply, cc, map_sum, map_mul, IsCMField.complexConj_apply_apply]

theorem herm_mulVec_left_eq (G Y : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0) (x y : Fin r → E) :
    herm G (Y *ᵥ x) y = herm G x (hAdj G Y *ᵥ y) := by
  rw [herm_eq_dotProduct, herm_eq_dotProduct, hAdj, cc_map_mulVec, mulVec_mulVec,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hG), Matrix.one_mul,
    ← mulVec_mulVec, dotProduct_mulVec, dotProduct_mulVec, vecMul_transpose]
  exact (dotProduct_mulVec _ _ _).symm

theorem hAdj_mem_endLat (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E))
    (Y : Matrix (Fin r) (Fin r) E) (h : SelfDualLat G Λ) (hY : Y ∈ endLat Λ) : hAdj G Y ∈ endLat Λ := by
  obtain ⟨hGh, hdet, -, -, hsd⟩ := h
  intro y hy
  refine (hsd _).1 fun x hx => ?_
  have h1 : IsIntegral ℤ (herm G x (hAdj G Y *ᵥ y)) := by
    rw [← herm_mulVec_left_eq G Y hdet]
    exact (hsd (Y *ᵥ x)).2 (hY x hx) y hy
  rw [← GlobalTheory.UCls.Det.herm_symm G hGh]
  exact h1.map (IsCMField.complexConj E)

end GlobalTheory.LieDisc

theorem GlobalTheory.LieDisc.hAdj_mem_endLat_main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Y : Matrix (Fin r) (Fin r) E), SelfDualLat G Λ → Y ∈ endLat Λ → hAdj G Y ∈ endLat Λ :=
  fun _ _ _ _ r G Λ Y h hY => GlobalTheory.LieDisc.hAdj_mem_endLat G Λ Y h hY
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdjointProperties
section
noncomputable section

namespace GlobalTheory.LieDisc.HAdjAlg

open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem map_mul_cc (A B : Matrix (Fin r) (Fin r) E) : (A * B).map cc = A.map cc * B.map cc :=
  Matrix.map_mul (f := (IsCMField.complexConj E : E →+* E))

theorem map_map_cc (A : Matrix (Fin r) (Fin r) E) : (A.map cc).map cc = A := by
  ext i j; simp [cc_cc]

theorem herm_eq_dot (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    herm G x y = x ⬝ᵥ (G *ᵥ fun b => cc (y b)) := by
  simp [herm, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem cc_mulVec (A : Matrix (Fin r) (Fin r) E) (y : Fin r → E) :
    (fun b => cc ((A *ᵥ y) b)) = A.map cc *ᵥ fun b => cc (y b) := by
  ext i; simp [mulVec, dotProduct, cc, map_sum, map_mul]

theorem map_one_cc : (1 : Matrix (Fin r) (Fin r) E).map cc = 1 := by
  exact Matrix.map_one cc (by simp [cc]) (by simp [cc])

theorem map_smul_cc (c : E) (A : Matrix (Fin r) (Fin r) E) : (c • A).map cc = cc c • A.map cc := by
  ext i j; simp [cc, map_mul]

theorem trace_map_cc (A : Matrix (Fin r) (Fin r) E) : (A.map cc).trace = cc A.trace := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.trace, cc, map_sum]

end GlobalTheory.LieDisc.HAdjAlg

open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc GlobalTheory.LieDisc.HAdjAlg

theorem GlobalTheory.LieDisc.hAdj_algebra : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → (∀ (Y : Matrix (Fin r) (Fin r) E) (x y : Fin r → E), herm G (Y *ᵥ x) y = herm G x (hAdj G Y *ᵥ y)) ∧ (∀ Y Z : Matrix (Fin r) (Fin r) E, hAdj G (Y * Z) = hAdj G Z * hAdj G Y) ∧ (∀ Y Z : Matrix (Fin r) (Fin r) E, hAdj G (Y + Z) = hAdj G Y + hAdj G Z) ∧ (∀ (c : E) (Y : Matrix (Fin r) (Fin r) E), hAdj G (c • Y) = cc c • hAdj G Y) ∧ hAdj G 1 = 1 ∧ (∀ Y : Matrix (Fin r) (Fin r) E, hAdj G (hAdj G Y) = Y) ∧ (∀ Y : Matrix (Fin r) (Fin r) E, (hAdj G Y).trace = cc Y.trace) ∧ (∀ Y : Matrix (Fin r) (Fin r) E, IsSkew G Y ↔ hAdj G Y = -Y) := by
  intro E _ _ _ r G hG hdet
  have hu : IsUnit G.det := isUnit_iff_ne_zero.mpr hdet
  have hGi : G * G⁻¹ = 1 := mul_nonsing_inv G hu
  have hiG : G⁻¹ * G = 1 := nonsing_inv_mul G hu
  have hGt : G.map cc = Gᵀ := by ext a b; simp [hG]
  have adj1 : ∀ (Y : Matrix (Fin r) (Fin r) E) (x y : Fin r → E),
      herm G (Y *ᵥ x) y = herm G x (hAdj G Y *ᵥ y) := by
    intro Y x y
    rw [herm_eq_dot, herm_eq_dot, cc_mulVec, hAdj, map_map_cc, mulVec_mulVec,
      show G * (G⁻¹ * Yᵀ * G) = Yᵀ * G by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hGi, Matrix.one_mul],
      ← mulVec_mulVec, dotProduct_mulVec x Yᵀ, vecMul_transpose]
  refine ⟨adj1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Y Z
    rw [hAdj, hAdj, hAdj, ← map_mul_cc, transpose_mul]
    congr 1
    simp only [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hu]
  · intro Y Z
    simp only [hAdj, transpose_add, Matrix.mul_add, Matrix.add_mul]
    ext i j; simp [cc]
  · intro c Y
    rw [hAdj, hAdj, ← map_smul_cc, transpose_smul, Matrix.mul_smul, Matrix.smul_mul]
  · rw [hAdj, transpose_one, Matrix.mul_one, hiG, map_one_cc]
  · intro Y
    have h1 : (G⁻¹).map cc * Gᵀ = 1 := by rw [← hGt, ← map_mul_cc, hiG, map_one_cc]
    have h2 : (G⁻¹)ᵀ * Gᵀ = 1 := by rw [← transpose_mul, hGi, transpose_one]
    rw [hAdj, hAdj, map_mul_cc, map_mul_cc, hGt, ← transpose_map, map_map_cc, transpose_mul, transpose_mul,
      transpose_transpose]
    calc _ = ((G⁻¹).map cc * Gᵀ) * Y * (G⁻¹ᵀ * Gᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = Y := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
  · intro Y
    rw [hAdj, trace_map_cc, trace_mul_comm, ← Matrix.mul_assoc, hGi, Matrix.one_mul, trace_transpose]
  · intro Y
    have hadd : ∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = herm G u ((hAdj G Y + Y) *ᵥ w) := by
      intro u w
      rw [adj1, herm_eq_dot, herm_eq_dot, herm_eq_dot, ← dotProduct_add, ← mulVec_add]
      congr 2
      ext b; simp [add_mulVec, cc, map_add (f := _)]
    constructor
    · intro hs
      have hv : ∀ w, (hAdj G Y + Y) *ᵥ w = 0 := by
        intro w
        set v := (hAdj G Y + Y) *ᵥ w
        have h0 : ∀ u, herm G u v = 0 := fun u => by rw [← hadd]; exact hs u w
        have hGv : G *ᵥ (fun b => cc (v b)) = 0 := by
          ext i
          have := h0 (Pi.single i 1)
          rw [herm_eq_dot, single_dotProduct, one_mul] at this
          simpa using this
        have hcv : (fun b => cc (v b)) = 0 := by
          rw [← one_mulVec (fun b => cc (v b)), ← hiG, ← mulVec_mulVec, hGv, mulVec_zero]
        ext b
        have := congrFun hcv b
        simp only [Pi.zero_apply] at this
        rw [← cc_cc (v b), this]; simp [cc]
      have hA : hAdj G Y + Y = 0 := by
        ext i j
        have := congrFun (hv (Pi.single j 1)) i
        simpa [mulVec_single] using this
      exact eq_neg_of_add_eq_zero_left hA
    · intro h u w
      rw [hadd, h, neg_add_cancel, zero_mulVec]
      simp [herm, cc]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianGramDiagonalSignatureUnitary
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

noncomputable section
namespace GlobalTheory.SUCovolConj
open MeasureTheory Set
open scoped Pointwise

section General

variable {X : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X]

theorem isFundamentalDomain_conj (μ : Measure X) [μ.IsMulLeftInvariant] [SFinite μ]
    (H H' : Subgroup X) (s : X) (hH : ∀ g, g ∈ H' ↔ s⁻¹ * g * s ∈ H) {D : Set X}
    (hD : IsFundamentalDomain H D μ) :
    IsFundamentalDomain H' ((MulAut.conj s).toEquiv '' D) μ := by
  refine hD.image_of_equiv (MulAut.conj s).toEquiv ?_
    { toFun := fun g => ⟨s⁻¹ * g.1 * s, (hH g.1).1 g.2⟩
      invFun := fun g => ⟨s * g.1 * s⁻¹, (hH _).2 (by simpa [mul_assoc] using g.2)⟩
      left_inv := fun g => by ext; simp [mul_assoc]
      right_inv := fun g => by ext; simp [mul_assoc] } ?_
  · have : ((MulAut.conj s).toEquiv.symm : X → X) = (fun x => x * s) ∘ (fun x => s⁻¹ * x) := by
      funext x; simp [mul_assoc]
    rw [this]
    exact (quasiMeasurePreserving_mul_right μ s).comp
      (measurePreserving_mul_left μ s⁻¹).quasiMeasurePreserving
  · intro g x
    simp [Subgroup.smul_def, mul_assoc]

theorem covolume_conj (μ : Measure X) [μ.IsMulLeftInvariant] [SFinite μ]
    (H H' : Subgroup X) [Countable H] [Countable H'] (s : X)
    (hH : ∀ g, g ∈ H' ↔ s⁻¹ * g * s ∈ H) :
    covolume H' X μ = covolume H X μ := by
  have hH2 : ∀ g, g ∈ H ↔ s⁻¹⁻¹ * g * s⁻¹ ∈ H' := fun g => by rw [hH]; simp [mul_assoc]
  by_cases h : HasFundamentalDomain H X μ
  · obtain ⟨D, hD⟩ := h.ExistsIsFundamentalDomain
    have h1 := isFundamentalDomain_conj μ H H' s hH hD
    have h2 : IsFundamentalDomain H ((Equiv.mulRight s⁻¹) '' D) μ := by
      refine hD.image_of_equiv (Equiv.mulRight s⁻¹) ?_ (Equiv.refl _) ?_
      · have : ((Equiv.mulRight s⁻¹).symm : X → X) = fun x => x * s := by funext x; simp
        rw [this]; exact quasiMeasurePreserving_mul_right μ s
      · intro g x; simp [Subgroup.smul_def, mul_assoc]
    rw [h1.covolume_eq_volume, hD.covolume_eq_volume, hD.measure_eq h2]
    have : (MulAut.conj s).toEquiv '' D = s • ((Equiv.mulRight s⁻¹) '' D) := by
      rw [← Set.image_smul, Set.image_image]
      refine Set.image_congr fun y _ => ?_
      simp [mul_assoc]
    rw [this, measure_smul]
  · have h' : ¬ HasFundamentalDomain H' X μ := by
      rintro ⟨D, hD⟩; exact h ⟨_, isFundamentalDomain_conj μ H' H s⁻¹ hH2 hD⟩
    simp [covolume, h, h']

end General
section Concrete

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem gram_eq_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G M = Mᵀ * G.map τ * M.map (starRingEnd ℂ) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem det_gram (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ) :
    (gram τ G M).det = M.det * (G.map τ).det * starRingEnd ℂ M.det := by
  rw [gram_eq_mul, det_mul, det_mul, det_transpose, (starRingEnd ℂ).map_det M, RingHom.mapMatrix_apply]

theorem col_eq_mulVec (M : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    ReciprocityTheory.ChartRestriction.G.FD.col M a = M *ᵥ ReciprocityTheory.ChartRestriction.G.FD.col (1 : Matrix (Fin r) (Fin r) ℂ) a := by
  ext k; simp [ReciprocityTheory.ChartRestriction.G.FD.col, mulVec, dotProduct, Matrix.one_apply]

theorem hermC_map_of_herm (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (γ : Matrix (Fin r) (Fin r) E)
    (h2 : ∀ x y, herm G (γ *ᵥ x) (γ *ᵥ y) = herm G x y) (u w : Fin r → ℂ) :
    hermC τ G (γ.map τ *ᵥ u) (γ.map τ *ᵥ w) = hermC τ G u w := by
  have key (a b : Fin r) : ∑ c, ∑ d, τ (γ c a) * τ (G c d) * (starRingEnd ℂ) (τ (γ d b)) =
      τ (G a b) := by
    have h := congrArg τ (h2 (Pi.single a 1) (Pi.single b 1))
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [herm, cc, mulVec_single_one, Matrix.col_apply, map_sum, map_mul,
      IsCMField.complexEmbedding_complexConj] at h
    rw [h, Finset.sum_eq_single a (by intro c _ hc; simp [hc]) (by simp),
      Finset.sum_eq_single b (by intro c _ hc; simp [hc]) (by simp)]
    simp
  have hR : hermC τ G u w = ∑ a, ∑ b, u a *
      (∑ c, ∑ d, τ (γ c a) * τ (G c d) * (starRingEnd ℂ) (τ (γ d b))) * (starRingEnd ℂ) (w b) := by
    simp only [hermC, key]
  rw [hR]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hermC, mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, Finset.mul_sum,
    Finset.sum_mul]
  calc _ = ∑ c, ∑ d, ∑ a, ∑ b,
        u a * (τ (γ c a) * τ (G c d) * (starRingEnd ℂ) (τ (γ d b))) * (starRingEnd ℂ) (w b) := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    _ = _ := by
        refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans (Finset.sum_comm.trans ?_)
        refine Finset.sum_congr rfl fun a _ => ?_
        exact (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans Finset.sum_comm

theorem hermC_smul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (c : ℂ) (u w : Fin r → ℂ) :
    hermC τ G (c • u) (c • w) = c * starRingEnd ℂ c * hermC τ G u w := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem countable_inReal (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E)
    (Γ : Subgroup (GL (Fin r) E)) : Countable (inReal Ψ G Γ) := by
  haveI : Countable E :=
    Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  haveI : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
  haveI : Countable (GL (Fin r) E) :=
    Function.Injective.countable (f := (Units.val : GL (Fin r) E → _)) fun _ _ h => Units.ext h
  have : ((inReal Ψ G Γ : Subgroup (realSU Ψ G)) : Set (realSU Ψ G)).Countable := by
    refine ((Set.countable_range (embGL Ψ r)).preimage Subtype.val_injective).mono fun g hg => ?_
    obtain ⟨δ, -, hδ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hg)
    exact ⟨δ, hδ⟩
  exact this.to_subtype

end Concrete

theorem covolume_inReal_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (γ : GL (Fin r) E) (Δ : Subgroup (GL (Fin r) E)), (∀ a b, cc (G a b) = G b a) → (∀ τ : Ψ, gram τ.1 G (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) → (∀ u v, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm G u v) → covolume (inReal Ψ G (Δ.map (MulAut.conj γ).toMonoidHom)) (realSU Ψ G) (riemHaar Ψ G x) = covolume (inReal Ψ G Δ) (realSU Ψ G) (riemHaar Ψ G x) := by
  intro E _ _ _ r p0 Ψ G x γ Δ _hG hx hγ
  set A : Ψ → GL (Fin r) ℂ := embGL Ψ r γ with hAdef
  have hAv : ∀ τ : Ψ, ((A τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      (γ : Matrix (Fin r) (Fin r) E).map τ.1 := fun τ => rfl
  have hA : ∀ τ : Ψ, ∀ u w, hermC τ.1 G ((A τ : Matrix (Fin r) (Fin r) ℂ) *ᵥ u)
      ((A τ : Matrix (Fin r) (Fin r) ℂ) *ᵥ w) = hermC τ.1 G u w := by
    intro τ u w; rw [hAv]; exact hermC_map_of_herm τ.1 G _ hγ u w
  have hdet : ∀ τ : Ψ, (A τ : Matrix (Fin r) (Fin r) ℂ).det *
      starRingEnd ℂ (A τ : Matrix (Fin r) (Fin r) ℂ).det = 1 := by
    intro τ
    have hg : (G.map τ.1).det ≠ 0 := by
      intro h0
      have h1 := congrArg Matrix.det (hx τ)
      rw [det_gram, h0, mul_zero, zero_mul, det_diagonal] at h1
      refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h1.symm
      simp only [sgn]; split_ifs <;> norm_num
    have e1 : ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 G (A τ : Matrix (Fin r) (Fin r) ℂ) =
        ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 G 1 := by
      ext a b
      simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply]
      rw [col_eq_mulVec (A τ : Matrix (Fin r) (Fin r) ℂ) a, col_eq_mulVec (A τ : Matrix (Fin r) (Fin r) ℂ) b, hA]
    have h2 := congrArg Matrix.det e1
    rw [det_gram, det_gram, det_one, map_one, one_mul, mul_one] at h2
    apply mul_right_cancel₀ hg
    linear_combination h2
  have hroot : ∀ τ : Ψ, ∃ m : ℂ, m ^ r = (A τ : Matrix (Fin r) (Fin r) ℂ).det ∧ m * starRingEnd ℂ m = 1 := by
    intro τ
    rcases Nat.eq_zero_or_pos r with hr | hr
    · refine ⟨1, ?_, by simp⟩
      subst hr; simp
    · obtain ⟨m, hm⟩ := IsAlgClosed.exists_pow_nat_eq ((A τ : Matrix (Fin r) (Fin r) ℂ).det) hr
      refine ⟨m, hm, ?_⟩
      have h1 : (m * starRingEnd ℂ m) ^ r = 1 := by rw [mul_pow, ← map_pow, hm, hdet τ]
      rw [Complex.mul_conj] at h1 ⊢
      have h3 : (Complex.normSq m) ^ r = 1 := by exact_mod_cast h1
      rw [(pow_eq_one_iff_of_nonneg (Complex.normSq_nonneg m) hr.ne').1 h3]; simp
  choose m hm using hroot
  have hm0 : ∀ τ, m τ ≠ 0 := fun τ h => by simpa [h] using (hm τ).2
  let z : Ψ → GL (Fin r) ℂ := fun τ =>
    Units.map (algebraMap ℂ (Matrix (Fin r) (Fin r) ℂ)).toMonoidHom (Units.mk0 (m τ)⁻¹ (inv_ne_zero (hm0 τ)))
  have hzv : ∀ τ, ((z τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (m τ)⁻¹ • (1 : Matrix (Fin r) (Fin r) ℂ) := by
    intro τ; simp [z, Algebra.algebraMap_eq_smul_one]
  have hzc : ∀ g : Ψ → GL (Fin r) ℂ, z * g = g * z := by
    intro g; funext τ; ext1
    simp only [Pi.mul_apply, Units.val_mul, hzv, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
  have hs0 : A * z ∈ realSU Ψ G := by
    intro τ
    have e : (((A * z) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
        (m τ)⁻¹ • (A τ : Matrix (Fin r) (Fin r) ℂ) := by
      simp only [Pi.mul_apply, Units.val_mul, hzv, Matrix.mul_smul, mul_one]
    rw [e]
    refine ⟨?_, fun u w => ?_⟩
    · rw [det_smul, Fintype.card_fin, inv_pow, (hm τ).1]
      have : (A τ : Matrix (Fin r) (Fin r) ℂ).det ≠ 0 := fun h => by simpa [h] using hdet τ
      exact inv_mul_cancel₀ this
    · rw [Matrix.smul_mulVec, Matrix.smul_mulVec, hermC_smul, hA, map_inv₀, ← mul_inv,
        (hm τ).2, inv_one, one_mul]
  let s : realSU Ψ G := ⟨A * z, hs0⟩
  have hconj : ∀ g : Ψ → GL (Fin r) ℂ, (A * z)⁻¹ * g * (A * z) = A⁻¹ * g * A := by
    intro g
    calc (A * z)⁻¹ * g * (A * z) = z⁻¹ * (A⁻¹ * g * A) * z := by group
      _ = z⁻¹ * (z * (A⁻¹ * g * A)) := by rw [mul_assoc, ← hzc]
      _ = A⁻¹ * g * A := by group
  haveI := countable_inReal Ψ G Δ
  haveI := countable_inReal Ψ G (Δ.map (MulAut.conj γ).toMonoidHom)
  haveI : (riemHaar Ψ G x).IsMulLeftInvariant := by unfold riemHaar; infer_instance
  haveI : SFinite (riemHaar Ψ G x) := by unfold riemHaar tangentHaar; infer_instance
  have key : ∀ δ, embGL Ψ r ((MulAut.conj γ).toMonoidHom δ) = A * embGL Ψ r δ * A⁻¹ := by
    intro δ; simp [hAdef, MulAut.conj_apply, map_mul, map_inv]
  refine covolume_conj (riemHaar Ψ G x) _ _ s fun g => ?_
  simp only [inReal, Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hconj]
  constructor
  · rintro ⟨δ', ⟨δ, hδ, rfl⟩, h⟩
    refine ⟨δ, hδ, ?_⟩
    rw [← h, key]
    group
  · rintro ⟨δ, hδ, h⟩
    refine ⟨_, ⟨δ, hδ, rfl⟩, ?_⟩
    rw [key, h]
    group

end GlobalTheory.SUCovolConj
end
end

