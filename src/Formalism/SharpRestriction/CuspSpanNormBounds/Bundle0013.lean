module

public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0012
public import Formalism.FlagUnipotentLattices.ArithmeticIdentityEntries
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0009
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.WeylBridge
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.BigCellDensity

@[expose] public section

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemVC
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemVC

open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne Formalism.MainNotions.BridgeLemVR nonZeroDivisors

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem isFrac {M : Submodule (𝓞 K) K} (hM : Submodule.IsFullLattice K M) : IsFractional (𝓞 K)⁰ M :=
  FractionalIdeal.isFractional_of_fg hM.toIsLattice.fg

def fracI {M : Submodule (𝓞 K) K} (hM : Submodule.IsFullLattice K M) : FractionalIdeal (𝓞 K)⁰ K :=
  ⟨M, isFrac hM⟩

theorem coe_fracI {M : Submodule (𝓞 K) K} (hM : Submodule.IsFullLattice K M) :
    ((fracI hM : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) = M :=
  FractionalIdeal.coeToSubmodule_mk _ _

theorem frac_ne_zero {M : Submodule (𝓞 K) K} (hM : Submodule.IsFullLattice K M) : fracI hM ≠ 0 := by
  obtain ⟨a, ha, h0⟩ := exists_ne_zero_of_isLattice hM
  intro e
  have h1 : a ∈ fracI hM := by rw [← FractionalIdeal.mem_coeToSubmodule, coe_fracI]; exact ha
  rw [e] at h1
  exact h0 ((FractionalIdeal.mem_zero_iff _).1 h1)

def fracU {M : Submodule (𝓞 K) K} (hM : Submodule.IsFullLattice K M) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 _ (frac_ne_zero hM)

theorem coe_fracU {M : Submodule (𝓞 K) K} (hM : Submodule.IsFullLattice K M) :
    (((fracU hM : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) = M :=
  coe_fracI hM

theorem exists_eq_span_mul {M M' : Submodule (𝓞 K) K} (hM : Submodule.IsFullLattice K M)
    (hM' : Submodule.IsFullLattice K M')
    (he : ClassGroup.mk K (fracU hM) = ClassGroup.mk K (fracU hM')) :
    ∃ a : K, a ≠ 0 ∧ M = Submodule.span (𝓞 K) {a} * M' := by
  have h1 : ClassGroup.mk K (fracU hM * (fracU hM')⁻¹) = 1 := by
    rw [map_mul, map_inv, he, mul_inv_cancel]
  rw [ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨⟨a, ha⟩⟩ := h1
  have hMa : M = Submodule.span (𝓞 K) {a} * M' := by
    calc M = (((fracU hM * (fracU hM')⁻¹ * fracU hM' : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
          FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by rw [inv_mul_cancel_right, coe_fracU]
      _ = Submodule.span (𝓞 K) {a} * M' := by
          rw [Units.val_mul, FractionalIdeal.coeToSubmodule_mul, ha, coe_fracU]
  refine ⟨a, fun h0 => ?_, hMa⟩
  obtain ⟨x, hx, hx0⟩ := exists_ne_zero_of_isLattice hM
  rw [hMa, h0, Submodule.mem_span_singleton_mul] at hx
  obtain ⟨y, -, hy⟩ := hx
  rw [zero_mul] at hy
  exact hx0 hy.symm

theorem exists_unitF {u : K} (hu0 : u ≠ 0) (hu : u ∈ (1 : Submodule (𝓞 K) K))
    (hu' : u⁻¹ ∈ (1 : Submodule (𝓞 K) K)) (hs : star u = u) :
    ∃ t : (𝓞 (cmF K))ˣ, (((t : 𝓞 (cmF K)) : cmF K) : K) = u := by
  have intF : ∀ x : cmF K, (x : K) ∈ (1 : Submodule (𝓞 K) K) → IsIntegral ℤ x := by
    intro x hx
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 hx
    have hK : IsIntegral ℤ (x : K) := by rw [← hr]; exact RingOfIntegers.isIntegral_coe r
    exact (isIntegral_algHom_iff ((cmF K).val.toRingHom.toIntAlgHom) Subtype.val_injective).1 hK
  have hs' : star u⁻¹ = u⁻¹ := by rw [star_inv₀, hs]
  let x : cmF K := ⟨u, (mem_cmF_iff K u).2 hs⟩
  let y : cmF K := ⟨u⁻¹, (mem_cmF_iff K _).2 hs'⟩
  let t0 : 𝓞 (cmF K) := ⟨x, intF x hu⟩
  let t1 : 𝓞 (cmF K) := ⟨y, intF y hu'⟩
  have hxy : t0 * t1 = 1 := by
    apply RingOfIntegers.ext
    apply Subtype.ext
    show u * u⁻¹ = 1
    exact mul_inv_cancel₀ hu0
  exact ⟨⟨t0, t1, hxy, by rw [mul_comm]; exact hxy⟩, rfl⟩

def iota (K : Type) [Field K] [NumberField K] [StarRing K] : (𝓞 (cmF K))ˣ →* K :=
  ((cmF K).val.toRingHom.comp (algebraMap (𝓞 (cmF K)) (cmF K))).toMonoidHom.comp (Units.coeHom _)

theorem exists_unitK (v : (𝓞 (cmF K))ˣ) : ∃ w : (𝓞 K)ˣ, algebraMap (𝓞 K) K (w : 𝓞 K) = iota K v :=
  ⟨Units.map (RingOfIntegers.mapRingHom ((cmF K).val.toRingHom)).toMonoidHom v, rfl⟩

theorem gmap_smul {b : K} (hb : b ≠ 0) (N : Submodule (𝓞 K) K) :
    gmap (LinearEquiv.smulOfNeZero K K b hb) N = Submodule.span (𝓞 K) {b} * N := by
  ext y
  rw [mem_gmap, Submodule.mem_span_singleton_mul]
  have hs : ∀ z, (LinearEquiv.smulOfNeZero K K b hb).symm z = b⁻¹ * z := fun z => rfl
  constructor
  · intro hy
    refine ⟨b⁻¹ * y, by rw [← hs]; exact hy, ?_⟩
    rw [← mul_assoc, mul_inv_cancel₀ hb, one_mul]
  · rintro ⟨n, hn, rfl⟩
    rw [hs, ← mul_assoc, inv_mul_cancel₀ hb, one_mul]
    exact hn

theorem gmap_one (N : Submodule (𝓞 K) K) : gmap (1 : K ≃ₗ[K] K) N = N := by
  ext y
  rw [mem_gmap]
  rfl

theorem span_unit_mul (w : (𝓞 K)ˣ) (N : Submodule (𝓞 K) K) :
    Submodule.span (𝓞 K) {algebraMap (𝓞 K) K (w : 𝓞 K)} * N = N := by
  ext y
  rw [Submodule.mem_span_singleton_mul]
  constructor
  · rintro ⟨n, hn, rfl⟩
    rw [← Algebra.smul_def]
    exact N.smul_mem _ hn
  · intro hy
    refine ⟨((w⁻¹ : (𝓞 K)ˣ) : 𝓞 K) • y, N.smul_mem _ hy, ?_⟩
    rw [Algebra.smul_def, ← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]

end Formalism.MainNotions.BridgeLemVC

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BridgeWeylDS
section

end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceExpansion
section
noncomputable section

namespace Formalism.MainNotions.OnePlaceExpansion

open MeasureTheory Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.BesselShellMomentBounds

section OnePl

variable (D : D7)

variable {D}

end OnePl

section ThmB

variable {D : D7}

end ThmB

section Frames


open Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.MainNotions.OnePlaceEstimates in
theorem frame_bound_of_bessel_torus (D : D7) (Cgf Cf : ℝ) (hCf : 2 ≤ Cf) (hOB : OneBesselTor D Cgf) :
    Formalism.MainNotions.OnePlaceEstimates.FrameBesselBound D Cgf Cf := by
  intro L f κ₀ κ τ hκ₀ hκ hτ hc hκN hκNt hε hgap hf
  obtain ⟨f₁, C, hC, hf₁, hJ, hO⟩ := hOB L f κ₀ κ τ hκ₀ hκ hτ hc hκN hκNt hε hgap hf
  have hk2 : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hk1 : 1 ≤ D.R.k := by omega
  have hCpos : 0 < ‖C‖ := norm_pos_iff.mpr hC
  have e1 : Tz D.R.k D.R.rS (trDat L κ τ hκ hτ).z = τ ^ 2 * Tz D.R.k D.R.rS L.z := Tz_smul _ _
  have e2 : Tz D.R.k D.R.rS (trDat L κ τ hκ hτ).z' = τ ^ 2 * Tz D.R.k D.R.rS L.z' := Tz_smul _ _
  refine ⟨trDat L κ τ hκ hτ, f₁, rfl, rfl, rfl, rfl, ?_, ?_, ?_, e1, e2, hf₁, ?_⟩
  · show (κ : ℂ) * L.c = _
    rw [hc]; unfold cOfDpsi; push_cast; ring
  · show 0 < L.κN * ENNReal.ofReal (deltaN D.R.k D.R.rS κ τ)
    exact ENNReal.mul_pos hκN.ne' (ENNReal.ofReal_pos.mpr (deltaN_pos hκ hτ)).ne'
  · show L.κN * ENNReal.ofReal (deltaN D.R.k D.R.rS κ τ) ≠ ⊤
    exact ENNReal.mul_ne_top hκNt ENNReal.ofReal_ne_top
  intro μsec hsec
  refine ⟨secTr τ μsec, isSection_tr hτ hsec, jacBig D.R.rS κ τ * wBig D.R.k D.R.rS κ τ * ‖C‖ ^ 2,
    mul_pos (mul_pos (jacBig_pos hκ hτ) (wBig_pos hκ hτ)) (pow_pos hCpos 2), ?_, ?_⟩
  · refine jNorm2_tr hκ hτ L (trDat L κ τ hκ hτ) e1 e2 f f₁ μsec (secTr τ μsec) C hk2 fun p hp hζ => ?_
    rw [secTr_sBig hτ]
    have hb : bigCell D.R.k D.R.rS (sBig D.R.rS κ τ p).1 (μsec p.2) =
        cj D.R.k D.R.rS κ τ (bigCell D.R.k D.R.rS p.1 (μsec p.2)) := by
      rw [bigCell_cj hκ hτ]; rfl
    rw [hb]
    show @hsNormSq L.Wp L.Wq _ _ _ _ _
      ((trDat L κ τ hκ hτ).J f₁ (cj D.R.k D.R.rS κ τ (bigCell D.R.k D.R.rS p.1 (μsec p.2)))) = _
    rw [J_trD hκ hτ L, hJ p.1 (μsec p.2) hp (hsec.2 p.2 hζ).1, Formalism.MainNotions.FrameBoundFromBesselTorus.hsNormSq_smul]
  · intro γ hG
    refine ⟨ptTr κ τ hκ hτ γ, rfl, ?_, ?_⟩
    · rw [e1, e2, GPoint_ptTr]
    · rw [e1, e2, orbSq_trDat hκ hτ L f f₁ γ C fun g μR ν h1 h2 h3 h4 => hO γ g μR ν hG h1 h2 h3 h4]
      have hα := alphaPt_pos hκ hτ γ
      have hw := ptWeight_ptTr hk1 hκ hτ (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ
      have hcard := card_rootPat_le γ
      refine frames_ineqs (orbSq L f γ) (by positivity)
        (mul_pos (mul_pos (jacBig_pos hκ hτ) (wBig_pos hκ hτ)) (pow_pos hCpos 2)).le (inv_pos.mpr (by positivity))
        (ratio_le_frameFactor hκ hτ hCf hcard) (by rw [inv_inv]; exact ratio_inv_le_frameFactor hκ hτ hCf hcard) ?_
      have hP : 0 < κ ^ (2 * (rootPat γ).card) := pow_pos hκ _
      have hpw : ptWeight D.R.k D.R.rS (τ ^ 2 * Tz D.R.k D.R.rS L.z) (τ ^ 2 * Tz D.R.k D.R.rS L.z')
          (ptTr κ τ hκ hτ γ) = Wbig D.R.k D.R.rS κ τ * alphaPt κ τ γ ^ 2 *
            ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ / κ ^ (2 * (rootPat γ).card) := by
        rw [eq_div_iff hP.ne']; exact hw
      rw [hpw, wBig_eq_Wbig hk1, jacBig_eq, pow_add]
      field_simp

end Frames

end Formalism.MainNotions.OnePlaceExpansion
end
end

