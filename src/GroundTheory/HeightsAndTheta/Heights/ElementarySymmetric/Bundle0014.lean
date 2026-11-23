module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0035
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0034
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0055
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartBergmanBound
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0047
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIntegralOfBergman
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBergmanIntegrable
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBergmanDensIntegrable
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0023

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.BergmanLerpSelf
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

noncomputable section

lemma bergman_lerp_self {D : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    {A : FinHolAtlas D X} {L : HolLineBundle A} (W : Weight L) (t : ℝ) (dV : SmoothVolume A)
    (V : Submodule ℂ (Fin A.n → X → ℂ)) (n : ℕ) (x : X) :
    bergman (W.lerp W t) dV V n x = bergman W dV V n x := by
  simp only [bergman, sectionL2NormSq, ptNormSq, lerp_self_φ]

lemma bergman_nonneg {D : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    {A : FinHolAtlas D X} {L : HolLineBundle A} (W : Weight L) (dV : SmoothVolume A)
    (V : Submodule ℂ (Fin A.n → X → ℂ)) (n : ℕ) (x : X) : 0 ≤ bergman W dV V n x :=
  Real.iSup_nonneg fun _ => div_nonneg (ptNormSq_nonneg W n _ x) (sectionL2NormSq_nonneg W dV n _)

theorem BergmanL1Convergence.proof (hL1 : L1Convergence.Statement)
    (hLoc : LocalBergmanBound.Statement) (hUnif : UniformBergmanBound.Statement)
    (hInt : IntegralOfBergman.Statement) (hBI : BergmanIntegrable.Statement)
    (hDI : BergmanDensIntegrable.Statement) : BergmanL1Convergence.Statement := by
  intro D X _ _ _ _ _ A L W dV hW V _ hV hdim
  have := dV.isProb
  obtain ⟨C, hC⟩ := hUnif A L W W dV hW hW
  have hpos : ∀ n : ℕ, (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ D := fun n => by positivity
  set g : ℕ → X → ℝ := fun n x =>
    (((n + 1 : ℕ) : ℝ) ^ D)⁻¹ * bergman W dV (V (n + 1)) (n + 1) x with hg
  have hbound : ∀ n x, 0 ≤ g n x ∧ g n x ≤ C := fun n x => by
    refine ⟨mul_nonneg (inv_nonneg.2 (hpos n).le) (bergman_nonneg _ _ _ _ _), ?_⟩
    have h := hC (n + 1) (by omega) 0 ⟨le_rfl, zero_le_one⟩ (V (n + 1)) (hV _) x
    rw [bergman_lerp_self] at h
    show (((n + 1 : ℕ) : ℝ) ^ D)⁻¹ * bergman W dV (V (n + 1)) (n + 1) x ≤ C
    rw [inv_mul_le_iff₀ (hpos n)]
    linarith [mul_comm C (((n + 1 : ℕ) : ℝ) ^ D)]
  have hlim : ∀ (x : X) (ε : ℝ), 0 < ε → ∀ᶠ n in atTop, g n x ≤ bergmanDens W dV x + ε := by
    intro x ε hε
    have h := (tendsto_add_atTop_nat 1).eventually (hLoc A L W dV hW V hV x ε hε)
    filter_upwards [h] with n hn
    show (((n + 1 : ℕ) : ℝ) ^ D)⁻¹ * bergman W dV (V (n + 1)) (n + 1) x ≤ _
    rw [inv_mul_le_iff₀ (hpos n)]
    linarith [mul_comm (bergmanDens W dV x + ε) (((n + 1 : ℕ) : ℝ) ^ D)]
  have hmass : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∫ x, bergmanDens W dV x ∂dV.μ - ε ≤ ∫ x, g n x ∂dV.μ := by
    intro ε hε
    have h := (tendsto_add_atTop_nat 1).eventually (hdim ε hε)
    filter_upwards [h] with n hn
    have hI : ∫ x, g n x ∂dV.μ =
        (((n + 1 : ℕ) : ℝ) ^ D)⁻¹ * Module.finrank ℂ (V (n + 1)) := by
      rw [hg, integral_const_mul, hInt A L W dV (n + 1) (V (n + 1)) (hV _)]
    rw [hI, le_inv_mul_iff₀ (hpos n)]
    linarith [mul_comm (∫ x, bergmanDens W dV x ∂dV.μ - ε) (((n + 1 : ℕ) : ℝ) ^ D)]
  have hgi : ∀ n, Integrable (g n) dV.μ := fun n =>
    (hBI A L W dV (n + 1) (V (n + 1)) (hV _)).const_mul _
  have h := hL1 dV.μ g (bergmanDens W dV) C hgi (hDI A L W dV) hbound hlim hmass
  exact (tendsto_add_atTop_iff_nat 1).1 h

theorem BergmanL1Convergence.full : BergmanL1Convergence.Statement :=
  BergmanL1Convergence.proof L1Convergence.proof
    (LocalBergmanBound.proof (ChartBergmanBound.proof PolydiscSubmean.proof ComplexTaylorTwo.proof))
    (UniformBergmanBound.proof PolydiscSubmean.proof ChartTaylorCover.proof)
    IntegralOfBergman.proof BergmanIntegrable.proof BergmanDensIntegrable.proof

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PAmpleCountAlongMultiplesX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

theorem AmpleCountAlongMultiples.statementB (hBig : NefBigCountAlongMultiples.Statement) (hPk : PackingStatement) :
    G6.StatementB := by
  intro K _ ι _ Ω _ _ y D M P0 II hD hII har hb hM
  obtain ⟨-, Cp, hCp⟩ := hPk K ι Ω y D M (chartLat y M.a) har hb hM.semipos.1
    (fun τ _ hs' c hc' => isIntegral_algebraMap (x := (⟨_, hs' c hc'⟩ : chartRingZ y c)))
  exact NefCountAlongMultiples.le_arithmeticVolume_of_alongMultiples hCp fun ε hε => hBig K ι Ω y D M P0 II hD hII har hb hM ε hε

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PNefBigCountAlongMultiples
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

namespace NefBigCountAlongMultiples

theorem two_zcomb_sub_one {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (M : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    (q k : ℕ) (hkq : k < q) :
    ((2 : ℕ) • (HermLine.zcomb M (fsH ι) ((q : ℤ) - k * ((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ)).a - fun _ => (1 : ℤ)) =
      ((2 * (q - k) : ℕ) : ℤ) • M.a + fun _ => ((1 : ℕ) : ℤ) := by
  funext j
  have hfs : (fsH ι).a j = 1 := rfl
  simp only [HermLine.zcomb, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hfs]
  rw [Nat.cast_mul, Nat.cast_sub hkq.le]
  push_cast
  ring

theorem along_of_shift (hAC : AmpleCountAlongMultiples.StatementAmple) (hGD : GenDegGeomDeg.Statement)
    (hPk : PackingStatement)
    {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {D : ℕ} {A N : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    {P0 : Ideal (MRing ι)} {II : IntersectionSystem} {e : Ω} {C T ε : ℝ} {p q : ℕ}
    (hD : 1 ≤ D) (hII : IsIntersectionSystem II) (har : IsArithVar (mCoordIdeal y) (D + 1)) (hb : Birational y)
    (hP0 : P0 ≤ mCoordIdeal y) (hsA : IsSmoothHerm A) (hq : 1 ≤ q) (hε : 0 < ε)
    (hsp : IsSemipositiveRel P0 (mCoordIdeal y) N) (hci : IsConjInvariantH N)
    (hamp : KH.AmpleV ℚ (KH.genIdeal y) N.a)
    (hamp2 : ∃ c : ℕ, 1 ≤ c ∧ KH.AmpleV ℚ (KH.genIdeal y) (c • N.a - fun _ => 1))
    (hampl : ∀ ℓ : ℕ, ℓ.Prime → KH.AmpleV (ZMod ℓ) (GroundTheory.Heights₂.Heights.HilbertSamuel.fibreIdeal ℓ y) N.a) (he0 : e ≠ 0)
    (hmap : ∀ (n : ℕ) (s : Ω), s ∈ chartLat y N.a n → s * e ^ (p * n) ∈ chartLat y A.a (q * n) ∧
      ∀ c : ℝ, IsBoundedH (mCoordIdeal y) y N n c s →
        IsBoundedH (mCoordIdeal y) y A (q * n) (c * Real.exp (((p * n : ℕ) : ℝ) * C)) (s * e ^ (p * n)))
    (hnum : (T - ε) * (q : ℝ) ^ (D + 1) + ε / 4 * (q : ℝ) ^ (D + 1) ≤
      II K ι (mCoordIdeal y) (D + 1) (fun _ => N) -
        ((D : ℝ) + 1) * ((p : ℝ) * C) * (genDeg (mCoordIdeal y) D N.a : ℝ)) :
    ∃ a : ℕ, 1 ≤ a ∧ ∀ᶠ k : ℕ in atTop,
      (T - ε) * (((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) ≤
        smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) (a * k) := by
  obtain ⟨b, hb1, hev⟩ := hAC K ι Ω y D (HermLine.constShift N ((p : ℝ) * C)) P0 II hD hII har hb hP0
    (isSemipositiveRel_constShift hsp _) (isConjInvariantH_constShift hci _)
    (by rw [constShift_a]; exact hamp) (by rw [constShift_a]; exact hamp2) (by rw [constShift_a]; exact hampl)
    (ε / 4 * (q : ℝ) ^ (D + 1)) (by positivity)
  have htop : II K ι (mCoordIdeal y) (D + 1) (fun _ => HermLine.constShift N ((p : ℝ) * C)) =
      II K ι (mCoordIdeal y) (D + 1) (fun _ => N) -
        ((D : ℝ) + 1) * ((p : ℝ) * C) * (genDeg (mCoordIdeal y) D N.a : ℝ) := by
    rw [ConstantShift.proof K ι (II K ι) (mCoordIdeal y) D N _ (hII K ι) har hsp.1, hGD K ι Ω y D N har hsp.1]
  have hfin := (hPk K ι Ω y D A (chartLat y A.a) har hb hsA
    (fun τ _ hs' c hc' => isIntegral_algebraMap (x := (⟨_, hs' c hc'⟩ : chartRingZ y c)))).1
  refine ⟨q * b, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
  filter_upwards [hev] with j hj
  have hX : (0 : ℝ) ≤ ((b * j : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := by positivity
  calc (T - ε) * (((q * b * j : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))
      = ((T - ε) * (q : ℝ) ^ (D + 1)) * (((b * j : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
        push_cast
        ring
    _ ≤ (II K ι (mCoordIdeal y) (D + 1) (fun _ => HermLine.constShift N ((p : ℝ) * C)) -
          ε / 4 * (q : ℝ) ^ (D + 1)) * (((b * j : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_right (by rw [htop]; linarith) hX
    _ ≤ _ := hj
    _ ≤ smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) (q * (b * j)) :=
        NefCountAlongMultiples.count_shift_le he0 (hmap (b * j)) (hfin _)
    _ = _ := by rw [mul_assoc]

theorem proof (hG2 : G2.Statement) (hAC : AmpleCountAlongMultiples.StatementAmple)
    (hNA : NefAmpleGeneric.Statement) (hGD : GenDegGeomDeg.Statement) (hPk : PackingStatement) :
    NefBigCountAlongMultiples.Statement := by
  intro K _ ι _ Ω _ y D A P0 II hD hII har hb hA ε hε
  have : CharZero Ω := ArithmeticVolumeDegreeZero.charZero_of_horizontal y har.2.2.1
  let _ : LinearOrder K := LinearOrder.lift' _ (Fintype.equivFin K).injective
  let _ : ∀ k, LinearOrder (ι k) := fun k => LinearOrder.lift' _ (Fintype.equivFin (ι k)).injective
  obtain ⟨k, e, C, -, hC, he0, -, -, hpq, hconv⟩ := hG2 K ι Ω y D A P0 II hD hII har hb hA
  obtain ⟨δ, hδ, hδc⟩ := hconv (ε / 4) (by linarith)
  have hg0 : (0 : ℝ) < (genDeg (mCoordIdeal y) D A.a : ℝ) := by exact_mod_cast hA.big
  obtain ⟨q, hq⟩ := exists_nat_gt ((k : ℝ) + 1 / δ +
    4 * (((D : ℝ) + 1) * C * ((genDeg (mCoordIdeal y) D A.a : ℝ) + ε / 4)) / ε)
  have hX0 : 0 ≤ 4 * (((D : ℝ) + 1) * C * ((genDeg (mCoordIdeal y) D A.a : ℝ) + ε / 4)) / ε := by
    positivity
  have hδ' : 0 < 1 / δ := by positivity
  have hkq : k * 1 < q := by
    have : (k : ℝ) < q := by linarith
    rw [mul_one]
    exact_mod_cast this
  have hq1 : 1 ≤ q := by omega
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  have hpqδ : ((1 : ℕ) : ℝ) / q < δ := by
    have h1 : 1 / δ < q := by linarith
    rw [div_lt_iff₀ hδ] at h1
    rw [Nat.cast_one, div_lt_iff₀ hqpos]
    linarith
  have hqC : ((D : ℝ) + 1) * C * ((genDeg (mCoordIdeal y) D A.a : ℝ) + ε / 4) < q * (ε / 4) := by
    have h1 : 4 * (((D : ℝ) + 1) * C * ((genDeg (mCoordIdeal y) D A.a : ℝ) + ε / 4)) / ε < q := by linarith
    rw [div_lt_iff₀ hε] at h1
    linarith
  obtain ⟨hsp, hci, hamp, hampl, hmap⟩ := hpq 1 q one_pos hkq
  obtain ⟨htop, hdeg⟩ := hδc 1 q one_pos (by omega) hpqδ
  have hamp2 : ∃ c : ℕ, 1 ≤ c ∧ KH.AmpleV ℚ (KH.genIdeal y)
      (c • (HermLine.zcomb A (fsH ι) ((q : ℤ) - k * ((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ)).a - fun _ => 1) := by
    refine ⟨2, by norm_num, ?_⟩
    rw [two_zcomb_sub_one A q k (by omega)]
    exact hNA K ι Ω y D A P0 (2 * (q - k)) 1 har hA.normalForm_baseLattice_le_dualSpan_sup_line hA.semipos (by omega) le_rfl
  exact along_of_shift hAC hGD hPk hD hII har hb hA.normalForm_baseLattice_le_dualSpan_sup_line hA.semipos.1 hq1 hε hsp hci hamp hamp2 hampl he0 hmap
    (NefCountAlongMultiples.num_bound hε hqpos hC htop hdeg hqC)

end NefBigCountAlongMultiples

end

end GroundTheory.Heights₂.Heights.Targets
end

