module

public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.Bundle0001
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0036
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemma3
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047

@[expose] public section

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.NonzeroKFinite
section
open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.QuantumDeterminants

theorem nonzero_K_finite : Formalism.MainNotions.S.Pv.AmpDD.NzKF := by
  intro hKD hKS k r ε lam H _ _ _ σ w0 Wp _ _ z c π hlam hσ hw0 l hl hnz
  obtain ⟨x, hxDD, hlx⟩ := hnz
  have hxs : x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ :=
    Formalism.FourierDecayAlt.P.DDSmoothness.DD_smooth hKS hlam hσ hw0 x hxDD
  obtain ⟨hadd, hsmul, -, C, Ws, hWs, hbd⟩ := hl
  have hpos : 0 < ‖l x‖ := norm_pos_iff.mpr hlx
  set e : ℝ := ‖l x‖ / (|C| + 1) with he
  have he0 : 0 < e := div_pos hpos (by positivity)
  obtain ⟨v, hvK, hv⟩ := hKD k r ε lam H σ hlam hσ x hxs Ws hWs e he0
  refine ⟨v, hvK, fun hlv => ?_⟩
  have hvs : v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := hKS k r ε lam H σ hlam hσ v hvK
  have hdiff_s : x - v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ v]
    exact Formalism.FourierDecayAlt.P.DDSmoothness.smooth_add hxs (Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul (-1) hvs)
  have hsplit : l x = l (x - v) + l v := by
    have := hadd (x - v) hdiff_s v hvs
    rw [sub_add_cancel] at this
    exact this
  rw [hlv, add_zero] at hsplit
  have hb := hbd (x - v) hdiff_s
  set S := (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w (x - v)‖).sum with hS
  have hS0 : 0 ≤ S := by
    rw [hS]; apply List.sum_nonneg; intro y hy
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hy; exact norm_nonneg _
  have h1 : ‖l x‖ ≤ |C| * S := by
    rw [hsplit]; exact hb.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hS0)
  have h2 : |C| * S ≤ |C| * e := mul_le_mul_of_nonneg_left hv.le (abs_nonneg C)
  have h3 : |C| * e < ‖l x‖ := by
    rw [he, mul_div_assoc']
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg C]
  linarith

end Formalism.MainNotions.S.Pv.AmpDDPf
end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.RStabInv
section
open MeasureTheory Matrix

noncomputable section

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.QuantumDeterminants

theorem bsetting_of (k r : ℕ) (hk : 1 ≤ k) (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z ∧ 0 < Tz k r z)
    (hz' : inWb k r z' ∧ 0 < Tz k r z') :
    ∃ D : Formalism.FourierDecayAlt.B.RealPlaceData k r ℂ ℂ, D.z = z ∧ D.z' = z' := by
  obtain ⟨D, h1, h2, -, -, -⟩ := Formalism.FourierDecayAlt.P.setting_with_prescribed_data_exists k r ℂ ℂ z z'
    (fun _ => ContinuousLinearMap.id ℂ ℂ) (fun _ => ContinuousLinearMap.id ℂ ℂ) hk hz.1 hz'.1 hz.2 hz'.2
    ⟨rfl, fun _ _ _ _ => rfl⟩ ⟨rfl, fun _ _ _ _ => rfl⟩ (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    continuousOn_const continuousOn_const
  exact ⟨D, h1, h2⟩

theorem haarR_bi (k r : ℕ) (hk : 1 ≤ k) (L : Formalism.MainNotions.S.LocBessel k r)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR : Measure (Mt k r))
    (hγ : γ ∈ UH (Hpk k r)) (hmono : Formalism.FourierDecayAlt.C2.IsMonomial (Formalism.QuantumDeterminants.Zhat k r L.z L.z' γ))
    (hμ : Formalism.MainNotions.S.IsHaarOn (Formalism.MainNotions.S.RStab k r γ) μR) : Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.FourierDecayAlt.C6.Rset γ) μR := by
  obtain ⟨w, d, hd, hZ⟩ := hmono
  obtain ⟨D, hDz, hDz'⟩ := bsetting_of k r hk L.z L.z' L.hz L.hz'
  have hγG : γ ∈ Formalism.FourierDecayAlt.B.GV k r := hγ
  have hunit : IsUnit γ.det := (Formalism.FourierDecayAlt.P.unitary_group_closed k r).unit γ hγG
  have hcl := Formalism.FourierDecayAlt.P.Dx2.OrbJ.closedR (k := k) (r := r) hunit
  have hν := Formalism.FourierDecayAlt.P.radial_measure_is_haar k r ℂ ℂ D γ w d hγG hd (by rw [hDz, hDz']; exact hZ)
  exact Formalism.MainNotions.BridgeLemma₃.hu_general hcl hν hμ

theorem rStabInv_of_k (k r : ℕ) (hk : 1 ≤ k) (L : Formalism.MainNotions.S.LocBessel k r)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR : Measure (Mt k r))
    (hγ : γ ∈ UH (Hpk k r)) (hmono : Formalism.FourierDecayAlt.C2.IsMonomial (Formalism.QuantumDeterminants.Zhat k r L.z L.z' γ))
    (hμ : Formalism.MainNotions.S.IsHaarOn (Formalism.MainNotions.S.RStab k r γ) μR) :
    μR.map (fun x => fun i j => (Matrix.of x)⁻¹ i j) = μR := by
  obtain ⟨w, d, hd, hZ⟩ := hmono
  obtain ⟨D, hDz, hDz'⟩ := bsetting_of k r hk L.z L.z' L.hz L.hz'
  have hγG : γ ∈ Formalism.FourierDecayAlt.B.GV k r := hγ
  have hunit : IsUnit γ.det := (Formalism.FourierDecayAlt.P.unitary_group_closed k r).unit γ hγG
  have hcl := Formalism.FourierDecayAlt.P.Dx2.OrbJ.closedR (k := k) (r := r) hunit
  have hν := Formalism.FourierDecayAlt.P.radial_measure_is_haar k r ℂ ℂ D γ w d hγG hd (by rw [hDz, hDz']; exact hZ)
  have hμ' : Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.FourierDecayAlt.C6.Rset γ) μR := Formalism.MainNotions.BridgeLemma₃.hu_general hcl hν hμ
  exact Formalism.FourierDecayAlt.P.haar_measure_inversion k r _ μR hcl hμ'

theorem right_stabilizer_invariance : Formalism.MainNotions.S.Pv.AmpDD.RStabInv := by
  intro k r L γ μR hk hγ _ _ hmono hμ
  exact rStabInv_of_k k r hk L γ μR hγ hmono hμ

end Formalism.MainNotions.S.Pv.AmpDDPf
end
end

