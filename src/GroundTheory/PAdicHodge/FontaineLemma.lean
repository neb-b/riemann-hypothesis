module

public import Mathlib
public import GroundTheory.PAdicHodge.FontaineLemmaPhi
public import GroundTheory.PAdicHodge.FontaineLemmaPeriod

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open _root_.WittVector

namespace ACris

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]

local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θdR" => IsPerfectoidField.thetaBDeRhamPlusField (K := K) p

theorem iterate_phiPlus_algebraMap (n : ℕ) (x : ACris K p) :
    (phiPlus K p)^[n] (algebraMap (ACris K p) (BCrisPlus K p) x) =
      algebraMap (ACris K p) (BCrisPlus K p) ((phi (K := K) (p := p))^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, phiPlus_algebraMap, Function.iterate_succ_apply']

theorem thetaField_iotaPlus_algebraMap (x : ACris K p) :
    θdR (iotaPlus K p (algebraMap (ACris K p) (BCrisPlus K p) x)) = (theta K p x : K) := by
  rw [iotaPlus_algebraMap, thetaField_iota]

theorem theta_phi_iterate_eq_zero_of_mul_eq {y : BCrisPlus K p} {a : ACris K p} {k : ℕ}
    (hya : y * algebraMap (ACris K p) (BCrisPlus K p) ((p : ACris K p) ^ k) =
      algebraMap (ACris K p) (BCrisPlus K p) a)
    (hy : ∀ n : ℕ, θdR (iotaPlus K p ((phiPlus K p)^[n] y)) = 0) (n : ℕ) :
    theta K p ((phi (K := K) (p := p))^[n] a) = 0 := by
  apply Subtype.ext
  rw [ZeroMemClass.coe_zero, ← thetaField_iotaPlus_algebraMap, ← iterate_phiPlus_algebraMap, ← hya,
    ← RingHom.coe_pow, map_mul, map_mul, map_mul, RingHom.coe_pow, hy n, zero_mul]


set_option maxHeartbeats 1600000 in
theorem phiPlus_mem_span_periodT {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) {y : BCrisPlus K p}
    (hy : ∀ n : ℕ, θdR (iotaPlus K p ((phiPlus K p)^[n] y)) = 0) :
    phiPlus K p y ∈ Ideal.span {algebraMap (ACris K p) (BCrisPlus K p) (periodT hε)} := by
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (p : ACris K p)) y
  obtain ⟨k, hk⟩ := s.2
  simp only at hs
  rw [← hk] at hs
  have ha := theta_phi_iterate_eq_zero_of_mul_eq hs hy

  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (p_mul_phi_mem_span_mu hε hζ ha)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (mu_mem_span_periodT (K := K) hε hζ)
  have hpa : (p : ACris K p) * phi (K := K) (p := p) a = periodT hε * (c * w) := by
    rw [← hw, ← hc]; ring

  have h1 := congrArg (phiPlus K p) hs
  rw [map_mul, phiPlus_algebraMap, phiPlus_algebraMap, map_pow, map_natCast] at h1
  have hu : IsUnit (algebraMap (ACris K p) (BCrisPlus K p) ((p : ACris K p) ^ (k + 1))) :=
    IsLocalization.map_units (BCrisPlus K p)
      (⟨(p : ACris K p) ^ (k + 1), k + 1, rfl⟩ : Submonoid.powers (p : ACris K p))
  rw [Ideal.mem_span_singleton']
  refine ⟨algebraMap (ACris K p) (BCrisPlus K p) (c * w) * ↑hu.unit⁻¹, ?_⟩
  have h2 : phiPlus K p y * algebraMap (ACris K p) (BCrisPlus K p) ((p : ACris K p) ^ (k + 1)) =
      algebraMap (ACris K p) (BCrisPlus K p) (periodT hε) *
        algebraMap (ACris K p) (BCrisPlus K p) (c * w) := by
    rw [pow_succ, map_mul, ← mul_assoc, h1, ← map_mul, mul_comm (phi (K := K) (p := p) a), hpa, map_mul]
  calc algebraMap (ACris K p) (BCrisPlus K p) (c * w) * ↑hu.unit⁻¹ *
        algebraMap (ACris K p) (BCrisPlus K p) (periodT hε)
      = phiPlus K p y * algebraMap (ACris K p) (BCrisPlus K p) ((p : ACris K p) ^ (k + 1)) *
          ↑hu.unit⁻¹ := by rw [h2]; ring
    _ = phiPlus K p y := by rw [mul_assoc, IsUnit.mul_val_inv, mul_one]

end ACris

end GroundTheory.PAdicHodge
