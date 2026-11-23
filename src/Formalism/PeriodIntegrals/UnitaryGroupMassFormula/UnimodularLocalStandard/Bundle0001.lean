module

public import Formalism.PeriodIntegrals.Bundle0008

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.Development
section
noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

def StepB : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a b c d →
    ∀ (m : Type) [Fintype m] [DecidableEq m] (Λa : AddSubgroup (m → ℂ)),
      IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λa →
      (∀ x ∈ Λa, cmTheta b d • x ∈ Λa) →
      relIdx (stdLat (cmL a b d ha hd lam hlam) m) Λa ≠ 0 →
      relIdx Λa (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0 →
      ∀ l : ℕ, l.Prime → ∃ g : (m → ℂ) ≃ₗ[ℂ] (m → ℂ),
        IsIsom (stdH (cmL a b d ha hd lam hlam) m) (stdH (cmL a b d ha hd lam hlam) m)
          (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) ∧
        relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) ≠ 0 ∧
        ¬ l ∣ relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) ∧
        relIdx (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0

def StepC : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a b c d →
    ∀ (m : Type) [Fintype m] [DecidableEq m] (Λa : AddSubgroup (m → ℂ)) (g : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)),
      (∀ x ∈ Λa, cmTheta b d • x ∈ Λa) →
      ∀ l : ℕ, l.Prime →
      IsIsom (stdH (cmL a b d ha hd lam hlam) m) (stdH (cmL a b d ha hd lam hlam) m)
          (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) →
        relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) ≠ 0 →
        ¬ l ∣ relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) →
        relIdx (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0 →
      ∃ δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ),
        IsIsom (stdH (cmL a b d ha hd lam hlam) m) (stdH (cmL a b d ha hd lam hlam) m)
          (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) ∧ (∀ x, δ x = x → x = 0) ∧
        relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) ≠ 0 ∧
        ¬ l ∣ relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) ∧
        relIdx (imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0

theorem target_of (hB : StepB) (hC : StepC) : PI.UnimodLocStd := by
  intro a b c d ha hd lam hlam hok m _ _ Λa hsd hθ h1 h2 l hl
  obtain ⟨g, hg, g1, g2, g3⟩ := hB a b c d ha hd lam hlam hok m Λa hsd hθ h1 h2 l hl
  exact hC a b c d ha hd lam hlam hok m Λa g hθ l hl hg g1 g2 g3

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.KeyDef
section
noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

def SatMem {m : Type*} (l : ℕ) (Λ : AddSubgroup (m → ℂ)) (x : m → ℂ) : Prop := ∃ n : ℕ, ¬ l ∣ n ∧ n • x ∈ Λ

def KeyRep : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a b c d →
    ∀ (m : Type) [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)),
      IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λ →
      (∀ x ∈ Λ, cmTheta b d • x ∈ Λ) →
      relIdx (stdLat (cmL a b d ha hd lam hlam) m) Λ ≠ 0 →
      relIdx Λ (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0 →
      ∀ l : ℕ, l.Prime → ∀ x y : ℤ, ¬ (l : ℤ) ∣ a * x ^ 2 + b * x * y + c * y ^ 2 →
      ∀ (T : Finset m) (i₀ : m), i₀ ∉ T →
        (∀ j ∈ T, SatMem l Λ (Pi.single j (lam * ((x * a : ℂ) + y * cmTheta b d)))) →
        ∃ v : m → ℂ, SatMem l Λ v ∧ (∀ j ∈ T, v j = 0) ∧
          stdH (cmL a b d ha hd lam hlam) m v v =
            stdH (cmL a b d ha hd lam hlam) m (Pi.single i₀ (lam * ((x * a : ℂ) + y * cmTheta b d)))
              (Pi.single i₀ (lam * ((x * a : ℂ) + y * cmTheta b d)))

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.QequivApply
section
noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

section QR
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (H : Sesq V)

def qmap (z : V) (ν : ℂ) : V →ₗ[ℂ] V := LinearMap.id - (ν • H.flip z).smulRight z

lemma qmap_apply (z : V) (ν : ℂ) (w : V) : qmap H z ν w = w - (ν * H w z) • z := by
  simp [qmap]

lemma qmap_coef {c h k : ℂ} (hc0 : c ≠ 0) (hc : c + conj c = k) :
    c⁻¹ * h + (conj c)⁻¹ * (h - c⁻¹ * h * k) = 0 := by
  subst hc
  have hc1 : conj c ≠ 0 := by simpa using hc0
  field_simp
  ring

lemma qmap_qmap {z : V} {c : ℂ} (hc0 : c ≠ 0) (hc : c + conj c = H z z) (w : V) :
    qmap H z (conj c)⁻¹ (qmap H z c⁻¹ w) = w := by
  rw [qmap_apply, qmap_apply]
  have e : H (w - (c⁻¹ * H w z) • z) z = H w z - c⁻¹ * H w z * H z z := by
    simp [map_sub, map_smul, mul_assoc]
  rw [e, sub_sub, ← add_smul, qmap_coef hc0 hc, zero_smul, sub_zero]

lemma qmap_qmap' {z : V} {c : ℂ} (hc0 : c ≠ 0) (hc : c + conj c = H z z) (w : V) :
    qmap H z c⁻¹ (qmap H z (conj c)⁻¹ w) = w := by
  have h1 := qmap_qmap H (c := conj c) (by simpa using hc0) (by rw [Complex.conj_conj, add_comm]; exact hc) w
  rwa [Complex.conj_conj] at h1

def qequiv (z : V) {c : ℂ} (hc0 : c ≠ 0) (hc : c + conj c = H z z) : V ≃ₗ[ℂ] V :=
  LinearEquiv.ofLinear (qmap H z c⁻¹) (qmap H z (conj c)⁻¹)
    (LinearMap.ext fun w => qmap_qmap' H hc0 hc w) (LinearMap.ext fun w => qmap_qmap H hc0 hc w)

lemma qequiv_apply (z : V) {c : ℂ} (hc0 : c ≠ 0) (hc : c + conj c = H z z) (w : V) :
    qequiv H z hc0 hc w = w - (c⁻¹ * H w z) • z := by
  show qmap H z c⁻¹ w = _
  exact qmap_apply H z c⁻¹ w

lemma qequiv_isom (hsym : ∀ x y, H y x = conj (H x y)) (z : V) {c : ℂ} (hc0 : c ≠ 0)
    (hc : c + conj c = H z z) : IsIsom H H (qequiv H z hc0 hc : V →ₗ[ℂ] V) := by
  intro x y
  have hc1 : conj c ≠ 0 := by simpa using hc0
  simp only [LinearEquiv.coe_coe]
  rw [qequiv_apply, qequiv_apply]
  simp only [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, map_mul, map_inv₀,
    RingHom.id_apply, hsym y z, ← hc]
  field_simp
  ring

end QR

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

