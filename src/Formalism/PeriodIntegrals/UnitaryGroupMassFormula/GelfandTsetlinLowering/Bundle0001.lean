module

public import Formalism.PeriodIntegrals.Bundle0020
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ZScalarVanish
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.SatisfiesGlRelationsBilinearLeft
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0007
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0004
public import Formalism.PeriodIntegrals.Bundle0019

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.Assembly
section
noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial

theorem ioIntegral_of (hZ : CapelliZ) (hL : LiftMod) (hV : ZScalarVanish) : IoIntegral := by
  intro n N h lam sg hI io0 hE hx hW s hs
  obtain ⟨Z, hZi, hZa⟩ := hZ n N h lam sg hI
  obtain ⟨m, hm, hd⟩ := hL n N h lam sg hI io0 hE hx hW s hs
  obtain ⟨f', hf', hZf⟩ := hZi m hm
  refine ⟨f', hf', ?_⟩
  have hsC : MvPolynomial.map (Int.castRingHom ℂ) s ∈ nablaSq ℂ n sg :=
    Formalism.GradedWeylDivisibility.dualWeylMap ℤ ℂ (Int.castRingHom ℂ) n n sg.natW s hs
  have hO : OtherPart h lam sg ≤ LinearMap.ker Z := by
    unfold OtherPart
    refine iSup_le fun mu => iSup_le fun hmu => iSup_le fun hne => iSup_le fun hw =>
      iSup_le fun φ => iSup_le fun hφ => ?_
    rintro _ ⟨t, ht, rfl⟩
    rw [LinearMap.mem_ker, hZa mu hmu φ hφ t ht, hV n N h lam sg mu hI hmu hne hw, Int.cast_zero, zero_smul]
  have h0 := hO hd
  rw [LinearMap.mem_ker, map_sub, hZf, hZa sg hI io0 hE _ hsC] at h0
  have hz : zScalar h lam sg sg = cBr h lam sg := rfl
  rw [hz] at h0
  rw [map_smul]
  exact (sub_eq_zero.mp h0).symm

theorem sqAct_smul {k : ℕ} (mu : DomWeight k) (g : GL (Fin k) ℂ) (c : ℂ)
    (x : MvPolynomial (Fin k × Fin k) ℂ) : sqAct ℂ k mu g (c • x) = c • sqAct ℂ k mu g x := by
  rw [sqAct, sqAct, map_smul, smul_comm]

theorem gTLower_of_steps (hN : Numbers) (hX : XiFacts) (hE : IoExists) (hP4 : IoIntegral)
    (hA : AdjointBr) (hB : BrIntegral) : PI.GTLower := by
  intro n N h lam sg hI
  obtain ⟨hc0, hcB, hdeg⟩ := hN n N h lam sg hI
  obtain ⟨hxi0, -⟩ := hX n N h lam sg hI
  obtain ⟨io0, ⟨hE1, hE2⟩, hx, hW⟩ := hE n N h lam sg hI
  let c : ℂ := ((cBr h lam sg : ℤ) : ℂ)
  let io := c • io0
  have hio : ∀ x, io x = c • io0 x := fun x => rfl
  have I2 : ∀ s ∈ nablaSq ℂ n sg, io s ∈ nablaSq ℂ N lam := fun s hs =>
    Submodule.smul_mem _ _ (hE1 s hs)
  have I3 : ∀ (g : GL (Fin n) ℂ), ∀ s ∈ nablaSq ℂ n sg,
      io (sqAct ℂ n sg g s) = sqAct ℂ N lam (embGL ℂ n N h g) (io s) := by
    intro g s hs
    rw [hio, hio, hE2 g s hs, sqAct_smul]
  have I4 : io (extremal ℂ n sg) = c • xi ℂ h lam sg := by rw [hio, hx]
  have I5 : LastWeight lam sg io := by
    intro a s hs
    rw [hio, sqAct_smul, hW a s hs, smul_comm]
  have I1 : ∀ s ∈ nablaSq ℤ n sg, ∃ f ∈ nablaSq ℤ N lam,
      io (MvPolynomial.map (Int.castRingHom ℂ) s) = MvPolynomial.map (Int.castRingHom ℂ) f := by
    intro s hs
    obtain ⟨f, hf, hf'⟩ := hP4 n N h lam sg hI io0 ⟨hE1, hE2⟩ hx hW s hs
    exact ⟨f, hf, by rw [hio, ← map_smul]; exact hf'⟩
  obtain ⟨I6, br, hrest, hT⟩ := hA n N h lam sg hI io ⟨I2, I3⟩ I4 I5
  have B1 := hB n N h lam sg hI io br I1 I2 hrest.1 hT
  exact ⟨hc0, hcB, hxi0, hdeg, io, br, ⟨I1, I2, I3, I4, I5, I6⟩, ⟨B1, hrest⟩, hT⟩

end PI.WGL
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.CapelliOps
section
noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

def pol (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) :
    MvPolynomial (Fin r × Fin m) R →ₗ[R] MvPolynomial (Fin r × Fin m) R :=
  ∑ s : Fin m, (LinearMap.mulLeft R (X (a, s))) ∘ₗ
    ((pderiv (b, s) : Derivation R (MvPolynomial (Fin r × Fin m) R) (MvPolynomial (Fin r × Fin m) R)).toLinearMap)

theorem pol_apply (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin m) R) :
    pol R a b f = ∑ s : Fin m, X (a, s) * pderiv (b, s) f := by
  simp [pol, LinearMap.sum_apply]

theorem pol_mul (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (f g : MvPolynomial (Fin r × Fin m) R) :
    pol R a b (f * g) = pol R a b f * g + f * pol R a b g := by
  simp only [pol_apply, Derivation.leibniz, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => by ring

theorem pol_X (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (v : Fin r × Fin m) :
    pol R a b (X v) = if v.1 = b then X (a, v.2) else 0 := by
  classical
  rw [pol_apply]
  by_cases hv : v.1 = b
  · rw [if_pos hv, Finset.sum_eq_single v.2]
    · have : (b, v.2) = v := by rw [← hv]
      rw [this, pderiv_X_self, mul_one]
    · intro s _ hs
      rw [pderiv_X_of_ne, mul_zero]
      intro h; exact hs (by rw [h])
    · simp
  · rw [if_neg hv]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [pderiv_X_of_ne, mul_zero]
    intro h; exact hv (by rw [h])

theorem pol_C (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (c : R) :
    pol R a b (C c : MvPolynomial (Fin r × Fin m) R) = 0 := by
  simp [pol_apply]

theorem rowGen_X' (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (v : Fin r × Fin m) :
    rowGen R a b (X v) = Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) := by
  simp [rowGen]

theorem deriv_rowGen (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin m) R) :
    (if a = b then 1 + Polynomial.X else 1) * Polynomial.derivative (rowGen R a b f) =
      rowGen R a b (pol R a b f) := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    rw [pol_C, map_zero]
    have : rowGen R a b (C c : MvPolynomial (Fin r × Fin m) R) = Polynomial.C (C c) := by
      simp [rowGen]
    rw [this, Polynomial.derivative_C, mul_zero]
  | add p q hp hq => rw [map_add (f := _), Polynomial.derivative_add, mul_add, hp, hq, map_add (f := _), map_add (f := _)]
  | mul_X p v hp =>
    rw [map_mul, Polynomial.derivative_mul, mul_add, pol_mul, map_add (f := _), map_mul, map_mul, ← hp, pol_X]
    have hg : (if a = b then 1 + Polynomial.X else 1) * Polynomial.derivative (rowGen R a b (X v)) =
        rowGen R a b (if v.1 = b then X (a, v.2) else 0) := by
      rw [rowGen_X']
      by_cases hv : v.1 = b
      · simp only [hv, if_true, Polynomial.derivative_add, Polynomial.derivative_C, zero_add,
          Polynomial.derivative_mul, Polynomial.derivative_X, one_mul, mul_zero, add_zero, rowGen_X']
        by_cases hab : a = b
        · simp [hab]; ring
        · simp [hab]
      · simp [hv]
    rw [← hg]; ring

theorem rowGen_coeff_zero (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin m) R) :
    (rowGen R a b f).coeff 0 = f := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  have hh : ((Polynomial.aeval (0 : MvPolynomial (Fin r × Fin m) R)).restrictScalars R).comp (rowGen R a b) =
      AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [rowGen]
    split_ifs <;> simp
  have h2 := congrArg (fun φ => φ f) hh
  simpa [Polynomial.coe_aeval_eq_eval] using h2

theorem rowDiv_zero (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin m) R) :
    rowDiv R a b 0 f = f := rowGen_coeff_zero R a b f

theorem rowDiv_succ (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin m) R) :
    rowDiv R a b (k + 1) f * ((k : MvPolynomial (Fin r × Fin m) R) + 1) +
      (if a = b then rowDiv R a b k f * (k : MvPolynomial (Fin r × Fin m) R) else 0) =
      rowDiv R a b k (pol R a b f) := by
  have h := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p k) (deriv_rowGen R a b f)
  unfold rowDiv
  rw [← h]
  by_cases hab : a = b
  · simp only [hab, if_true, add_mul, one_mul, Polynomial.coeff_add]
    rw [Polynomial.coeff_derivative]
    cases k with
    | zero => simp [Polynomial.coeff_derivative]
    | succ k =>
      rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
      push_cast; ring
  · simp only [hab, if_false, one_mul, add_zero, Polynomial.coeff_derivative]

theorem pol_eq_rowDiv (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin m) R) :
    pol R a b f = rowDiv R a b 1 f := by
  have h := rowDiv_succ R a b 0 f
  simp only [Nat.cast_zero, zero_add, mul_one, mul_zero, ite_self, add_zero, rowDiv_zero] at h
  exact h.symm

theorem pol_map {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) {r m : ℕ} (a b : Fin r)
    (f : MvPolynomial (Fin r × Fin m) R) :
    pol S a b (MvPolynomial.map ψ f) = MvPolynomial.map ψ (pol R a b f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [pol_apply, pderiv_map, map_sum]

theorem pol_mem_dualWeyl (R : Type) [CommRing R] {r m : ℕ} (ν : Fin m → ℕ) (a b : Fin r)
    (f : MvPolynomial (Fin r × Fin m) R) (hf : f ∈ dualWeyl R r m ν) : pol R a b f ∈ dualWeyl R r m ν := by
  rw [pol_eq_rowDiv]; exact dualWeylModuleRowDividedPowerStable R r m ν a b 1 f hf

theorem pol_eq_Eg {r m : ℕ} (a b : Fin r) :
    pol ℂ (m := m) a b = Formalism.REAL.Eg (fun _ => true) (fun _ => true) a b := by
  apply LinearMap.ext; intro f
  simp [pol_apply, Formalism.REAL.Eg, Formalism.REAL.bpl, Formalism.REAL.bop, Formalism.REAL.sgnv, LinearMap.sum_apply]

theorem pol_glRel (r m : ℕ) : Formalism.REAL.GlRel (fun a b : Fin r => (pol ℂ (m := m) a b : Module.End ℂ _)) := by
  have h := (Formalism.REAL.fockPairGl_of Formalism.REAL.canonicalCommutation_holds r m (fun _ => true) (fun _ => true)).1
  intro a b c d
  simp only [pol_eq_Eg]
  exact h a b c d

end PI.WGL
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftDefs
section
noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

def eRow {n N : ℕ} (h : n + 1 = N) (a : Fin n) : Fin N := ⟨a.1, by omega⟩

def lastW (N : ℕ) : Fin N × Fin N → ℕ := fun v => if v.1.1 + 1 = N then 1 else 0

def dLast {n N : ℕ} (lam : DomWeight N) (mu : DomWeight n) : ℕ := (degZ lam mu - lam.detShift).toNat

def liftWt {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n) (ω : Fin n → ℕ) : Fin N → ℕ :=
  fun a => if ha : a.1 < n then ω ⟨a.1, ha⟩ + (mu.detShift - lam.detShift).toNat else dLast lam mu

def liftWord {n N : ℕ} (h : n + 1 = N) (w : List (Fin n × Fin n × ℕ)) : List (Fin N × Fin N × ℕ) :=
  w.map fun x => (eRow h x.1, eRow h x.2.1, x.2.2)

def OffDiag {r : ℕ} (w : List (Fin r × Fin r × ℕ)) : Prop := ∀ x ∈ w, x.1 ≠ x.2.1

def tupCnt {n K : ℕ} {sz : Fin K → ℕ} (I : ∀ k, Fin (sz k) → Fin n) (a : Fin n) : ℕ :=
  ∑ k, (Finset.univ.filter fun p : Fin (sz k) => I k p = a).card

def EqvDiv : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (mu : DomWeight n) (lam : DomWeight N)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ), IsEqv h mu lam φ →
    ∀ (a b : Fin n), a ≠ b → ∀ (k : ℕ), ∀ s ∈ nablaSq ℂ n mu,
      φ (rowDiv ℂ a b k s) = rowDiv ℂ (eRow h a) (eRow h b) k (φ s)

def EqvRowWt : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n), Interlace h lam mu →
    ∀ (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ), IsEqv h mu lam φ →
    ∀ (ω : Fin n → ℕ), ∀ s ∈ nablaSq ℂ n mu, IsWeightedHomogeneous (rowW n n) s ω →
      IsWeightedHomogeneous (rowW N N) (φ s) (liftWt h lam mu ω)

def EqvLast : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n), Interlace h lam mu →
    ∀ (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ), IsEqv h mu lam φ →
    ∀ s ∈ nablaSq ℂ n mu, IsWeightedHomogeneous (lastW N) (φ s) (dLast lam mu)

def Decomp : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    ∀ (io0 : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ),
      IsEqv h sg lam io0 → io0 (extremal ℂ n sg) ≠ 0 →
      ∀ f ∈ nablaSq ℂ N lam, IsWeightedHomogeneous (lastW N) f (dLast lam sg) →
        ∃ u ∈ nablaSq ℂ n sg, f - io0 u ∈ OtherPart h lam sg

def ZComm : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N)
    (Z : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ),
    (∀ (mu : DomWeight n), Interlace h lam mu →
      ∀ (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ), IsEqv h mu lam φ →
        ∃ z : ℂ, ∀ s ∈ nablaSq ℂ n mu, Z (φ s) = z • φ s) →
    (∀ f ∈ nablaSq ℂ N lam, Z f ∈ nablaSq ℂ N lam) ∧
    (∀ (a b : Fin n), a ≠ b → ∀ (k : ℕ), ∀ f ∈ nablaSq ℂ N lam,
      Z (rowDiv ℂ (eRow h a) (eRow h b) k f) = rowDiv ℂ (eRow h a) (eRow h b) k (Z f)) ∧
    (∀ (ω : Fin N → ℕ), ∀ f ∈ nablaSq ℂ N lam, IsWeightedHomogeneous (rowW N N) f ω →
      IsWeightedHomogeneous (rowW N N) (Z f) ω)

def FockDetect : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    ∀ (io0 : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ),
      IsEqv h sg lam io0 → io0 (extremal ℂ n sg) = xi ℂ h lam sg →
      ∀ u ∈ nablaSq ℂ n sg,
        (∀ w : List (Fin n × Fin n × ℕ), OffDiag w →
          Formalism.REAL.fockF (applyWord ℂ (liftWord h w) (io0 u)) (xi ℂ h lam sg) = 0) →
        io0 u = 0

def TupleCore : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    ∀ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n), shapeDeg sz = sg.natW →
    ∃ M : (∀ k, Fin (sz k) → Fin n) → MvPolynomial (Fin N × Fin N) ℤ,
      (∀ I, M I ∈ nablaSq ℤ N lam ∧
        IsWeightedHomogeneous (rowW N N) (M I) (liftWt h lam sg (tupCnt I)) ∧
        IsWeightedHomogeneous (rowW n n) (bideterminant ℤ sz hsz I) (tupCnt I)) ∧
      (∀ I, ∀ w : List (Fin n × Fin n × ℕ), OffDiag w →
        ∃ d : (∀ k, Fin (sz k) → Fin n) →₀ ℤ,
          applyWord ℤ w (bideterminant ℤ sz hsz I) = d.sum (fun J c => c • bideterminant ℤ sz hsz J) ∧
          applyWord ℤ (liftWord h w) (M I) = d.sum (fun J c => c • M J)) ∧
      (∀ J, tupCnt J = sg.natW →
        ∃ ε : ℤ, bideterminant ℤ sz hsz J = ε • extremal ℤ n sg ∧ M J = ε • xi ℤ h lam sg) ∧
      (∃ J0, tupCnt J0 = sg.natW ∧ bideterminant ℤ sz hsz J0 = extremal ℤ n sg ∧ M J0 = xi ℤ h lam sg)

end PI.WGL
end
end

