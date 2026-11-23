module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0369
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0370
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0366
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOperatorHeckeTQEqUAddVTwist
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormPowSubPowLtOneOfUltra
section
namespace GlobalTheory.PowerDifferenceNorm

theorem norm_pow_sub_pow_lt_one_of_ultra {K : Type*} [NormedCommRing K] [IsUltrametricDist K]
    {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (h : ‖x - y‖ < 1) (n : ℕ) :
    ‖x ^ n - y ^ n‖ < 1 := by
  rcases n with _ | n
  · simp
  induction n with
  | zero => simpa using h
  | succ n ih =>
    have e : x ^ (n + 1 + 1) - y ^ (n + 1 + 1)
        = x * (x ^ (n + 1) - y ^ (n + 1)) + (x - y) * y ^ (n + 1) := by ring
    rw [e]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt ((norm_mul_le _ _).trans
        (mul_le_of_le_one_left (norm_nonneg _) hx)) ih
    · have hp : ‖y ^ (n + 1)‖ ≤ 1 :=
        (norm_pow_le' y n.succ_pos).trans (pow_le_one₀ (norm_nonneg _) hy)
      exact lt_of_le_of_lt ((norm_mul_le _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _) hp)) h

theorem norm_pow_sub_pow_lt_one :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {x y : Formalism.ConjugateSelfDual.Qbar l}, ‖x‖ ≤ (1 : ℝ) → ‖y‖ ≤ (1 : ℝ) →
      ‖x - y‖ < (1 : ℝ) → ∀ (n : ℕ), ‖x ^ n - y ^ n‖ < (1 : ℝ) := by
  intro l _ x y hx hy h n
  exact norm_pow_sub_pow_lt_one_of_ultra hx hy h n

end GlobalTheory.PowerDifferenceNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdDualGeneratorPairingModPowNondegenerateStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

theorem _root_.GlobalTheory.T.ordDualGeneratorPairing_modPow_nondegenerate : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (n : ℕ) (b : Qn c n), (∀ a : Qn c n, GlobalTheory.Ord2.SelPerp.tbA c n (a * b) = 0) → b = 0 := by
  first | exact @GlobalTheory.Ord2.SelPerp.pair_nondeg | exact GlobalTheory.Ord2.SelPerp.pair_nondeg | (intros; apply GlobalTheory.Ord2.SelPerp.pair_nondeg <;> assumption) | exact @GlobalTheory.Ord2.SelPerp.tau_mul_dvd | exact GlobalTheory.Ord2.SelPerp.tau_mul_dvd | (intros; apply GlobalTheory.Ord2.SelPerp.tau_mul_dvd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ShiftedCocycleLimitIntegralStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shifted_cocycle_limit_integral : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (η : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (y : G ℚ Ω → Fin 2 → Qbar l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ r x i, Continuous fun s => Y r s x i) → (∀ r s x i, Y r s x i ∈ c.O) → (∀ r, ShCoc (mat W) (cycMod ℚ Ω l r)⁻¹ (Y r)) → (∀ r s, Y r s = push (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) (Y (r + 1)) s) → (∀ r x, η r x ∈ c.O) → (∀ r s i, ‖y s i - spec (η r) (Y r) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → ∀ q : Pl, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ ∃ v : Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B, y s = mat W s *ᵥ v - v := by
  first | exact @GlobalTheory.InertCoh.unr_of_limit_spec | exact GlobalTheory.InertCoh.unr_of_limit_spec | (intros; apply GlobalTheory.InertCoh.unr_of_limit_spec ; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TateDualCocycleCoboundaryOfVanishOnFixing
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem h1dual_of_vanish_fix : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ)
    (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ z ∈ Z1 (Loc.colRep (dual1 W)),
    (∀ g ∈ N0g W, z g = 0) → z ∈ ReciprocityTheory.Gal.B1 (Loc.colRep (dual1 W)) := by
  intro l _ Ω _ _ _ e S A W hW z hz hN
  obtain ⟨a, haK, hae⟩ := _root_.GlobalTheory.Ord2.exists_ker_eps_ne_one l Ω e S A W hW
  have hWa : W a = 1 := haK
  have hdual : ∀ v : Fin 2 → Qbar l, Loc.colRep (dual1 W) a v = eps l a • v := by
    intro v
    show Matrix.toLin' ((dual1 W a : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) v = _
    rw [dual1, UpperTheory.V.Af.tw_val, hWa]
    simp [dt, hWa, eps, Matrix.toLin'_apply]
  have hcomm : ∀ g, z (a * g) = z (g * a) := by
    intro g
    have hn : (g * a)⁻¹ * (a * g) ∈ N0g W := by
      refine ⟨?_, ?_⟩
      · show cycBar ℚ Ω l ((g * a)⁻¹ * (a * g)) = 1
        simp [map_mul, map_inv, mul_comm, mul_left_comm, mul_assoc]
      · show W ((g * a)⁻¹ * (a * g)) = 1
        simp [map_mul, map_inv, hWa]
    have h1 : a * g = (g * a) * ((g * a)⁻¹ * (a * g)) := by group
    rw [h1, hz.2, hN _ hn, map_zero, add_zero]
  have hne : eps l a - 1 ≠ 0 := sub_ne_zero.mpr hae
  rw [mem_coboundaries1]
  refine ⟨(eps l a - 1)⁻¹ • z a, fun g => ?_⟩
  have key := hcomm g
  rw [hz.2, hz.2, hdual] at key

  have : (eps l a - 1) • z g = Loc.colRep (dual1 W) g (z a) - z a := by
    rw [sub_smul, one_smul]; rw [← sub_eq_zero] at key ⊢; rw [← key]; abel
  rw [map_smul, ← smul_sub, ← this, smul_smul, inv_mul_cancel₀ hne, one_smul]

end GlobalTheory.Ord2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOperatorHeckeTQEqUAddVTwistStatement
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaOperator_heckeT_q_eq_U_add_V_twist : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], Algebra.IsAlgebraic ℚ Ω → (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → 1 ≤ N → ∀ (n w d q : ℕ), Odd w → q.Prime → ¬ q ∣ N * l → ((q : Ω))⁻¹ ∈ A → (l : Ω) ∈ A.nonunits → l ≠ 2 → ¬ l ∣ N → d.Coprime N → ∀ b : X.Fn l, b ∈ X.B N l w → ∀ φ φ' : HahnSeries ℚ Ω, IsLat 1 φ → IsLat 1 φ' →
  IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) φ →
  IsThB X A N l n (X.act l (sgD N l (d * q) : Matrix (Fin 2) (Fin 2) ℤ) b) φ' →
    IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeT N l q b)) (hq ε q φ + ((q : Ω) ^ (w + 1)) • vq q φ') := by
  first | exact @GlobalTheory.HeckeTh.isThB_heckeT | exact GlobalTheory.HeckeTh.isThB_heckeT | (intros; apply GlobalTheory.HeckeTh.isThB_heckeT <;> assumption)
end

