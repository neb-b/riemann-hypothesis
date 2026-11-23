module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0893
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0770
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIntegralContinuationNearRealHalfLinePoleOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralLatticeUnramifiedDescent

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScaledLocalCharacterUnitConductorConductorExpone
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun

namespace GlobalTheory.RamShift

theorem condOne_condExp : ∀ (E : Type) [Field E] [NumberField E] (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (w : HeightOneSpectrum (𝓞 E)), IsUnifV E w (ϖ w : w.adicCompletion E) → GlobalTheory.RamShift.CondOne w ((ϖ w ^ GlobalTheory.RamShift.condExp ϖ w : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
  intro E _ _ ϖ w hϖ
  obtain ⟨ψ, hψ, hlc, hne⟩ := GlobalTheory.JSW.psiLoc_addChar_locallyConstant_ne_one E w
  have hcont : Continuous ψ := hlc.continuous
  have hnorm : ∀ t, ‖ψ t‖ = 1 := fun t => by
    rw [hψ]; exact Circle.norm_coe _
  have hne' : ∃ t, ψ t ≠ 1 := by
    by_contra h
    push_neg at h
    exact hne (AddChar.ext _ _ fun x => by rw [h x, AddChar.one_apply])
  obtain ⟨n, hn⟩ := GlobalTheory.CharConductor.exists_conductor_exponent E w ψ hcont hnorm hne'
  have hval : Valued.v (((ϖ w ^ (-n) : (w.adicCompletion E)ˣ)) : w.adicCompletion E) = WithZero.exp n := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ]
    rw [← WithZero.exp, ← WithZero.exp_zsmul]
    simp
  have key : CondOne w (((ϖ w ^ (-n) : (w.adicCompletion E)ˣ)) : w.adicCompletion E) := by
    intro x
    have h1 := hn ((((ϖ w ^ (-n) : (w.adicCompletion E)ˣ)) : w.adicCompletion E) * x)
    simp only [hψ] at h1
    rw [map_mul, hval] at h1
    have h2 : WithZero.exp n * Valued.v x ≤ WithZero.exp n ↔ Valued.v x ≤ 1 := by
      conv_lhs => rhs; rw [← mul_one (WithZero.exp n)]
      exact mul_le_mul_iff_right₀ (zero_lt_iff.mpr WithZero.exp_ne_zero)
    rw [h2] at h1
    exact h1
  unfold condExp
  split_ifs with h1 h2
  · simpa using h1
  · exact h2.choose_spec
  · exact absurd ⟨-n, key⟩ h2

end GlobalTheory.RamShift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalWhittakerDiagonalShiftRamifiedCharacter
section
noncomputable section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun

namespace GlobalTheory.JSW.ShiftWhit
open GlobalTheory.IwaCell
variable {k : Type} [Field k] {n : ℕ}

theorem val_tD' (ϖ : kˣ) (a : Fin n → ℤ) : (tD ϖ a).val = Matrix.diagonal fun i => ((ϖ ^ a i : kˣ) : k) :=
  GlobalTheory.SmGL.val_diagT k _

theorem conj_tD_apply (ϖ : kˣ) (c : Fin n → ℤ) (u : GL (Fin n) k) (i j : Fin n) :
    ((tD ϖ c * u * tD ϖ (-c) : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      ((ϖ ^ c i : kˣ) : k) * (u : Matrix (Fin n) (Fin n) k) i j * ((ϖ ^ (-c) j : kˣ) : k) := by
  rw [Units.val_mul, Units.val_mul, val_tD', val_tD', Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem tD_eq_diagPow (ϖ : kˣ) (ν : Fin n → ℤ) (h : ∀ i, 0 ≤ ν i) :
    tD ϖ ν = GlobalTheory.JSW.diagPow ϖ (fun i => (ν i).toNat) := by
  have e : (fun i => ((ϖ ^ ν i : kˣ) : k)) = fun i => ((ϖ ^ (ν i).toNat : kˣ) : k) :=
    funext fun i => by rw [← zpow_natCast, Int.toNat_of_nonneg (h i)]
  ext i j
  rw [val_tD', e]
  rfl

theorem commute_tD_const (ϖ : kˣ) (c : ℤ) (x : GL (Fin n) k) : Commute (tD ϖ (fun _ : Fin n => c)) x := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, val_tD']
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

theorem conj_mem_unipB (ϖ : kˣ) (c : Fin n → ℤ) {u : GL (Fin n) k} (hu : u ∈ GlobalTheory.SmGL.unipB k (Fin n)) :
    tD ϖ c * u * tD ϖ (-c) ∈ GlobalTheory.SmGL.unipB k (Fin n) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB k).1 hu
  refine (GlobalTheory.SmGL.mem_unipB k).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [conj_tD_apply, h1 i j hij, mul_zero, zero_mul]
  · rw [conj_tD_apply, h2 i, mul_one, ← Units.val_mul, Pi.neg_apply, ← _root_.zpow_add, add_neg_cancel, zpow_zero, Units.val_one]

theorem superDiag_conj (ϖ : kˣ) (e : ℤ) (m : ℕ) (u : GL (Fin (m + 1)) k) :
    GlobalTheory.Whittaker.superDiag (tD ϖ (fun i : Fin (m + 1) => e * ((m : ℤ) - ((i : ℕ) : ℤ))) * u *
      tD ϖ (-(fun i : Fin (m + 1) => e * ((m : ℤ) - ((i : ℕ) : ℤ))))) =
      ((ϖ ^ e : kˣ) : k) * GlobalTheory.Whittaker.superDiag u := by
  rw [GlobalTheory.Whittaker.superDiag, GlobalTheory.Whittaker.superDiag, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : (j : ℕ) = (i : ℕ) + 1 := (Finset.mem_filter.1 hj).2
  rw [conj_tD_apply]
  have hz : (ϖ ^ (e * ((m : ℤ) - ((i : ℕ) : ℤ))) : kˣ) * ϖ ^ ((-(fun i : Fin (m + 1) => e * ((m : ℤ) - ((i : ℕ) : ℤ)))) j) = ϖ ^ e := by
    rw [← _root_.zpow_add]
    congr 1
    simp only [Pi.neg_apply, hj']
    push_cast
    ring
  rw [← hz, Units.val_mul]
  ring

end GlobalTheory.JSW.ShiftWhit

namespace GlobalTheory.JSW.ShiftWhit
open GlobalTheory.IwaCell GlobalTheory.JSW GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.MultiplicityOne GlobalTheory.PRep
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

def psiScaled (w : HeightOneSpectrum (𝓞 E)) (c : w.adicCompletion E) : AddChar (w.adicCompletion E) ℂ :=
  (psiLocChar w).compAddMonoidHom (AddMonoidHom.mulLeft c)

theorem psiScaled_apply (w : HeightOneSpectrum (𝓞 E)) (c x : w.adicCompletion E) :
    psiScaled w c x = psiLoc w (c * x) := rfl

theorem main_of_fixed (m : ℕ) (π : CuspSub E (m + 1)) (w : HeightOneSpectrum (𝓞 E))
    (α : Fin (m + 1) → ℂˣ) (hα : HasSatGL w (π.locRep w) (Finset.univ.val.map α))
    (φ : π.V) (hφ : φ ∈ fixed (π.locRep w) (KGL w (n := (m + 1))))
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifV E w (ϖ : w.adicCompletion E)) (e : ℤ)
    (hc : GlobalTheory.RamShift.CondOne w ((ϖ ^ e : (w.adicCompletion E)ˣ) : w.adicCompletion E))
    (g : GA E (m + 1)) (hg : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g = 1)
    (ν : Fin (m + 1) → ℤ) (hν : 0 ≤ ν (Fin.last m)) :
    whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ (fun i => e * ((m : ℤ) - ((i : ℕ) : ℤ)) + ν i)))) =
      GlobalTheory.RSCell.sphZ (qV E w) (fun i => (α i : ℂ)) ν *
        whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ (fun i => e * ((m : ℤ) - ((i : ℕ) : ℤ)))))) := by
  classical
  set c : Fin (m + 1) → ℤ := fun i => e * ((m : ℤ) - ((i : ℕ) : ℤ)) with hcdef
  have hsplit : tD ϖ (fun i => c i + ν i) = tD ϖ c * tD ϖ ν := by rw [← tD_add]; rfl
  have hcont : ∀ ψ : π.V, Continuous ψ.1.1 := fun ψ => (π.cusp _ ψ.2).1.continuous
  have hleft : AutomorphicForm.IsLeftInvariant φ.1.1 := fun γ y => by
    rw [show AdelicGLn.diagonal E (m + 1) γ = ratGL E (m + 1) γ from Units.ext (Matrix.ext fun _ _ => rfl)]
    exact (π.cusp _ φ.2).1.left γ y
  let f : π.V →ₗ[ℂ] (GL (Fin (m + 1)) (w.adicCompletion E) → ℂ) :=
    { toFun := fun ψ h => whit ψ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * h)))
      map_add' := fun ψ ψ' => funext fun h => whit_add (hcont ψ) (hcont ψ') _
      map_smul' := fun c ψ => funext fun h => whit_smul c ψ.1.1 _ }
  have hmul : ∀ h k : GL (Fin (m + 1)) (w.adicCompletion E),
      g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * (h * k))) =
        (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * h))) * finGL E (m + 1) (locGL E (m + 1) w k) := by
    intro h k
    rw [← mul_assoc (tD ϖ c) h k, map_mul (locGL E (m + 1) w), map_mul (finGL E (m + 1)), mul_assoc]
  have hf : ∀ k (ψ : π.V), f (π.locRep w k ψ) = rightReg ℂ _ ℂ k (f ψ) := by
    intro k ψ
    funext h
    change whit (fun z => ψ.1.1 (z * finGL E (m + 1) (locGL E (m + 1) w k)))
        (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * h))) =
      whit ψ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * (h * k))))
    rw [hmul, whit_mul_right ψ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * h)))]

  have hN0 : ∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin (m + 1)), ∀ h : GL (Fin (m + 1)) (w.adicCompletion E),
      whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (u * h))) =
        psiLoc w (GlobalTheory.Whittaker.superDiag u) * whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w h)) := by
    intro u hu h
    rw [map_mul, map_mul, ← mul_assoc, commute_finGL_locGL w hg u, mul_assoc, finGL_locGL_eq_uGL w hu, whit,
      whittaker_uGL_mul (hcont φ) hleft, supSum_sLoc]
    rfl
  have hN : ∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin (m + 1)), ∀ h,
      f φ (u * h) = psiScaled w ((ϖ ^ e : (w.adicCompletion E)ˣ) : w.adicCompletion E)
        (GlobalTheory.Whittaker.superDiag u) * f φ h := by
    intro u hu h
    change whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * (u * h)))) =
      _ * whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * h)))
    have e1 : tD ϖ c * (u * h) = (tD ϖ c * u * tD ϖ (-c)) * (tD ϖ c * h) := by rw [tD_neg]; group
    rw [e1, hN0 _ (conj_mem_unipB ϖ c hu), psiScaled_apply, hcdef, superDiag_conj]
  have hK : ∀ h, ∀ k ∈ KGL w (n := (m + 1)), f φ (h * k) = f φ h := by
    intro h k hk
    change whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * (h * k)))) =
      whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * h)))
    rw [hmul, whit_mul_right φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * h)))]
    congr 1
    funext z
    exact congrArg (fun ψ : π.V => ψ.1.1 z) (GlobalTheory.LGrp.mem_fixed.1 hφ k hk)
  have hψ : ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w,
      psiScaled w ((ϖ ^ e : (w.adicCompletion E)ˣ) : w.adicCompletion E) (x * y) = 1) ↔ x ∈ Ov E w := by
    intro x
    simp only [psiScaled_apply, ← mul_assoc]
    exact hc x
  have hgoal : f φ (tD ϖ ν) = GlobalTheory.RSCell.sphZ (qV E w) (fun i => (α i : ℂ)) ν * f φ 1 := by
    by_cases h0 : φ = 0
    · subst h0
      have hz : ∀ h, f 0 h = 0 := fun h => by rw [map_zero]; rfl
      rw [hz, hz, mul_zero]
    by_cases hanti : Antitone ν
    · have hpos : ∀ i, 0 ≤ ν i := fun i => hν.trans (hanti (Fin.le_last i))
      have hsat := hα.2 φ hφ h0
      have hmain := GlobalTheory.T.shintani_formula_alt E w (m + 1) _ hψ (f φ) α hN hK ?_ ϖ hϖ (fun i => (ν i).toNat)
      · rw [GlobalTheory.RSCell.sphZ, if_pos hanti, tD_eq_diagPow ϖ ν hpos]
        exact hmain
      · intro ϖ' hϖ' j hj
        rw [← map_heckeVec (Final.GLintComm E w (m + 1)) (Tj_mem_hecke hϖ' j) f hf, hsat.2.2.2 ϖ' hϖ' j hj, map_smul]
    · rw [GlobalTheory.RSCell.sphZ, if_neg hanti, zero_mul]
      set M : ℕ := ∑ i, (ν i).natAbs
      have hM : ∀ i, (ν i).natAbs ≤ M := fun i =>
        Finset.single_le_sum (f := fun i => (ν i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      set ν' : Fin (m + 1) → ℤ := fun i => ν i + M
      have hpos : ∀ i, 0 ≤ ν' i := fun i => by have := hM i; simp only [ν']; omega
      set z := tD ϖ (fun _ : Fin (m + 1) => -(M : ℤ))
      have hνz : tD ϖ ν = tD ϖ ν' * z := by
        rw [← tD_add]; congr 1; funext i; simp only [ν', Pi.add_apply]; ring
      have hanti' : ¬ Antitone (fun i => (ν' i).toNat) := by
        intro ha
        refine hanti fun i j hij => ?_
        have := ha hij
        have h1 := Int.toNat_of_nonneg (hpos i)
        have h2 := Int.toNat_of_nonneg (hpos j)
        simp only [ν'] at this h1 h2
        omega
      have hz := GlobalTheory.T.whittaker_diagonal_eq_zero_of_not_antitone E w (m + 1) _ hψ (fun h => f φ (h * z))
        (fun u hu h => by simp only [mul_assoc]; exact hN u hu (h * z))
        (fun h k hk => by
          show f φ (h * k * z) = f φ (h * z)
          rw [mul_assoc, ← (commute_tD_const ϖ _ k).eq, ← mul_assoc, hK _ k hk])
        ϖ hϖ (fun i => (ν' i).toNat) hanti'
      rw [hνz, tD_eq_diagPow ϖ ν' hpos]
      exact hz
  have e2 := hgoal
  change whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * tD ϖ ν))) = _ *
    whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * 1))) at e2
  rw [mul_one, ← hsplit] at e2
  exact e2

end GlobalTheory.JSW.ShiftWhit

namespace GlobalTheory.JSW

theorem whit_mul_locGL_tD_shift : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (π : CuspSub E (m + 1)) (w : HeightOneSpectrum (𝓞 E)) (α : Fin (m + 1) → ℂˣ), HasSatGL w (π.locRep w) (Finset.univ.val.map α) → ∀ φ ∈ π.V, (∀ k ∈ KGL w (n := (m + 1)), act (.fin (locGL E (m + 1) w k)) φ = φ) → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ e : ℤ, GlobalTheory.RamShift.CondOne w ((ϖ ^ e : (w.adicCompletion E)ˣ) : w.adicCompletion E) → ∀ g : GA E (m + 1), GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g = 1 → ∀ ν : Fin (m + 1) → ℤ, 0 ≤ ν (Fin.last m) → GlobalTheory.JSW.whit φ.1 (g * finGL E (m + 1) (locGL E (m + 1) w (GlobalTheory.IwaCell.tD ϖ (fun i => e * ((m : ℤ) - ((i : ℕ) : ℤ)) + ν i)))) = GlobalTheory.RSCell.sphZ (qV E w) (fun i => (α i : ℂ)) ν * GlobalTheory.JSW.whit φ.1 (g * finGL E (m + 1) (locGL E (m + 1) w (GlobalTheory.IwaCell.tD ϖ (fun i => e * ((m : ℤ) - ((i : ℕ) : ℤ)))))) := by
  intro E _ _ _ m π w α hα φ hφV hφ ϖ hϖ e hc g hg ν hν
  exact GlobalTheory.JSW.ShiftWhit.main_of_fixed m π w α hα ⟨φ, hφV⟩
    (GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (hφ k hk)) ϖ hϖ e hc g hg ν hν

end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIntegralContinuationNearRealHalfLinePoleOneStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaIntegral_continuation_nearRealHalfLine_poleOne : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ℓ : Fin a) (Φ : (Fin a → Cinf E) → ℂ), ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ → ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 𝓕' : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (latticeGL E a) 𝓕' μ → ∃ c : ℂ, ((∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) → Φ ≠ 0 → c ≠ 0) ∧ ∀ (π π' : CuspSub E a) (ω ω' : HChar E), ω.IsUnitary → ω'.IsUnitary → π.HasCentChar ω → π'.HasCentChar ω' → ∀ φ φ' : Sm E a, (φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) → (φ' ∈ π'.V ∨ φ'.1 ∈ GlobalTheory.JSW.mspanR π') → ∃ F : ℂ → ℂ, (∀ x : ℝ, 0 < x → AnalyticAt ℂ F (x : ℂ)) ∧ (∀ x : ℝ, 1 < x → F (x : ℂ) = ((x - 1 : ℝ) : ℂ) * ∫ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ) ∂μ) ∧ (ω = ω' → F 1 = c * ∫ g in 𝓕', φ.1 g * starRingEnd ℂ (φ'.1 g) ∂μ) ∧ (ω ≠ ω' → F 1 = 0) := by
  first | exact @GlobalTheory.RSThetaCont.theta_integral_continuation | exact GlobalTheory.RSThetaCont.theta_integral_continuation | (intros; apply GlobalTheory.RSThetaCont.theta_integral_continuation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceIntegralOfSmallAtOtherPlaces
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Pj
open scoped WithZero

namespace GlobalTheory.TraceSmall

theorem valV_le_one_of_ext {T T' : CDVR} (i : T.Fr →+* T'.Fr) {e' : ℕ} (he' : 0 < e')
    (hv : ∀ z : T.Fr, z ≠ 0 → vV T'.V (i z) = (e' : ℤ) * vV T.V z) (z : T.Fr) :
    valV T'.V (i z) ≤ 1 ↔ valV T.V z ≤ 1 := by
  by_cases hz : z = 0
  · subst hz; simp
  have h1 : valV T'.V (i z) ≠ 0 := valV_ne_zero ((map_ne_zero i).2 hz)
  have h2 : valV T.V z ≠ 0 := valV_ne_zero hz
  have h := hv z hz
  have he : (0 : ℤ) < e' := by exact_mod_cast he'
  rw [← WithZero.log_le_log h1 one_ne_zero, ← WithZero.log_le_log h2 one_ne_zero, WithZero.log_one]
  unfold vV at h
  constructor <;> intro h' <;> nlinarith

theorem exists_bound {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (p : HeightOneSpectrum (𝓞 K)) {m : ℕ} (y : Fin m → L) :
    ∃ N : ℕ, ∀ la' : HeightOneSpectrum (𝓞 L), la'.asIdeal.under (𝓞 K) = p.asIdeal → ∀ k,
      la'.valuation L (y k) ≤ WithZero.exp (N : ℤ) := by
  have hS : {la' : HeightOneSpectrum (𝓞 L) | la'.asIdeal.under (𝓞 K) = p.asIdeal}.Finite := by
    refine (Set.Finite.preimage (f := fun la' : HeightOneSpectrum (𝓞 L) => la'.asIdeal)
      (fun a _ b _ h => HeightOneSpectrum.ext h)
      (IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 L))).subset fun la' h => ?_
    exact ⟨la'.isPrime, ⟨h.symm⟩⟩
  obtain ⟨B, hB⟩ := ((hS.prod (Set.finite_univ (α := Fin m))).image
    fun q : HeightOneSpectrum (𝓞 L) × Fin m => WithZero.log (q.1.valuation L (y q.2))).bddAbove
  refine ⟨B.toNat, fun la' h k => ?_⟩
  by_cases hy : y k = 0
  · simp [hy]
  have h0 : la'.valuation L (y k) ≠ 0 := by simpa using hy
  have := hB ⟨(la', k), ⟨h, Set.mem_univ _⟩, rfl⟩
  rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
  simp only at this
  omega

theorem valuation_le_of_mem {L : Type} [Field L] [NumberField L] (la' : HeightOneSpectrum (𝓞 L)) {N : ℕ}
    {b : 𝓞 L} (hb : b ∈ la'.asIdeal ^ N) : la'.valuation L (b : L) ≤ WithZero.exp (-(N : ℤ)) :=
  (la'.valuation_of_algebraMap b).trans_le ((la'.intValuation_le_pow_iff_mem b N).2 hb)

theorem trace_le_one : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (p : HeightOneSpectrum (𝓞 K)) (la : HeightOneSpectrum (𝓞 L)), la.asIdeal.under (𝓞 K) = p.asIdeal → ∀ (m : ℕ) (y : Fin m → L), ∃ N : ℕ, ∀ b : 𝓞 L, (∀ la' : HeightOneSpectrum (𝓞 L), la' ≠ la → la'.asIdeal.under (𝓞 K) = p.asIdeal → b ∈ la'.asIdeal ^ N) → ∀ (T : CDVR), T.FinRes → ∀ (io : K →+* T.Fr) (e : ℕ), OverLa p T.V io e → ∀ x : Fin m → T.Fr, (∀ k, valV T.V (x k) ≤ 1) → (∀ (T' : CDVR) (i : T.Fr →+* T'.Fr) (e' : ℕ) (τ : L →+* T'.Fr) (e'' : ℕ), 0 < e' → (∀ z : T.Fr, z ≠ 0 → vV T'.V (i z) = (e' : ℤ) * vV T.V z) → T'.FinRes → (∀ z : K, τ (algebraMap K L z) = i (io z)) → OverLa la T'.V τ e'' → valV T'.V (∑ k, τ (y k) * i (x k)) ≤ 1) → valV T.V (∑ k, io (Algebra.trace K L ((b : L) * y k)) * x k) ≤ 1 := by
  intro K L _ _ _ _ _ p la hla m y
  obtain ⟨N, hN⟩ := exists_bound p y
  refine ⟨N, fun b hb T hT io e ho x hx H => ?_⟩
  let Ω := AlgebraicClosure L
  let F := IntermediateField.normalClosure K L Ω
  obtain ⟨T', i, e', σ₀, he', hv, hT', hσ₀⟩ := GlobalTheory.SupDescent.exists_ext (L := F) T hT io
  have hv' : ∀ a : T.Fr, vV T'.V (i a) = (e' : ℤ) * vV T.V a := fun a => by
    by_cases h : a = 0
    · subst h; simp [vV]
    · exact hv a h
  have ho' := ho.bc i he' hv'
  have hF : ∀ (ρ : L →ₐ[K] Ω) (z : L), ρ z ∈ F := fun ρ z =>
    AlgHom.fieldRange_le_normalClosure ρ ⟨z, rfl⟩
  let τ : (L →ₐ[K] Ω) → L →+* T'.Fr := fun ρ =>
    σ₀.comp ((ρ.codRestrict F.toSubalgebra (hF ρ)).toRingHom)
  have hτ : ∀ ρ z, τ ρ z = σ₀ ⟨ρ z, hF ρ z⟩ := fun _ _ => rfl
  have hτK : ∀ ρ (a : K), τ ρ (algebraMap K L a) = i (io a) := fun ρ a => by
    rw [hτ, ← hσ₀ a]
    congr 1
    exact Subtype.ext (ρ.commutes a)
  have htr : ∀ z : L, i (io (Algebra.trace K L z)) = ∑ ρ : L →ₐ[K] Ω, τ ρ z := fun z => by
    have h1 := trace_eq_sum_embeddings Ω (K := K) (L := L) (x := z)
    have h2 : algebraMap K F (Algebra.trace K L z) = ∑ ρ : L →ₐ[K] Ω, (⟨ρ z, hF ρ z⟩ : F) := by
      apply Subtype.val_injective
      rw [IntermediateField.coe_sum]
      exact h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hσ₀, h2, map_sum]
    exact Finset.sum_congr rfl fun ρ _ => (hτ ρ z).symm
  rw [← valV_le_one_of_ext i he' hv]
  have hsum : i (∑ k, io (Algebra.trace K L ((b : L) * y k)) * x k) =
      ∑ ρ : L →ₐ[K] Ω, ∑ k, τ ρ (b : L) * (τ ρ (y k) * i (x k)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul (f := i), htr, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, mul_assoc]
  rw [hsum]
  refine Valuation.map_sum_le _ fun ρ _ => ?_
  have hunit (v : T'.V) : valV T'.V (algebraMap T'.V T'.Fr v) = 1 ↔ IsUnit v := by
    have hlt : valV T'.V (algebraMap T'.V T'.Fr v) < 1 ↔ v ∈ IsLocalRing.maximalIdeal T'.V := HeightOneSpectrum.valuation_lt_one_iff_mem _ v
    rw [← IsLocalRing.notMem_maximalIdeal, ← hlt, not_lt]
    exact ⟨fun h => h.ge, fun h => le_antisymm (HeightOneSpectrum.valuation_le_one _ v) h⟩
  have hpos_aux {v : T'.V} (h0 : v ≠ 0) (h : v ∈ IsLocalRing.maximalIdeal T'.V) :
      0 < vV T'.V (algebraMap T'.V T'.Fr v) := by
    have h1 : algebraMap T'.V T'.Fr v ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective T'.V T'.Fr)).2 h0
    have h2 := (WithZero.log_lt_log (valV_ne_zero (V := T'.V) h1) one_ne_zero).2
      ((HeightOneSpectrum.valuation_lt_one_iff_mem _ v).2 h)
    simp only [WithZero.log_one] at h2
    simp only [vV]; omega
  have hex : ∃ (la : HeightOneSpectrum (𝓞 L)) (e : ℕ), OverLa la T'.V (τ ρ) e := by
    have hint : ∀ a : 𝓞 L, ∃ v : T'.V, algebraMap T'.V T'.Fr v = (τ ρ) a := fun a =>
      IsIntegrallyClosed.algebraMap_eq_of_integral (R := T'.V) (K := T'.Fr)
        (IsIntegral.map_of_comp_eq (Int.castRingHom T'.V) (τ ρ) (RingHom.ext_int _ _) a.isIntegral_coe)
    choose g0 hg0 using hint
    have hinj := IsFractionRing.injective T'.V T'.Fr
    let g : 𝓞 L →+* T'.V :=
      { toFun := g0
        map_one' := hinj (by simp [hg0])
        map_mul' := fun a b => hinj (by simp [hg0])
        map_zero' := hinj (by simp [hg0])
        map_add' := fun a b => hinj (by simp [hg0]) }
    have hg : ∀ a, algebraMap T'.V T'.Fr (g a) = (τ ρ) (algebraMap (𝓞 L) L a) := hg0
    have hne : (IsLocalRing.maximalIdeal T'.V).comap g ≠ ⊥ := by
      have : Finite (IsLocalRing.ResidueField T'.V) := hT'
      have hc : Nat.card (IsLocalRing.ResidueField T'.V) ≠ 0 := Nat.card_pos.ne'
      intro h
      have h1 : ((Nat.card (IsLocalRing.ResidueField T'.V) : ℕ) : 𝓞 L) ∈ (IsLocalRing.maximalIdeal T'.V).comap g := by
        rw [Ideal.mem_comap, map_natCast, ← IsLocalRing.residue_eq_zero_iff, map_natCast, ← nsmul_one]
        exact card_nsmul_eq_zero'
      rw [h, Ideal.mem_bot] at h1
      exact hc (by exact_mod_cast h1)
    let la : HeightOneSpectrum (𝓞 L) := ⟨(IsLocalRing.maximalIdeal T'.V).comap g, Ideal.comap_isPrime _ _, hne⟩
    have hun : ∀ a : 𝓞 L, a ∉ la.asIdeal → valV T'.V ((τ ρ) (algebraMap (𝓞 L) L a)) = 1 := fun a ha => by
      rw [← hg, hunit]
      exact IsLocalRing.notMem_maximalIdeal.1 ha
    have hone : ∀ x : L, la.valuation L x = 1 → valV T'.V ((τ ρ) x) = 1 := fun x hx => by
      obtain ⟨n, d, h⟩ := la.exists_primeCompl_mul_eq_of_integer x hx.le
      have hd : la.valuation L (algebraMap (𝓞 L) L d) = 1 := (la.valuation_eq_one_iff_notMem).2 d.2
      have hn : la.valuation L (algebraMap (𝓞 L) L n) = 1 := by rw [← h, map_mul, hx, hd, one_mul]
      have h2 := hun n ((la.valuation_eq_one_iff_notMem).1 hn)
      rwa [← h, map_mul, map_mul, hun d d.2, mul_one] at h2
    obtain ⟨π, hπ⟩ := la.intValuation_exists_uniformizer
    have hπK : la.valuation L (algebraMap (𝓞 L) L π) = WithZero.exp (-1 : ℤ) := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, hπ]
    have hπ0 : algebraMap (𝓞 L) L π ≠ 0 := fun h => by simp [h] at hπK; exact WithZero.exp_ne_zero hπK.symm
    have hπm : π ∈ la.asIdeal := by
      rw [← la.valuation_lt_one_iff_mem (K := L), hπK, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    have hpos : 0 < vV T'.V ((τ ρ) (algebraMap (𝓞 L) L π)) := by
      rw [← hg]
      refine hpos_aux (fun h => ?_) hπm
      have := hg π
      rw [h, map_zero] at this
      exact (map_ne_zero (τ ρ)).2 hπ0 this.symm
    refine ⟨la, (vV T'.V ((τ ρ) (algebraMap (𝓞 L) L π))).toNat, by omega, fun a => ?_⟩
    rw [Int.toNat_of_nonneg hpos.le]
    by_cases ha : a = 0
    · simp [ha, vV, vLa]
    have hva : la.valuation L a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
    have h1 := hone (a * (algebraMap (𝓞 L) L π) ^ (-vLa la a)) (by
      rw [map_mul, map_zpow₀, hπK, ← WithZero.exp_zsmul, ← WithZero.exp_log hva, ← WithZero.exp_add]
      simp [vLa])
    have h2 := congrArg WithZero.log h1
    rw [map_mul, map_mul, map_zpow₀, map_zpow₀, WithZero.log_mul (valV_ne_zero ((map_ne_zero (τ ρ)).2 ha))
      (zpow_ne_zero _ (valV_ne_zero ((map_ne_zero (τ ρ)).2 hπ0))), WithZero.log_zpow, WithZero.log_one] at h2
    simp only [vV, smul_eq_mul] at h2 ⊢
    linarith
  obtain ⟨la', e'', hol⟩ := hex
  have hunder : la'.asIdeal.under (𝓞 K) = p.asIdeal := Ideal.ext fun a => by
    rw [Ideal.under_def, Ideal.mem_comap, ← GlobalTheory.SupDescent.val_lt_one_iff_mem hol,
      ← GlobalTheory.SupDescent.val_lt_one_iff_mem ho']
    exact Iff.of_eq (congrArg (fun t => valV T'.V t < 1) (hτK ρ a))
  rcases eq_or_ne la' la with rfl | hne
  · rw [← Finset.mul_sum, map_mul]
    exact mul_le_one' ((GlobalTheory.SupDescent.val_le_one_iff hol _).2 (la'.valuation_le_one b))
      (H T' i e' (τ ρ) e'' he' hv hT' (hτK ρ) hol)
  · refine Valuation.map_sum_le _ fun k _ => ?_
    rw [← mul_assoc, ← map_mul, map_mul]
    refine mul_le_one' ((GlobalTheory.SupDescent.val_le_one_iff hol _).2 ?_) ((valV_le_one_of_ext i he' hv _).2 (hx k))
    rw [map_mul]
    calc la'.valuation L (b : L) * la'.valuation L (y k)
        ≤ WithZero.exp (-(N : ℤ)) * WithZero.exp (N : ℤ) :=
          mul_le_mul' (valuation_le_of_mem la' (hb la' hne hunder)) (hN la' hunder k)
      _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]

end GlobalTheory.TraceSmall
end
end

