module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import GroundTheory.GlobalFields.Artin.LogCharpoly
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0006
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationCocycleLiftCriterion
public import Formalism.LandauZeroFreeBounds.Statement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PerronIntegralShiftPrimitiveLFunction
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TruncatedPerronPsi

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConjOnInterQuadraticKernelsOfTraceEq
section
open Formalism.MainNotions.N

namespace GlobalTheory.QuadKernelConj

section Restrict

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ}

def tr (ρ : Γ →* GL (Fin n) k) (g : Γ) (U : Submodule k (Fin n → k)) : Submodule k (Fin n → k) :=
  U.map (Matrix.toLin' ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))

theorem tr_mul (ρ : Γ →* GL (Fin n) k) (g h : Γ) (U : Submodule k (Fin n → k)) :
    tr ρ (g * h) U = tr ρ g (tr ρ h U) := by
  unfold tr
  rw [map_mul, Units.val_mul, Matrix.toLin'_mul, Submodule.map_comp]

theorem tr_mono (ρ : Γ →* GL (Fin n) k) (g : Γ) {U V : Submodule k (Fin n → k)} (h : U ≤ V) :
    tr ρ g U ≤ tr ρ g V := Submodule.map_mono h

theorem tr_sup (ρ : Γ →* GL (Fin n) k) (g : Γ) (U V : Submodule k (Fin n → k)) :
    tr ρ g (U ⊔ V) = tr ρ g U ⊔ tr ρ g V := Submodule.map_sup _ _ _

theorem tr_inf_le (ρ : Γ →* GL (Fin n) k) (g : Γ) (U V : Submodule k (Fin n → k)) :
    tr ρ g (U ⊓ V) ≤ tr ρ g U ⊓ tr ρ g V :=
  le_inf (tr_mono ρ g inf_le_left) (tr_mono ρ g inf_le_right)

theorem tr_le_iff (ρ : Γ →* GL (Fin n) k) (g : Γ) (U : Submodule k (Fin n → k)) :
    tr ρ g U ≤ U ↔ ∀ v ∈ U, ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v ∈ U := by
  unfold tr
  rw [Submodule.map_le_iff_le_comap]
  rfl

theorem isInv_iff (ρ : Γ →* GL (Fin n) k) (U : Submodule k (Fin n → k)) :
    IsInv ρ U ↔ ∀ g, tr ρ g U ≤ U :=
  forall_congr' fun g => (tr_le_iff ρ g U).symm

theorem isInv_ker_iff (ρ : Γ →* GL (Fin n) k) (η : Γ →* ℤˣ) (U : Submodule k (Fin n → k)) :
    IsInv (ρ.comp η.ker.subtype) U ↔ ∀ g, η g = 1 → tr ρ g U ≤ U := by
  constructor
  · intro h g hg
    exact (tr_le_iff ρ g U).2 (h ⟨g, hg⟩)
  · intro h g
    exact (tr_le_iff ρ g.1 U).1 (h g.1 g.2)

theorem isSSRep_ker (ρ : Γ →* GL (Fin n) k) (η : Γ →* ℤˣ) (hρ : IsSSRep ρ) :
    IsSSRep (ρ.comp η.ker.subtype) := by
  intro W hW
  rw [isInv_ker_iff] at hW
  by_cases hη : ∀ g, η g = 1
  · obtain ⟨W', h1, h2⟩ := hρ W ((isInv_iff ρ W).2 fun g => hW g (hη g))
    exact ⟨W', (isInv_ker_iff ρ η W').2 fun g _ => (isInv_iff ρ W').1 h1 g, h2⟩
  obtain ⟨t, ht⟩ := not_forall.1 hη
  have ht' : η t = -1 := (Int.units_eq_one_or (η t)).resolve_left ht

  have hconj : ∀ U, (∀ g, η g = 1 → tr ρ g U ≤ U) → ∀ g, η g = 1 → tr ρ g (tr ρ t U) ≤ tr ρ t U := by
    intro U hU g hg
    have e : g * t = t * (t⁻¹ * g * t) := by group
    rw [← tr_mul, e, tr_mul]
    refine tr_mono ρ t (hU _ ?_)
    rw [map_mul, map_mul, hg, map_inv, mul_one, inv_mul_cancel]
  have hall : ∀ U, (∀ g, η g = 1 → tr ρ g U ≤ U) → tr ρ t U ≤ U → IsInv ρ U := by
    intro U hU hUt
    rw [isInv_iff]
    intro g
    rcases Int.units_eq_one_or (η g) with hg | hg
    · exact hU g hg
    · have e : g = t * (t⁻¹ * g) := by group
      rw [e, tr_mul]
      refine (tr_mono ρ t (hU _ ?_)).trans hUt
      rw [map_mul, map_inv, hg, ht', inv_mul_cancel]
  have htt : tr ρ t (tr ρ t W) ≤ W := by
    rw [← tr_mul]
    refine hW _ ?_
    rw [map_mul, ht']
    simp
  have hAt : tr ρ t (W ⊓ tr ρ t W) ≤ W ⊓ tr ρ t W :=
    (tr_inf_le ρ t _ _).trans (le_inf (inf_le_right.trans htt) inf_le_left)
  have hA : IsInv ρ (W ⊓ tr ρ t W) :=
    hall _ (fun g hg => (tr_inf_le ρ g _ _).trans (inf_le_inf (hW g hg) (hconj W hW g hg))) hAt
  have hB : IsInv ρ (W ⊔ tr ρ t W) := by
    refine hall _ (fun g hg => ?_) ?_
    · rw [tr_sup]
      exact sup_le_sup (hW g hg) (hconj W hW g hg)
    · rw [tr_sup]
      exact sup_le le_sup_right (htt.trans le_sup_left)
  obtain ⟨D, hD, hAD⟩ := hρ _ hA
  obtain ⟨C, hC, hBC⟩ := hρ _ hB
  rw [isInv_iff] at hD hC
  have hW1 : ∀ g, η g = 1 → tr ρ g (W ⊓ D) ≤ W ⊓ D := fun g hg =>
    (tr_inf_le ρ g _ _).trans (inf_le_inf (hW g hg) (hD g))
  have hWeq : (W ⊓ tr ρ t W) ⊔ (W ⊓ D) = W := by
    rw [inf_comm W D, ← sup_inf_assoc_of_le D (inf_le_left : W ⊓ tr ρ t W ≤ W), hAD.sup_eq_top,
      top_inf_eq]
  have hsup : W ⊔ tr ρ t (W ⊓ D) = W ⊔ tr ρ t W := by
    refine le_antisymm (sup_le_sup_left (tr_mono ρ t inf_le_left) _) (sup_le le_sup_left ?_)
    calc tr ρ t W = tr ρ t ((W ⊓ tr ρ t W) ⊔ (W ⊓ D)) := by rw [hWeq]
      _ ≤ W ⊔ tr ρ t (W ⊓ D) := by
        rw [tr_sup]
        exact sup_le_sup_right (hAt.trans inf_le_left) _
  have hdis : Disjoint W (tr ρ t (W ⊓ D)) := by
    rw [disjoint_iff_inf_le, ← hAD.inf_eq_bot]
    exact le_inf (inf_le_inf_left _ (tr_mono ρ t inf_le_left))
      (inf_le_right.trans ((tr_mono ρ t inf_le_right).trans (hD t)))
  refine ⟨tr ρ t (W ⊓ D) ⊔ C, (isInv_ker_iff ρ η _).2 fun g hg => ?_, ?_, ?_⟩
  · rw [tr_sup]
    exact sup_le_sup (hconj _ hW1 g hg) (hC g)
  · exact hdis.disjoint_sup_right_of_disjoint_sup_left (hsup ▸ hBC.disjoint)
  · rw [codisjoint_iff, ← sup_assoc, hsup, hBC.sup_eq_top]

end Restrict

theorem charpoly_eq_of_trace_pow {k : Type} [Field k] [CharZero k] {n : ℕ} (A B : Matrix (Fin n) (Fin n) k)
    (h : ∀ m : ℕ, (A ^ m).trace = (B ^ m).trace) : A.charpoly = B.charpoly := by
  have h1 := GroundTheory.Global.reverse_charpoly_eq_of_trace_pow_eq (Matrix.toLin' A) (Matrix.toLin' B)
    (fun m _ => by
      rw [← Matrix.toLin'_pow, ← Matrix.toLin'_pow, Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq, h m])
  rw [Matrix.charpoly_toLin', Matrix.charpoly_toLin', Polynomial.reverse, Polynomial.reverse,
    Matrix.charpoly_natDegree_eq_dim, Matrix.charpoly_natDegree_eq_dim] at h1
  have h2 := congrArg (Polynomial.reflect (Fintype.card (Fin n))) h1
  rwa [Polynomial.reflect_reflect, Polynomial.reflect_reflect] at h2

theorem conj_on_ker_inf_ker : ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ) (ρ ρ' : Γ →* GL (Fin n) k) (χ₁ χ₂ : Γ →* ℤˣ), IsSSRep ρ → IsSSRep ρ' → (∀ g, χ₁ g = 1 → χ₂ g = 1 → ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace = ((ρ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace) → ∃ P : GL (Fin n) k, ∀ g, χ₁ g = 1 → χ₂ g = 1 → ρ' g = P⁻¹ * ρ g * P := by
  intro Γ k _ _ _ n ρ ρ' χ₁ χ₂ hρ hρ' htr
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix _ _
    (isSSRep_ker _ (χ₁.comp χ₂.ker.subtype) (isSSRep_ker ρ χ₂ hρ))
    (isSSRep_ker _ (χ₁.comp χ₂.ker.subtype) (isSSRep_ker ρ' χ₂ hρ')) (fun g => by
      refine charpoly_eq_of_trace_pow _ _ fun m => ?_
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← map_pow, ← map_pow]
      exact htr (g ^ m).1.1 (g ^ m).2 (g ^ m).1.2)
  exact ⟨P, fun g h1 h2 => hP ⟨⟨g, h2⟩, h1⟩⟩

end GlobalTheory.QuadKernelConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeDiscriminantEqWeierstrassDiscr
section
noncomputable section

namespace GlobalTheory.LatticePeriodEtaProof

open Formalism.MainNotions.TaylorLogMetric GlobalTheory.IndefiniteRowSideFullHecke.PeriodLatticeAgreement
open scoped UpperHalfPlane

theorem lattice_discriminant_eq_weierstrass_discr (Λ : AddSubgroup ℂ) : discr Λ = Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.discr Λ := rfl

theorem latt_eq_closure (ω₁ τ : ℂ) : latt ω₁ τ = AddSubgroup.closure {ω₁, ω₁ * τ} := by
  ext w
  rw [mem_latt, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.jac_mem_closure]
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨![n, m], by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; ring⟩
  · rintro ⟨v, rfl⟩
    exact ⟨v 1, v 0, by ring⟩

theorem discrEta : DiscrEta := by
  intro ω₁ τ h
  rw [lattice_discriminant_eq_weierstrass_discr, latt_eq_closure]
  exact Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.jac_discr ω₁ τ h τ.2

theorem im_conj_mul (ω τ : ℂ) (m n m' n' : ℤ) :
    ((starRingEnd ℂ) (ω * ((m : ℂ) + (n : ℂ) * τ)) * (ω * ((m' : ℂ) + (n' : ℂ) * τ))).im =
      ‖ω‖ ^ 2 * τ.im * ((m * n' - n * m' : ℤ) : ℝ) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_im, Complex.mul_re]
  ring

theorem areaEq : AreaEq := by
  intro ω₁ τ h
  have hy : 0 < τ.im := τ.2
  have hω : 0 < ‖ω₁‖ := norm_pos_iff.2 h
  have hc : 0 < ‖ω₁‖ ^ 2 * τ.im := by positivity
  unfold area
  apply IsLeast.csInf_eq
  refine ⟨⟨hc, ω₁ * ((1 : ℤ) + ((0 : ℤ) : ℂ) * (τ : ℂ)), ⟨1, 0, rfl⟩,
    ω₁ * (((0 : ℤ) : ℂ) + ((1 : ℤ) : ℂ) * (τ : ℂ)), ⟨0, 1, rfl⟩, ?_⟩, ?_⟩
  · rw [im_conj_mul]
    norm_num [UpperHalfPlane.coe_im, abs_of_pos hy]
  · rintro a ⟨ha, w₁, ⟨m, n, rfl⟩, w₂, ⟨m', n', rfl⟩, rfl⟩
    rw [im_conj_mul] at ha ⊢
    simp only [UpperHalfPlane.coe_im] at ha ⊢
    rw [abs_mul, abs_of_pos hc]
    have hd : (m * n' - n * m' : ℤ) ≠ 0 := by
      rintro h0
      rw [h0] at ha
      simp at ha
    have h1 : (1 : ℝ) ≤ |((m * n' - n * m' : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hd
    nlinarith

theorem periodEta : PeriodEta := by
  intro ω₁ τ h
  have hω : 0 < ‖ω₁‖ := norm_pos_iff.2 h
  have hπ : 0 < Real.pi := Real.pi_pos
  unfold period
  rw [discrEta ω₁ τ h, areaEq ω₁ τ h]
  have e : ‖(2 * (Real.pi : ℂ) / ω₁) ^ 12 * ModularForm.eta (τ : ℂ) ^ 24‖ =
      ((2 * Real.pi / ‖ω₁‖) ^ 2 * ‖ModularForm.eta (τ : ℂ)‖ ^ 4) ^ 6 := by
    rw [norm_mul, norm_pow, norm_pow, norm_div, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hπ.le]
    norm_num
    ring
  have hx : 0 ≤ (2 * Real.pi / ‖ω₁‖) ^ 2 * ‖ModularForm.eta (τ : ℂ)‖ ^ 4 := by positivity
  rw [e, show ((1 : ℝ) / 6) = ((6 : ℕ) : ℝ)⁻¹ by norm_num, Real.pow_rpow_inv_natCast hx (by norm_num)]
  field_simp
  ring

theorem discrScale : DiscrScale := by
  intro ω₁ τ c h hc
  rw [scale_latt, discrEta _ τ (mul_ne_zero hc h), discrEta ω₁ τ h]
  rw [zpow_neg, show (12 : ℤ) = ((12 : ℕ) : ℤ) from rfl, zpow_natCast]
  field_simp

theorem hasSum_G (L : PeriodPair) {n : ℕ} (hn : 2 < n) :
    HasSum (fun w : {w : ℂ // w ∈ L.lattice.toAddSubgroup ∧ w ≠ 0} => 1 / (w : ℂ) ^ n) (L.G n) := by
  have h := L.hasSum_sumInvPow 0 hn
  simp only [sub_zero, PeriodPair.sumInvPow_zero] at h
  have h1 : HasSum (((L.lattice : Set ℂ)).indicator (fun w : ℂ => 1 / w ^ n)) (L.G n) := by
    rw [← hasSum_subtype_iff_indicator]
    simp only [one_div]
    exact h
  have h2 : ((L.lattice : Set ℂ)).indicator (fun w : ℂ => 1 / w ^ n) =
      ({w : ℂ | w ∈ L.lattice.toAddSubgroup ∧ w ≠ 0}).indicator (fun w : ℂ => 1 / w ^ n) := by
    ext w
    by_cases hw : w = 0
    · subst hw
      simp [Set.indicator, zero_pow (by omega : n ≠ 0)]
    · classical
      have e : (w ∈ (L.lattice : Set ℂ)) ↔ (w ∈ L.lattice.toAddSubgroup ∧ w ≠ 0) :=
        ⟨fun h => ⟨h, hw⟩, fun h => h.1⟩
      simp only [Set.indicator]
      exact if_congr e rfl rfl
  rw [h2, ← hasSum_subtype_iff_indicator] at h1
  exact h1

theorem agreePeriodPair : AgreePeriodPair := by
  intro L
  have hk : ∀ k : ℕ, 2 ≤ k →
      (Summable (fun w : {w : ℂ // w ∈ L.lattice.toAddSubgroup ∧ w ≠ 0} => 1 / (w : ℂ) ^ (2 * k)) ∧
      eisG L.lattice.toAddSubgroup k = L.G (2 * k)) := by
    intro k hk
    have h := hasSum_G L (n := 2 * k) (by omega)
    exact ⟨h.summable, h.tsum_eq⟩
  refine ⟨hk, ?_, ?_⟩
  · rw [g2, PeriodPair.g₂, (hk 2 le_rfl).2]
  · rw [g3, PeriodPair.g₃, (hk 3 (by norm_num)).2]

theorem latticePeriodEta : LatticePeriodEta :=
  ⟨discrEta, areaEq, periodEta, discrScale, agreePeriodPair⟩

end GlobalTheory.LatticePeriodEtaProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NeOneOfIsPrimitive
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory

namespace GlobalTheory.ZeroFreeHalf

theorem inRegion_of_max {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 3 ≤ N) {ρ : ℂ}
    (h : 1 - c / 2 / Real.log (max (N : ℝ) (N * |ρ.im|)) ≤ ρ.re) : Formalism.ZeroFreeDirichlet.InRegion c N ρ := by
  unfold Formalism.ZeroFreeDirichlet.InRegion
  set M := max (N : ℝ) (N * |ρ.im|) with hM
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hMN : (N : ℝ) ≤ M := le_max_left _ _
  have hMt : (N : ℝ) * |ρ.im| ≤ M := le_max_right _ _
  have hMpos : 0 < M := by linarith
  have ht := abs_nonneg ρ.im
  have hA : (N : ℝ) * (|ρ.im| + 2) ≤ M ^ 2 := by nlinarith
  have hA1 : 1 < (N : ℝ) * (|ρ.im| + 2) := by nlinarith
  have hL : 0 < Real.log ((N : ℝ) * (|ρ.im| + 2)) := Real.log_pos hA1
  have hle : Real.log ((N : ℝ) * (|ρ.im| + 2)) ≤ 2 * Real.log M := by
    have e := Real.log_le_log (by linarith) hA
    rw [Real.log_pow] at e
    push_cast at e
    linarith
  have hdiv : c / (2 * Real.log M) ≤ c / Real.log ((N : ℝ) * (|ρ.im| + 2)) :=
    div_le_div_of_nonneg_left hc.le hL hle
  rw [div_div] at h
  linarith

theorem isRealChar_of_sq {N : ℕ} (χ : DirichletCharacter ℂ N) (h : χ ^ 2 = 1) : IsRealChar χ := by
  intro a
  by_cases ha : IsUnit a
  · have h2 : χ a * χ a = 1 := by
      rw [← pow_two, ← MulChar.pow_apply' χ two_ne_zero, h, MulChar.one_apply ha]
    rcases mul_self_eq_one_iff.mp h2 with e | e <;> simp [e]
  · simp [MulChar.map_nonunit χ ha]

theorem ne_one_of_isPrimitive {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hp : χ.IsPrimitive)
    (hN : 3 ≤ N) : χ ≠ 1 := by
  intro h1
  rw [DirichletCharacter.isPrimitive_def, h1, DirichletCharacter.conductor_one] at hp
  omega

theorem main : Formalism.ZeroFreeDirichlet.ZFRDirichlet → ∃ c : ℝ, 0 < c ∧ (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → 3 ≤ N → ∀ ρ : ℂ, LFunction χ ρ = 0 → 1 - c / Real.log (max (N : ℝ) (N * |ρ.im|)) ≤ ρ.re → IsRealChar χ ∧ ρ.im = 0 ∧ analyticOrderNatAt (LFunction χ) ρ = 1 ∧ ∀ ρ' : ℂ, LFunction χ ρ' = 0 → 1 - c / Real.log (max (N : ℝ) (N * |ρ'.im|)) ≤ ρ'.re → ρ' = ρ) ∧ (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≤ 1 - c / Real.log (|ρ.im| + 3)) := by
  intro hZ
  obtain ⟨c, hc, hZ⟩ := hZ
  refine ⟨c / 2, by positivity, ?_, ?_⟩
  · intro N _ χ hp hN ρ hρ hreg
    have hχ1 : χ ≠ 1 := ne_one_of_isPrimitive χ hp hN
    obtain ⟨hsq, -, him, hder, huniq⟩ :=
      hZ N χ ρ (inRegion_of_max hc hN hreg) ⟨Or.inl hχ1, hρ⟩
    refine ⟨isRealChar_of_sq χ hsq, him, ?_, ?_⟩
    · have han : AnalyticAt ℂ (LFunction χ) ρ :=
        (DirichletCharacter.differentiable_LFunction hχ1).analyticAt ρ
      simp [analyticOrderNatAt, han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hρ hder]
    · intro ρ' hρ' hreg'
      exact (huniq χ ρ' (inRegion_of_max hc hN hreg') ⟨Or.inl hχ1, hρ'⟩).2
  · intro ρ hρ _ hre1
    by_contra hlt
    rw [not_le] at hlt
    have ht := abs_nonneg ρ.im
    have hR : Formalism.ZeroFreeDirichlet.InRegion c 1 ρ := by
      unfold Formalism.ZeroFreeDirichlet.InRegion
      have ha : 0 < Real.log (|ρ.im| + 2) := Real.log_pos (by linarith)
      have hab : Real.log (|ρ.im| + 2) ≤ 2 * Real.log (|ρ.im| + 3) := by
        have e := Real.log_le_log (by linarith) (by linarith : |ρ.im| + 2 ≤ |ρ.im| + 3)
        have e2 : 0 ≤ Real.log (|ρ.im| + 3) := Real.log_nonneg (by linarith)
        linarith
      have hdiv := div_le_div_of_nonneg_left hc.le ha hab
      rw [div_div] at hlt
      simp only [Nat.cast_one, one_mul]
      linarith
    have hne : ρ ≠ 1 := by
      rintro rfl
      simp at hre1
    have hZ0 : Formalism.ZeroFreeDirichlet.IsLZero (1 : DirichletCharacter ℂ 1) ρ :=
      ⟨Or.inr hne, by rw [DirichletCharacter.LFunction_modOne_eq]; exact hρ⟩
    exact (hZ 1 1 ρ hR hZ0).2.1 rfl

end GlobalTheory.ZeroFreeHalf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TruncatedExplicitFormula
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory

namespace GlobalTheory.ExplicitFormula

theorem truncated_explicit_formula : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ u T : ℝ, 2 ≤ T → T ≤ u → {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ LFunction χ ρ = 0}.Finite ∧ ‖psi0 χ u + ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ LFunction χ ρ = 0}, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ C * (u * Real.log (N * u * T) ^ 2 / T + Real.log (N * u) + ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ LFunction χ ρ = 0}, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖) := by
  obtain ⟨C₁, hC₁, h₁⟩ := GlobalTheory.PerronPsi.truncated_perron_psi
  obtain ⟨C₂, hC₂, h₂⟩ := _root_.GlobalTheory.PerronShift.perron_shift
  obtain ⟨C₃, hC₃, h₃⟩ := GlobalTheory.ZeroBand.zeros_band
  refine ⟨C₁ + C₂ + C₃, by positivity, fun N _ χ hχ u T hT hTu => ?_⟩
  obtain ⟨T', hT1, hT2, hs⟩ := h₂ N χ hχ u T hT hTu
  obtain ⟨hfin, hb⟩ := h₃ N χ hχ u T T' hT hTu hT1 hT2
  have hp := h₁ N χ u T' (by linarith) (by linarith) (by linarith)
  refine ⟨hfin, ?_⟩
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hiff : χ = 1 ↔ N = 1 := by
    constructor
    · intro h
      have h1 : χ.conductor = N := hχ
      rw [h, DirichletCharacter.conductor_one] at h1
      exact h1.symm
    · intro h
      subst h
      exact DirichletCharacter.level_one χ
  have hpsi : psi0 χ u = (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, (Λ n : ℂ) * χ (n : ZMod N)) -
      (if N = 1 then (u : ℂ) else 0) := by
    unfold psi0
    by_cases h : N = 1
    · rw [if_pos h, if_pos (hiff.mpr h)]
    · rw [if_neg h, if_neg (fun h' => h (hiff.mp h'))]
  rw [hpsi]
  have hZ : 0 ≤ ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ LFunction χ ρ = 0},
      ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖ :=
    finsum_nonneg fun ρ => finsum_nonneg fun _ => by positivity
  have hu : (2 : ℝ) ≤ u := hT.trans hTu
  have hlu : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
  have hl1 : Real.log u ≤ Real.log (N * u) :=
    Real.log_le_log (by linarith) (by nlinarith)
  have hl2 : Real.log u ≤ Real.log (N * u * T) := by
    refine Real.log_le_log (by linarith) ?_
    have : u ≤ N * u := by nlinarith
    nlinarith
  have hA : u * Real.log u ^ 2 / T' ≤ u * Real.log (N * u * T) ^ 2 / T := by
    have : Real.log u ^ 2 ≤ Real.log (N * u * T) ^ 2 := pow_le_pow_left₀ hlu hl2 2
    gcongr
  have hA0 : 0 ≤ u * Real.log (N * u * T) ^ 2 / T := by
    have : 0 ≤ u := by linarith
    have : 0 ≤ T := by linarith
    positivity
  have key : ∀ S P m Z Z' : ℂ, ‖S - m + Z‖ ≤ ‖S - P‖ + ‖P - m + Z'‖ + ‖Z' - Z‖ := by
    intro S P m Z Z'
    have : S - m + Z = (S - P) + (P - m + Z') - (Z' - Z) := by ring
    rw [this]
    exact (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
  refine (key _ _ _ _ _).trans ((add_le_add (add_le_add hp hs) hb).trans ?_)
  generalize (∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ LFunction χ ρ = 0},
      ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖) = Z at hZ ⊢
  generalize u * Real.log (N * u * T) ^ 2 / T = A at hA hA0 ⊢
  generalize u * Real.log u ^ 2 / T' = A' at hA ⊢
  generalize Real.log (N * u) = B at hl1 ⊢
  generalize Real.log u = B' at hl1 hlu ⊢
  have e1 : C₁ * (A' + B') ≤ C₁ * (A + B + Z) :=
    mul_le_mul_of_nonneg_left (by linarith) hC₁.le
  have e2 : C₃ * A ≤ C₃ * (A + B + Z) :=
    mul_le_mul_of_nonneg_left (by linarith) hC₃.le
  nlinarith

end GlobalTheory.ExplicitFormula
end

