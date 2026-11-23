module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0434
public import GroundTheory.PAdicHodge.FactorizationFactorialLe
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0454
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0436
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0437
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.WeilBound.ThetaLifts.Reductions.SiegelPar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0455
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0238
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0102
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0007
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0014

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoinvariantLeviActionModulus
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.QLevi

theorem tmul_scalars {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (x : A) (y : B)
    (c d d' e f : ℂ) (hd : d * d' = 1) :
    (c * (e * f)) • (x ⊗ₜ[ℂ] y) = (d * e) • ((c • d' • x) ⊗ₜ[ℂ] (f • y)) := by
  rw [smul_smul, TensorProduct.smul_tmul_smul, smul_smul]
  congr 1
  linear_combination (-(c * e * f)) * hd

theorem qC_sigX : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (h : MirabolicParabolic k (i + 1) t) (η : HPG k (i + 1) (t + 1)) (hη : pgProj k (i + 1) (t + 1) η = (levi k (i + 1) (gpProj k (i + 1) t h).1, (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k))) (w : τ.V ⊗[ℂ] σ.V), qC τ σ (sigX τ σ η w) = ((dpow (i + 1) (1 / 2) (gpProj k (i + 1) t h).1 * dpow (t + 1) (-1 / 2) (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k) : ℂˣ) : ℂ) • sigC τ σ h (qC τ σ w) := by
  intro k _ _ _ _ i t τ σ h η hη w
  generalize hgdef : (gpProj k (i + 1) t h).1 = g at *
  generalize hpdef : (gpProj k (i + 1) t h).2 = p at *
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]
  | tmul a b =>
    have hL : sigX τ σ η (a ⊗ₜ[ℂ] b) =
        (((dpowM (i + 1) (((t + 1 : ℕ) : ℝ) / 2) (levi k (i + 1) g) : ℂˣ) : ℂ) • τ.ρ (levi k (i + 1) g) a) ⊗ₜ[ℂ]
        (((dpow (t + 1) (-((i + 1 + 1 : ℕ) : ℝ) / 2) (p : GL (Fin (t + 1)) k) : ℂˣ) : ℂ) • σ.ρ (p : GL (Fin (t + 1)) k) b) := by
      show extTensor _ _ (pgProj k (i + 1) (t + 1) η) _ = _
      rw [hη]
      exact extTensor_tmul (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ
        (levi k (i + 1) g, (p : GL (Fin (t + 1)) k)) a b
    have hR : sigC τ σ h (qC τ σ (a ⊗ₜ[ℂ] b)) =
        (((dpow (i + 1) (((t + 1 : ℕ) : ℝ) / 2) g : ℂˣ) : ℂ) • ((dpow (i + 1) (-1 / 2) g : ℂˣ) : ℂ) •
          ((twKer τ.ρ (MirUin k (i + 1)) 1).mkQ (τ.ρ (levi k (i + 1) g) a) : (psiN τ).V)) ⊗ₜ[ℂ]
        (((dpow (t + 1) (-((i + 1 : ℕ) : ℝ) / 2) (p : GL (Fin (t + 1)) k) : ℂˣ) : ℂ) • σ.ρ (p : GL (Fin (t + 1)) k) b) := by
      show extTensor _ _ (gpProj k (i + 1) t h) (qC τ σ (a ⊗ₜ[ℂ] b)) = _
      have hq : qC τ σ (a ⊗ₜ[ℂ] b) = ((twKer τ.ρ (MirUin k (i + 1)) 1).mkQ a : (psiN τ).V) ⊗ₜ[ℂ] b := rfl
      have hgp : gpProj k (i + 1) t h = (g, p) := Prod.ext hgdef hpdef
      rw [hq, hgp]
      exact extTensor_tmul ((psiN τ).tw (((t + 1 : ℕ) : ℝ) / 2)).ρ (mtw (gres σ) (-((i + 1 : ℕ) : ℝ) / 2)).ρ (g, p)
        ((twKer τ.ρ (MirUin k (i + 1)) 1).mkQ a : (psiN τ).V) b
    have hg : dpow (i + 1) (1 / 2) g * dpow (i + 1) (-1 / 2) g = (1 : ℂˣ) := by
      have e := DFunLike.congr_fun (GlobalTheory.CompanionTheory.LeibOrd.DerivTw.dpow_add (k := k) (i + 1) (-1 / 2) (1 / 2)) g
      rw [MonoidHom.mul_apply] at e
      rw [← e, show (-1 / 2 + 1 / 2 : ℝ) = 0 by norm_num, GlobalTheory.CompanionTheory.LeibOrd.DerivTw.dpow_zero]
      rfl
    have hp : dpow (t + 1) (-((i + 1 + 1 : ℕ) : ℝ) / 2) (p : GL (Fin (t + 1)) k) =
        dpow (t + 1) (-1 / 2) (p : GL (Fin (t + 1)) k) * dpow (t + 1) (-((i + 1 : ℕ) : ℝ) / 2) (p : GL (Fin (t + 1)) k) := by
      have e := DFunLike.congr_fun (GlobalTheory.CompanionTheory.LeibOrd.DerivTw.dpow_add (k := k) (t + 1) (-((i + 1 : ℕ) : ℝ) / 2) (-1 / 2))
        (p : GL (Fin (t + 1)) k)
      rw [MonoidHom.mul_apply] at e
      rw [← e]
      congr 2
      push_cast
      ring
    have hg' : ((dpow (i + 1) (1 / 2) g : ℂˣ) : ℂ) * ((dpow (i + 1) (-1 / 2) g : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, hg, Units.val_one]
    have hq : qC τ σ ((τ.ρ (levi k (i + 1) g) a) ⊗ₜ[ℂ] (σ.ρ (p : GL (Fin (t + 1)) k) b)) =
        ((twKer τ.ρ (MirUin k (i + 1)) 1).mkQ (τ.ρ (levi k (i + 1) g) a) : (psiN τ).V) ⊗ₜ[ℂ] (σ.ρ (p : GL (Fin (t + 1)) k) b) := rfl
    rw [hL, hR, GlobalTheory.CompanionTheory.LeibOrd.DerivTw.dpowM_levi, hp, TensorProduct.smul_tmul_smul, map_smul, hq]
    exact tmul_scalars _ _ _ _ _ _ _ hg'

end GlobalTheory.CompanionTheory.BZPhiPG.QLevi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactConjugateCentrePowerBounded
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.CuspGrowth


open GlobalTheory.IdeleCovolume GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele in
theorem abs_le_of_conj_mem_compact : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a →
    ∀ Q : Set (GA E a), IsCompact Q → ∃ n₀ : ℕ, ∀ (γ : GL (Fin a) E) (n : ℤ) (x : GA E a),
      x⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * x ∈ Q → |n| ≤ n₀ := by
  intro E _ _ _ a ha Q hQ
  have hf : Continuous fun g : GA E a => Real.log (ideleNorm (E := E) (GeneralLinearGroup.det g)) :=
    (continuous_ideleNorm.comp GeneralLinearGroup.continuous_det).log fun _ => ideleNorm_ne_zero _
  obtain ⟨B, hB⟩ := (hQ.image hf).isBounded.exists_norm_le
  have hL : 0 < Real.log (ideleNorm (E := E) (eIdele E)) := Real.log_pos (one_lt_ideleNorm_eIdele E)
  set L := Real.log (ideleNorm (E := E) (eIdele E)) with hLdef
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  refine ⟨⌈B / (a * L)⌉₊, fun γ n x hx => ?_⟩
  have hd : GeneralLinearGroup.det (ratGL E a γ) = diag E (GeneralLinearGroup.det γ) :=
    Units.ext (by rw [ratGL, GlobalTheory.CuspRep.det_map]; rfl)
  have hv : Real.log (ideleNorm (E := E) (GeneralLinearGroup.det
      (x⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * x))) = (n : ℝ) * (a * L) := by
    have h1 : GeneralLinearGroup.det (x⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * x) =
        diag E (GeneralLinearGroup.det γ) * (eIdele E ^ a) ^ n := by
      rw [map_mul, map_mul, map_mul, map_inv, map_zpow, hd, det_splitCentre_one, mul_comm, ← mul_assoc,
        mul_inv_cancel, one_mul]
    rw [h1, map_mul, show ideleNorm (E := E) (diag E _) = 1 from ideleNorm_principalIdele _, one_mul,
      map_zpow, map_pow, Real.log_zpow, Real.log_pow]
  have hb := hB _ ⟨_, hx, rfl⟩
  beta_reduce at hb
  rw [hv, Real.norm_eq_abs, abs_mul, abs_of_pos (mul_pos ha' hL)] at hb
  have h2 : ((|n| : ℤ) : ℝ) ≤ B / (a * L) := by
    rw [le_div_iff₀ (mul_pos ha' hL)]
    simpa using hb
  have h3 : ((|n| : ℤ) : ℝ) ≤ ((⌈B / (a * L)⌉₊ : ℤ) : ℝ) := by
    rw [Int.cast_natCast]
    exact h2.trans (Nat.le_ceil _)
  exact Int.cast_le.1 h3

end GlobalTheory.CompanionTheory.CuspGrowth
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactConjugateRationalEntriesBounded
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic
open scoped ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.GrowthEntries

open GlobalTheory.CompanionTheory.BoxBound

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem norm_entry_le_toL (A : Matrix (Fin a) (Fin a) (Cinf E)) (i j : Fin a) (w : InfinitePlace E) :
    ‖A i j w‖ ≤ ‖toL A‖ :=
  (norm_le_pi_norm (A i j) w).trans
    ((norm_le_pi_norm (toL A i) j).trans (norm_le_pi_norm (toL A) i))

theorem norm_toL_le_height (y : GL (Fin a) (Cinf E)) : ‖toL y.val‖ ≤ height y := by
  have := norm_nonneg (toL (y⁻¹).val)
  unfold height
  linarith

theorem norm_toL_inv_le_height (y : GL (Fin a) (Cinf E)) : ‖toL (y⁻¹).val‖ ≤ height y := by
  have := norm_nonneg (toL y.val)
  unfold height
  linarith

theorem norm_toL_mul_le_of_le {u v : GL (Fin a) (Cinf E)} {p r : ℝ} (hu : ‖toL u.val‖ ≤ p)
    (hv : ‖toL v.val‖ ≤ r) : ‖toL (u * v).val‖ ≤ a * (p * r) :=
  (norm_toL_mul_le u.val v.val).trans (mul_le_mul_of_nonneg_left
    (mul_le_mul hu hv (norm_nonneg _) ((norm_nonneg _).trans hu)) (Nat.cast_nonneg a))

theorem gFin_mul (g h : GA E a) : gFin (g * h) = gFin g * gFin h := map_mul _ g h

theorem gFin_inv (g : GA E a) : gFin g⁻¹ = (gFin g)⁻¹ := map_inv _ g

theorem gFin_zpow (g : GA E a) (n : ℤ) : gFin (g ^ n) = gFin g ^ n := map_zpow _ g n

theorem gInf_mul (g h : GA E a) : gInf (g * h) = gInf g * gInf h := map_mul _ g h

theorem gInf_inv (g : GA E a) : gInf g⁻¹ = (gInf g)⁻¹ := map_inv _ g

theorem gFin_splitCentre (t : ℝ) : gFin (splitCentre E a t) = 1 := pFin_infGL _

theorem exists_bound_splitCentre (n₀ : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ m : ℤ, |m| ≤ n₀ →
    ‖toL (gInf (splitCentre E a 1 ^ m)).val‖ ≤ B := by
  refine ⟨∑ m ∈ Finset.Icc (-(n₀ : ℤ)) n₀, ‖toL (gInf (splitCentre E a 1 ^ m)).val‖,
    Finset.sum_nonneg fun _ _ => norm_nonneg _, fun m hm => ?_⟩
  exact Finset.single_le_sum (f := fun m : ℤ => ‖toL (gInf (splitCentre E a 1 ^ m)).val‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_Icc.2 (abs_le.1 hm))

theorem place_eq_norm_pInf (x : E) (w : InfinitePlace E) :
    w x = ‖pInf E (algebraMap E (Ad E) x) w‖ := by
  rw [pInf_algebraMap, InfinitePlace.norm_embedding_eq]

theorem entries_bound : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (g₀ : GA E a)
    (Q : Set (GA E a)), IsCompact Q → ∀ n₀ : ℕ, ∃ (Qf : Set (Af E)) (C : ℝ), IsCompact Qf ∧ 0 ≤ C ∧
      ∀ (y : GL (Fin a) (Cinf E)) (γ : GL (Fin a) E) (n : ℤ), |n| ≤ n₀ →
        (g₀ * infGL E a y)⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * (g₀ * infGL E a y) ∈ Q →
        ∀ i j, algebraMap E (Af E) (γ.val i j) ∈ Qf ∧ ∀ w : InfinitePlace E, w (γ.val i j) ≤ C * height y ^ 2 := by
  intro E _ _ _ a g₀ Q hQ n₀
  have hK : IsCompact ((fun q : GA E a => gFin g₀ * gFin q * (gFin g₀)⁻¹) '' Q) :=
    hQ.image ((continuous_const.mul continuous_gFin).mul continuous_const)
  have hent : ∀ i j : Fin a, Continuous fun g : GL (Fin a) (Af E) => g.val i j := fun i j =>
    (Units.continuous_val : Continuous fun g : GL (Fin a) (Af E) => (g.val : Matrix (Fin a) (Fin a) (Af E))).matrix_elem i j
  obtain ⟨B, hB0, hB⟩ := exists_height_bound (E := E) (a := a) hQ
  obtain ⟨Z, hZ0, hZ⟩ := exists_bound_splitCentre (E := E) (a := a) n₀
  set g1 : ℝ := ‖toL (gInf g₀).val‖ with hg1
  set g2 : ℝ := ‖toL ((gInf g₀)⁻¹).val‖ with hg2
  have hg10 : 0 ≤ g1 := norm_nonneg _
  have hg20 : 0 ≤ g2 := norm_nonneg _
  refine ⟨⋃ i, ⋃ j, (fun g : GL (Fin a) (Af E) => g.val i j) '' ((fun q : GA E a => gFin g₀ * gFin q * (gFin g₀)⁻¹) '' Q),
    (a : ℝ) ^ 5 * (g1 * g2 * B * Z),
    isCompact_iUnion fun i => isCompact_iUnion fun j => hK.image (hent i j),
    mul_nonneg (pow_nonneg (Nat.cast_nonneg a) 5) (mul_nonneg (mul_nonneg (mul_nonneg hg10 hg20) hB0) hZ0), ?_⟩
  intro y γ n hn hq i j
  set X : GA E a := g₀ * infGL E a y with hX
  set q : GA E a := X⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * X with hqdef
  have h1 : ratGL E a γ * splitCentre E a 1 ^ n = X * q * X⁻¹ := by
    rw [hqdef]; group
  have hfin : gFin (ratGL E a γ) = gFin g₀ * gFin q * (gFin g₀)⁻¹ := by
    have e1 : gFin X = gFin g₀ := by
      rw [hX, gFin_mul, show gFin (infGL E a y) = 1 from pFin_infGL y, mul_one]
    have e2 : gFin (splitCentre E a 1 ^ n) = 1 := by
      rw [gFin_zpow, gFin_splitCentre, _root_.one_zpow]
    have h := congrArg gFin h1
    rw [gFin_mul, e2, mul_one, gFin_mul, gFin_mul, gFin_inv, e1] at h
    exact h
  have hinf : gInf (ratGL E a γ) =
      gInf g₀ * y * gInf q * y⁻¹ * (gInf g₀)⁻¹ * gInf (splitCentre E a 1 ^ (-n)) := by
    have h2 : ratGL E a γ = X * q * X⁻¹ * splitCentre E a 1 ^ (-n) := by
      rw [← h1, _root_.zpow_neg, mul_inv_cancel_right]
    have e1 : gInf X = gInf g₀ * y := by
      rw [hX, gInf_mul, show gInf (infGL E a y) = y from pInf_infGL y]
    have h := congrArg gInf h2
    rw [gInf_mul, gInf_mul, gInf_mul, gInf_inv, e1] at h
    rw [h]
    group
  refine ⟨?_, fun w => ?_⟩
  · refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, ?_⟩⟩
    exact ⟨gFin (ratGL E a γ), ⟨q, hq, hfin.symm⟩, rfl⟩
  · have hy := norm_toL_le_height y
    have hy' := norm_toL_inv_le_height y
    have hR : ‖toL (gInf q).val‖ ≤ B := (norm_toL_le_height _).trans (hB q hq)
    have hZn : ‖toL (gInf (splitCentre E a 1 ^ (-n))).val‖ ≤ Z := hZ (-n) (by rwa [abs_neg])
    have hM := norm_toL_mul_le_of_le (norm_toL_mul_le_of_le (norm_toL_mul_le_of_le
      (norm_toL_mul_le_of_le (norm_toL_mul_le_of_le (le_refl g1) hy) hR) hy') (le_refl g2)) hZn
    rw [← hinf] at hM
    rw [place_eq_norm_pInf]
    have he : ‖pInf E (algebraMap E (Ad E) (γ.val i j)) w‖ ≤ ‖toL (gInf (ratGL E a γ)).val‖ :=
      norm_entry_le_toL (gInf (ratGL E a γ)).val i j w
    refine he.trans (hM.trans_eq ?_)
    ring

end GlobalTheory.CompanionTheory.GrowthEntries

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactFiniteAdelicDenominator
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.AdeleDenom

open IsDedekindDomain

theorem isIntegral_of_forall_mem_adicCompletionIntegers {F : Type} [Field F] [NumberField F] (f : F)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), (f : v.adicCompletion F) ∈ HeightOneSpectrum.adicCompletionIntegers F v) :
    IsIntegral ℤ f := by
  obtain ⟨r, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) (x := f)
    (fun v => by
      have hv := h v
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.adicCompletion.valued_coe] at hv
      exact hv)
  exact NumberField.RingOfIntegers.isIntegral_coe r

theorem exists_nat_mul_isIntegral_of_isCompact (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (L : Set (Af F ⊗[F] E)) (hL : IsCompact L) :
    ∃ d : ℕ, 0 < d ∧ ∀ e : E, inclR (F := F) (Af F) e ∈ L → IsIntegral ℤ ((d : E) * e) := by
  classical
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have key : ∀ x : E, ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : E) * x) := by
    intro x
    have halg : IsAlgebraic ℤ x :=
      (IsFractionRing.isAlgebraic_iff (A := ℤ) (K := ℚ) (C := E)).mpr (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x)
    obtain ⟨y, hy, hyx⟩ := halg.exists_integral_multiple
    refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
    have hc : ((y.natAbs : ℕ) : E) = ((|y| : ℤ) : E) := by
      rw [← Int.cast_natCast, Int.natCast_natAbs]
    rcases abs_choice y with h | h
    · rw [hc, h, ← zsmul_eq_mul]
      exact hyx
    · rw [hc, h, Int.cast_neg, neg_mul, ← zsmul_eq_mul]
      exact hyx.neg
  let b := Module.finBasis F E
  choose mm hmm0 hmm using fun i => key (b i)
  obtain ⟨m, hm0, hmb⟩ : ∃ m : ℕ, 0 < m ∧ ∀ i, IsIntegral ℤ ((m : E) * b i) := by
    refine ⟨∏ i, mm i, Finset.prod_pos fun i _ => hmm0 i, fun i => ?_⟩
    have hsplit : ((∏ j, mm j : ℕ) : E) = ((∏ j ∈ Finset.univ.erase i, mm j : ℕ) : E) * (mm i : E) := by
      rw [← Nat.cast_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    rw [hsplit, mul_assoc]
    refine IsIntegral.mul ?_ (hmm i)
    simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := ((∏ j ∈ Finset.univ.erase i, mm j : ℕ) : ℤ)))
  let B := Algebra.TensorProduct.basis (Af F) b
  let φ : (Af F ⊗[F] E) →ₗ[Af F] (Fin (Module.finrank F E) → Af F) := B.equivFun.toLinearMap
  have hφ : Continuous φ := IsModuleTopology.continuous_of_linearMap φ
  obtain ⟨N, hN, hNK⟩ := GlobalTheory.WeilM.exists_nat_mul_integral_of_isCompact F (hL.image hφ)
  refine ⟨N * m, Nat.mul_pos hN hm0, fun e he => ?_⟩
  have hx := hNK (φ (inclR (F := F) (Af F) e)) ⟨_, he, rfl⟩
  have hcoord : ∀ i, φ (inclR (F := F) (Af F) e) i = algebraMap F (Af F) (b.repr e i) := by
    intro i
    have hincl : inclR (F := F) (Af F) e = (1 : Af F) ⊗ₜ[F] e := rfl
    simp [φ, B, hincl, Algebra.TensorProduct.basis_repr_tmul]
  have hint : ∀ i, IsIntegral ℤ ((N : F) * b.repr e i) := by
    intro i
    refine isIntegral_of_forall_mem_adicCompletionIntegers _ fun v => ?_
    have h1 := hx i v
    rw [hcoord, ← map_natCast (algebraMap F (Af F)) N, ← map_mul] at h1
    exact h1
  have hsum : ((N * m : ℕ) : E) * e = ∑ i, algebraMap F E ((N : F) * b.repr e i) * ((m : E) * b i) := by
    conv_lhs => rw [← b.sum_repr e]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, map_natCast]
    push_cast
    ring
  rw [hsum]
  exact IsIntegral.sum _ fun i _ => (hint i).algebraMap.mul (hmb i)

end GlobalTheory.CompanionTheory.AdeleDenom
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousHermPart
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HermVol

variable (D : D7) (r : ℕ)

def hermPart (x : Mx D r r) : Mx D r r := half D • (x + adj x)

variable {D r}

theorem hermPart_mem (x : Mx D r r) : hermPart D r x ∈ hermA D r := by
  change adj (hermPart D r x) = hermPart D r x
  rw [hermPart, adj_smul, cA_half, adj_add, adj_adj, add_comm]

theorem hermPart_of_mem {c : Mx D r r} (hc : c ∈ hermA D r) : hermPart D r c = c := by
  have h : adj c = c := hc
  rw [hermPart, h, smul_add, half_smul_add]

theorem hermPart_add (x y : Mx D r r) : hermPart D r (x + y) = hermPart D r x + hermPart D r y := by
  rw [hermPart, hermPart, hermPart, adj_add, add_add_add_comm, smul_add]

theorem hermPart_rat {x : Mx D r r} (hx : x ∈ ratMx D r r) : hermPart D r x ∈ ratMx D r r := by
  obtain ⟨γ, rfl⟩ := (mem_ratMx).1 hx
  refine (mem_ratMx).2 ⟨(1 / 2 : D.host.E) • (γ + γᴴ), ?_⟩
  rw [rat_smul, rat_add, rat_conjTranspose]; rfl

set_option synthInstance.maxHeartbeats 400000 in
theorem continuous_hermPart : Continuous (hermPart D r) :=
  haveI : IsTopologicalAddGroup (Mx D r r) := (lattice_Mx D r r).1
  show Continuous fun x => half D • (x + adj x) from (continuous_id.add continuous_adj).const_smul (half D)

theorem isClosed_hermA : IsClosed (hermA D r : Set (Mx D r r)) :=
  haveI : T2Space (Mx D r r) := (lattice_Mx D r r).2.2.2.1
  isClosed_eq continuous_adj continuous_id

theorem isCoLat_herm : GlobalTheory.CuspGeneric.IsCoLat (ratHerm D r) := by
  obtain ⟨-, -, -, -, i5, K, hK, hKc⟩ := lattice_Mx D r r
  refine ⟨?_, ?_⟩
  · let φ : ratHerm D r → ratMx D r r := fun q => ⟨q.1.1, q.2⟩
    have hinj : Function.Injective φ := fun a b h =>
      Subtype.ext (Subtype.ext (by simpa [φ] using congrArg Subtype.val h))
    have hcont : Continuous φ :=
      ((continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
    exact DiscreteTopology.of_continuous_injective hcont hinj
  · let P : Mx D r r → hermA D r := fun x => ⟨hermPart D r x, hermPart_mem x⟩
    have hP : Continuous P := continuous_hermPart.subtype_mk _
    refine ⟨P '' K, hK.image hP, fun x => ?_⟩
    obtain ⟨γ, hγ, hx⟩ := hKc x.1
    refine ⟨P γ, AddSubgroup.mem_comap.2 (hermPart_rat hγ), γ + x.1, hx, ?_⟩
    apply Subtype.ext
    change hermPart D r (γ + x.1) = hermPart D r γ + x.1
    rw [hermPart_add, hermPart_of_mem x.2]

theorem exists_isCovolOneH : ∀ (D : Formalism.BasicNotions.D7) (r : ℕ), ∃ (lam : Measure (PositivityTheory.GramSchwartzFunctions.BC.hermA D r)) (𝓖 : Set (PositivityTheory.GramSchwartzFunctions.BC.hermA D r)), PositivityTheory.GramSchwartzFunctions.BC.IsCovolOneH lam 𝓖 := by
  intro D r
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D r r
  haveI : IsTopologicalAddGroup (Mx D r r) := i1
  haveI : LocallyCompactSpace (Mx D r r) := i2
  haveI : SecondCountableTopology (Mx D r r) := i3
  haveI : T2Space (Mx D r r) := i4
  haveI : SecondCountableTopology (hermA D r) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (hermA D r) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : BorelSpace (Mx D r r) := ⟨rfl⟩
  haveI : LocallyCompactSpace (hermA D r) := (isClosed_hermA (D := D) (r := r)).locallyCompactSpace
  obtain ⟨μ, 𝓕, hμ, hF, h1⟩ :=
    GlobalTheory.CuspGeneric.exists_fundamentalDomain_mass_one (hermA D r) _ isCoLat_herm
  exact ⟨μ, 𝓕, hμ, hF, h1⟩

end GlobalTheory.CompanionTheory.HermVol
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousResQ
section
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum

noncomputable section
namespace GlobalTheory.CompanionTheory.CuspTransfer

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def resQ (φ : GA E a → ℂ) : RightCosetSpace (rationalGLOne (K := E) (n := a)) → ℂ :=
  fun q => φ ((Quotient.out q : normOneGL (K := E) (n := a)) : GA E a)

theorem resQ_mk {φ : GA E a → ℂ} (h : ∀ γ g, φ (ratGL E a γ * g) = φ g) (x : normOneGL (K := E) (n := a)) :
    resQ φ (RightCosetSpace.mk _ x) = φ x := by
  have e : RightCosetSpace.mk (rationalGLOne (K := E) (n := a))
      (Quotient.out (RightCosetSpace.mk (rationalGLOne (K := E) (n := a)) x)) = RightCosetSpace.mk _ x :=
    Quotient.out_eq _
  obtain ⟨γ, hγ⟩ := RightCosetSpace.mk_eq_mk_iff.1 e
  obtain ⟨δ, hδ⟩ : ((γ : normOneGL (K := E) (n := a)) : GA E a) ∈ AdelicGLn.rationalGL E a := γ.2
  unfold resQ
  rw [← hγ]
  change φ (((γ : normOneGL (K := E) (n := a)) : GA E a) * (x : GA E a)) = _
  rw [← hδ]
  exact h δ x.1

theorem continuous_resQ {φ : GA E a → ℂ} (hc : Continuous φ) (h : ∀ γ g, φ (ratGL E a γ * g) = φ g) :
    Continuous (resQ φ) := by
  refine (RightCosetSpace.isOpenQuotientMap_mk (rationalGLOne (K := E) (n := a))).isQuotientMap.continuous_iff.2 ?_
  have : resQ φ ∘ RightCosetSpace.mk (rationalGLOne (K := E) (n := a)) = fun x : normOneGL (K := E) (n := a) => φ x :=
    funext fun x => resQ_mk h x
  rw [this]
  exact hc.comp continuous_subtype_val

end GlobalTheory.CompanionTheory.CuspTransfer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHeckeFunctionalStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_hecke_functional : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ), IsSec K χ s₁ f → IsHecke F E χ → ∀ (t : ℝ) (Ê : ℂ → G2 σ Y → ℂ), (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) → ∀ s : ℂ, t < s.re → ∀ γ ∈ rat2 σ Y, ∀ x, Ê s (γ * x) = Ê s x := by
  first | exact @GlobalTheory.CompanionTheory.EisRat.eis_left_rat | exact GlobalTheory.CompanionTheory.EisRat.eis_left_rat | (intros; apply GlobalTheory.CompanionTheory.EisRat.eis_left_rat <;> assumption)
end

