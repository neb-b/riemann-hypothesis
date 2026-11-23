module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0314
public import GroundTheory.AutomorphicForms.Bundle0023
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0616
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0300
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0313
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.QcohLocal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0315
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0301

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentLatticeDecomposition
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusCh.Signs

theorem sMeet_single_single {m : ℕ} {j k : Fin m} (hjk : j ≠ k) (x y : SignType) :
    sMeet (Pi.single j x) (Pi.single k y) = (0 : Fin m → SignType) := by
  funext i
  unfold sMeet
  by_cases hij : i = j
  · subst hij
    have h1 : (Pi.single k y : Fin m → SignType) i = 0 := Pi.single_eq_of_ne hjk _
    rw [h1, Pi.single_eq_same]
    by_cases hx : x = 0 <;> simp [hx]
  · have h1 : (Pi.single j x : Fin m → SignType) i = 0 := Pi.single_eq_of_ne hij _
    rw [h1]
    simp

theorem sLe_single {m : ℕ} (e : Fin m → SignType) (j : Fin m) : SLe (Pi.single j (e j)) e := by
  intro i hi
  by_cases hij : i = j
  · subst hij
    simp
  · exact absurd (Pi.single_eq_of_ne hij _) hi

theorem sLe_of_sMeet {m : ℕ} {e e' : Fin m → SignType} (h : sMeet e e' = e) : SLe e e' := by
  intro i hi
  have h1 := congrFun h i
  unfold sMeet at h1
  by_cases h2 : e i = e' i
  · exact h2.symm
  · rw [if_neg h2] at h1
    exact absurd h1.symm hi

theorem eq_neg_one_of {x : SignType} : x ≠ 0 → x ≠ 1 → x = -1 := by
  revert x
  decide

variable {R : Type} [CommRing R] (σ : R →+* R) {m : ℕ} (P : (Fin m → SignType) → R)

theorem additive (hP2 : ∀ e, P e * P e = P e) (hiso : ∀ e, P e * σ (P e) = 0)
    (hsurj : ∀ p, p * p = p → p * σ p = 0 → ∃ e, P e = p) (hinj : Function.Injective P) (hP0 : P 0 = 0)
    (hmeet : ∀ e e', P (sMeet e e') = P e * P e') (hle : ∀ e e', SLe e e' → P e * P e' = P e)
    (e : Fin m → SignType) : P e = ∑ j, P (Pi.single j (e j)) := by
  set a : Fin m → Fin m → SignType := fun j => Pi.single j (e j) with ha
  have h2 : ∀ j k, j ≠ k → P (a j) * P (a k) = 0 := by
    intro j k hjk
    rw [← hmeet, ha]
    simp only
    rw [sMeet_single_single hjk, hP0]
  have h4 : ∀ j, P (a j) * P e = P (a j) := fun j => hle _ _ (sLe_single e j)
  set q : R := ∑ j, P (a j) with hq
  have h5 : ∀ j, P (a j) * q = P (a j) := by
    intro j
    rw [hq, Finset.mul_sum, Finset.sum_eq_single j (fun k _ hk => h2 j k hk.symm)
      (fun h => absurd (Finset.mem_univ j) h), hP2]
  have hqq : q * q = q := by
    conv_lhs => rw [hq, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => h5 j
  have hqe : q * P e = q := by
    conv_lhs => rw [hq, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => h4 j
  have hPe := hP2 e
  set r : R := P e - q with hr
  have hrr : r * r = r := by
    rw [hr]
    linear_combination hPe - 2 * hqe + hqq
  have hre : r * P e = r := by
    rw [hr]
    linear_combination hPe - hqe
  have hrs : r * σ r = 0 := by
    calc r * σ r = (r * P e) * σ (r * P e) := by rw [hre]
      _ = r * σ r * (P e * σ (P e)) := by rw [map_mul]; ring
      _ = 0 := by rw [hiso, mul_zero]
  obtain ⟨e', he'⟩ := hsurj r hrr hrs
  have hm : sMeet e' e = e' := hinj (by rw [hmeet, he', hre])
  have hse : SLe e' e := sLe_of_sMeet hm
  have he0 : e' = 0 := by
    funext j
    by_contra hne
    have hne' : e' j ≠ 0 := hne
    have hej : e j = e' j := hse j hne'
    have hs : SLe (a j) e' := by
      intro i hi
      by_cases hij : i = j
      · subst hij
        simp [ha, hej]
      · exact absurd (Pi.single_eq_of_ne hij _) hi
    have h6 : P (a j) * r = P (a j) := by
      rw [← he']
      exact hle _ _ hs
    have h7 : P (a j) * r = 0 := by
      rw [hr, mul_sub, h4, h5, sub_self]
    have h8 : a j = 0 := hinj (by rw [hP0, ← h6, h7])
    have h9 := congrFun h8 j
    simp only [ha, Pi.single_eq_same, Pi.zero_apply] at h9
    exact hne' (hej ▸ h9)
  have hr0 : r = 0 := by rw [← he', he0, hP0]
  exact sub_eq_zero.1 hr0

theorem conj_single (hσ : ∀ x, σ (σ x) = x) (hP2 : ∀ e, P e * P e = P e) (hiso : ∀ e, P e * σ (P e) = 0)
    (hsurj : ∀ p, p * p = p → p * σ p = 0 → ∃ e, P e = p) (hinj : Function.Injective P) (hP0 : P 0 = 0)
    (hle : ∀ e e', SLe e e' → P e * P e' = P e) (j : Fin m) :
    P (Pi.single j (-1)) = σ (P (Pi.single j 1)) := by
  set δ : Fin m → SignType := Pi.single j 1 with hδ
  have hδ0 : δ ≠ 0 := by
    intro h
    have h1 := congrFun h j
    simp [hδ] at h1
  set p : R := P δ with hp
  set s : R := σ p with hs
  have hpp : p * p = p := hP2 δ
  have hps : p * s = 0 := hiso δ
  have hss : s * s = s := by rw [hs, ← map_mul, hpp]
  have hsp : σ s = p := hσ p
  have hsσ : s * σ s = 0 := by rw [hsp, mul_comm, hps]
  obtain ⟨e'', he''⟩ := hsurj s hss hsσ
  have hsupp : ∀ k, k ≠ j → e'' k = 0 := by
    intro k hkj
    by_contra hne
    set β : Fin m → SignType := Pi.single k (e'' k) with hβ
    set c : Fin m → SignType := Function.update δ k (e'' k) with hc
    have hδc : SLe δ c := by
      intro i hi
      have hik : i ≠ k := by
        rintro rfl
        exact hi (Pi.single_eq_of_ne hkj _)
      exact Function.update_of_ne hik _ _
    have hβc : SLe β c := by
      intro i hi
      by_cases hik : i = k
      · subst hik
        simp [hβ, hc]
      · exact absurd (Pi.single_eq_of_ne hik _) hi
    have h1 : p * σ (P β) = 0 := by
      calc p * σ (P β) = (p * P c) * σ (P β * P c) := by rw [hp, hle _ _ hδc, hle _ _ hβc]
        _ = p * σ (P β) * (P c * σ (P c)) := by rw [map_mul]; ring
        _ = 0 := by rw [hiso, mul_zero]
    have h2 : P β * s = P β := by
      rw [← he'']
      exact hle _ _ (sLe_single e'' k)
    have h3 : σ (P β) * p = σ (P β) := by
      have := congrArg σ h2
      rwa [map_mul, hsp] at this
    have h4 : σ (P β) = 0 := by
      rw [← h3, mul_comm, h1]
    have h5 : P β = 0 := by
      rw [← hσ (P β), h4, map_zero]
    have h6 : β = 0 := hinj (by rw [h5, hP0])
    have h7 := congrFun h6 k
    simp only [hβ, Pi.single_eq_same, Pi.zero_apply] at h7
    exact hne h7
  have hform : e'' = Pi.single j (e'' j) := by
    funext i
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Pi.single_eq_of_ne hij, hsupp i hij]
  have hne0 : e'' j ≠ 0 := by
    intro h0
    have h1 : e'' = 0 := by
      rw [hform, h0]
      simp
    have h2 : s = 0 := by rw [← he'', h1, hP0]
    have h3 : p = 0 := by rw [← hsp, h2, map_zero]
    exact hδ0 (hinj (by rw [hP0, ← hp, h3]))
  have hne1 : e'' j ≠ 1 := by
    intro h1
    have h2 : e'' = δ := by rw [hform, h1]
    have h3 : s = p := by rw [← he'', h2]
    have h4 : p = 0 := by
      have h5 := hps
      rwa [h3, hpp] at h5
    exact hδ0 (hinj (by rw [hP0, ← hp, h4]))
  have hm1 := eq_neg_one_of hne0 hne1
  rw [← hm1, ← hform, he'']

end GlobalTheory.CompanionTheory.TorusCh.Signs

namespace GlobalTheory.CompanionTheory.TorusCh

theorem isotropicIdempotent_signs : ∀ (R : Type) [Ring R], (∀ x y : R, x * y = y * x) → ∀ (σ : R →+* R), (∀ x, σ (σ x) = x) →
    ∀ (m : ℕ) (P : (Fin m → SignType) → R), (∀ e, P e * P e = P e) → (∀ e, P e * σ (P e) = 0) →
    (∀ p, p * p = p → p * σ p = 0 → ∃ e, P e = p) → Function.Injective P → P 0 = 0 →
    (∀ e e', P (sMeet e e') = P e * P e') → (∀ e e', SLe e e' → P e * P e' = P e) →
    (∀ e, P e = ∑ j, P (Pi.single j (e j))) ∧ ∀ j, P (Pi.single j (-1)) = σ (P (Pi.single j 1)) := by
  intro R _ hc σ hσ m P hP2 hiso hsurj hinj hP0 hmeet hle
  letI : CommRing R := { (inferInstance : Ring R) with mul_comm := hc }
  exact ⟨fun e => Signs.additive σ P hP2 hiso hsurj hinj hP0 hmeet hle e,
    fun j => Signs.conj_single σ P hσ hP2 hiso hsurj hinj hP0 hle j⟩

end GlobalTheory.CompanionTheory.TorusCh
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRightDerivativeEqZero
section
noncomputable section

open Matrix MeasureTheory
open scoped ContDiff
open PositivityTheory.RgBcC (GLs Rd)
open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS.SkewInt

open scoped Matrix.Norms.Operator in
theorem exp_entry_hasDerivAt {n : ℕ} (X : Mat n) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) : Mat n) i j)
      ((NormedSpace.exp (t • X) * X : Mat n) i j) t := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X t
  let L : Mat n →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  exact L.hasFDerivAt.comp_hasDerivAt t h

theorem exp_hasDerivAt {n : ℕ} (X : Mat n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) : Mat n)) (NormedSpace.exp (t • X) * X) t := by
  have : HasDerivAt (fun s : ℝ => (fun i j => (NormedSpace.exp (s • X) : Mat n) i j : Fin n → Fin n → ℂ))
      (fun i j => (NormedSpace.exp (t • X) * X : Mat n) i j) t := by
    rw [hasDerivAt_pi]
    intro i
    rw [hasDerivAt_pi]
    intro j
    exact exp_entry_hasDerivAt X t i j
  exact this

theorem curve_hasDerivAt {n : ℕ} (k X : Mat n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => k * (NormedSpace.exp (s • X) : Mat n)) (k * NormedSpace.exp (t • X) * X) t := by
  let L : Mat n →L[ℝ] Mat n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ k)
  have h := L.hasFDerivAt.comp_hasDerivAt t (exp_hasDerivAt X t)
  have e : L (NormedSpace.exp (t • X) * X) = k * NormedSpace.exp (t • X) * X := by
    rw [Matrix.mul_assoc]
    rfl
  exact h.congr_deriv e

theorem exp_mem_unitary {n : ℕ} {X : Mat n} (hX : Xᴴ = -X) (t : ℝ) :
    (NormedSpace.exp (t • X) : Mat n) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, ← Matrix.exp_conjTranspose, conjTranspose_smul,
    star_trivial, hX, smul_neg, Matrix.exp_neg]
  exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _))

theorem integral_Rd_skew : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ] [κ.IsMulRightInvariant] (u : Mat n → ℂ), ContDiffOn ℝ ∞ u (GLs n) → ∀ X : Mat n, Xᴴ = -X → ∫ k : Matrix.unitaryGroup (Fin n) ℂ, Rd X u k.1 ∂κ = 0 := by
  intro n _ _ κ _ _ u hu X hX
  haveI : CompactSpace (Matrix.unitaryGroup (Fin n) ℂ) := GlobalTheory.compactSpace_unitaryGroup (Fin n) ℂ
  haveI : SecondCountableTopology (Mat n) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix.unitaryGroup (Fin n) ℂ) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have hmem (k : Matrix.unitaryGroup (Fin n) ℂ) : k.1 ∈ GLs n :=
    (Matrix.UnitaryGroup.det_isUnit k).ne_zero
  let kt : ℝ → Matrix.unitaryGroup (Fin n) ℂ := fun t => ⟨NormedSpace.exp (t • X), exp_mem_unitary hX t⟩
  have hval : ∀ (y : Matrix.unitaryGroup (Fin n) ℂ) (t : ℝ),
      y.1 * (NormedSpace.exp (t • X) : Mat n) = (y * kt t).1 := fun _ _ => rfl
  have hcv : Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => k.1 := continuous_subtype_val
  have hRd := GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hu
  have cU : Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => u k.1 :=
    hu.continuousOn.comp_continuous hcv hmem
  have cR : Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => Rd X u k.1 :=
    hRd.continuousOn.comp_continuous hcv hmem
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn cR.continuousOn
  have key := GlobalTheory.CompanionTheory.RCalc.ByParts.integral_deriv_eq_zero (μ := κ) (V := ℂ)
    (F := fun t y => u (y.1 * (NormedSpace.exp (t • X) : Mat n)))
    (F' := fun t y => Rd X u (y.1 * (NormedSpace.exp (t • X) : Mat n)))
    (K := Set.univ) isCompact_univ (ε := 1) one_pos C ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa using key
  · intro t _
    simp only [hval]
    exact cU.comp (continuous_mul_const (kt t))
  · simp only [hval]
    exact cR.comp (continuous_mul_const (kt 0))
  · intro y t _
    have hg : y.1 * (NormedSpace.exp (t • X) : Mat n) ∈ GLs n := by
      rw [hval]
      exact hmem _
    have h := (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hu hg).hasFDerivAt.comp_hasDerivAt t
      (curve_hasDerivAt y.1 X t)
    exact h
  · intro y hy
    exact absurd (Set.mem_univ y) hy
  · intro t _ y hy
    exact absurd (Set.mem_univ y) hy
  · intro t _ y _
    simp only [hval]
    exact hC _ (Set.mem_univ _)
  · intro t _
    simp only [hval]
    have h0 : kt 0 = 1 := by
      apply Subtype.ext
      simp [kt]
    rw [h0]
    simp only [mul_one]
    exact integral_mul_right_eq_self (fun y : Matrix.unitaryGroup (Fin n) ℂ => u y.1) (kt t)

end GlobalTheory.CompanionTheory.ModelS.SkewInt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriLeviUnipotentFactor
section
open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

namespace GlobalTheory.CompanionTheory.KOneFactor

open GlobalTheory.LocGL GlobalTheory.LocGL.IwahoriFactor

theorem sub_one_apply_eq_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n s : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n)
    {c : GL (Fin n) k} (hc : c ∈ unipRadLower k e) (i j : Fin n)
    (hij : ¬ (e.symm j).1 < (e.symm i).1) : ((c : Matrix (Fin n) (Fin n) k) - 1) i j = 0 := by
  obtain ⟨hP, hD⟩ := (GlobalTheory.SmGL.mem_unipRadLower k).1 hc
  have hB := (GlobalTheory.SmGL.mem_parabLower_iff k).1 hP
  obtain ⟨⟨a, p⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, q⟩, rfl⟩ := e.surjective j
  simp only [Equiv.symm_apply_apply] at hij
  rw [Matrix.sub_apply, sub_eq_zero]
  rcases (not_lt.1 hij).lt_or_eq with hab | rfl
  · rw [hB a b p q hab, GlobalTheory.LocGL.IwahoriFactor.one_ne e hab.ne p q]
  · rw [hD a p q, GlobalTheory.LocGL.IwahoriFactor.one_same e a p q]

theorem kone_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ∀ g ∈ KOne k (Fin n),
    ∃ m : Levi k (fun a => Fin (d a)), leviEmb k e m ∈ KOne k (Fin n) ∧
      ∃ x ∈ unipRad k e ⊓ KOne k (Fin n), ∃ c ∈ lowC k e, g = leviEmb k e m * x * c := by
  intro k _ _ _ _ n s d e g hg
  obtain ⟨c, hc, hgc⟩ := GlobalTheory.LocGL.IwahoriFactor.exists_mul_mem_parab e hg
  have hcP : c ∈ GlobalTheory.SplitWeil.KOne k (Fin n) := by
    first
    | exact hc.2
    | exact hc.1
    | exact (Subgroup.mem_inf.1 hc).2
    | exact (Subgroup.mem_inf.1 hc).1
  have hcl : c⁻¹ ∈ GlobalTheory.SmGL.unipRadLower k e := by
    have hci := inv_mem hc
    first
    | exact hci.1
    | exact hci.2
    | exact (Subgroup.mem_inf.1 hci).1
    | exact (Subgroup.mem_inf.1 hci).2
    | exact hci
  obtain ⟨u, hu, hpu⟩ := GlobalTheory.SmGL.exists_levi_mul_unip k e ⟨g * c, hgc⟩
  let m := GlobalTheory.SmGL.leviProj k e ⟨g * c, hgc⟩
  have hpP : leviEmb k e m ∈ KOne k (Fin n) := by
    apply StepData.mem_KOne.2
    intro i j
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
    by_cases hab : a = b
    · subst b
      have h := StepData.mem_KOne.1 (mul_mem hg hcP) (e ⟨a, i⟩) (e ⟨a, j⟩)
      rw [Matrix.sub_apply, one_same] at h
      simpa [Matrix.sub_apply, one_same, m] using h
    · rw [Matrix.sub_apply, GlobalTheory.SmGL.leviEmb_apply_ne k e m hab, one_ne e hab, sub_zero, map_zero]
      exact zero_lt_one
  refine ⟨m, hpP, u, ?_, c⁻¹, ?_, eq_mul_inv_of_mul_eq hpu⟩
  · have hug : (GlobalTheory.SmGL.leviEmb k e m)⁻¹ * (g * c) = u := inv_mul_eq_iff_eq_mul.2 hpu
    have huP : u ∈ GlobalTheory.SplitWeil.KOne k (Fin n) := by
      rw [← hug]
      exact mul_mem (inv_mem hpP) (mul_mem hg hcP)
    have hur : u ∈ GlobalTheory.SmGL.unipRad k e := by
      first
      | exact hu
      | exact hu.1
      | exact hu.2
      | exact (Subgroup.mem_inf.1 hu).1
      | exact (Subgroup.mem_inf.1 hu).2
    exact Subgroup.mem_inf.2 ⟨hur, huP⟩
  · show _ ∧ _
    exact ⟨inv_mem hcP, fun i j hij => GlobalTheory.CompanionTheory.KOneFactor.sub_one_apply_eq_zero e hcl i j hij⟩

end GlobalTheory.CompanionTheory.KOneFactor
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelOperatorsEventuallyGenerate
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.UV

variable {X : Scheme.{0}} {k : ℕ} {M : ℕ → X.Modules} {T : Fin (k + 1) → ∀ e, M e ⟶ M (e + 1)}


variable (M T) in
def kerι (e : ℕ) : kerSeq M T e ⟶ M e := kernel.ι (T (Fin.last k) e)

theorem kerι_comp (e : ℕ) : kerι M T e ≫ T (Fin.last k) e = 0 :=
  kernel.condition _

theorem kerOps_comp_kerι (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (i : Fin k)
    (e : ℕ) : kerOps hc i e ≫ kerι M T (e + 1) = kerι M T e ≫ T i.castSucc e := by
  simp [kerOps, kerι, kerSeq, kernel.map]


open GlobalTheory.CompanionTheory.GE.KerSeq in
theorem kerOps_gen_bounded : GlobalTheory.CompanionTheory.GE.GradedNoeth → ∀ {X : AlgebraicGeometry.Scheme.{0}} [AlgebraicGeometry.IsLocallyNoetherian X] {k : ℕ} {M : ℕ → X.Modules} {T : Fin (k + 1) → ∀ e, M e ⟶ M (e + 1)} {d : ℕ} (hM : GlobalTheory.CompanionTheory.GE.OpSeq (k + 1) M T d) (U : X.affineOpens), ∃ d₁ : ℕ, ∀ e, d₁ ≤ e → Submodule.span Γ(X, U) (⋃ i, Set.range ((GlobalTheory.CompanionTheory.GE.UV.kerOps hM.comm i e).app U)) = ⊤ := by
  intro hG X _ k M T d hM U
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  haveI : ∀ e, Module.Finite Γ(X, U) Γ(M e, (U : X.Opens)) := fun e => (hM.coherent e).2 U U.2
  have hcomm : ∀ (i j : Fin (k + 1)) (e : ℕ) (x : Γ(M e, (U : X.Opens))),
      secMap (T j (e + 1)) (U : X.Opens) (secMap (T i e) (U : X.Opens) x) =
        secMap (T i (e + 1)) (U : X.Opens) (secMap (T j e) (U : X.Opens) x) := by
    intro i j e x
    simp only [secMap_comp]
    rw [hM.comm i j e]
  obtain ⟨d', hd'⟩ := hG Γ(X, U) (k + 1) (fun e => Γ(M e, (U : X.Opens)))
    (fun i e => secMap (T i e) (U : X.Opens)) hcomm d
    (fun e he => by
      have h := hM.gen e he U
      rw [eq_top_iff, ← h, Submodule.span_le]
      intro w hw
      obtain ⟨i, z, rfl⟩ := Set.mem_iUnion.1 hw
      exact Submodule.mem_iSup_of_mem i ⟨z, rfl⟩)
    (fun e => LinearMap.ker (secMap (T (Fin.last k) e) (U : X.Opens)))
    (fun i e => by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : secMap (T (Fin.last k) e) (U : X.Opens) x = 0 := hx
      change secMap (T (Fin.last k) (e + 1)) (U : X.Opens) (secMap (T i e) (U : X.Opens) x) = 0
      rw [hcomm i (Fin.last k) e x, hx', map_zero])
  refine ⟨d', fun e he => ?_⟩

  have hι : ∀ e, Function.Injective (secMap (kerι M T e) (U : X.Opens)) :=
    fun e => kernel_ι_app_injective _ _
  have hιo : ∀ (i : Fin k) e (y : Γ(kerSeq M T e, (U : X.Opens))),
      secMap (kerι M T (e + 1)) (U : X.Opens)
          (secMap (kerOps hM.comm i e) (U : X.Opens) y) =
        secMap (T i.castSucc e) (U : X.Opens)
          (secMap (kerι M T e) (U : X.Opens) y) := by
    intro i e y
    rw [secMap_comp, secMap_comp, kerOps_comp_kerι]
  set S : Submodule Γ(X, U) Γ(kerSeq M T (e + 1), (U : X.Opens)) :=
    Submodule.span Γ(X, U) (⋃ i, Set.range ((kerOps hM.comm i e).app U)) with hS

  have hle : LinearMap.ker (secMap (T (Fin.last k) (e + 1)) (U : X.Opens)) ≤
      S.map (secMap (kerι M T (e + 1)) (U : X.Opens)) := by
    rw [← hd' e he]
    refine iSup_le fun i => ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y : Γ(kerSeq M T e, (U : X.Opens)), secMap (kerι M T e) (U : X.Opens) y = x :=
      kernel_ι_app_exact (T (Fin.last k) e) (U : X.Opens) x hx
    subst hy
    change secMap (T i e) (U : X.Opens) (secMap (kerι M T e) (U : X.Opens) y) ∈ _
    induction i using Fin.lastCases with
    | last =>
      rw [show secMap (T (Fin.last k) e) (U : X.Opens)
          (secMap (kerι M T e) (U : X.Opens) y) = 0 from hx]
      exact Submodule.zero_mem _
    | cast i =>
      refine ⟨secMap (kerOps hM.comm i e) (U : X.Opens) y, ?_, hιo i e y⟩
      exact Submodule.subset_span (Set.mem_iUnion.2 ⟨i, y, rfl⟩)
  rw [eq_top_iff]
  intro z _
  have hz : secMap (kerι M T (e + 1)) (U : X.Opens) z ∈
      LinearMap.ker (secMap (T (Fin.last k) (e + 1)) (U : X.Opens)) := by
    rw [LinearMap.mem_ker, secMap_comp, kerι_comp]
    simp [secMap_apply, Scheme.Modules.Hom.zero_app]
  obtain ⟨w, hw, hwz⟩ := hle hz
  rwa [← hι _ hwz]

end GlobalTheory.CompanionTheory.GE.UV
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OperatorSequenceSumEpiStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.operator_sequence_sum_epi : ∀ {X : Scheme.{0}} {k : ℕ} {M : ℕ → X.Modules} {T : Fin k → ∀ e, M e ⟶ M (e + 1)} {d : ℕ}, OpSeq k M T d → ∀ e, Epi (KerSeq.sumMap T d e) := by
  first | exact @GlobalTheory.CompanionTheory.GE.KerSeq.epi_sumMap_of_opSeq | exact GlobalTheory.CompanionTheory.GE.KerSeq.epi_sumMap_of_opSeq | (intros; apply GlobalTheory.CompanionTheory.GE.KerSeq.epi_sumMap_of_opSeq <;> assumption)
end

