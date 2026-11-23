module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0036
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0034
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0356
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0355
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0345
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0360
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0348
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0376
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0362
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0359
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0363
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0353
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0361
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0358
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0370

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult MeasureTheory

namespace Zl.JC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem claim {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (hs : IsSmooth π) (hi : π.IsIrreducible) {h : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N)
    (hjm : Zc.jm x hd π ≠ 0) (t : kˣ) (hv : ValuativeRel.valuation k (t : k) < 1) (c : Fin h → ℂ)
    (hc : ∀ i, Zl.ScalarBy (x i) t (c i)) (j : Fin h) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ (w : V) (l : Module.Dual ℂ V),
      (∀ g ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, π g w = w) ∧
      (∀ g ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, l ∘ₗ π g = l) ∧
      ∀ r : ℕ, l (π ((leviEmb k (stdBlocks (fun a => (x a).1) hd) (zj (fun a => (x a).1) t j)) ^ r) w) =
        ((((deltaHalf k (fun a => Fin ((x a).1)) (zj (fun a => (x a).1) t j) : ℂˣ) : ℂ)) *
          ∏ i ∈ Finset.univ.filter (· ≤ j), c i) ^ r := by
  classical
  have := hi
  have hsF : GroundTheory.Automorphic.IsSmooth π := _root_.GlobalTheory.CompanionTheory.SmoothTransfer.isSmooth_found k N π hs
  have hadm : GroundTheory.Automorphic.IsAdmissible π := GroundTheory.Automorphic.Parabolic.isAdmissible_of_isIrreducible hsF
  obtain ⟨S, T, hST⟩ := GlobalTheory.T.jacquet_multiplicity_ne_zero_subquotient k x hd π hjm
  have hscal := GlobalTheory.T.pi_tensor_central_block_scalar k x t c hc j
  set Λ : ℂ := ∏ i ∈ Finset.univ.filter (· ≤ j), c i with hΛdef
  set δ : ℂ := ((deltaHalf k (fun a => Fin ((x a).1)) (zj (fun a => (x a).1) t j) : ℂˣ) : ℂ) with hδdef
  have hmod : ∀ s ∈ S.toSubmodule, jac (stdBlocks (fun a => (x a).1) hd) π (zj (fun a => (x a).1) t j) s - Λ • s
      ∈ T.toSubmodule :=
    _root_.GlobalTheory.CompanionTheory.SubQuotScalar.sub_smul_mem_of_equiv_subQuot _ _ S T hST (zj (fun a => (x a).1) t j) Λ hscal
  have := GlobalTheory.T.pi_tensor_irreducible_nontrivial k x
  have hΛ : Λ ≠ 0 := by
    intro h0
    obtain ⟨v, hv0⟩ := exists_ne (0 : PiTensorProduct ℂ (fun a => (x a).2.rep.V))
    apply hv0
    have h2 : piTensor (fun a => (x a).rep) (zj (fun a => (x a).1) t j)⁻¹
        (piTensor (fun a => (x a).rep) (zj (fun a => (x a).1) t j) v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [hscal v, h0, zero_smul, map_zero] at h2
    exact h2.symm
  have hδ : δ ≠ 0 := Units.ne_zero _
  have hjacU : ∀ s, jacU (stdBlocks (fun a => (x a).1) hd) π (zj (fun a => (x a).1) t j) s =
      δ • jac (stdBlocks (fun a => (x a).1) hd) π (zj (fun a => (x a).1) t j) s := by
    intro s
    simp only [jac, twist_apply, smul_smul]
    rw [hδdef, ← Units.val_mul, MonoidHom.inv_apply, mul_inv_cancel, Units.val_one, one_smul]
  obtain ⟨e, -, he2⟩ := GlobalTheory.T.jacquet_module_equiv_foundation k N π h (fun a => (x a).1) hd
  have ha := GlobalTheory.T.levi_embedding_mem_levi k h N (fun a => (x a).1) hd (zj (fun a => (x a).1) t j)
  have hcen := GlobalTheory.T.block_central_element_commutes_levi k h N (fun a => (x a).1) hd t j
  have hmono := _root_.GlobalTheory.CompanionTheory.BlockIndex.blockIdx_monotone h N (fun a => (x a).1) hd
  set W := S.toSubmodule.map e.toLinearMap
  set T' := (S.toSubmodule ⊓ T.toSubmodule).map e.toLinearMap
  have hle : T' ≤ W := Submodule.map_mono inf_le_left
  have hSU : ∀ s ∈ S.toSubmodule, jacU (stdBlocks (fun a => (x a).1) hd) π (zj (fun a => (x a).1) t j) s ∈ S.toSubmodule := by
    intro s hs'
    rw [hjacU]
    exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule _ hs')
  have hWst : ∀ w ∈ W, GroundTheory.Automorphic.Parabolic.jacquetAction k N (blockIdx (fun a => (x a).1) hd) π ⟨_, ha⟩ w ∈ W := by
    rintro _ ⟨s, hs', rfl⟩
    refine ⟨_, hSU s hs', ?_⟩
    exact he2 _ ha s
  have hWmod : ∀ w ∈ W, GroundTheory.Automorphic.Parabolic.jacquetAction k N (blockIdx (fun a => (x a).1) hd) π ⟨_, ha⟩ w -
      (δ * Λ) • w ∈ T' := by
    rintro _ ⟨s, hs', rfl⟩
    refine ⟨δ • (jac (stdBlocks (fun a => (x a).1) hd) π (zj (fun a => (x a).1) t j) s - Λ • s), ⟨?_, ?_⟩, ?_⟩
    · exact S.toSubmodule.smul_mem _ (S.toSubmodule.sub_mem (S.apply_mem_toSubmodule _ hs') (S.toSubmodule.smul_mem _ hs'))
    · exact T.toSubmodule.smul_mem _ (hmod s hs')
    · simp only [LinearEquiv.coe_coe]
      rw [← he2 _ ha s, hjacU]
      simp only [map_smul, map_sub, smul_sub, smul_smul]
  have hex : ∃ w ∈ W, w ∉ T' := by
    obtain ⟨s, hsS, hsT⟩ := _root_.GlobalTheory.CompanionTheory.SubQuotNe.exists_mem_not_mem_of_subQuot_equiv _ _ S T hST inferInstance
    refine ⟨e s, ⟨s, hsS, rfl⟩, ?_⟩
    rintro ⟨s', hs', hes⟩
    have : s' = s := e.injective hes
    exact hsT (this ▸ hs'.2)
  obtain ⟨m₀, hm₀⟩ := _root_.GlobalTheory.CompanionTheory.JacquetEigen.exists_eigenvector_fixed k N π hadm (blockIdx (fun a => (x a).1) hd) hmono _ ha hcen W T' (δ * Λ)
    (mul_ne_zero hδ hΛ) hle hWst hWmod hex
  obtain ⟨y, hy0, hyfix, hyeig⟩ := hm₀ (max m₀ 1) (le_max_left _ _)
  obtain ⟨hcN, hcNbar⟩ := _root_.GlobalTheory.CompanionTheory.ZjContract.zj_contract k h N (fun a => (x a).1) hd t hv.le j (max m₀ 1)
  obtain ⟨w, l, hw, hl, hcoef⟩ := _root_.GlobalTheory.CompanionTheory.JacquetCoeff.exists_coeff_geometric k N π hadm (blockIdx (fun a => (x a).1) hd) hmono (max m₀ 1)
    (le_max_right _ _) _ ha hcen hcN hcNbar y (δ * Λ) hy0 hyfix hyeig
  exact ⟨max m₀ 1, le_max_right _ _, w, l, hw, hl, hcoef⟩

theorem lpBound {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (hs : IsSmooth π) (hi : π.IsIrreducible) {h : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N)
    (hpos : ∀ a, 0 < (x a).1) (hjm : Zc.jm x hd π ≠ 0) (t : kˣ) (hv : ValuativeRel.valuation k (t : k) < 1)
    (c : Fin h → ℂ) (hc : ∀ i, Zl.ScalarBy (x i) t (c i)) (j : Fin h) (hj : j.val + 1 < h) (p : ℝ) (hp : 0 < p)
    (hL : CoeffLp p π) :
    (modulus k (fun a => Fin ((x a).1)) (zj (fun a => (x a).1) t j))⁻¹ *
      (Real.sqrt (modulus k (fun a => Fin ((x a).1)) (zj (fun a => (x a).1) t j)) *
        ‖∏ i ∈ Finset.univ.filter (· ≤ j), c i‖) ^ p < 1 := by
  classical
  obtain ⟨m, hm, w, l, hw, hl, hcoef⟩ := claim π hs hi x hd hjm t hv c hc j
  borelize (AdGL k N)
  have hopen : IsOpen {g : GL (Fin N) k | l ∘ₗ π g = l} :=
    GlobalTheory.T.invariant_functional_open_stabilizer π (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m)
      (GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k N m) l hl
  obtain ⟨F, hF, hFmem⟩ := hL (Measure.haar (G := AdGL k N)) inferInstance w l hopen
  obtain ⟨hmeas, hdisj⟩ := GlobalTheory.T.contracting_double_coset_measurable k h N (fun a => (x a).1) hd hpos t hv j hj m hm
  obtain ⟨c0, hc0, hvol⟩ := GlobalTheory.T.contracting_double_coset_volume_bound k h N (fun a => (x a).1) hd hpos t hv j hj m hm
    (Measure.haar (G := AdGL k N)) inferInstance
  set δ : ℂ := ((deltaHalf k (fun a => Fin ((x a).1)) (zj (fun a => (x a).1) t j) : ℂˣ) : ℂ) with hδdef
  set Λ : ℂ := ∏ i ∈ Finset.univ.filter (· ≤ j), c i
  have hnorm : ‖δ * Λ‖ = Real.sqrt (modulus k (fun a => Fin ((x a).1)) (zj (fun a => (x a).1) t j)) * ‖Λ‖ := by
    rw [norm_mul, hδdef, val_deltaHalf, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [← hnorm]
  refine GlobalTheory.T.not_mem_Lp_of_growth (Measure.haar (G := AdGL k N)) F p hp hFmem _ hmeas hdisj c0 _ 1 ‖δ * Λ‖ hc0 one_pos
    (norm_nonneg _) hvol ?_
  rintro r _ ⟨g, ⟨x1, hx1, y1, hy1, rfl⟩, rfl⟩
  rw [hF, one_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hw y1 hy1]
  have h1 : l (π x1 (π ((leviEmb k (stdBlocks (fun a => (x a).1) hd) (zj (fun a => (x a).1) t j)) ^ r) w)) =
      l (π ((leviEmb k (stdBlocks (fun a => (x a).1) hd) (zj (fun a => (x a).1) t j)) ^ r) w) :=
    LinearMap.congr_fun (hl x1 hx1) _
  rw [h1, hcoef r, norm_pow]
  exact le_of_eq (abs_of_nonneg (by positivity)).symm

theorem totalNorm {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (hs : IsSmooth π) (hi : π.IsIrreducible) {h : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N)
    (hjm : Zc.jm x hd π ≠ 0) (t : kˣ) (hv : ValuativeRel.valuation k (t : k) < 1)
    (c : Fin h → ℂ) (hc : ∀ i, Zl.ScalarBy (x i) t (c i)) (hh : 0 < h) (p : ℝ) (hL : CoeffLp p π) :
    ∏ i, ‖c i‖ = 1 := by
  classical
  set jl : Fin h := ⟨h - 1, by omega⟩
  obtain ⟨m, hm, w, l, hw, hl, hcoef⟩ := claim π hs hi x hd hjm t hv c hc jl
  obtain ⟨hsc, hmod1⟩ := GlobalTheory.T.last_block_central_scalar_modulus_one k h N (fun a => (x a).1) hd t jl (by simp [jl]; omega)
  have hopen : IsOpen {g : GL (Fin N) k | l ∘ₗ π g = l} :=
    GlobalTheory.T.invariant_functional_open_stabilizer π (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m)
      (GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k N m) l hl
  have hcent : leviEmb k (stdBlocks (fun a => (x a).1) hd) (zj (fun a => (x a).1) t jl) ∈
      Subgroup.center (GL (Fin N) k) := by
    rw [hsc]
    refine Subgroup.mem_center_iff.2 fun g => Units.ext ?_
    exact (Matrix.scalar_commute (t : k) (fun _ => Commute.all _ _) g.val).symm.eq
  have hc1 := _root_.GlobalTheory.CompanionTheory.CoeffCentral.norm_coeff_central k N π p hL _ hcent w l hopen
  have h0 := hcoef 0
  have h1 := hcoef 1
  simp only [pow_zero, map_one, Module.End.one_apply] at h0
  simp only [pow_one] at h1
  rw [h1, h0, norm_one, norm_mul, val_deltaHalf, hmod1, Real.sqrt_one, Complex.ofReal_one, norm_one, one_mul,
    norm_prod] at hc1
  have hfilt : Finset.univ.filter (· ≤ jl) = Finset.univ := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact Fin.le_iff_val_le_val.2 (by simp [jl]; omega)
  rw [hfilt] at hc1
  exact hc1

theorem casselmanNecSq_holds (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : Zl.CasselmanNecSq k := by
  intro N V _ _ π hN hs hi hsq h x hd hpos hjm t ht c hc
  have hv := _root_.GlobalTheory.CompanionTheory.Val.valuation_lt_one_of_tendsto_pow_zero k t ht
  have hh : 0 < h := by
    rcases Nat.eq_zero_or_pos h with rfl | hh
    · simp at hd; omega
    · exact hh
  refine ⟨fun j hj => ?_, totalNorm π hs hi x hd hjm t hv c hc hh 2 hsq⟩
  have key := lpBound π hs hi x hd hpos hjm t hv c hc j hj 2 two_pos hsq
  have := _root_.GlobalTheory.CompanionTheory.Casselman.lt_one_of_inv_mul_sqrt_mul_rpow_two_lt_one _ _ (modulus_pos k _) (norm_nonneg _) key
  rwa [norm_prod] at this

theorem casselmanNecTemp_holds (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : Zl.CasselmanNecTemp k := by
  intro N V _ _ π hN hs hi htemp h x hd hpos hjm t ht c hc
  have hv := _root_.GlobalTheory.CompanionTheory.Val.valuation_lt_one_of_tendsto_pow_zero k t ht
  have hh : 0 < h := by
    rcases Nat.eq_zero_or_pos h with rfl | hh
    · simp at hd; omega
    · exact hh
  refine ⟨fun j hj => ?_, totalNorm π hs hi x hd hjm t hv c hc hh (2 + 1) (htemp 1 one_pos)⟩
  have hlt := _root_.GlobalTheory.CompanionTheory.JCModulus.modulus_zj_lt_one k h N (fun a => (x a).1) hd hpos t hv j hj
  have := _root_.GlobalTheory.CompanionTheory.Casselman.le_one_of_forall_sqrt_mul_rpow_lt _ _ (modulus_pos k _) hlt (norm_nonneg _)
    (fun ε hε => lpBound π hs hi x hd hpos hjm t hv c hc j hj (2 + ε) (by linarith) (htemp ε hε))
  rwa [norm_prod] at this

end Zl.JC

end
