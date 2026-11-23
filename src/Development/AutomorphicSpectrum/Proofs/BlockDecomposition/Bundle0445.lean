module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle0001
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0427
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0418
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelFamInf
section
noncomputable section

open NumberField GlobalTheory.BCT PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.FC

namespace GlobalTheory.CompanionTheory.FamClP

section Generic

variable {H : Type} [Group H]

theorem mem_rStab' {u : H → ℂ} {r : H} : r ∈ rStab u ↔ ∀ x, u (x * r) = u x := Iff.rfl

theorem hint_zero (K : Subgroup H) : hint K (fun _ => (0 : ℂ)) = 0 := by
  simp [hint]

theorem rStab_left (u : H → ℂ) (k : H) : rStab (fun z => u (k * z)) = rStab u := by
  ext r
  rw [mem_rStab', mem_rStab']
  constructor
  · intro h x
    simpa [mul_assoc] using h (k⁻¹ * x)
  · intro h x
    simpa [mul_assoc] using h (k * x)

theorem hint_left (K : Subgroup H) (u : H → ℂ) (k : H) :
    hint K (fun z => u (k * z)) = hint K u := by
  unfold hint
  rw [rStab_left]
  congr 1
  refine Eq.trans ?_ (finsum_comp_equiv (MulAction.toPerm k : H ⧸ (rStab u ⊓ K) ≃ H ⧸ (rStab u ⊓ K)))
  refine finsum_congr fun q => ?_
  have hq : (MulAction.toPerm k : H ⧸ (rStab u ⊓ K) ≃ H ⧸ (rStab u ⊓ K)) q =
      ((k * q.out : H) : H ⧸ (rStab u ⊓ K)) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [hq]
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (rStab u ⊓ K) (k * q.out)
  rw [hh]
  exact (h.2.1 _).symm

theorem rStab_ind (K : Subgroup H) : rStab ((K : Set H).indicator (1 : H → ℂ)) = K := by
  ext r
  rw [mem_rStab']
  constructor
  · intro h
    by_contra hr
    have := h 1
    simp [Set.indicator, hr, one_mem] at this
  · intro hr x
    by_cases hx : x ∈ K
    · have hxr : x * r ∈ K := mul_mem hx hr
      simp [Set.indicator, hx, hxr]
    · have hxr : x * r ∉ K := fun h => hx (by simpa using mul_mem h (inv_mem hr))
      simp [Set.indicator, hx, hxr]

theorem hint_ind (K : Subgroup H) : hint K ((K : Set H).indicator (1 : H → ℂ)) = 1 := by
  unfold hint
  rw [rStab_ind, inf_idem, Subgroup.relIndex_self]
  rw [finsum_eq_single _ ((1 : H) : H ⧸ K)]
  · obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K (1 : H)
    have hm : (((1 : H) : H ⧸ K)).out ∈ K := by
      rw [hh]
      simpa using h.2
    simp [Set.indicator, hm]
  · intro q hq
    have hn : q.out ∉ K := by
      intro hm
      apply hq
      rw [← QuotientGroup.out_eq' q]
      exact QuotientGroup.eq.2 (by simpa using inv_mem hm)
    simp [Set.indicator, hn]

variable [TopologicalSpace H]

variable [IsTopologicalGroup H]

end Generic

section Fam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

end Fam

end GlobalTheory.CompanionTheory.FamClP

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviAdjointOnChains
section
open Finset PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.LvChain
open CompanionTheory.D.LK (Pos)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.LvChainAdj

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def ip (x z : Cq n V) : ℂ := ∑ A, ⟪x A, z A⟫_ℂ

theorem sgL_conj (i : Lt n) (A : Finset (Lt n)) : (starRingEnd ℂ) (sgL i A) = sgL i A := by
  simp [PositivityTheory.RgBcC.RealD.sgL]

theorem sgL_erase_self (i : Lt n) {A : Finset (Lt n)} (h : i ∈ A) : sgL i (A.erase i) = sgL i A := by
  rw [GlobalTheory.CompanionTheory.LvChain.sgL_erase i h, GlobalTheory.CompanionTheory.LvChain.twL_self, one_mul]

theorem ip_creL (i : Lt n) (x z : Cq n V) : ip (creL i x) z = ip x (annL i z) := by
  classical
  have hL : GlobalTheory.CompanionTheory.LvChainAdj.ip (PositivityTheory.RgBcC.RealD.creL i x) z =
      ∑ A ∈ Finset.univ.filter (fun A => i ∈ A),
        PositivityTheory.RgBcC.RealD.sgL i A * ⟪x (A.erase i), z A⟫_ℂ := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [GlobalTheory.CompanionTheory.LvChain.creL_apply]
    split_ifs <;> simp [inner_smul_left, GlobalTheory.CompanionTheory.LvChainAdj.sgL_conj] <;> ring
  have hR : GlobalTheory.CompanionTheory.LvChainAdj.ip x (PositivityTheory.RgBcC.RealD.annL i z) =
      ∑ B ∈ Finset.univ.filter (fun B => i ∉ B),
        PositivityTheory.RgBcC.RealD.sgL i B * ⟪x B, z (insert i B)⟫_ℂ := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [GlobalTheory.CompanionTheory.LvChain.annL_apply]
    split_ifs <;> simp [inner_smul_right]
  rw [hL, hR]
  refine Finset.sum_nbij' (fun A => A.erase i) (fun B => insert i B) ?_ ?_ ?_ ?_ ?_
  · intro A _
    simp
  · intro B _
    simp
  · intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA
    exact Finset.insert_erase hA
  · intro B hB
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hB
    exact Finset.erase_insert hB
  · intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA
    rw [GlobalTheory.CompanionTheory.LvChainAdj.sgL_erase_self i hA, Finset.insert_erase hA]

theorem ip_conj (x z : Cq n V) : (starRingEnd ℂ) (ip x z) = ip z x := by
  unfold GlobalTheory.CompanionTheory.LvChainAdj.ip
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun A _ => inner_conj_symm (z A) (x A)

theorem ip_annL (i : Lt n) (x z : Cq n V) : ip (annL i x) z = ip x (creL i z) := by
  rw [← GlobalTheory.CompanionTheory.LvChainAdj.ip_conj z (PositivityTheory.RgBcC.RealD.annL i x), ← GlobalTheory.CompanionTheory.LvChainAdj.ip_creL i z x,
    GlobalTheory.CompanionTheory.LvChainAdj.ip_conj]

theorem ip_creL_annL (i k : Lt n) (x z : Cq n V) :
    ip ((creL k * annL i : Module.End ℂ (Cq n V)) x) z = ip x ((creL i * annL k : Module.End ℂ (Cq n V)) z) := by
  rw [Module.End.mul_apply, Module.End.mul_apply, GlobalTheory.CompanionTheory.LvChainAdj.ip_creL,
    GlobalTheory.CompanionTheory.LvChainAdj.ip_annL]

theorem ip_add_left (x y z : Cq n V) : ip (x + y) z = ip x z + ip y z := by
  unfold GlobalTheory.CompanionTheory.LvChainAdj.ip
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun A _ => by rw [← inner_add_left]; rfl

theorem ip_add_right (x y z : Cq n V) : ip x (y + z) = ip x y + ip x z := by
  unfold GlobalTheory.CompanionTheory.LvChainAdj.ip
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun A _ => by rw [← inner_add_right]; rfl

theorem ip_smul_left (c : ℂ) (x z : Cq n V) : ip (c • x) z = (starRingEnd ℂ) c * ip x z := by
  unfold GlobalTheory.CompanionTheory.LvChainAdj.ip
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun A _ => by rw [← inner_smul_left]; rfl

theorem ip_smul_right (c : ℂ) (x z : Cq n V) : ip x (c • z) = c * ip x z := by
  unfold GlobalTheory.CompanionTheory.LvChainAdj.ip
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun A _ => by rw [← inner_smul_right]; rfl

theorem ip_zero_left (z : Cq n V) : ip (0 : Cq n V) z = 0 := by
  unfold GlobalTheory.CompanionTheory.LvChainAdj.ip
  exact Finset.sum_eq_zero fun A _ => by
    rw [show (0 : PositivityTheory.RgBcC.RealD.Cq n V) A = 0 from rfl, inner_zero_left]

theorem ip_zero_right (x : Cq n V) : ip x (0 : Cq n V) = 0 := by
  unfold GlobalTheory.CompanionTheory.LvChainAdj.ip
  exact Finset.sum_eq_zero fun A _ => by
    rw [show (0 : PositivityTheory.RgBcC.RealD.Cq n V) A = 0 from rfl, inner_zero_right]

theorem ip_sum_left {ι : Type} (s : Finset ι) (f : ι → Cq n V) (z : Cq n V) :
    ip (∑ a ∈ s, f a) z = ∑ a ∈ s, ip (f a) z := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, GlobalTheory.CompanionTheory.LvChainAdj.ip_zero_left]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, GlobalTheory.CompanionTheory.LvChainAdj.ip_add_left, ih]

theorem ip_sum_right {ι : Type} (s : Finset ι) (x : Cq n V) (f : ι → Cq n V) :
    ip x (∑ a ∈ s, f a) = ∑ a ∈ s, ip x (f a) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, GlobalTheory.CompanionTheory.LvChainAdj.ip_zero_right]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, GlobalTheory.CompanionTheory.LvChainAdj.ip_add_right, ih]

theorem adCL_conj (p q : Fin n) (l k : Lt n) : (starRingEnd ℂ) (adCL false p q l k) = adCL false p q l k := by
  unfold PositivityTheory.RgBcC.RealD.adCL
  split_ifs <;> simp

theorem adCL_swap (p q : Fin n) (l k : Lt n) : adCL false p q l k = adCL false q p k l := by
  unfold PositivityTheory.RgBcC.RealD.adCL
  simp only [Bool.false_xor, Bool.false_bne, Prod.ext_iff]
  congr 1
  · exact if_congr
      ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h3.symm, h2.symm, h1.symm, h4.symm⟩,
        fun ⟨h1, h2, h3, h4⟩ => ⟨h3.symm, h2.symm, h1.symm, h4.symm⟩⟩ rfl rfl
  · exact if_congr
      ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h4, h2.symm, h3.symm, h1⟩,
        fun ⟨h1, h2, h3, h4⟩ => ⟨h4, h2.symm, h3.symm, h1⟩⟩ rfl rfl

theorem inUU_iff_of_adCL {lev : Fin n → ℕ} {p q : Fin n} (h : lev p = lev q) {l k : Lt n}
    (hc : adCL false p q l k ≠ 0) : inUU lev l ↔ inUU lev k := by
  unfold PositivityTheory.RgBcC.RealD.adCL at hc
  unfold PositivityTheory.RgBcC.RealD.inUU
  split_ifs at hc with h1 h2 h2
  · exact absurd (sub_self _) hc
  · obtain ⟨hq, -, hk⟩ := h1
    simp [hk, h, hq]
  · obtain ⟨hp, -, hk⟩ := h2
    simp [hk, hp, h]
  · exact absurd (sub_self _) hc

theorem ip_term {lev : Fin n → ℕ} {p q : Fin n} (h : lev p = lev q) (l k : Lt n) (x z : Cq n V) :
    ip ((if inUU lev l then adCL false p q l k • (creL k * annL l) else 0 : Module.End ℂ (Cq n V)) x) z =
      ip x ((if inUU lev k then adCL false q p k l • (creL l * annL k) else 0 : Module.End ℂ (Cq n V)) z) := by
  rw [← GlobalTheory.CompanionTheory.LvChainAdj.adCL_swap p q l k]
  by_cases hc : PositivityTheory.RgBcC.RealD.adCL false p q l k = 0
  · simp only [hc, zero_smul, ite_self, LinearMap.zero_apply, GlobalTheory.CompanionTheory.LvChainAdj.ip_zero_left,
      GlobalTheory.CompanionTheory.LvChainAdj.ip_zero_right]
  · have hiff := GlobalTheory.CompanionTheory.LvChainAdj.inUU_iff_of_adCL h hc
    by_cases hl : PositivityTheory.RgBcC.RealD.inUU lev l
    · rw [if_pos hl, if_pos (hiff.mp hl), LinearMap.smul_apply, LinearMap.smul_apply,
        GlobalTheory.CompanionTheory.LvChainAdj.ip_smul_left, GlobalTheory.CompanionTheory.LvChainAdj.ip_smul_right, GlobalTheory.CompanionTheory.LvChainAdj.adCL_conj,
        GlobalTheory.CompanionTheory.LvChainAdj.ip_creL_annL]
    · rw [if_neg hl, if_neg (mt hiff.mpr hl), LinearMap.zero_apply, LinearMap.zero_apply,
        GlobalTheory.CompanionTheory.LvChainAdj.ip_zero_left, GlobalTheory.CompanionTheory.LvChainAdj.ip_zero_right]

theorem ip_adLL {lev : Fin n → ℕ} {p q : Fin n} (h : lev p = lev q) (x z : Cq n V) :
    ip (adLL lev false p q x) z = ip x (adLL lev false q p z) := by
  unfold PositivityTheory.RgBcC.RealD.adLL
  simp only [LinearMap.sum_apply, GlobalTheory.CompanionTheory.LvChainAdj.ip_sum_left, GlobalTheory.CompanionTheory.LvChainAdj.ip_sum_right]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  exact GlobalTheory.CompanionTheory.LvChainAdj.ip_term h l k x z

theorem ip_liftL {E1 E2 : Fin n → Fin n → Module.End ℂ V}
    (hU : ∀ a b (x y : V), ⟪kA E1 E2 a b x, y⟫_ℂ = ⟪x, kA E1 E2 b a y⟫_ℂ) (p q : Fin n) (x z : Cq n V) :
    ip (liftL n (kA E1 E2 p q) x) z = ip x (liftL n (kA E1 E2 q p) z) := by
  unfold GlobalTheory.CompanionTheory.LvChainAdj.ip
  exact Finset.sum_congr rfl fun A _ => hU p q (x A) (z A)

theorem Lv_adjoint : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V),
    (∀ a b (x y : V), ⟪kA E1 E2 a b x, y⟫_ℂ = ⟪x, kA E1 E2 b a y⟫_ℂ) → ∀ p q : Fin n, lev p = lev q → ∀ x z : Cq n V,
      ∑ A, ⟪Lv lev E1 E2 p q x A, z A⟫_ℂ = ∑ A, ⟪x A, Lv lev E1 E2 q p z A⟫_ℂ := by
  intro n lev V _ _ E1 E2 hU p q h x z
  show GlobalTheory.CompanionTheory.LvChainAdj.ip _ _ = GlobalTheory.CompanionTheory.LvChainAdj.ip _ _
  unfold GlobalTheory.CompanionTheory.LvChain.Lv
  rw [LinearMap.add_apply, LinearMap.add_apply, GlobalTheory.CompanionTheory.LvChainAdj.ip_add_left,
    GlobalTheory.CompanionTheory.LvChainAdj.ip_add_right, GlobalTheory.CompanionTheory.LvChainAdj.ip_liftL hU,
    GlobalTheory.CompanionTheory.LvChainAdj.ip_adLL h]

end GlobalTheory.CompanionTheory.LvChainAdj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOneLMemZalg
section
open NumberField GlobalTheory.CuspRep Polynomial Finset

namespace GlobalTheory.CompanionTheory.CapelliTrace

theorem mem_of_dual {A : Type} [Ring A] [Algebra ℂ A] (S : Subalgebra ℂ A) (x : A)
    (h : ∀ f : A →ₗ[ℂ] ℂ, (∀ z ∈ S, f z = 0) → f x = 0) : x ∈ S := by
  by_contra hx
  have hx' : x ∉ Subalgebra.toSubmodule S := hx
  obtain ⟨f, hf1, hf2⟩ := Submodule.exists_le_ker_of_notMem hx'
  exact hf1 (h f fun z hz => LinearMap.mem_ker.1 (hf2 hz))

theorem prod_X_sub {n : ℕ} (s : Finset (Fin n)) :
    (∏ l ∈ s, (X - C ((l : ℕ) : ℂ))).natDegree = s.card ∧ (∏ l ∈ s, (X - C ((l : ℕ) : ℂ))).Monic := by
  refine ⟨?_, monic_prod_of_monic _ _ fun l _ => monic_X_sub_C _⟩
  rw [natDegree_prod_of_monic _ _ fun l _ => monic_X_sub_C _, Finset.sum_congr rfl fun l _ => natDegree_X_sub_C _]
  simp

theorem trace_mem {A : Type} [Ring A] [Algebra ℂ A] (S : Subalgebra ℂ A) (n : ℕ) (M : Fin n → Fin n → A)
    (h : ∀ u : ℂ, Formalism.REAL.qdet M u ∈ S) : ∑ i, M i i ∈ S := by
  obtain ⟨Rm, hR⟩ := GlobalTheory.qdet_top_three_orders A n M
  refine mem_of_dual S _ fun f hf => ?_
  have f1 : f 1 = 0 := hf 1 S.one_mem
  set Q : ℂ[X] := ∑ i, C (f (M i i)) * ∏ l ∈ univ.erase i, (X - C ((l : ℕ) : ℂ)) +
    ∑ i, ∑ j ∈ univ.filter (fun j => i < j), C (f (M i i * M j j - M j i * M i j)) *
      ∏ l ∈ (univ.erase i).erase j, (X - C ((l : ℕ) : ℂ)) +
    ∑ d ∈ range (n - 2), C (f (Rm d)) * X ^ d with hQ
  have hQ0 : Q = 0 := Polynomial.funext fun u => by
    have h1 := hf _ (h u)
    rw [hR u] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, map_smul, smul_eq_mul, f1, mul_zero, zero_add] at h1
    simp only [hQ, eval_add, eval_finsetSum, eval_mul, eval_C, eval_prod, eval_sub, eval_X, eval_pow, eval_zero]
    rw [← h1]
    congr 1
    · congr 1
      · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
    · exact Finset.sum_congr rfl fun d _ => mul_comm _ _
  have hc := congrArg (fun p : ℂ[X] => p.coeff (n - 1)) hQ0
  simp only [hQ, coeff_add, finsetSum_coeff, coeff_C_mul, coeff_zero] at hc
  have t1 : ∀ i : Fin n, (∏ l ∈ univ.erase i, (X - C ((l : ℕ) : ℂ))).coeff (n - 1) = 1 := fun i => by
    obtain ⟨hd, hm⟩ := prod_X_sub (univ.erase i)
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at hd
    rw [← hd]; exact hm.coeff_natDegree
  have t2 : ∀ i : Fin n, ∀ j ∈ univ.filter (fun j => i < j),
      (∏ l ∈ (univ.erase i).erase j, (X - C ((l : ℕ) : ℂ))).coeff (n - 1) = 0 := fun i j hj => by
    have hij : i < j := (mem_filter.1 hj).2
    have hj' : (j : ℕ) < n := j.2
    have hi' : (i : ℕ) < j := hij
    obtain ⟨hd, -⟩ := prod_X_sub ((univ.erase i).erase j)
    rw [card_erase_of_mem (mem_erase.2 ⟨hij.ne', mem_univ _⟩), card_erase_of_mem (mem_univ _), card_univ,
      Fintype.card_fin] at hd
    exact coeff_eq_zero_of_natDegree_lt (by omega)
  have t3 : ∀ d ∈ range (n - 2), ((X : ℂ[X]) ^ d).coeff (n - 1) = 0 := fun d hd => by
    rw [coeff_X_pow, if_neg]
    have := mem_range.1 hd
    omega
  have e3 : ∑ d ∈ range (n - 2), f (Rm d) * ((X : ℂ[X]) ^ d).coeff (n - 1) = 0 :=
    Finset.sum_eq_zero fun d hd => by rw [t3 d hd, mul_zero]
  have e2 : ∑ i : Fin n, ∑ j ∈ univ.filter (fun j => i < j), f (M i i * M j j - M j i * M i j) *
      (∏ l ∈ (univ.erase i).erase j, (X - C ((l : ℕ) : ℂ))).coeff (n - 1) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j hj => by rw [t2 i j hj, mul_zero]
  have e1 : ∑ i : Fin n, f (M i i) * (∏ l ∈ univ.erase i, (X - C ((l : ℕ) : ℂ))).coeff (n - 1) = ∑ i, f (M i i) :=
    Finset.sum_congr rfl fun i _ => by rw [t1 i, mul_one]
  rw [e1, e2, e3, add_zero, add_zero] at hc
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact hc

end GlobalTheory.CompanionTheory.CapelliTrace

namespace GlobalTheory.CompanionTheory.CapelliTrace

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
open Classical in
theorem atEmb_one (τ : E →+* ℂ) : atEmb τ 1 = Pi.single (InfinitePlace.mk τ) 1 := by
  unfold atEmb; split_ifs <;> simp

theorem Eop_add_conj (τ : E →+* ℂ) (i j : Fin a) :
    Eop τ i j + Eop (ComplexEmbedding.conjugate τ) i j = lieS E a i j (atEmb τ 1) := by
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by rw [atEmb_eq]; simp
  simp only [Eop, atEmb_conj, map_one, Complex.conj_I, e, map_neg, smul_neg, sub_neg_eq_add]
  module

theorem sum_atEmb_one : ∑ τ : E →+* ℂ, atEmb τ 1 = (2 : Cinf E) := by
  classical
  funext w
  simp only [atEmb_one, Finset.sum_apply, Pi.single_apply]
  rw [Finset.sum_boole]
  have h := InfinitePlace.card_filter_mk_eq w
  have h2 : InfinitePlace.mult w = 2 := by
    simp [InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)]
  have h3 : (Finset.univ.filter fun τ : E →+* ℂ => w = InfinitePlace.mk τ) =
      Finset.univ.filter fun τ : E →+* ℂ => InfinitePlace.mk τ = w := by
    ext τ; simp [eq_comm]
  rw [h3, h, h2]
  simp

end GlobalTheory.CompanionTheory.CapelliTrace

namespace GlobalTheory.CompanionTheory.CapelliTrace

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem sum_Eop (i j : Fin a) : ∑ τ : E →+* ℂ, Eop τ i j = lieS E a i j 1 := by
  set X := ∑ τ : E →+* ℂ, Eop τ i j
  have hc : ∑ τ : E →+* ℂ, Eop (ComplexEmbedding.conjugate τ) i j = X :=
    Equiv.sum_comp (Function.Involutive.toPerm _ (ComplexEmbedding.involutive_conjugate E)) fun τ => Eop τ i j
  have h2 : (2 : ℂ) • X = (2 : ℂ) • lieS E a i j 1 := by
    rw [two_smul, two_smul]
    nth_rewrite 2 [← hc]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun τ _ => Eop_add_conj τ i j, ← map_sum, sum_atEmb_one,
      show (2 : Cinf E) = 1 + 1 from one_add_one_eq_two.symm, map_add]
  exact smul_right_injective _ two_ne_zero h2

theorem lie_oneL_eq : lie E a (oneL E a) = ∑ τ : E →+* ℂ, ∑ i, Eop τ i i := by
  rw [Finset.sum_comm, Finset.sum_congr rfl fun i _ => sum_Eop i i]
  have e : oneL E a = ∑ i : Fin a, toL (Matrix.single i i (1 : Cinf E)) := by
    funext k l
    change (1 : Matrix (Fin a) (Fin a) (Cinf E)) k l = (∑ i : Fin a, Matrix.single i i (1 : Cinf E)) k l
    rw [Matrix.sum_apply]
    by_cases h : k = l
    · subst h; simp [Matrix.single_apply]
    · rw [Matrix.one_apply_ne h]
      exact (Finset.sum_eq_zero fun c _ => by
        rw [Matrix.single_apply, if_neg fun hc => h (hc.1.symm.trans hc.2)]).symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum]
  rfl

theorem lie_oneL_mem_Zalg : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
    lie E a (oneL E a) ∈ Zalg E a := by
  intro E _ _ _ a
  rw [lie_oneL_eq]
  refine Subalgebra.sum_mem _ fun τ _ => trace_mem (Zalg E a) a (Eop τ) fun u => ?_
  have h : cap (a := a) τ (u - ((a : ℂ) - 1) / 2) ∈ Zalg E a := Algebra.subset_adjoin ⟨τ, _, rfl⟩
  rwa [cap, sub_add_cancel] at h

end GlobalTheory.CompanionTheory.CapelliTrace
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBrauerRootsUnityEquiv
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory.CompanionTheory.LocalInv

theorem nonempty_H2_muLoc_equiv_zmod : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → Nonempty (H2 (muLoc F l r A) ≃ₗ[ZMod (l ^ r)] ZMod (l ^ r)) := by
  intro F Ω _ _ _ _ _ l _ r hr A v hA
  exact (GlobalTheory.CompanionTheory.Hypotheses₂.localTateDuality F Ω l r (ZMod (l ^ r)) A (muLoc F l r A) v hr hA
    (GlobalTheory.TameQuot.contAction_muDec A l r)).1

end GlobalTheory.CompanionTheory.LocalInv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalConstancyTwistedTranslate
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.TwFibre

theorem twisted_fibre_isLocallyConstant_hasCompactSupport : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)), IsLocallyConstant (fun d : Fin (t + 1) → k => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • evX f (dEmb k i t d * y)) ∧ HasCompactSupport (fun d : Fin (t + 1) → k => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • evX f (dEmb k i t d * y)) := by
  intro k _ _ _ _ i t ψ hψ τ σ f y
  obtain ⟨hl, hc⟩ := _root_.GlobalTheory.CompanionTheory.BZPhiPG.Fib.fibre_isLocallyConstant_hasCompactSupport k i t τ σ f y
  refine ⟨?_, ?_⟩
  · have h1 : IsLocallyConstant (fun d : Fin (t + 1) → k => ψ (d (Fin.last t))) :=
      (GlobalTheory.IrredSB.char_isLocallyConstant ψ hψ).comp_continuous (continuous_apply _)
    have h2 : IsLocallyConstant (fun d : Fin (t + 1) → k =>
        (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ)) :=
      h1.comp (fun z : Circle => (((Circle.toUnits z)⁻¹ : ℂˣ) : ℂ))
    exact IsLocallyConstant.comp₂ h2 hl (fun a b => a • b)
  · refine hc.mono fun d hd h0 => hd ?_
    have h0' : evX f (dEmb k i t d * y) = 0 := h0
    show (_ : ℂ) • evX f (dEmb k i t d * y) = 0
    rw [h0', smul_zero]

end GlobalTheory.CompanionTheory.BZPhiPG.TwFibre
end

