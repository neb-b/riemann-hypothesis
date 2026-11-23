module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0012
public import Formalism.GradedWeylDivisibility.FinalD
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0099
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
public import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerSpaceDimFiniteGLLeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleDistinctUnitary
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyDirectSumEquivOfFinrankLe
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0040
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlBlockFiniteDimModuleStructure

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockActionDiagonalCoefficientSpaceSmul
section
open Formalism.L2.Ker MvPolynomial

noncomputable section

namespace GlobalTheory.CoefScale

lemma weight_colW_apply {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) (t : Fin n) :
    Finsupp.weight (Formalism.GradedWeylDivisibility.colW r n) m t = ∑ a : Fin r, m (a, t) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    Fintype.sum_prod_type_right]
  rw [Finset.sum_eq_single t]
  · refine Finset.sum_congr rfl fun a _ => ?_
    simp [Formalism.GradedWeylDivisibility.colW]
  · intro s _ hs
    refine Finset.sum_eq_zero fun a _ => ?_
    simp [Formalism.GradedWeylDivisibility.colW, Pi.single_apply, Ne.symm hs]
  · simp

theorem rowAct_scalar_dualWeyl {r n : ℕ} (ν : Fin n → ℕ) (c : ℂ) (F : MvPolynomial (Fin r × Fin n) ℂ)
    (hF : F ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ r n ν) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (Matrix.diagonal fun _ : Fin r => c) F = c ^ (∑ t, ν t) • F := by
  have hw : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW r n) F ν :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).1 (Submodule.mem_inf.1 hF).1
  ext m
  rw [Formalism.GradedWeylDivisibility.ldrow_coeff_rowAct_diag, coeff_smul, smul_eq_mul]
  by_cases h : AddMonoidAlgebra.coeff F m = 0
  · simp [h]
  · have hm := hw h
    rw [Finset.prod_pow_eq_pow_sum, mul_comm]
    congr 2
    simp only [Formalism.GradedWeylDivisibility.rowDeg]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← weight_colW_apply, hm]

end GlobalTheory.CoefScale

namespace GlobalTheory

theorem blockAct_diag_mem_VV {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight n) (c : ι → ℂ)
    (Q : Formalism.L2.DIV.Pol ℂ ι n) (hQ : Q ∈ Formalism.L2.DIV.VV ℂ lam) :
    Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => Matrix.diagonal fun _ : Fin n => c τ) Q =
      (∏ τ, c τ ^ ∑ a, (lam τ).natW a) • Q := by
  unfold Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat at hQ
  induction hQ using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨F, hF, rfl⟩ := hP
    have h1 := (Formalism.GradedWeylDivisibility.blockActTensor ℂ ℂ ι n n (fun τ => Matrix.diagonal fun _ : Fin n => c τ)).1
    rw [map_prod]
    simp_rw [h1]
    have h2 : ∀ τ, Formalism.GradedWeylDivisibility.rowAct ℂ (Matrix.diagonal fun _ : Fin n => c τ) (F τ) =
        c τ ^ (∑ a, (lam τ).natW a) • F τ := fun τ =>
      GlobalTheory.CoefScale.rowAct_scalar_dualWeyl _ _ _ (hF τ)
    simp_rw [h2, map_smul, Algebra.smul_def, Finset.prod_mul_distrib, map_prod]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul a x _ hx => rw [map_smul, hx, smul_comm]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardMinusSignsHalfOfEvenStatement
section
open Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_minus_signs_half_of_even : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ} {ε : Fin (n + 1) → Bool} {mu : Fin n → ℝ} {ε' : Fin n → Bool}, Even G.m → 0 < G.ga → IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' → (Finset.univ.filter fun a => ε a = false).card = G.m / 2 ∧ (Finset.univ.filter fun i => ε' i = false).card = G.m / 2 := by
  first | exact @GlobalTheory.SignedHC.GridData.card_minus_signs_interlacing_parameters | exact GlobalTheory.SignedHC.GridData.card_minus_signs_interlacing_parameters | (intros; apply GlobalTheory.SignedHC.GridData.card_minus_signs_interlacing_parameters <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvAtParabNeZero
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.TypeDim

section Finite

variable {F : Type} [Field F] {N : ℕ} {V V' W W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V']
  [Module ℂ V'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

end Finite

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r t : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

abbrev part (r t : ℕ) := two (stdSum (rfl : r + t = r + t))

variable {σ : Representation ℂ (GL (Fin r) k) V} {χW χV : kˣ →* ℂˣ}

def diagO (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) : GL (Fin (r + t)) 𝒪[k] :=
  emb₂ 𝒪[k] (stdSum (rfl : r + t = r + t)) (a, d)

theorem diagO_ul (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) (i j : Fin r) :
    (diagO a d).val (Fin.castAdd t i) (Fin.castAdd t j) = a.val i j := by
  simp [diagO, val_emb₂, stdSum, Matrix.reindex_apply]

theorem diagO_lr (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) (i j : Fin t) :
    (diagO a d).val (Fin.natAdd r i) (Fin.natAdd r j) = d.val i j := by
  simp [diagO, val_emb₂, stdSum, Matrix.reindex_apply]

theorem diagO_ll (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) (i : Fin t) (j : Fin r) :
    (diagO a d).val (Fin.natAdd r i) (Fin.castAdd t j) = 0 := by
  simp [diagO, val_emb₂, stdSum, Matrix.reindex_apply]

theorem diagO_ur (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) (i : Fin r) (j : Fin t) :
    (diagO a d).val (Fin.castAdd t i) (Fin.natAdd r j) = 0 := by
  simp [diagO, val_emb₂, stdSum, Matrix.reindex_apply]

theorem hasBlocks_diagO (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) : HasBlocks (diagO a d) a d := by
  refine ⟨diagO_ul a d, diagO_lr a d, fun i j => ?_⟩
  rw [diagO_ll]
  exact Ideal.zero_mem _

theorem incl_val {n : ℕ} (a : GL (Fin n) 𝒪[k]) (i j : Fin n) :
    (incl k n a).val i j = (a.val i j : k) := rfl

theorem red_val {n : ℕ} (a : GL (Fin n) 𝒪[k]) (i j : Fin n) :
    (red k n a).val i j = IsLocalRing.residue 𝒪[k] (a.val i j) := rfl

theorem incl_diagO_one (a : GL (Fin r) 𝒪[k]) : incl k (r + t) (diagO a 1) = diagOne k r t a := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [incl_val]
  simp only [diagO, diagOne, MonoidHom.comp_apply, MonoidHom.inl_apply, val_emb₂, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  generalize (stdSum (rfl : r + t = r + t)).symm i = x
  generalize (stdSum (rfl : r + t = r + t)).symm j = y
  rcases x with x | x <;> rcases y with y | y <;> simp [incl_val, Matrix.one_apply, apply_ite]

def Nice (r t : ℕ) (w : Equiv.Perm (Fin (r + t))) (S : Finset (Fin r)) : Prop :=
  (∀ i, i ∉ S → w (Fin.castAdd t i) = Fin.castAdd t i) ∧
  (∀ i ∈ S, r ≤ (w (Fin.castAdd t i) : ℕ) ∧ r ≤ (w.symm (Fin.castAdd t i) : ℕ)) ∧ (S = ∅ → w = 1)

end Local

end GlobalTheory.TypeDim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsColAddFixedOfStable
section
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

namespace GlobalTheory.GLDuality

theorem rename_swap_matRep_one_right {n n' : ℕ} (g : GL (Fin n) ℂ) (v : MvPolynomial (Fin n' × Fin n) ℂ) :
    rename Prod.swap (matRep n n' (g, 1) v) =
      rowAct ℂ (g : Matrix (Fin n) (Fin n) ℂ)ᵀ (rename Prod.swap v) := by
  have : (rename (R := ℂ) (Prod.swap : Fin n' × Fin n → Fin n × Fin n')).comp
      (sub (((1 : GL (Fin n') ℂ) : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ (g : Matrix (Fin n) (Fin n) ℂ))ᵀ) =
      (rowAct ℂ (g : Matrix (Fin n) (Fin n) ℂ)ᵀ).comp (rename Prod.swap) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    simp [sub, rowAct, Fintype.sum_prod_type, Matrix.one_apply, apply_ite C]
  rw [matRep_apply]
  exact DFunLike.congr_fun this v

theorem rename_swap_colAdd {n n' : ℕ} (l j : Fin n) (c : ℂ) (v : MvPolynomial (Fin n' × Fin n) ℂ) :
    rename Prod.swap (colAdd ℂ l j c v) =
      Polynomial.eval (C c) (rowGen ℂ l j (rename Prod.swap v)) := by
  induction v using MvPolynomial.induction_on with
  | C a => simp [colAdd, rowGen]
  | add p q hp hq => simp only [map_add (f := _), hp, hq, Polynomial.eval_add]
  | mul_X p v hp =>
    obtain ⟨a, s⟩ := v
    simp only [map_mul, hp, Polynomial.eval_mul]
    congr 1
    by_cases h : s = j <;> simp [colAdd, rowGen, h, mul_comm (C c)]

theorem rowGen_coeff_zero_eq {r n : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) ℂ) :
    (rowGen ℂ a b f).coeff 0 = f := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  induction f using MvPolynomial.induction_on with
  | C a => simp [rowGen]
  | add p q hp hq => simp only [map_add (f := _), hp, hq, Polynomial.eval_add]
  | mul_X p v hp =>
    simp only [map_mul, hp, Polynomial.eval_mul]
    congr 1
    by_cases h : v.1 = b <;> simp [rowGen, h]

theorem exists_colAdd_fixed_of_stable (n n' : ℕ) (N : Submodule ℂ (MvPolynomial (Fin n' × Fin n) ℂ)) (hN : N ≠ ⊥)
    (hst : ∀ g : GL (Fin n) ℂ, ∀ v ∈ N, matRep n n' (g, 1) v ∈ N) :
    ∃ v ∈ N, v ≠ 0 ∧ ∀ l j : Fin n, l < j → ∀ c : ℂ, colAdd ℂ l j c v = v := by
  have hinj : Function.Injective
      (rename (R := ℂ) (Prod.swap : Fin n' × Fin n → Fin n × Fin n')) :=
    rename_injective _ Prod.swap_injective
  let M : Submodule ℂ (MvPolynomial (Fin n × Fin n') ℂ) :=
    N.map (rename (R := ℂ) (Prod.swap : Fin n' × Fin n → Fin n × Fin n')).toLinearMap
  have hU : ∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ f ∈ M, rowAct ℂ u f ∈ M := by
    rintro u hu _ ⟨f, hf, rfl⟩
    let t : Matrix.unitaryGroup (Fin n) ℂ := Matrix.UnitaryGroup.transpose ⟨u, hu⟩
    exact ⟨_, hst (unitaryIncl n t) f hf, rename_swap_matRep_one_right (unitaryIncl n t) f⟩
  have hcl := rowDivClosed_of_rowAct_stable M (rowAct_mem_of_unitary_stable M hU)
  have hne : M ≠ ⊥ := fun e => hN (Submodule.map_injective_of_injective hinj
    (e.trans (Submodule.map_bot _).symm))
  obtain ⟨_, ⟨v, hv, rfl⟩, hv0, hkill⟩ := exists_killed_of_rowDivClosed M hcl hne
  refine ⟨v, hv, fun e => hv0 (by rw [e, map_zero]), fun l j hlj c => hinj ?_⟩
  have hC : rowGen ℂ l j (rename Prod.swap v) = Polynomial.C (rename Prod.swap v) := by
    apply Polynomial.ext
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [rowGen_coeff_zero_eq, Polynomial.coeff_C_zero]
    · rw [Polynomial.coeff_C_of_ne_zero hk.ne']
      exact hkill l j hlj k hk
  rw [rename_swap_colAdd, hC, Polynomial.eval_C]

end GlobalTheory.GLDuality
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteDimensionalForallMapMem
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

namespace GlobalTheory.KHomFinite

theorem isKC_Eab_of_sameBlock {p q : ℕ} {a b : Ix p q} (h : sameBlock a b) : IsKC (Eab a b) := by
  intro c d hcd
  unfold Eab
  rw [Matrix.single_apply]
  split_ifs with hc
  · obtain ⟨rfl, rfl⟩ := hc
    exact absurd h hcd
  · rfl

theorem sameBlock_self {p q : ℕ} (a : Ix p q) : sameBlock a a := by
  cases a <;> trivial

theorem sameBlock_of_posC {p q : ℕ} {a b : Ix p q} (h : posC a b) : sameBlock a b := by
  cases a <;> cases b <;> first | trivial | exact h.elim

theorem map_mem_hwSub {p q : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V']
    [Module ℂ V'] (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (act' : Mat p q →ₗ[ℂ] Module.End ℂ V')
    (φ : V →ₗ[ℂ] V') (hφ : ∀ Z, IsKC Z → ∀ v, φ (act Z v) = act' Z (φ v))
    (μ : Ix p q → ℚ) (v : V) (hv : v ∈ hwSub act μ) : φ v ∈ hwSub act' μ := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hv ⊢
  obtain ⟨hw, hhi⟩ := hv
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · rw [← hφ _ (isKC_Eab_of_sameBlock (sameBlock_self a)), ← map_smul, ← map_sub, hw a, map_zero]
  · rw [← hφ _ (isKC_Eab_of_sameBlock (sameBlock_of_posC hab)), hhi a b hab, map_zero]

theorem kStable_sup {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {A B : Submodule ℂ V} (hA : KStable act A)
    (hB : KStable act B) : KStable act (A ⊔ B) := by
  intro X hX w hw
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
  rw [map_add (f := _)]
  exact Submodule.add_mem_sup (hA X hX y hy) (hB X hX z hz)

theorem exists_kStable_ge {p q : ℕ} (M : GKMod p q) (H : Submodule ℂ M.V)
    (hH : FiniteDimensional ℂ H) :
    ∃ E : Submodule ℂ M.V, FiniteDimensional ℂ E ∧ H ≤ E ∧ KStable M.act E := by
  classical
  obtain ⟨s, hs⟩ := (Submodule.fg_iff_finiteDimensional H).mpr hH
  have key : ∀ t : Finset M.V, ∃ E : Submodule ℂ M.V, FiniteDimensional ℂ E ∧
      Submodule.span ℂ (t : Set M.V) ≤ E ∧ KStable M.act E := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · refine ⟨⊥, inferInstance, by simp, ?_⟩
      intro X _ w hw
      rw [Submodule.mem_bot] at hw ⊢
      rw [hw, map_zero]
    · intro x t _ ih
      obtain ⟨E₁, hE₁, hx, hK₁⟩ := M.kfin x
      obtain ⟨E₂, hE₂, ht, hK₂⟩ := ih
      refine ⟨E₁ ⊔ E₂, inferInstance, ?_, kStable_sup hK₁ hK₂⟩
      rw [Finset.coe_insert, Submodule.span_insert]
      exact sup_le_sup ((Submodule.span_singleton_le_iff_mem _ _).mpr hx) ht
  obtain ⟨E, hE, hsE, hK⟩ := key s
  refine ⟨E, hE, ?_, hK⟩
  rw [← hs]
  exact hsE

theorem exists_finiteDimensional_forall_map_mem :
    ∀ (p q : ℕ) (M : GKMod p q), AdmGK M → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsKLieAct act → ∀ W : Submodule ℂ V, FiniteDimensional ℂ W → KStable act W → (∀ v ∈ W, v ∈ ⨆ μ : Ix p q → ℚ, wtSub act μ) → ∃ E : Submodule ℂ M.V, FiniteDimensional ℂ E ∧ ∀ φ : V →ₗ[ℂ] M.V, (∀ Z, IsKC Z → ∀ v, φ (act Z v) = M.act Z (φ v)) → ∀ v ∈ W, φ v ∈ E := by
  intro p q M hM V _ _ act hact W hW hWK hWwt
  suffices key : ∀ n : ℕ, ∀ U : Submodule ℂ V, U ≤ W → KStable act U → Module.finrank ℂ U = n →
      ∃ E : Submodule ℂ M.V, FiniteDimensional ℂ E ∧ ∀ φ : V →ₗ[ℂ] M.V,
        (∀ Z, IsKC Z → ∀ v, φ (act Z v) = M.act Z (φ v)) → ∀ v ∈ U, φ v ∈ E from
    key _ W le_rfl hWK rfl
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih U hUW hUK hn
  have hUfd : FiniteDimensional ℂ U := Submodule.finiteDimensional_of_le hUW
  obtain ⟨hsplit, hhw, -, -⟩ := _root_.GlobalTheory.BlockReps.finite_module_structure p q V act hact U hUfd hUK
    (fun v hv => hWwt v (hUW hv))
  by_cases hU0 : U = ⊥
  · refine ⟨⊥, inferInstance, fun φ _ v hv => ?_⟩
    rw [hU0, Submodule.mem_bot] at hv
    rw [hv, map_zero]
    exact Submodule.zero_mem _
  obtain ⟨μ, v, hvU, hv⟩ := hhw hU0
  set N : Submodule ℂ V := sInf {N | v ∈ N ∧ KStable act N} with hN
  have hNK : KStable act N := by
    intro X hX w hw
    rw [Submodule.mem_sInf] at hw ⊢
    intro N' hN'
    exact hN'.2 X hX w (hw N' hN')
  have hvN : v ∈ N := Submodule.mem_sInf.mpr fun N' hN' => hN'.1
  have hNU : N ≤ U := sInf_le ⟨hvU, hUK⟩
  obtain ⟨U', hU'K, hdisj, hsup⟩ := hsplit N hNU hNK
  have hU'U : U' ≤ U := by
    rw [← hsup]
    exact le_sup_right
  have hvU' : v ∉ U' := by
    intro h
    have hmem : v ∈ N ⊓ U' := ⟨hvN, h⟩
    rw [hdisj, Submodule.mem_bot] at hmem
    exact hv.1 hmem
  have hlt : Module.finrank ℂ U' < n := by
    rw [← hn]
    exact Submodule.finrank_lt_finrank_of_lt
      (lt_of_le_of_ne hU'U fun h => hvU' (by rw [h]; exact hvU))
  obtain ⟨E', hE', hE'mem⟩ := ih _ hlt U' (hU'U.trans hUW) hU'K rfl
  obtain ⟨Eμ, hEμ, hle, hEμK⟩ := exists_kStable_ge M (hwSub M.act μ) (hM μ)
  refine ⟨Eμ ⊔ E', inferInstance, fun φ hφ w hw => ?_⟩
  have hNφ : N ≤ Submodule.comap φ Eμ := by
    refine sInf_le ⟨?_, ?_⟩
    · exact hle (map_mem_hwSub act M.act φ hφ μ v hv.2)
    · intro X hX x hx
      rw [Submodule.mem_comap] at hx ⊢
      rw [hφ X hX x]
      exact hEμK X hX _ hx
  rw [← hsup] at hw
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hw
  rw [map_add (f := _)]
  exact Submodule.add_mem_sup (hNφ hx) (hE'mem φ hφ y hy)

end GlobalTheory.KHomFinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMapNablaSqPad
section
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open scoped Matrix

noncomputable section

namespace GlobalTheory.GLDuality

def dropCols (r m : ℕ) : MvPolynomial (Fin r × Fin r) ℂ →ₐ[ℂ] MvPolynomial (Fin r × Fin m) ℂ :=
  aeval fun v => if h : v.2.val < m then X (v.1, ⟨v.2.val, h⟩) else 0

theorem dropCols_rowAct (r m : ℕ) (g : Matrix (Fin r) (Fin r) ℂ) (f : MvPolynomial (Fin r × Fin r) ℂ) :
    dropCols r m (rowAct ℂ g f) = rowAct ℂ g (dropCols r m f) := by
  have : (dropCols r m).comp (rowAct ℂ g) = (rowAct ℂ g).comp (dropCols r m) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    by_cases hs : s.val < m <;> simp [dropCols, rowAct, hs]
  exact DFunLike.congr_fun this f

theorem dropCols_lpMinor (r m s : ℕ) (hr : s ≤ r) (hm : s ≤ m) :
    dropCols r m (lpMinor ℂ s hr hr) = lpMinor ℂ s hr hm := by
  unfold lpMinor
  rw [AlgHom.map_det]
  congr 1
  ext1 p q
  have hq : q.val < m := lt_of_lt_of_le q.2 hm
  simp [dropCols, hq, Fin.castLE]

theorem dropCols_hw (r m : ℕ) (h : m ≤ r) (ν : Fin m → ℕ) :
    dropCols r m (hw ℂ (le_refl r) (rowNu ν)) = hw ℂ h ν := by
  unfold hw
  rw [map_prod]
  symm
  refine Finset.prod_of_injOn (Fin.castLE h) (Fin.castLE_injective h).injOn (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro s _ hs
    have hs' : ¬ s.val < m := fun hlt => hs ⟨⟨s.val, hlt⟩, by simp, rfl⟩
    simp [rowNu, hs']
  · intro s _
    rw [map_pow]
    have e : nuNext (rowNu (r := r) ν) (Fin.castLE h s) = nuNext ν s := by
      simp only [nuNext, rowNu, Fin.val_castLE]
      split_ifs with h1 h2 h3
      · rfl
      · rfl
      · omega
      · rfl
    have e' : rowNu (r := r) ν (Fin.castLE h s) = ν s := by simp [rowNu]
    rw [e, e']
    congr 1
    exact (dropCols_lpMinor r m (s.val + 1) _ _).symm

theorem pad_detShift_nonneg {m : ℕ} (r : ℕ) (a : Part m) : 0 ≤ (pad r a).detShift := by
  unfold DomWeight.detShift
  split_ifs
  · exact Nat.cast_nonneg _
  · exact le_rfl

theorem pad_natW_add {m : ℕ} (r : ℕ) (a : Part m) (i : Fin r) :
    (pad r a).natW i + (pad r a).detShift.toNat = rowNu a.1 i := by
  have h0 := pad_detShift_nonneg r a
  have h1 : (pad r a).detShift ≤ (pad r a).w i := by
    unfold DomWeight.detShift
    rw [dite_eq_left i.pos]
    apply (pad r a).anti
    rw [Fin.le_def]
    have := i.2
    simp only
    omega
  have h2 : (pad r a).w i = (rowNu (r := r) a.1 i : ℕ) := rfl
  simp only [DomWeight.natW]
  omega

theorem exists_map_nablaSq_pad : ∀ (r m : ℕ) (h : m ≤ r) (a : Part m), ∃ j : nablaSq ℂ r (pad r a) →ₗ[ℂ] MvPolynomial (Fin r × Fin m) ℂ, (∀ (g : GL (Fin r) ℂ) (f : nablaSq ℂ r (pad r a)), j (sqRep ℂ r (pad r a) g f) = rowAct ℂ (g : Matrix (Fin r) (Fin r) ℂ)ᵀ (j f)) ∧ ∀ f : nablaSq ℂ r (pad r a), (f : MvPolynomial (Fin r × Fin r) ℂ) = extremal ℂ r (pad r a) → j f = hw ℂ h a.1 := by
  intro r m h a
  obtain ⟨c, hc⟩ := Int.eq_ofNat_of_zero_le (pad_detShift_nonneg r a)
  let j : nablaSq ℂ r (pad r a) →ₗ[ℂ] MvPolynomial (Fin r × Fin m) ℂ :=
    (dropCols r m).toLinearMap ∘ₗ LinearMap.mulLeft ℂ (lpMinor ℂ r le_rfl le_rfl ^ c) ∘ₗ
      (nablaSq ℂ r (pad r a)).subtype
  have hj : ∀ f, j f = dropCols r m (lpMinor ℂ r le_rfl le_rfl ^ c * f) := fun _ => rfl
  refine ⟨j, fun g f => ?_, fun f hf => ?_⟩
  · rw [hj, hj, ← dropCols_rowAct, (genericDet_pow_mul r c (fun _ => 0)).2.1, sqRep_coe, sqAct, hc,
      mul_smul_comm, Matrix.det_transpose]
    simp [detPow]
  · rw [hj, hf, extremal, genericDet_pow_mul_hw, ← dropCols_hw r m h]
    congr 2
    funext i
    have := pad_natW_add r a i
    rwa [hc, Int.toNat_natCast] at this

end GlobalTheory.GLDuality
end
end

