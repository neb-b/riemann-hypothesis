module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1783
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1028
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FinalC
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1790
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1795
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1773

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JointRowWeightAntitoneOfMaxPotential
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial

namespace GlobalTheory.HighWt

def permMat {O : Type} [CommRing O] {N : ℕ} (σ : Equiv.Perm (Fin N)) : Matrix (Fin N) (Fin N) O :=
  Matrix.of fun i j => if σ i = j then 1 else 0

theorem permMat_mul {O : Type} [CommRing O] {N : ℕ} (σ ρ : Equiv.Perm (Fin N)) :
    (permMat σ : Matrix (Fin N) (Fin N) O) * permMat ρ = permMat (σ.trans ρ) := by
  ext i k
  simp only [permMat, Matrix.mul_apply, Matrix.of_apply, Equiv.trans_apply]
  rw [Finset.sum_eq_single (σ i)]
  · by_cases h : ρ (σ i) = k <;> simp [h]
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

theorem permMat_refl {O : Type} [CommRing O] {N : ℕ} :
    (permMat (Equiv.refl (Fin N)) : Matrix (Fin N) (Fin N) O) = 1 := by
  ext i k
  by_cases h : i = k <;> simp [permMat, Matrix.one_apply, h]

def permGL {O : Type} [CommRing O] {N : ℕ} (σ : Equiv.Perm (Fin N)) : GL (Fin N) O :=
  ⟨permMat σ, permMat σ.symm, by rw [permMat_mul, Equiv.self_trans_symm, permMat_refl],
    by rw [permMat_mul, Equiv.symm_trans_self, permMat_refl]⟩

theorem rowAct_permMat {O : Type} [CommRing O] {N : ℕ} (σ : Equiv.Perm (Fin N)) (f : MvPolynomial (Fin N × Fin N) O) :
    Formalism.GradedWeylDivisibility.rowAct O (n := N) (permMat σ) f = rename (fun v : Fin N × Fin N => (σ v.1, v.2)) f := by
  have : Formalism.GradedWeylDivisibility.rowAct O (n := N) (permMat σ) = rename (fun v : Fin N × Fin N => (σ v.1, v.2)) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [Formalism.GradedWeylDivisibility.rowAct, permMat, rename_X]
  rw [this]

theorem weight_mapDomain_perm {N : ℕ} (σ : Equiv.Perm (Fin N)) (d : Fin N × Fin N →₀ ℕ) (a : Fin N) :
    Finsupp.weight (Formalism.GradedWeylDivisibility.rowW N N) (d.mapDomain (fun v : Fin N × Fin N => (σ v.1, v.2))) (σ a) =
      Finsupp.weight (Formalism.GradedWeylDivisibility.rowW N N) d a := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [Finsupp.mapDomain_add, map_add (f := _), map_add (f := _), Pi.add_apply, Pi.add_apply, hf, hg]
  | single v c =>
    rw [Finsupp.mapDomain_single, Finsupp.weight_single, Finsupp.weight_single]
    simp only [Pi.smul_apply, Formalism.GradedWeylDivisibility.rowW, Pi.single_apply, σ.injective.eq_iff]

end GlobalTheory.HighWt

namespace GlobalTheory.HighWt

theorem rowComp_rename_perm {O : Type} [CommRing O] {N : ℕ} (σ : Equiv.Perm (Fin N)) (u : Fin N → ℕ)
    (f : MvPolynomial (Fin N × Fin N) O) :
    weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW N N) u (rename (fun v : Fin N × Fin N => (σ v.1, v.2)) f) =
      rename (fun v : Fin N × Fin N => (σ v.1, v.2)) (weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW N N) (u ∘ σ) f) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [rename_monomial]
    have key : Finsupp.weight (Formalism.GradedWeylDivisibility.rowW N N) (d.mapDomain (fun v : Fin N × Fin N => (σ v.1, v.2))) = u ↔
        Finsupp.weight (Formalism.GradedWeylDivisibility.rowW N N) d = u ∘ σ := by
      constructor
      · intro h
        funext a
        rw [Function.comp_apply, ← h, weight_mapDomain_perm]
      · intro h
        funext b
        obtain ⟨a, rfl⟩ := σ.surjective b
        rw [weight_mapDomain_perm, h, Function.comp_apply]
    rw [weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_monomial _ _ _ rfl),
      weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_monomial _ _ _ rfl)]
    by_cases h : Finsupp.weight (Formalism.GradedWeylDivisibility.rowW N N) d = u ∘ σ
    · rw [if_pos (Eq.symm (key.2 h)), if_pos h.symm, rename_monomial]
    · rw [if_neg (fun h' => h (key.1 h'.symm)), if_neg (fun h' => h h'.symm), map_zero]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _), map_add (f := _)]

variable (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ)

theorem grp_tprod (g : ι → GL (Fin N) O) (x : ∀ τ, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ))) :
    grp O N lam g (PiTensorProduct.tprod O x) =
      PiTensorProduct.tprod O (fun τ => Formalism.UG.dualWeylRep O N N (res N (lam τ)) (g τ) (x τ)) := by
  simp only [grp, Formalism.CohomologicalDescent.RealLocalDeltaNabla.nablaRep, MonoidHom.coe_comp, Function.comp_apply]
  rw [PiTensorProduct.mapMonoidHom_apply, PiTensorProduct.map_tprod]
  rfl

theorem grp_inv_mul (g : ι → GL (Fin N) O) : grp O N lam g⁻¹ * grp O N lam g = 1 := by
  simp only [grp]
  rw [← map_mul, inv_mul_cancel, map_one]

theorem dualWeylRep_mul_inv (ν : Fin N → ℕ) (h : GL (Fin N) O) (v : Formalism.GradedWeylDivisibility.dualWeyl O N N ν) :
    Formalism.UG.dualWeylRep O N N ν h (Formalism.UG.dualWeylRep O N N ν h⁻¹ v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem isProj_conj (g : ι → GL (Fin N) O) (τ' : ι) (u u' : Fin N → ℕ)
    (h : ∀ f, weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW N N) u (Formalism.UG.dwAct O N N (g τ')⁻¹ f) =
      Formalism.UG.dwAct O N N (g τ')⁻¹ (weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW N N) u' f))
    (b : Module.End O (NablaT O N lam)) (hb : IsProj O N lam τ' u b) :
    IsProj O N lam τ' u' (grp O N lam g * b * grp O N lam g⁻¹) := by
  intro x y hy
  set x'' : ∀ τ, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ)) := fun τ => Formalism.UG.dualWeylRep O N N (res N (lam τ)) (g τ)⁻¹ (x τ) with hx''
  have h1 : grp O N lam g⁻¹ (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O x'' := by
    rw [grp_tprod]; rfl
  have hy'' : ((Formalism.UG.dualWeylRep O N N (res N (lam τ')) (g τ')⁻¹ y : Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ'))) :
      MvPolynomial (Fin N × Fin N) O) = weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW N N) u (x'' τ' : MvPolynomial (Fin N × Fin N) O) := by
    rw [Formalism.UG.dualWeylRep_apply, hy, ← h, hx'', Formalism.UG.dualWeylRep_apply]
  have h2 := hb x'' _ hy''
  rw [Module.End.mul_apply, Module.End.mul_apply, h1, h2, grp_tprod]
  congr 1
  funext i
  by_cases hi : i = τ'
  · subst hi
    rw [Function.update_self, Function.update_self, dualWeylRep_mul_inv]
  · rw [Function.update_of_ne hi, Function.update_of_ne hi, hx'', dualWeylRep_mul_inv]

end GlobalTheory.HighWt

namespace GlobalTheory.HighWt

theorem grpA_inv_mul (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ) (g : ι → GL (Fin N) O) :
    grpA O N lam g⁻¹ * grpA O N lam g = 1 :=
  Subtype.ext (grp_inv_mul O N lam g)

theorem jointWt_perm (O : Type) [CommRing O] (N : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ)
    (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm] (w : ι → Fin N → ℕ) (hw : JointWt O N lam Gm w)
    (τ : ι) (σ : Equiv.Perm (Fin N)) : JointWt O N lam Gm (Function.update w τ (w τ ∘ σ)) := by
  obtain ⟨z, hz0, hz⟩ := hw
  set g : ι → GL (Fin N) O := Pi.mulSingle τ (permGL σ) with hg
  refine ⟨grpA O N lam g • z, ?_, ?_⟩
  · intro h0
    apply hz0
    have := congrArg (fun t => grpA O N lam g⁻¹ • t) h0
    simp only [smul_smul, grpA_inv_mul, one_smul, smul_zero] at this
    exact this
  · intro τ' a ha
    obtain ⟨b0, hb0, -⟩ := GlobalTheory.ExpFrame.exists_unique_isProj O N ι lam τ' (w τ')
    obtain ⟨c, -, huniq⟩ := GlobalTheory.ExpFrame.exists_unique_isProj O N ι lam τ' (Function.update w τ (w τ ∘ σ) τ')
    have hconj : IsProj O N lam τ' (Function.update w τ (w τ ∘ σ) τ') (grp O N lam g * b0 * grp O N lam g⁻¹) := by
      apply isProj_conj O N lam g τ' (w τ') _ _ b0 hb0
      intro f
      by_cases hτ : τ' = τ
      · subst hτ
        have hgt : g τ' = permGL σ := by rw [hg, Pi.mulSingle_eq_same]
        rw [hgt, Function.update_self]
        simp only [Formalism.UG.dwAct, inv_inv]
        show weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW N N) (w τ') (Formalism.GradedWeylDivisibility.rowAct O (n := N) (permMat σ) f) =
          Formalism.GradedWeylDivisibility.rowAct O (n := N) (permMat σ) (weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW N N) (w τ' ∘ σ) f)
        rw [rowAct_permMat, rowAct_permMat, rowComp_rename_perm]
      · have hgt : g τ' = 1 := by rw [hg, Pi.mulSingle_eq_of_ne hτ]
        rw [hgt, Function.update_of_ne hτ, inv_one, (Formalism.UG.P.dual_weyl_action_mul O N N 1 1).2]
        rfl
    have haeq : (a : Module.End O (NablaT O N lam)) = grp O N lam g * b0 * grp O N lam g⁻¹ :=
      (huniq _ ha).trans (huniq _ hconj).symm
    set b : alg O N lam := ⟨b0, Algebra.subset_adjoin (Or.inr ⟨τ', w τ', hb0⟩)⟩ with hbdef
    have haeq' : a = grpA O N lam g * b * grpA O N lam g⁻¹ := Subtype.ext haeq
    rw [haeq', smul_smul, mul_assoc, grpA_inv_mul, mul_one, mul_smul, hz τ' b hb0]

theorem sum_lt_swap {N : ℕ} (v : Fin N → ℕ) (a b : Fin N) (hab : (b : ℕ) = a + 1) (h : v a < v b) :
    ∑ c : Fin N, (N - (c : ℕ)) * v c < ∑ c : Fin N, (N - (c : ℕ)) * (v ∘ Equiv.swap a b) c := by
  classical
  have hne : a ≠ b := fun e => by rw [e] at hab; omega
  rw [← Finset.sum_add_sum_compl {a, b}, ← Finset.sum_add_sum_compl {a, b} (fun c : Fin N => (N - (c : ℕ)) * (v ∘ Equiv.swap a b) c)]
  have hrest : ∑ c ∈ ({a, b} : Finset (Fin N))ᶜ, (N - (c : ℕ)) * v c =
      ∑ c ∈ ({a, b} : Finset (Fin N))ᶜ, (N - (c : ℕ)) * (v ∘ Equiv.swap a b) c := by
    apply Finset.sum_congr rfl
    intro c hc
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hc.1 hc.2]
  rw [hrest, Finset.sum_pair hne, Finset.sum_pair hne]
  simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have hb : (b : ℕ) < N := b.isLt
  have hk : N - (a : ℕ) = (N - (b : ℕ)) + 1 := by omega
  rw [hk]
  have : (N - (b : ℕ) + 1) * v a + (N - b) * v b < (N - (b : ℕ) + 1) * v b + (N - b) * v a := by nlinarith
  omega

theorem pot_lt_swap {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → Fin N → ℕ) (τ : ι) (a b : Fin N)
    (hab : (b : ℕ) = a + 1) (h : w τ a < w τ b) : pot N w < pot N (Function.update w τ (w τ ∘ Equiv.swap a b)) := by
  unfold pot
  apply Finset.sum_lt_sum
  · intro i _
    by_cases hi : i = τ
    · subst hi
      rw [Function.update_self]
      exact (sum_lt_swap _ a b hab h).le
    · rw [Function.update_of_ne hi]
  · exact ⟨τ, Finset.mem_univ _, by rw [Function.update_self]; exact sum_lt_swap _ a b hab h⟩

theorem antitone_of_adj {N : ℕ} (v : Fin N → ℕ) (h : ∀ a b : Fin N, (b : ℕ) = a + 1 → v b ≤ v a) : Antitone v := by
  cases N with
  | zero => intro a; exact a.elim0
  | succ n => exact Fin.antitone_iff_succ_le.2 fun i => h i.castSucc i.succ (by simp)

theorem antitone_of_pot_max : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι]
    [DecidableEq ι] (lam : ι → ℕ → ℕ) (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm] (w : ι → Fin N → ℕ),
    GlobalTheory.HighWt.JointWt O N lam Gm w → (∀ w' : ι → Fin N → ℕ, GlobalTheory.HighWt.JointWt O N lam Gm w' → GlobalTheory.HighWt.pot N w' ≤ GlobalTheory.HighWt.pot N w) →
    ∀ τ, Antitone (w τ) := by
  intro O _ _ _ _ N ι _ _ lam Gm _ _ w hw hmax τ
  apply antitone_of_adj
  intro a b hab
  by_contra hlt
  push_neg at hlt
  have h1 := hmax _ (jointWt_perm O N lam Gm w hw τ (Equiv.swap a b))
  have h2 := pot_lt_swap w τ a b hab hlt
  omega

end GlobalTheory.HighWt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JointRowWeightBoundsDualWeylModule
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

set_option autoImplicit false

open MvPolynomial Formalism.GradedWeylDivisibility

namespace GlobalTheory.HighWt

theorem dualWeyl_rowDeg_dominance (O : Type) [CommRing O] [IsDomain O] (N : ℕ) (ν : Fin N → ℕ)
    (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ dualWeyl O N N ν) : ∀ m ∈ f.support,
      (∀ k : ℕ, (∑ a : Fin N with a.val < k, rowDeg m a) ≤ ∑ t : Fin N with t.val < k, ν t) ∧
      ∑ a : Fin N, rowDeg m a = ∑ t : Fin N, ν t := by
  classical
  rw [standardMonomialSpanDomain O N N ν] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, hshape, rfl⟩ := hx
    intro m hm
    have h := bideterminantDominance O N N K sz hsz I m hm
    rw [hshape] at h
    exact h
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm
    rcases Finset.mem_union.mp (support_add hm) with h | h
    · exact hx m h
    · exact hy m h
  | smul c x _ hx =>
    intro m hm
    exact hx m (support_smul hm)

theorem rename_rowPerm_mem (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (σ : Equiv.Perm (Fin N))
    (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ dualWeyl O N N ν) :
    rename (fun v : Fin N × Fin N => (σ v.1, v.2)) f ∈ dualWeyl O N N ν := by
  classical
  have h : (rename (fun v : Fin N × Fin N => (σ v.1, v.2)) : MvPolynomial (Fin N × Fin N) O →ₐ[O] _) =
      rowAct O (Matrix.of fun a b : Fin N => if σ a = b then (1 : O) else 0) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [rowAct]
  rw [h]
  exact dualWeylRowStable O N N ν _ f hf

theorem weight_rowW_eq_rowDeg {N : ℕ} (m : Fin N × Fin N →₀ ℕ) (a : Fin N) :
    Finsupp.weight (rowW N N) m a = rowDeg m a := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · simp [rowW, rowDeg]
  · intro b _ hb
    simp [rowW, Ne.symm hb]
  · simp

end GlobalTheory.HighWt

namespace GlobalTheory.HighWt

open MvPolynomial Formalism.GradedWeylDivisibility

theorem sum_fin_lt_one {N : ℕ} (h : 0 < N) (g : Fin N → ℕ) : ∑ b : Fin N with b.val < 1, g b = g ⟨0, h⟩ := by
  rw [Finset.sum_eq_single_of_mem (⟨0, h⟩ : Fin N) (by simp)]
  intro b hb hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
  exact absurd (Fin.ext (by simp; omega)) hne

theorem sum_fin_split_last {N : ℕ} (h : 0 < N) (g : Fin N → ℕ) :
    ∑ b : Fin N, g b = ∑ b : Fin N with b.val < N - 1, g b + g ⟨N - 1, by omega⟩ := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun b : Fin N => b.val < N - 1)]
  congr 1
  rw [Finset.sum_eq_single_of_mem (⟨N - 1, by omega⟩ : Fin N) (by simp; omega)]
  intro b hb hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hb
  exact absurd (Fin.ext (by simp; omega)) hne

theorem jointWt_bounds : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι]
    [DecidableEq ι] (lam : ι → ℕ → ℕ), (∀ τ, Antitone (res N (lam τ))) → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm]
    (w : ι → Fin N → ℕ), GlobalTheory.HighWt.JointWt O N lam Gm w → ∀ τ, ∑ a : Fin N, w τ a = ∑ a : Fin N, lam τ a ∧
      ∀ a : Fin N, lam τ (N - 1) ≤ w τ a ∧ w τ a ≤ lam τ 0 := by
  intro O _ _ _ _ N ι _ _ lam _ Gm _ _ w hw τ
  classical
  obtain ⟨z, hz0, hz⟩ := hw
  obtain ⟨a0, ha0, -⟩ := GlobalTheory.ExpFrame.exists_unique_isProj O N ι lam τ (w τ)
  have hmem : a0 ∈ alg O N lam := Algebra.subset_adjoin (Or.inr ⟨τ, w τ, ha0⟩)
  have hex : ∃ x : ∀ τ, dualWeyl O N N (res N (lam τ)),
      weightedHomogeneousComponent (rowW N N) (w τ) (x τ : MvPolynomial (Fin N × Fin N) O) ≠ 0 := by
    by_contra hne
    push_neg at hne
    have ha0z : a0 = 0 := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro x
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.zero_apply]
      rw [ha0 x 0 (by simp [hne x])]
      exact MultilinearMap.map_coord_zero _ τ (by simp)
    have h1 := hz τ ⟨a0, hmem⟩ ha0
    have h0 : (⟨a0, hmem⟩ : alg O N lam) = 0 := Subtype.ext ha0z
    rw [h0, zero_smul] at h1
    exact hz0 h1.symm
  obtain ⟨x, hx⟩ := hex
  set f := weightedHomogeneousComponent (rowW N N) (w τ) (x τ : MvPolynomial (Fin N × Fin N) O) with hfdef
  have hfmem : f ∈ dualWeyl O N N (res N (lam τ)) := dualWeylRowGraded O N N _ _ _ (x τ).2
  have hfhom : IsWeightedHomogeneous (rowW N N) f (w τ) := weightedHomogeneousComponent_isWeightedHomogeneous _ _
  obtain ⟨m, hm⟩ := support_nonempty.2 hx
  have hrd : ∀ a, rowDeg m a = w τ a := fun a => by
    rw [← weight_rowW_eq_rowDeg, hfhom (mem_support_iff.1 hm)]
  have key : ∀ σ : Equiv.Perm (Fin N),
      (∀ k : ℕ, (∑ b : Fin N with b.val < k, w τ (σ.symm b)) ≤ ∑ t : Fin N with t.val < k, res N (lam τ) t) ∧
      ∑ b : Fin N, w τ (σ.symm b) = ∑ t : Fin N, res N (lam τ) t := by
    intro σ
    let e : Fin N × Fin N → Fin N × Fin N := fun v => (σ v.1, v.2)
    have he : Function.Injective e := by
      intro u v huv
      simp only [e, Prod.mk.injEq] at huv
      exact Prod.ext (σ.injective huv.1) huv.2
    have hm' : m.mapDomain e ∈ (rename e f).support := by
      rw [mem_support_iff, coeff_rename_mapDomain e he]
      exact mem_support_iff.1 hm
    have hrd' : ∀ b, rowDeg (m.mapDomain e) b = w τ (σ.symm b) := by
      intro b
      rw [← hrd]
      unfold rowDeg
      refine Finset.sum_congr rfl fun s _ => ?_
      have : (b, s) = e (σ.symm b, s) := by simp [e]
      rw [this, Finsupp.mapDomain_apply_of_injective he]
    have hd := dualWeyl_rowDeg_dominance O N _ _ (rename_rowPerm_mem O N _ σ f hfmem) _ hm'
    simp only [hrd'] at hd
    exact hd
  have hres : ∀ t : Fin N, res N (lam τ) t = lam τ t := fun t => rfl
  refine ⟨?_, fun a => ⟨?_, ?_⟩⟩
  · have h := (key (Equiv.refl _)).2
    simpa [hres] using h
  · have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) a.isLt
    obtain ⟨h1, h2⟩ := key (Equiv.swap ⟨N - 1, by omega⟩ a)
    have h3 := h1 (N - 1)
    rw [sum_fin_split_last hN, sum_fin_split_last hN] at h2
    have h4 : w τ ((Equiv.swap ⟨N - 1, by omega⟩ a).symm ⟨N - 1, by omega⟩) = w τ a := by simp
    rw [h4] at h2
    have h5 : res N (lam τ) ⟨N - 1, by omega⟩ = lam τ (N - 1) := rfl
    rw [h5] at h2
    omega
  · have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) a.isLt
    have h1 := (key (Equiv.swap ⟨0, hN⟩ a)).1 1
    rw [sum_fin_lt_one hN, sum_fin_lt_one hN] at h1
    have h2 : w τ a ≤ res N (lam τ) ⟨0, hN⟩ := by simpa using h1
    exact h2

end GlobalTheory.HighWt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamGApply
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial

namespace GlobalTheory.FrameRead

def detPol (R : Type) [CommRing R] (n : ℕ) : MvPolynomial (Fin n × Fin n) R :=
  Matrix.det (Matrix.of fun a s => X (a, s))

def liftPol {K C : Type} [CommRing K] [CommRing C] {n : ℕ} (e0 : K →+* C) (k : ℕ) (f : MvPolynomial (Fin n × Fin n) K) :
    MvPolynomial (Fin n × Fin n) C :=
  detPol C n ^ k * MvPolynomial.map e0 f

def Shift {ι : Type} {n : ℕ} (lam : ι → DomWeight n) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) : Prop :=
  ∀ τ (a : Fin n), (lamW τ a : ℤ) = (lam τ).w a + c τ

def IsPhi {K C : Type} [Field K] [Field C] {ι : Type} [Fintype ι] {n : ℕ} (e0 : K →+* C) (lam : ι → DomWeight n) (lamW : ι → ℕ → ℕ)
    (Φ : VV K lam →ₛₗ[e0] NablaT C n lamW) : Prop :=
  ∀ (x : ι → MvPolynomial (Fin n × Fin n) K) (v : VV K lam), (∀ τ, x τ ∈ nablaSq K n (lam τ)) → (v : Pol K ι n) = ten x →
    ∃ y : ∀ τ, dualWeyl C n n (res n (lamW τ)),
      (∀ τ, (y τ : MvPolynomial (Fin n × Fin n) C) = liftPol e0 (lamW τ (n - 1)) (x τ)) ∧ Φ v = PiTensorProduct.tprod C y

def lamG (C : Type) [CommRing C] {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) :
    (ι → GL (Fin n) C) →* Module.End C (NablaT C n lamW) where
  toFun g := ((∏ τ, Matrix.GeneralLinearGroup.det (g τ) ^ c τ : Cˣ) : C) • grp C n lamW g
  map_one' := by simp [grp]
  map_mul' g h := by
    simp only [grp, map_mul, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib, Units.val_mul, smul_mul_smul_comm]

theorem lamG_apply (C : Type) [CommRing C] {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (lamW : ι → ℕ → ℕ) (c : ι → ℤ)
    (g : ι → GL (Fin n) C) (z : NablaT C n lamW) :
    lamG C n lamW c g z = ((∏ τ, Matrix.GeneralLinearGroup.det (g τ) ^ c τ : Cˣ) : C) • grp C n lamW g z := rfl

def AtPlace {K : Type} [Field K] [NumberField K] {l : ℕ} [Fact l.Prime] (w : HeightOneSpectrum (𝓞 K)) (e0 : K →+* PadicAlgCl l) : Prop :=
  ∀ x : 𝓞 K, x ∈ w.asIdeal ↔ ‖e0 x‖ < 1

end GlobalTheory.FrameRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoBlockConstantCentred
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpTie.Lift

theorem block_centre : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.ExpTie.Lift.ValsAt L j τ → (∀ a, Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ ≤ a → a < Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ + (GlobalTheory.ExpTie.parOf L j).t → (GlobalTheory.ExpTie.Lift.wts L j).lam τ a = (GlobalTheory.ExpTie.Lift.wts L j).lam τ (Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ)) ∧ (((GlobalTheory.ExpTie.Lift.wts L j).bot (GlobalTheory.ExpTie.parOf L j) τ : ℝ) + (((GlobalTheory.ExpTie.parOf L j).t : ℝ) - 1) / 2 - (GlobalTheory.ExpTie.Lift.wts L j).c τ = -(GlobalTheory.ExpTie.Lift.wts L j).e τ) := by
  intro D L j τ hv
  have hk := D.R.m_add_three_le_k
  have ht0 := D.R.t_odd.pos
  have hkc : Formalism.CohomologicalDescent.ShortWeightBounds.kc (parOf L j) + (wts L j).j τ = D.R.k + (j : ℕ) := by
    simp only [Formalism.CohomologicalDescent.ShortWeightBounds.kc, parOf, wts]; omega
  have htt : (parOf L j).t = D.R.t := rfl
  have he : (wts L j).e τ = wj D ((j : ℕ) + 1) τ := rfl
  constructor
  · intro a ha1 ha2
    rw [hkc] at ha1 ⊢
    rw [hkc, htt] at ha2
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ha1
    have h1 := hv.2.2.1 s (by omega)
    have h0 := hv.2.2.1 0 ht0
    simp only [add_zero, Nat.cast_zero, sub_zero] at h0
    have hU : ((wts L j).U (parOf L j) τ (D.R.k + j + s) : ℝ) = (((wts L j).U (parOf L j) τ (D.R.k + j) - s : ℤ) : ℝ) := by
      push_cast; linarith
    have hU' := Int.cast_injective (α := ℝ) hU
    change Formalism.CohomologicalDescent.UnitNormBounds.UN _ _ _ = Formalism.CohomologicalDescent.UnitNormBounds.UN _ _ _ - _ at hU'
    unfold Formalism.CohomologicalDescent.UnitNormBounds.UN at hU'
    push_cast at hU'
    omega
  · have hrow : Formalism.CohomologicalDescent.ShortWeightBounds.kc (parOf L j) + (wts L j).j τ + (parOf L j).t - 1 = D.R.k + (j : ℕ) + (D.R.t - 1) := by
      rw [hkc, htt]; omega
    have h := hv.2.2.1 (D.R.t - 1) (by omega)
    have hts : ((D.R.t - 1 : ℕ) : ℝ) = (D.R.t : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hts] at h
    rw [Formalism.CohomologicalDescent.ShortWeightBounds.Wts.bot, hrow, htt, he]
    linarith

end GlobalTheory.ExpTie.Lift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedPullbackPolynomialRightActionOfCocycleStatement
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedPullbackPolynomial_rightAction_of_cocycle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (a : U → C → ℂˣ), (∀ (g h : U) (c : C), a (h * g) c = a g c * a h (g • c)) → tw M (fun c => (a 1 c : ℂ)) 1 = AlgHom.id ℂ _ ∧ ∀ u v : U, (tw M (fun c => (a v c : ℂ)) v).comp (tw M (fun c => (a u c : ℂ)) u) = tw M (fun c => (a (u * v) c : ℂ)) (u * v) := by
  first | exact @GlobalTheory.CuspEmb.tw_law | exact GlobalTheory.CuspEmb.tw_law | (intros; apply GlobalTheory.CuspEmb.tw_law <;> assumption)
end

