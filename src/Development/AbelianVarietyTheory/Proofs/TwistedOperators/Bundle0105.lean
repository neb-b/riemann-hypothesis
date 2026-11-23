module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleDistinctUnitary
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyDirectSumEquivOfFinrankLe
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0040
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FinalB

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowDivEqZeroOfMatRepUnipotentFixed
section
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

namespace GlobalTheory.GLDuality

private theorem rowGen_eval_C_eq_rowAct_transvection {n n' : ℕ} (a b : Fin n') (t : ℂ)
    (f : MvPolynomial (Fin n' × Fin n) ℂ) :
    (rowGen ℂ a b f).eval (C t) = rowAct ℂ (Matrix.transvection a b t)ᵀ f := by
  have key : (Polynomial.evalRingHom (C t : MvPolynomial (Fin n' × Fin n) ℂ)).comp
      (rowGen ℂ (n := n) a b).toRingHom = (rowAct ℂ (n := n) (Matrix.transvection a b t)ᵀ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [rowGen, rowAct]
    · rintro ⟨i, s⟩
      by_cases h : i = b
      · subst h
        simp [rowGen, rowAct, Matrix.transvection, Matrix.single, Matrix.one_apply, add_mul,
          Finset.sum_add_distrib, ite_and, add_comm]
        rw [Finset.sum_eq_single a (fun x _ hx => by simp [Ne.symm hx]) (by simp), if_pos rfl, mul_comm]
      · simp [rowGen, rowAct, Matrix.transvection, Matrix.single, Matrix.one_apply, add_mul,
          Finset.sum_add_distrib, h, Ne.symm h]
  exact RingHom.congr_fun key f

theorem rowDiv_eq_zero_of_matRep_unipotent_fixed : ∀ (n n' : ℕ) (v : MvPolynomial (Fin n' × Fin n) ℂ), (∀ g : GL (Fin n') ℂ, (g : Matrix (Fin n') (Fin n') ℂ).BlockTriangular id → (∀ a, (g : Matrix (Fin n') (Fin n') ℂ) a a = 1) → matRep n n' (1, g) v = v) → ∀ a b : Fin n', a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ a b k v = 0 := by
  intro n n' v hv a b hab k hk
  have hroot : ∀ t : ℂ, (rowGen ℂ a b v).eval (C t) = v := by
    intro t
    rw [rowGen_eval_C_eq_rowAct_transvection]
    have hdet : IsUnit (Matrix.transvection a b t).det := by
      rw [Matrix.det_transvection_of_ne _ _ (ne_of_lt hab)]
      exact isUnit_one
    let g : GL (Fin n') ℂ := Matrix.nonsingInvUnit _ hdet
    have hgv : (g : Matrix (Fin n') (Fin n') ℂ) = Matrix.transvection a b t := rfl
    have hbt : (g : Matrix (Fin n') (Fin n') ℂ).BlockTriangular id := by
      intro i j hij
      have hne : i ≠ j := fun h => by simp [h] at hij
      have hne' : ¬(a = i ∧ b = j) := by
        rintro ⟨rfl, rfl⟩
        exact absurd (lt_trans hab hij) (lt_irrefl _)
      simp [hgv, Matrix.transvection, Matrix.single, hne, hne']
    have hdiag : ∀ i, (g : Matrix (Fin n') (Fin n') ℂ) i i = 1 := by
      intro i
      have hne' : ¬(a = i ∧ b = i) := by
        rintro ⟨rfl, rfl⟩
        exact lt_irrefl _ hab
      simp [hgv, Matrix.transvection, Matrix.single, hne']
    have hg := hv g hbt hdiag
    rw [matRep_one_left, hgv] at hg
    exact hg
  have hconst : rowGen ℂ a b v = Polynomial.C v := by
    rw [← sub_eq_zero]
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_
      (Set.infinite_range_of_injective (MvPolynomial.C_injective (Fin n' × Fin n) ℂ))
    rintro _ ⟨t, rfl⟩
    simp [Polynomial.IsRoot, hroot t]
  show (rowGen ℂ a b v).coeff k = 0
  rw [hconst, Polynomial.coeff_C, if_neg (by omega)]

end GlobalTheory.GLDuality
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaJetMapWeightedTableScale
section
open Formalism.L2.Ker MvPolynomial

noncomputable section

namespace GlobalTheory.JetScale

section General

variable {σ : Type} [Fintype σ]

def scaleVar (w : σ → ℂ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
  aeval fun v => C (w v) * X v

lemma monomial_eq_prod (s : σ →₀ ℕ) (r : ℂ) :
    (monomial s r : MvPolynomial σ ℂ) = C r * ∏ v, X v ^ s v := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]

lemma scaleVar_monomial (w : σ → ℂ) (s : σ →₀ ℕ) (r : ℂ) :
    scaleVar w (monomial s r) = monomial s (r * ∏ v, w v ^ s v) := by
  rw [monomial_eq_prod, monomial_eq_prod, scaleVar, map_mul, aeval_C, map_prod, map_mul C, map_prod C]
  simp only [map_pow, aeval_X, mul_pow, Finset.prod_mul_distrib, algebraMap_eq]
  ring

end General

section Jet

variable {ι : Type} [Fintype ι] {a b : ℕ}

lemma jetLin_monomial (J : (DVar ι a b →₀ ℕ) → ℂ) (m : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ) (r : ℂ) :
    jetLin J (monomial m r) =
      monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn) (r * J (m.comapDomain Sum.inr Sum.inr_injective.injOn)) := by
  have h : (monomial m r : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ) =
      r • basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ m := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, jetLin, Module.Basis.constr_basis, smul_monomial, smul_eq_mul]

def wDer (c : ι → ℂ) : (ι × Fin b × Fin b) ⊕ DVar ι a b → ℂ := Sum.elim (fun _ => 1) (fun k => c k.1)

def wCoord (c : ι → ℂ) : (ι × Fin b × Fin b) ⊕ DVar ι a b → ℂ := Sum.elim (fun k => c k.1) (fun _ => 1)

lemma jetLin_scaleDer (c : ι → ℂ) (J : (DVar ι a b →₀ ℕ) → ℂ) (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ) :
    jetLin J (scaleVar (wDer c) Q) = jetLin (fun m => (∏ k, c k.1 ^ m k) * J m) Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial m r =>
    rw [scaleVar_monomial, jetLin_monomial, jetLin_monomial, Fintype.prod_sum_type]
    simp [wDer, Finsupp.comapDomain_apply]
    congr 1
    ring
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]

lemma blockAct_diag (c : ι → ℂ) :
    Formalism.GradedWeylDivisibility.blockAct ℂ (n := b) (fun τ => Matrix.diagonal fun _ : Fin b => c τ) = scaleVar (fun v : ι × Fin b × Fin b => c v.1) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [Formalism.GradedWeylDivisibility.blockAct, scaleVar, Matrix.diagonal_apply, apply_ite C, ite_mul, Finset.sum_ite_eq]

lemma jetLin_scaleCoord (c : ι → ℂ) (J : (DVar ι a b →₀ ℕ) → ℂ) (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ) :
    jetLin J (scaleVar (wCoord c) Q) = scaleVar (fun v : ι × Fin b × Fin b => c v.1) (jetLin J Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial m r =>
    rw [scaleVar_monomial, jetLin_monomial, jetLin_monomial, scaleVar_monomial, Fintype.prod_sum_type]
    simp [wCoord, Finsupp.comapDomain_apply]
    congr 1
    ring
  | add p q hp hq => simp only [map_add (f := _), hp, hq]

lemma scale_subD (c : ι → ℂ) :
    (scaleVar (wDer (a := a) (b := b) c)).comp (subD ℂ ι a b) = (scaleVar (wCoord c)).comp (subD ℂ ι a b) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, subD, aeval_X]
  split_ifs
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [map_sum, map_mul, scaleVar, aeval_X, wDer, wCoord, Sum.elim_inl, Sum.elim_inr, map_one, one_mul]
      refine Finset.sum_congr rfl fun β _ => ?_
      ring
  · simp

lemma jetLin_smul_table (u : ℂ) (J : (DVar ι a b →₀ ℕ) → ℂ) (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ) :
    jetLin (fun m => u * J m) Q = u • jetLin J Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial m r =>
    rw [jetLin_monomial, jetLin_monomial, smul_monomial, smul_eq_mul]
    congr 1
    ring
  | add p q hp hq => simp only [map_add (f := _), hp, hq, smul_add]

end Jet

theorem jetMap_weight_scale {ι : Type} [Fintype ι] {a b : ℕ} (u : ℂ) (c : ι → ℂ) (J : (DVar ι a b →₀ ℕ) → ℂ) (nn : ι → ℕ)
    (P : Formalism.L2.DIV.Pol ℂ ι a) :
    jetMap (fun m => u * ((m.prod fun k e => c k.1 ^ e) * J m)) nn P =
      u • Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => Matrix.diagonal fun _ : Fin b => c τ) (jetMap J nn P) := by
  have hJ : (fun m : DVar ι a b →₀ ℕ => u * ((m.prod fun k e => c k.1 ^ e) * J m)) =
      fun m => u * ((∏ k, c k.1 ^ m k) * J m) := by
    funext m
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [hJ, blockAct_diag]
  rw [jetMap, jetMap, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply]
  have key := DFunLike.congr_fun (scale_subD (a := a) (b := b) c) (LinearMap.mulRight ℂ (∏ τ, frDet ℂ a τ ^ nn τ) P)
  rw [AlgHom.comp_apply, AlgHom.comp_apply] at key
  rw [jetLin_smul_table, ← jetLin_scaleDer, key, jetLin_scaleCoord]

end GlobalTheory.JetScale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeightMapDomain
section
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

namespace GlobalTheory.GLDuality.HighestLine

theorem weight_mapDomain {r m n : ℕ} (h : m ≤ n) (u : Fin r × Fin m →₀ ℕ) (i : Fin m) :
    Finsupp.weight (colW r n) (Finsupp.mapDomain (Prod.map id (Fin.castLE h)) u) (Fin.castLE h i) =
      Finsupp.weight (colW r m) u i := by
  classical
  simp only [Finsupp.weight_apply]
  rw [Finsupp.sum_mapDomain_index (h := fun (x : Fin r × Fin n) (c : ℕ) => c • colW r n x)
    (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  rw [Finsupp.sum, Finsupp.sum, Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [colW, Pi.single_apply, Fin.castLE_inj]

theorem le_weight {r n : ℕ} (u : Fin r × Fin n →₀ ℕ) (x : Fin r × Fin n) :
    u x ≤ Finsupp.weight (colW r n) u x.2 := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  by_cases hx : u x = 0
  · rw [hx]; exact Nat.zero_le _
  · refine le_trans ?_ (Finset.single_le_sum (f := fun y => (u y • colW r n y) x.2)
      (fun y _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr hx))
    simp [colW]

theorem colAdd_rename {r m n : ℕ} (h : m ≤ n) (l j : Fin m) (c : ℂ) (f : MvPolynomial (Fin r × Fin m) ℂ) :
    colAdd ℂ (Fin.castLE h l) (Fin.castLE h j) c (rename (Prod.map id (Fin.castLE h)) f) =
      rename (Prod.map id (Fin.castLE h)) (colAdd ℂ l j c f) := by
  have key : (colAdd ℂ (Fin.castLE h l) (Fin.castLE h j) c).comp (rename (Prod.map id (Fin.castLE h))) =
      (rename (Prod.map id (Fin.castLE h))).comp (colAdd ℂ (r := r) l j c) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    simp only [AlgHom.comp_apply, rename_X, colAdd, aeval_X, Prod.map_apply, id_eq, Fin.castLE_inj]
    split_ifs <;> simp [rename_X]
  exact DFunLike.congr_fun key f

theorem rowDiv_rename {r m n : ℕ} (h : m ≤ n) (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin m) ℂ) :
    rowDiv ℂ a b k (rename (Prod.map id (Fin.castLE h)) f) =
      rename (Prod.map id (Fin.castLE h)) (rowDiv ℂ a b k f) := by
  have key : (rowGen ℂ (n := n) a b).comp (rename (Prod.map id (Fin.castLE h))) =
      (Polynomial.mapAlgHom (rename (Prod.map id (Fin.castLE h)))).comp (rowGen ℂ (n := m) a b) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨x, s⟩
    simp only [AlgHom.comp_apply, rename_X, rowGen, aeval_X, Prod.map_apply, id_eq]
    split_ifs <;> simp [rename_X, Polynomial.coe_mapAlgHom]
  have hf := DFunLike.congr_fun key f
  simp only [AlgHom.comp_apply] at hf
  simp only [rowDiv]
  rw [hf]
  simp [Polynomial.coe_mapAlgHom, Polynomial.coeff_map]

theorem wide {r n : ℕ} (h : r ≤ n) (ν : Fin n → ℕ) (hν : Antitone ν) (h0 : ∀ s : Fin n, r ≤ s.val → ν s = 0)
    (f : MvPolynomial (Fin r × Fin n) ℂ) (hf : f ∈ dualWeyl ℂ r n ν)
    (hk : ∀ a b : Fin r, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ a b k f = 0) :
    ∃ c : ℂ, f = c • rename (Prod.map id (Fin.castLE h)) (hw ℂ le_rfl fun i => ν (Fin.castLE h i)) := by
  classical
  have hφi : Function.Injective (Prod.map id (Fin.castLE h) : Fin r × Fin r → Fin r × Fin n) :=
    Function.Injective.prodMap Function.injective_id (Fin.castLE_injective h)
  have hpt := (dualWeylPoint ℂ r n ν f).1 hf
  have hvars : (f.vars : Set (Fin r × Fin n)) ⊆
      Set.range (Prod.map id (Fin.castLE h) : Fin r × Fin r → Fin r × Fin n) := by
    intro x hx
    rw [Finset.mem_coe, MvPolynomial.mem_vars_iff_mem_support] at hx
    obtain ⟨u, hu, hxu⟩ := hx
    have hwu : Finsupp.weight (colW r n) u = ν := hpt.1 (MvPolynomial.mem_support_iff.mp hu)
    have hx2 : x.2.val < r := by
      by_contra hlt
      have h1 := le_weight u x
      rw [hwu, h0 x.2 (not_lt.mp hlt)] at h1
      exact (Finsupp.mem_support_iff.mp hxu) (Nat.le_zero.mp h1)
    exact ⟨(x.1, ⟨x.2.val, hx2⟩), Prod.ext rfl (Fin.ext rfl)⟩
  obtain ⟨g, rfl⟩ := exists_rename_eq_of_vars_subset_range f _ hφi hvars
  have hgw : IsWeightedHomogeneous (colW r r) g (fun i => ν (Fin.castLE h i)) := by
    intro u hu
    have hu' : AddMonoidAlgebra.coeff (rename (Prod.map id (Fin.castLE h)) g)
        (Finsupp.mapDomain (Prod.map id (Fin.castLE h)) u) ≠ 0 := by
      rwa [coeff_rename_mapDomain _ hφi]
    have hwu := hpt.1 hu'
    funext i
    rw [← weight_mapDomain h u i, hwu]
  have hgc : ∀ l j : Fin r, l < j → ∀ c : ℂ, colAdd ℂ l j c g = g := by
    intro l j hlj c
    apply rename_injective _ hφi
    rw [← colAdd_rename h]
    exact hpt.2 _ _ (show Fin.castLE h l < Fin.castLE h j from hlj) c
  have hg : g ∈ dualWeyl ℂ r r (fun i => ν (Fin.castLE h i)) :=
    (dualWeylPoint ℂ r r _ g).2 ⟨hgw, hgc⟩
  have hgk : ∀ a b : Fin r, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ a b k g = 0 := by
    intro a b hab k hk1
    apply rename_injective _ hφi
    rw [← rowDiv_rename h, map_zero]
    exact hk a b hab k hk1
  have hant : Antitone (fun i : Fin r => ν (Fin.castLE h i)) := fun i j hij =>
    hν (show Fin.castLE h i ≤ Fin.castLE h j from hij)
  obtain ⟨c, hc⟩ := hwLine ℂ r r le_rfl _ hant g hg hgk
  exact ⟨c, by rw [hc, map_smul]⟩

theorem highest_line : ∀ (r n : ℕ) (ν : Fin n → ℕ) (v : MvPolynomial (Fin r × Fin n) ℂ), v ∈ dualWeyl ℂ r n ν → (∀ a b : Fin r, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ a b k v = 0) → v ≠ 0 → (∃ a : Part (min n r), ν = rowNu (r := n) a.1) ∧ ∀ w ∈ dualWeyl ℂ r n ν, (∀ a b : Fin r, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ a b k w = 0) → ∃ c : ℂ, w = c • v := by
  intro r n ν v hv hkv hv0
  have hant : Antitone ν := by
    intro i j hij
    by_contra hlt
    push Not at hlt
    have hij' : i < j := lt_of_le_of_ne hij (by rintro rfl; exact lt_irrefl _ hlt)
    have hbot := dualWeylNonDom ℂ r n ν ⟨i, j, hij', hlt⟩
    rw [hbot] at hv
    exact hv0 ((Submodule.mem_bot ℂ).mp hv)
  have h0 : ∀ s : Fin n, r ≤ s.val → ν s = 0 := by
    intro s hs
    by_contra hne
    exact hv0 (hwLineTall ℂ r n ν ⟨s, hs, Nat.pos_of_ne_zero hne⟩ v hv hkv)
  have hline : ∃ H : MvPolynomial (Fin r × Fin n) ℂ, ∀ w ∈ dualWeyl ℂ r n ν,
      (∀ a b : Fin r, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ a b k w = 0) → ∃ c : ℂ, w = c • H := by
    rcases le_total n r with hnr | hrn
    · exact ⟨hw ℂ hnr ν, fun w hw' hk => hwLine ℂ r n hnr ν hant w hw' hk⟩
    · exact ⟨_, fun w hw' hk => wide hrn ν hant h0 w hw' hk⟩
  obtain ⟨H, hH⟩ := hline
  refine ⟨⟨⟨fun i => ν (Fin.castLE (min_le_left n r) i), fun i j hij =>
    hant (show Fin.castLE (min_le_left n r) i ≤ Fin.castLE (min_le_left n r) j from hij)⟩, ?_⟩, ?_⟩
  · funext s
    simp only [rowNu]
    split_ifs with hs
    · exact congrArg ν (Fin.ext rfl)
    · have hsn := s.isLt
      exact h0 s (by omega)
  · intro w hw' hkw
    obtain ⟨c₀, hc₀⟩ := hH v hv hkv
    obtain ⟨c₁, hc₁⟩ := hH w hw' hkw
    have hc0 : c₀ ≠ 0 := by
      rintro rfl
      exact hv0 (by rw [hc₀, zero_smul])
    refine ⟨c₁ / c₀, ?_⟩
    rw [hc₁, hc₀, smul_smul, div_mul_cancel₀ _ hc0]

end GlobalTheory.GLDuality.HighestLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeightedHomogeneousComponentColWMem
section
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

namespace GlobalTheory.GLDuality

theorem matRep_diagGL_monomial {n n' : ℕ} (t : Fin n → ℂˣ) (d : Fin n' × Fin n →₀ ℕ) (c : ℂ) :
    matRep n n' (diagGL ℂ n t, 1) (monomial d c) =
      (∏ s, (t s : ℂ) ^ (Finsupp.weight (colW n' n) d s)) • monomial d c := by
  have hX : ∀ v : Fin n' × Fin n, matRep n n' (diagGL ℂ n t, 1) (X v) = (t v.2 : ℂ) • X v := by
    rintro ⟨a, s⟩
    rw [matRep_X, Finset.sum_eq_single a, Finset.sum_eq_single s]
    · simp [diagGL, smul_eq_C_mul]
    · intro b _ hb
      simp [diagGL, hb]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  induction d using Finsupp.induction_linear generalizing c with
  | zero => simp [matRep_apply]
  | add d e hd he =>
    have h1 : (monomial (d + e) c : MvPolynomial (Fin n' × Fin n) ℂ) = monomial d c * monomial e 1 := by
      rw [monomial_mul, mul_one]
    have hd' := hd c
    have he' := he 1
    rw [matRep_apply] at hd' he'
    rw [h1, matRep_apply, map_mul, hd', he', smul_mul_smul_comm, ← Finset.prod_mul_distrib]
    simp only [map_add (f := _), Pi.add_apply, pow_add]
  | single v k =>
    have h1 := hX v
    rw [matRep_apply] at h1
    rw [← C_mul_X_pow_eq_monomial, matRep_apply, map_mul, map_pow, h1, smul_pow, mul_smul_comm]
    congr 1
    · rw [Finset.prod_eq_single v.2]
      · simp [Finsupp.weight_single, colW]
      · intro b _ hb
        simp [Finsupp.weight_single, colW, hb]
      · simp
    · simp

theorem matRep_diagGL_component {n n' : ℕ} (t : Fin n → ℂˣ) (μ : Fin n → ℕ)
    (v : MvPolynomial (Fin n' × Fin n) ℂ) :
    matRep n n' (diagGL ℂ n t, 1) (weightedHomogeneousComponent (colW n' n) μ v) =
      (∏ s, (t s : ℂ) ^ μ s) • weightedHomogeneousComponent (colW n' n) μ v := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [weightedHomogeneousComponent_apply, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [matRep_diagGL_monomial, (Finset.mem_filter.1 hd).2]

noncomputable def torusPowChar {n : ℕ} (μ : Fin n → ℕ) : (Fin n → ℂˣ) →* ℂ where
  toFun t := ∏ s, (t s : ℂ) ^ μ s
  map_one' := by simp
  map_mul' a b := by simp [mul_pow, Finset.prod_mul_distrib]

theorem torusPowChar_injective {n : ℕ} : Function.Injective (torusPowChar (n := n)) := by
  classical
  intro μ ν h
  funext a
  let t : Fin n → ℂˣ := Pi.mulSingle a (Units.mk0 2 two_ne_zero)
  have hprod : ∀ e : Fin n → ℕ, torusPowChar e t = 2 ^ e a := by
    intro e
    change ∏ s, (t s : ℂ) ^ e s = _
    rw [Finset.prod_eq_single a]
    · simp [t]
    · intro b _ hb
      simp [t, hb]
    · simp
  have h1 : (2 : ℂ) ^ μ a = 2 ^ ν a := by rw [← hprod, ← hprod, h]
  have h' : (2 : ℕ) ^ μ a = 2 ^ ν a := by exact_mod_cast h1
  exact Nat.pow_right_injective le_rfl h'

theorem weightedHomogeneousComponent_colW_mem (n n' : ℕ) (M : Submodule ℂ (MvPolynomial (Fin n' × Fin n) ℂ))
    (hM : ∀ t : Fin n → ℂˣ, ∀ v ∈ M, matRep n n' (diagGL ℂ n t, 1) v ∈ M) (ν : Fin n → ℕ)
    (v : MvPolynomial (Fin n' × Fin n) ℂ) (hv : v ∈ M) :
    weightedHomogeneousComponent (colW n' n) ν v ∈ M := by
  classical
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro l hl
  have hfin := weightedHomogeneousComponent_finsupp (w := colW n' n) v
  have hsum := sum_weightedHomogeneousComponent (colW n' n) v
  rw [finsum_eq_sum _ hfin] at hsum
  by_cases hν : ν ∈ hfin.toFinset
  · have hli := (linearIndependent_monoidHom (Fin n → ℂˣ) ℂ).comp _ (torusPowChar_injective (n := n))
    refine linearIndependent_iff'.1 hli hfin.toFinset
      (fun μ => l (weightedHomogeneousComponent (colW n' n) μ v)) ?_ ν hν
    funext t
    have h0 := (Submodule.mem_dualAnnihilator l).1 hl _ (hM t v hv)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hsum, map_sum, map_sum] at h0
    rw [Finset.sum_apply, Pi.zero_apply, ← h0]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [matRep_diagGL_component, map_smul, smul_eq_mul, mul_comm]
    rfl
  · have : weightedHomogeneousComponent (colW n' n) ν v = 0 := by
      by_contra h
      exact hν (hfin.mem_toFinset.2 h)
    rw [this, map_zero]

end GlobalTheory.GLDuality
end

