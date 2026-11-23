module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0437
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0446
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0445
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0817
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0538
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0412
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0419

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairVEqOfProdFunEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ExpansionInvariance

theorem chainTo_congr_lt {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    {k k' : ∀ j, V j →ₗ[ℂ] V (j + 1)} : ∀ n, (∀ j, j < n → k j = k' j) → chainTo k n = chainTo k' n
  | 0, _ => rfl
  | n + 1, h => by
    show k n ∘ₗ chainTo k n = k' n ∘ₗ chainTo k' n
    rw [h n n.lt_succ_self, chainTo_congr_lt n fun j hj => h j (by omega)]

theorem chainTo_add_at {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    {k₁ k₂ k₃ : ∀ j, V j →ₗ[ℂ] V (j + 1)} (j₀ : ℕ) (h₂ : ∀ j, j ≠ j₀ → k₂ j = k₁ j) (h₃ : ∀ j, j ≠ j₀ → k₃ j = k₁ j)
    (h : k₁ j₀ = k₂ j₀ + k₃ j₀) : ∀ n, j₀ < n → chainTo k₁ n = chainTo k₂ n + chainTo k₃ n
  | 0, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, hn => by
    show k₁ n ∘ₗ chainTo k₁ n = k₂ n ∘ₗ chainTo k₂ n + k₃ n ∘ₗ chainTo k₃ n
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h' | h'
    · rw [chainTo_add_at j₀ h₂ h₃ h n h', h₂ n (by omega), h₃ n (by omega), LinearMap.comp_add]
    · subst h'
      rw [chainTo_congr_lt (k := k₂) (k' := k₁) j₀ (fun j hj => h₂ j (by omega)),
        chainTo_congr_lt (k := k₃) (k' := k₁) j₀ (fun j hj => h₃ j (by omega)), h, LinearMap.add_comp]

theorem chainTo_smul_at {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    {k₁ k₂ : ∀ j, V j →ₗ[ℂ] V (j + 1)} (j₀ : ℕ) (a : ℂ) (h₂ : ∀ j, j ≠ j₀ → k₂ j = k₁ j)
    (h : k₁ j₀ = a • k₂ j₀) : ∀ n, j₀ < n → chainTo k₁ n = a • chainTo k₂ n
  | 0, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, hn => by
    show k₁ n ∘ₗ chainTo k₁ n = a • (k₂ n ∘ₗ chainTo k₂ n)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h' | h'
    · rw [chainTo_smul_at j₀ a h₂ h n h', h₂ n (by omega), LinearMap.comp_smul]
    · subst h'
      rw [chainTo_congr_lt (k := k₂) (k' := k₁) j₀ (fun j hj => h₂ j (by omega)), h, LinearMap.smul_comp]

theorem jetOp_mul_tab {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a)
    (lam' : ι → DomWeight b) (c : K) (J : (Formalism.L2.Ker.DVar ι a b →₀ ℕ) → K) (n : ι → ℕ) :
    Formalism.L2.Ker.jetOp lam lam' (fun k => c * J k) n = c • Formalism.L2.Ker.jetOp lam lam' J n := by
  have e : Formalism.L2.Ker.jetLin (fun k => c * J k) = c • Formalism.L2.Ker.jetLin J := by
    refine (MvPolynomial.basisMonomials ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) K).ext fun m => ?_
    simp only [Formalism.L2.Ker.jetLin, LinearMap.smul_apply, Module.Basis.constr_basis, MvPolynomial.smul_monomial,
      smul_eq_mul]
  ext1 P
  simp only [Formalism.L2.Ker.jetOp, Formalism.L2.Ker.jetMap, e, LinearMap.comp_apply, LinearMap.smul_apply, map_smul]

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem kkVec_smul (S : GridChoice W U) (p : Pair T) (a : ℂ) (f : WO (G.pS p) (G.pT p) → ℂ) (x : FinPt G p.small)
    (y : FinPt G p.big) : GlobalTheory.TopZeroInv.kkVec S p (a • f) x y = a • GlobalTheory.TopZeroInv.kkVec S p f x y := by
  have hJ : ∀ x' y', jetTab W S.N.frC p (a • f) x' y' = fun k => a * jetTab W S.N.frC p f x' y' k := by
    intro x' y'
    funext k
    simp only [jetTab, kerFin, fockIn, GlobalTheory.FiniteFock.pureTensorO_smul, GridData.Weil.ker, thetaKO, map_smul,
      Pi.smul_apply, smul_eq_mul]
  unfold GlobalTheory.TopZeroInv.kkVec fockComp
  rw [hJ, jetOp_mul_tab, smul_comm]

def colML (S : GridChoice W U) (t : T) (x : ∀ j, FinPt G (.top j)) :
    MultilinearMap (RingHom.id ℂ) (fun j : Fin D.R.m => ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))))
      (VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (wt G (.top D.R.m))) where
  toFun cc := colMapV S t (fun j => (cc j : WO _ _ → ℂ)) x
  map_update_add' := by
    intro _ cc j₀ a b
    unfold colMapV
    rw [← LinearMap.add_comp]
    congr 1
    refine chainTo_add_at j₀.1 ?_ ?_ ?_ D.R.m j₀.2
    · intro j hj
      dsimp only
      split_ifs with h
      · have hne : (⟨j, h⟩ : Fin D.R.m) ≠ j₀ := fun e => hj (congrArg Fin.val e)
        simp only [Function.update_of_ne hne]
      · rfl
    · intro j hj
      dsimp only
      split_ifs with h
      · have hne : (⟨j, h⟩ : Fin D.R.m) ≠ j₀ := fun e => hj (congrArg Fin.val e)
        simp only [Function.update_of_ne hne]
      · rfl
    · simp only [dif_pos j₀.2, Fin.eta, Function.update_self, Submodule.coe_add]
      exact GlobalTheory.TopZeroInv.kkVec_add S _ a.2 b.2 _ _
  map_update_smul' := by
    intro _ cc j₀ c a
    unfold colMapV
    rw [← LinearMap.smul_comp]
    congr 1
    refine chainTo_smul_at j₀.1 c ?_ ?_ D.R.m j₀.2
    · intro j hj
      dsimp only
      split_ifs with h
      · have hne : (⟨j, h⟩ : Fin D.R.m) ≠ j₀ := fun e => hj (congrArg Fin.val e)
        simp only [Function.update_of_ne hne]
      · rfl
    · simp only [dif_pos j₀.2, Fin.eta, Function.update_self, Submodule.coe_smul]
      exact kkVec_smul S _ c _ _ _

def rowML (S : GridChoice W U) (t : T) (y : ∀ i, FinPt G (.grid i D.R.m)) :
    MultilinearMap (RingHom.id ℂ) (fun i : Fin D.R.m => ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))))
      (VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] VV ℂ (wt G (.grid D.R.m D.R.m))) where
  toFun rr := rowMapV S (fun i => (rr i : WO _ _ → ℂ)) y
  map_update_add' := by
    intro _ rr i₀ a b
    unfold rowMapV
    rw [← LinearMap.add_comp]
    congr 1
    refine chainTo_add_at i₀.1 ?_ ?_ ?_ D.R.m i₀.2
    · intro i hi
      dsimp only
      split_ifs with h
      · have hne : (⟨i, h⟩ : Fin D.R.m) ≠ i₀ := fun e => hi (congrArg Fin.val e)
        simp only [Function.update_of_ne hne]
      · rfl
    · intro i hi
      dsimp only
      split_ifs with h
      · have hne : (⟨i, h⟩ : Fin D.R.m) ≠ i₀ := fun e => hi (congrArg Fin.val e)
        simp only [Function.update_of_ne hne]
      · rfl
    · simp only [dif_pos i₀.2, Fin.eta, Function.update_self, Submodule.coe_add]
      exact GlobalTheory.TopZeroInv.kkVec_add S _ a.2 b.2 _ _
  map_update_smul' := by
    intro _ rr i₀ c a
    unfold rowMapV
    rw [← LinearMap.smul_comp]
    congr 1
    refine chainTo_smul_at i₀.1 c ?_ ?_ D.R.m i₀.2
    · intro i hi
      dsimp only
      split_ifs with h
      · have hne : (⟨i, h⟩ : Fin D.R.m) ≠ i₀ := fun e => hi (congrArg Fin.val e)
        simp only [Function.update_of_ne hne]
      · rfl
    · simp only [dif_pos i₀.2, Fin.eta, Function.update_self, Submodule.coe_smul]
      exact kkVec_smul S _ c _ _ _

def pairRowL (S : GridChoice W U) (t : T) (y : ∀ i, FinPt G (.grid i D.R.m)) (u : VV ℂ (wt G (.top 0)))
    (v : VV ℂ (listedWt G (.grid 0 D.R.m))) :
    (VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (wt G (.top D.R.m))) →ₗ[ℂ]
      MultilinearMap (RingHom.id ℂ) (fun i : Fin D.R.m => ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)))) ℂ where
  toFun A := ((brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m)) (A u)).comp
    (LinearMap.applyₗ v)).compMultilinearMap (rowML S t y)
  map_add' A B := by
    ext rr
    simp only [LinearMap.add_apply, map_add (f := _), LinearMap.add_comp, MultilinearMap.add_apply]
    rfl
  map_smul' c A := by
    ext rr
    simp only [LinearMap.smul_apply, map_smul, LinearMap.smul_comp, MultilinearMap.smul_apply, RingHom.id_apply]
    rfl

def pairML (S : GridChoice W U) (t : T) (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m))
    (u : VV ℂ (wt G (.top 0))) (v : VV ℂ (listedWt G (.grid 0 D.R.m))) :
    MultilinearMap (RingHom.id ℂ) (fun j : Fin D.R.m => ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))))
      (MultilinearMap (RingHom.id ℂ) (fun i : Fin D.R.m => ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)))) ℂ) :=
  (pairRowL S t y u v).compMultilinearMap (colML S t x)

theorem pairML_apply (S : GridChoice W U) (t : T) (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m))
    (u : VV ℂ (wt G (.top 0))) (v : VV ℂ (listedWt G (.grid 0 D.R.m))) (cc rr) :
    pairML S t x y u v cc rr = (brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))).compl₁₂
      (colMapV S t (fun j => (cc j : WO _ _ → ℂ)) x) (rowMapV S (fun i => (rr i : WO _ _ → ℂ)) y) u v := rfl

theorem pairV_eq_of_prodFun_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T)
    {δ : Type} (τ : δ →₀ ℂ) (c c' : δ → ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ)
    (r r' : δ → ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ),
    (∀ d ∈ τ.support, ∀ j : Fin D.R.m, IsThetaFunO W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) (c d j) ∧
      IsThetaFunO W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) (c' d j)) →
    (∀ d ∈ τ.support, ∀ i : Fin D.R.m, IsThetaFunO W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (r d i) ∧
      IsThetaFunO W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (r' d i)) →
    (∀ (w : ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)))
      (z : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      (τ.sum fun d a => a * (∏ j, c d j (w j)) * ∏ i, r d i (z i)) = τ.sum fun d a => a * (∏ j, c' d j (w j)) * ∏ i, r' d i (z i)) →
    ∀ x y, pairV S t τ c r x y = pairV S t τ c' r' x y := by
  intro D T L sc G W U S t δ τ c c' r r' hc hr hprod x y
  classical
  refine LinearMap.ext fun u => LinearMap.ext fun v => ?_
  let f : δ → ∀ j : Fin D.R.m, ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))) :=
    fun d j => if h : d ∈ τ.support then ⟨c d j, (hc d h j).1⟩ else 0
  let f' : δ → ∀ j : Fin D.R.m, ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))) :=
    fun d j => if h : d ∈ τ.support then ⟨c' d j, (hc d h j).2⟩ else 0
  let g : δ → ∀ i : Fin D.R.m, ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) :=
    fun d i => if h : d ∈ τ.support then ⟨r d i, (hr d h i).1⟩ else 0
  let g' : δ → ∀ i : Fin D.R.m, ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) :=
    fun d i => if h : d ∈ τ.support then ⟨r' d i, (hr d h i).2⟩ else 0
  have ef : ∀ d ∈ τ.support, (fun j => (f d j : WO _ _ → ℂ)) = c d := fun d hd => funext fun j => by simp only [f, dif_pos hd]
  have ef' : ∀ d ∈ τ.support, (fun j => (f' d j : WO _ _ → ℂ)) = c' d := fun d hd => funext fun j => by simp only [f', dif_pos hd]
  have eg : ∀ d ∈ τ.support, (fun i => (g d i : WO _ _ → ℂ)) = r d := fun d hd => funext fun i => by simp only [g, dif_pos hd]
  have eg' : ∀ d ∈ τ.support, (fun i => (g' d i : WO _ _ → ℂ)) = r' d := fun d hd => funext fun i => by simp only [g', dif_pos hd]
  have key := GlobalTheory.funProd_multilinear_sum_eq (pairML S t x y u v) τ f f' g g' (fun w z => by
    rw [Finsupp.sum, Finsupp.sum]
    have h1 := hprod w z
    rw [Finsupp.sum, Finsupp.sum] at h1
    refine (Finset.sum_congr rfl fun d hd => ?_).trans (h1.trans (Finset.sum_congr rfl fun d hd => ?_))
    · rw [← ef d hd, ← eg d hd]
    · rw [← ef' d hd, ← eg' d hd])
  have hL : ∀ (cc : δ → ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ)
      (rr : δ → ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)
      (F : δ → ∀ j : Fin D.R.m, ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))))
      (H : δ → ∀ i : Fin D.R.m, ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)))),
      (∀ d ∈ τ.support, (fun j => (F d j : WO _ _ → ℂ)) = cc d) → (∀ d ∈ τ.support, (fun i => (H d i : WO _ _ → ℂ)) = rr d) →
      pairV S t τ cc rr x y u v = τ.sum fun d a => a * pairML S t x y u v (F d) (H d) := by
    intro cc rr F H hF hH
    unfold pairV
    rw [Finsupp.sum, Finsupp.sum, LinearMap.sum_apply, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, pairML_apply, hF d hd, hH d hd]
  rw [hL c r f g ef eg, hL c' r' f' g' ef' eg']
  exact key

end GlobalTheory.ExpansionInvariance

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairVecSumEqOfProdEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.TopZeroInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TopZeroInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}


variable (W) in
def thetaSub (p : Pair T) : Submodule ℂ (WO (G.pS p) (G.pT p) → ℂ) where
  carrier := {f | IsThetaFunO W.ψ _ _ f}
  add_mem' := by
    intro f g hf hg
    change IsThetaFunO W.ψ _ _ f at hf
    change IsThetaFunO W.ψ _ _ g at hg
    refine ⟨?_, ?_, hf.cont.add hg.cont, fun k L hL hfin w =>
      (hf.smooth k L hL hfin w).add (hg.smooth k L hL hfin w)⟩
    · intro γ w
      simp only [Pi.add_apply, hf.quasi, hg.quasi, mul_add]
    · obtain ⟨A, hA, hAf⟩ := hf.level
      obtain ⟨B, hB, hBg⟩ := hg.level
      refine ⟨A ⊓ B, hA.inter hB, fun u hu hfin => ?_⟩
      funext w
      have ef := congrFun (hAf u hu.1 hfin) w
      have eg := congrFun (hBg u hu.2 hfin) w
      unfold heisO at ef eg ⊢
      rw [Pi.add_apply, Pi.add_apply, mul_add, ef, eg]
  zero_mem' := by
    refine ⟨?_, ⟨⊤, isOpen_univ, ?_⟩, continuous_const, fun _ _ _ _ _ => contDiff_const⟩
    · intro γ w
      simp only [Pi.zero_apply, mul_zero]
    · intro u _ _
      funext w
      simp only [heisO, Pi.zero_apply, mul_zero]
  smul_mem' c f hf := by
    change IsThetaFunO W.ψ _ _ f at hf
    refine ⟨?_, ?_, hf.cont.const_smul c, fun k L hL hfin w =>
      (hf.smooth k L hL hfin w).const_smul c⟩
    · intro γ w
      rw [Pi.smul_apply, Pi.smul_apply, hf.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm]
    · obtain ⟨A, hA, hAf⟩ := hf.level
      refine ⟨A, hA, fun u hu hfin => ?_⟩
      funext w
      have ef := congrFun (hAf u hu hfin) w
      unfold heisO at ef ⊢
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, ef]

theorem colV_congr (S : GridChoice W U) {t : T} {fs fs' : Vecs G t} (h : ∀ j, fs (.inl j) = fs' (.inl j))
    (x : ∀ j, FinPt G (.top j)) : colV S fs x = colV S fs' x := by
  have e : (fun j => if h : j < D.R.m then kkVec S (.top t j) (fs (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) =
      (fun j => if h : j < D.R.m then kkVec S (.top t j) (fs' (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) := by
    funext j; split_ifs with hj
    · rw [h]
    · rfl
  simp only [colV, e]

theorem rowV_congr (S : GridChoice W U) {t : T} {fs fs' : Vecs G t} (h : ∀ i, fs (.inr i) = fs' (.inr i))
    (y : ∀ i, FinPt G (.grid i D.R.m)) : rowV S fs y = rowV S fs' y := by
  have e : (fun i => if h : i < D.R.m then kkVec S (.chi i D.R.m) (fs (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) =
      (fun i => if h : i < D.R.m then kkVec S (.chi i D.R.m) (fs' (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) := by
    funext i; split_ifs with hi
    · rw [h]
    · rfl
  simp only [rowV, e]

theorem colK_update (S : GridChoice W U) {t : T} (fs : Vecs G t) (x : ∀ j, FinPt G (.top j)) (j₀ : Fin D.R.m)
    (F : WO (G.pS (arrP t (.inl j₀ : Arr D))) (G.pT (arrP t (.inl j₀ : Arr D))) → ℂ) :
    (fun j => if h : j < D.R.m then kkVec S (.top t j) (Function.update fs (.inl j₀) F (.inl ⟨j, h⟩)) (x j) (x (j + 1))
      else 0) =
    Function.update (fun j => if h : j < D.R.m then kkVec S (.top t j) (fs (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) j₀.1
      (kkVec S (.top t j₀.1) F (x j₀.1) (x (j₀.1 + 1))) := by
  funext j
  by_cases hj : j = j₀.1
  · subst hj
    rw [Function.update_self, dif_pos j₀.2]
    show kkVec S (.top t j₀.1) (Function.update fs (.inl j₀) F (.inl j₀)) _ _ = _
    rw [Function.update_self]
  · rw [Function.update_of_ne hj]
    split_ifs with h
    · rw [Function.update_of_ne]
      intro e; exact hj (congrArg Fin.val (Sum.inl_injective e))
    · rfl

end GlobalTheory.TopZeroInv

namespace GlobalTheory.TopZeroInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem rowK_update (S : GridChoice W U) {t : T} (fs : Vecs G t) (y : ∀ i, FinPt G (.grid i D.R.m)) (i₀ : Fin D.R.m)
    (F : WO (G.pS (arrP t (.inr i₀ : Arr D))) (G.pT (arrP t (.inr i₀ : Arr D))) → ℂ) :
    (fun i => if h : i < D.R.m then kkVec S (.chi i D.R.m) (Function.update fs (.inr i₀) F (.inr ⟨i, h⟩)) (y i) (y (i + 1))
      else 0) =
    Function.update (fun i => if h : i < D.R.m then kkVec S (.chi i D.R.m) (fs (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) i₀.1
      (kkVec S (.chi i₀.1 D.R.m) F (y i₀.1) (y (i₀.1 + 1))) := by
  funext i
  by_cases hi : i = i₀.1
  · subst hi
    rw [Function.update_self, dif_pos i₀.2]
    show kkVec S (.chi i₀.1 D.R.m) (Function.update fs (.inr i₀) F (.inr i₀)) _ _ = _
    rw [Function.update_self]
  · rw [Function.update_of_ne hi]
    split_ifs with h
    · rw [Function.update_of_ne]
      intro e; exact hi (congrArg Fin.val (Sum.inr_injective e))
    · rfl

theorem colV_update_add (S : GridChoice W U) {t : T} (fs : Vecs G t) (x : ∀ j, FinPt G (.top j)) (j₀ : Fin D.R.m)
    {F F' : WO (G.pS (arrP t (.inl j₀ : Arr D))) (G.pT (arrP t (.inl j₀ : Arr D))) → ℂ}
    (hF : IsThetaFunO W.ψ _ _ F) (hF' : IsThetaFunO W.ψ _ _ F') :
    colV S (Function.update fs (.inl j₀) (F + F')) x =
      colV S (Function.update fs (.inl j₀) F) x + colV S (Function.update fs (.inl j₀) F') x := by
  have h : kkVec S (.top t j₀.1) (F + F') (x j₀.1) (x (j₀.1 + 1)) =
      kkVec S (.top t j₀.1) F (x j₀.1) (x (j₀.1 + 1)) + kkVec S (.top t j₀.1) F' (x j₀.1) (x (j₀.1 + 1)) :=
    _root_.GlobalTheory.TopZeroInv.kkVec_add S (.top t j₀.1) hF hF' _ _
  rw [colV, colV, colV, colK_update, colK_update, colK_update, h, _root_.GlobalTheory.chainTo_update_add _ _ _ _ _ j₀.2, LinearMap.add_comp]

theorem colV_update_smul (S : GridChoice W U) {t : T} (fs : Vecs G t) (x : ∀ j, FinPt G (.top j)) (j₀ : Fin D.R.m) (c : ℂ)
    (F : WO (G.pS (arrP t (.inl j₀ : Arr D))) (G.pT (arrP t (.inl j₀ : Arr D))) → ℂ) :
    colV S (Function.update fs (.inl j₀) (c • F)) x = c • colV S (Function.update fs (.inl j₀) F) x := by
  have h : kkVec S (.top t j₀.1) (c • F) (x j₀.1) (x (j₀.1 + 1)) = c • kkVec S (.top t j₀.1) F (x j₀.1) (x (j₀.1 + 1)) :=
    _root_.GlobalTheory.TopZeroInv.kkVec_smul S (.top t j₀.1) c F _ _
  rw [colV, colV, colK_update, colK_update, h, GlobalTheory.T.linearMapChainComposite_update_smul _ _ _ _ _ j₀.2, LinearMap.smul_comp]

theorem rowV_update_add (S : GridChoice W U) {t : T} (fs : Vecs G t) (y : ∀ i, FinPt G (.grid i D.R.m)) (i₀ : Fin D.R.m)
    {F F' : WO (G.pS (arrP t (.inr i₀ : Arr D))) (G.pT (arrP t (.inr i₀ : Arr D))) → ℂ}
    (hF : IsThetaFunO W.ψ _ _ F) (hF' : IsThetaFunO W.ψ _ _ F') :
    rowV S (Function.update fs (.inr i₀) (F + F')) y =
      rowV S (Function.update fs (.inr i₀) F) y + rowV S (Function.update fs (.inr i₀) F') y := by
  have h : kkVec S (.chi i₀.1 D.R.m) (F + F') (y i₀.1) (y (i₀.1 + 1)) =
      kkVec S (.chi i₀.1 D.R.m) F (y i₀.1) (y (i₀.1 + 1)) + kkVec S (.chi i₀.1 D.R.m) F' (y i₀.1) (y (i₀.1 + 1)) :=
    _root_.GlobalTheory.TopZeroInv.kkVec_add S (.chi i₀.1 D.R.m) hF hF' _ _
  rw [rowV, rowV, rowV, rowK_update, rowK_update, rowK_update, h, _root_.GlobalTheory.chainTo_update_add _ _ _ _ _ i₀.2, LinearMap.add_comp]

theorem rowV_update_smul (S : GridChoice W U) {t : T} (fs : Vecs G t) (y : ∀ i, FinPt G (.grid i D.R.m)) (i₀ : Fin D.R.m)
    (c : ℂ) (F : WO (G.pS (arrP t (.inr i₀ : Arr D))) (G.pT (arrP t (.inr i₀ : Arr D))) → ℂ) :
    rowV S (Function.update fs (.inr i₀) (c • F)) y = c • rowV S (Function.update fs (.inr i₀) F) y := by
  have h : kkVec S (.chi i₀.1 D.R.m) (c • F) (y i₀.1) (y (i₀.1 + 1)) = c • kkVec S (.chi i₀.1 D.R.m) F (y i₀.1) (y (i₀.1 + 1)) :=
    _root_.GlobalTheory.TopZeroInv.kkVec_smul S (.chi i₀.1 D.R.m) c F _ _
  rw [rowV, rowV, rowK_update, rowK_update, h, GlobalTheory.T.linearMapChainComposite_update_smul _ _ _ _ _ i₀.2, LinearMap.smul_comp]

end GlobalTheory.TopZeroInv

namespace GlobalTheory.TopZeroInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem coe_update {t : T} (m : ∀ l : Arr D, thetaSub W (arrP t l)) (i : Arr D) (z : thetaSub W (arrP t i)) :
    (fun l => ((Function.update m i z l : thetaSub W (arrP t l)) : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) =
      Function.update (fun l => (m l : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) i (z : _ → ℂ) :=
  funext fun l => Function.apply_update (fun l (q : thetaSub W (arrP t l)) => (q : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) m i z l

theorem pairVec_apply (S : GridChoice W U) {t : T} (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (fs : Vecs G t)
    (v : VV ℂ (wt G (.top 0))) (w : VV ℂ (listedWt G (.grid 0 D.R.m))) :
    pairVec S x y fs v w =
      brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m)) (colV S fs x v) (rowV S fs y w) := rfl

def pairML (S : GridChoice W U) {t : T} (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m))
    (v : VV ℂ (wt G (.top 0))) (w : VV ℂ (listedWt G (.grid 0 D.R.m))) :
    (∀ l : Arr D, thetaSub W (arrP t l)) →ₘₗ[ℂ] ℂ where
  toFun fs := pairVec S (t := t) x y (fun l => ((fs l : thetaSub W (arrP t l)) : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) v w
  map_update_add' := by
    intro inst m i a b
    obtain rfl : inst = (by clear inst; infer_instance : DecidableEq (Arr D)) := Subsingleton.elim _ _
    simp only [coe_update, Submodule.coe_add]
    rcases i with j₀ | i₀
    · have hr : ∀ F, rowV S (Function.update (fun l => (m l : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) (.inl j₀) F) y =
          rowV S (fun l => (m l : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) y := fun F =>
        rowV_congr S (fun i => Function.update_of_ne (Sum.inr_ne_inl) _ _) y
      rw [pairVec_apply, pairVec_apply, pairVec_apply, hr, hr, hr, colV_update_add S _ x j₀ a.2 b.2, LinearMap.add_apply]
      exact LinearMap.map_add₂ _ _ _ _
    · have hc : ∀ F, colV S (Function.update (fun l => (m l : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) (.inr i₀) F) x =
          colV S (fun l => (m l : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) x := fun F =>
        colV_congr S (fun j => Function.update_of_ne (Sum.inl_ne_inr) _ _) x
      rw [pairVec_apply, pairVec_apply, pairVec_apply, hc, hc, hc, rowV_update_add S _ y i₀ a.2 b.2, LinearMap.add_apply]
      exact map_add _ _ _
  map_update_smul' := by
    intro inst m i c a
    obtain rfl : inst = (by clear inst; infer_instance : DecidableEq (Arr D)) := Subsingleton.elim _ _
    simp only [coe_update, Submodule.coe_smul, RingHom.id_apply]
    rcases i with j₀ | i₀
    · have hr : ∀ F, rowV S (Function.update (fun l => (m l : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) (.inl j₀) F) y =
          rowV S (fun l => (m l : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) y := fun F =>
        rowV_congr S (fun i => Function.update_of_ne (Sum.inr_ne_inl) _ _) y
      rw [pairVec_apply, pairVec_apply, hr, hr, colV_update_smul S _ x j₀, LinearMap.smul_apply]
      exact LinearMap.map_smul₂ _ _ _ _
    · have hc : ∀ F, colV S (Function.update (fun l => (m l : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) (.inr i₀) F) x =
          colV S (fun l => (m l : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) x := fun F =>
        colV_congr S (fun j => Function.update_of_ne (Sum.inl_ne_inr) _ _) x
      rw [pairVec_apply, pairVec_apply, hc, hc, rowV_update_smul S _ y i₀, LinearMap.smul_apply]
      exact map_smul _ _ _

end GlobalTheory.TopZeroInv

namespace GlobalTheory.TopZeroInv

theorem pairVec_sum_eq_of_prod_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T} {κ : Type} (a : κ →₀ ℂ) (f g : κ → Vecs G t)
    (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (v : VV ℂ (wt G (.top 0)))
    (w : VV ℂ (listedWt G (.grid 0 D.R.m))),
    (∀ c ∈ a.support, ∀ l, IsThetaFunO W.ψ _ _ (f c l)) → (∀ c ∈ a.support, ∀ l, IsThetaFunO W.ψ _ _ (g c l)) →
    (∀ z : ∀ l : Arr D, WO (G.pS (arrP t l)) (G.pT (arrP t l)),
      (a.sum fun c b => b * ∏ l, f c l (z l)) = a.sum fun c b => b * ∏ l, g c l (z l)) →
    (a.sum fun c b => b * pairVec S x y (f c) v w) = a.sum fun c b => b * pairVec S x y (g c) v w := by
  intro D T L sc G W U S t κ a f g x y v w hf hg hprod
  classical
  let f' : κ → ∀ l : Arr D, thetaSub W (arrP t l) := fun c l => if h : c ∈ a.support then ⟨f c l, hf c h l⟩ else 0
  let g' : κ → ∀ l : Arr D, thetaSub W (arrP t l) := fun c l => if h : c ∈ a.support then ⟨g c l, hg c h l⟩ else 0
  have ef : ∀ c ∈ a.support, ∀ l, ((f' c l : thetaSub W (arrP t l)) : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ) = f c l :=
    fun c h l => by simp only [f', dif_pos h]
  have eg : ∀ c ∈ a.support, ∀ l, ((g' c l : thetaSub W (arrP t l)) : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ) = g c l :=
    fun c h l => by simp only [g', dif_pos h]
  have key := GlobalTheory.T.multilinearMap_sum_eq_of_sum_prod_eval_eq (fun l : Arr D => thetaSub W (arrP t l)) (pairML S x y v w) a f' g' (fun z => by
    have := hprod z
    unfold Finsupp.sum at this ⊢
    refine (Finset.sum_congr rfl fun c h => ?_).trans (this.trans (Finset.sum_congr rfl fun c h => ?_))
    · simp only [ef c h]
    · simp only [eg c h])
  unfold Finsupp.sum at key ⊢
  refine (Finset.sum_congr rfl fun c h => ?_).trans (key.trans (Finset.sum_congr rfl fun c h => ?_))
  · change _ = _ * pairVec S (t := t) x y (fun l => ((f' c l : thetaSub W (arrP t l)) : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) v w
    rw [funext (ef c h)]
  · change _ * pairVec S (t := t) x y (fun l => ((g' c l : thetaSub W (arrP t l)) : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) v w = _
    rw [funext (eg c h)]

end GlobalTheory.TopZeroInv
end
end

