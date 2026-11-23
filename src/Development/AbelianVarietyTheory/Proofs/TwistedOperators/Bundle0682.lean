module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0446
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0460
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0451
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0508
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0677
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0465
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0455
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0676
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0484

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProdExpansionFunctionsRowVertexInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowVertexInv
open GlobalTheory.SplitFlip

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

abbrev movPt (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) :
    ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)) :=
  Function.update (Function.update z (.inr ⟨j, by omega⟩)
    (actO _ _ (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.1 (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.2
      (z (.inr ⟨j, by omega⟩)) : WO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T))))
    (.inr ⟨j + 1, hj⟩) (actO _ _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.1
      (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.2 (z (.inr ⟨j + 1, hj⟩)) :
      WO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T)))

theorem movPt_two (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) :
    movPt S j hj k z (.inr ⟨j + 1, hj⟩) = actO _ _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.1
      (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.2 (z (.inr ⟨j + 1, hj⟩)) :=
  Function.update_self _ _ _

theorem movPt_one (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) :
    movPt S j hj k z (.inr ⟨j, by omega⟩) = actO _ _ (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.1
      (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.2 (z (.inr ⟨j, by omega⟩)) :=
  (Function.update_of_ne (by simp) _ _).trans (Function.update_self _ _ _)

theorem movPt_other (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) (a : Fin D.R.m ⊕ Fin D.R.m)
    (h1 : a ≠ .inr ⟨j, by omega⟩) (h2 : a ≠ .inr ⟨j + 1, hj⟩) : movPt S j hj k z a = z a :=
  (Function.update_of_ne h2 _ _).trans (Function.update_of_ne h1 _ _)

theorem movFn_two (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (v : ∀ a, FactorFn G t a) (x : WO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T))) :
    movFn S j hj k v (.inr ⟨j + 1, hj⟩) x = v (.inr ⟨j + 1, hj⟩) (actO _ _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.1
      (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.2 x) := by
  unfold movFn; rw [Function.update_self]

theorem movFn_one (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (v : ∀ a, FactorFn G t a) (x : WO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T))) :
    movFn S j hj k v (.inr ⟨j, by omega⟩) x = v (.inr ⟨j, by omega⟩) (actO _ _ (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.1
      (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.2 x) := by
  unfold movFn; rw [Function.update_of_ne (by simp), Function.update_self]

theorem movFn_other (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (v : ∀ a, FactorFn G t a) (a : Fin D.R.m ⊕ Fin D.R.m)
    (h1 : a ≠ .inr ⟨j, by omega⟩) (h2 : a ≠ .inr ⟨j + 1, hj⟩) : movFn S j hj k v a = v a := by
  unfold movFn; rw [Function.update_of_ne h2, Function.update_of_ne h1]

theorem scale_movFn_apply (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (c₁ c₂ : ℂ) (v : ∀ a, FactorFn G t a) (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)))
    (a : Fin D.R.m ⊕ Fin D.R.m) :
    (scaleAt j hj c₁ c₂ a • movFn S j hj k v a) (z a) =
      ((Pi.mulSingle (.inr ⟨j, by omega⟩ : Fin D.R.m ⊕ Fin D.R.m) c₁ : Fin D.R.m ⊕ Fin D.R.m → ℂ) a *
        (Pi.mulSingle (.inr ⟨j + 1, hj⟩ : Fin D.R.m ⊕ Fin D.R.m) c₂ : Fin D.R.m ⊕ Fin D.R.m → ℂ) a) *
        v a (movPt S j hj k z a) := by
  have hne : (.inr ⟨j, by omega⟩ : Fin D.R.m ⊕ Fin D.R.m) ≠ .inr ⟨j + 1, hj⟩ := by simp
  by_cases h2' : a = .inr ⟨j + 1, hj⟩
  · subst h2'
    have e1 : movFn S j hj k v (.inr ⟨j + 1, hj⟩) (z (.inr ⟨j + 1, hj⟩)) =
        v (.inr ⟨j + 1, hj⟩) (movPt S j hj k z (.inr ⟨j + 1, hj⟩)) :=
      (movFn_two S j hj k v (z (.inr ⟨j + 1, hj⟩))).trans (congrArg (v _) (movPt_two S j hj k z).symm)
    rw [Pi.smul_apply, smul_eq_mul, e1]
    simp [scaleAt, Pi.mulSingle_apply, hne.symm]
  · by_cases h1' : a = .inr ⟨j, by omega⟩
    · subst h1'
      have e1 : movFn S j hj k v (.inr ⟨j, by omega⟩) (z (.inr ⟨j, by omega⟩)) =
          v (.inr ⟨j, by omega⟩) (movPt S j hj k z (.inr ⟨j, by omega⟩)) :=
        (movFn_one S j hj k v (z (.inr ⟨j, by omega⟩))).trans (congrArg (v _) (movPt_one S j hj k z).symm)
      rw [Pi.smul_apply, smul_eq_mul, e1]
      simp [scaleAt, Pi.mulSingle_apply, hne, Function.update_of_ne hne]
    · rw [Pi.smul_apply, smul_eq_mul, movFn_other S j hj k v a h1' h2', movPt_other S j hj k z a h1' h2']
      simp [scaleAt, Pi.mulSingle_apply, h1', h2', Function.update_of_ne h1', Function.update_of_ne h2']

end GlobalTheory.RowVertexInv

namespace GlobalTheory.RowVertexInv
open GlobalTheory.SplitFlip

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem prod_scale_movFn (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (c₁ c₂ : ℂ) (v : ∀ a, FactorFn G t a) (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) :
    ∏ a, (scaleAt j hj c₁ c₂ a • movFn S j hj k v a) (z a) = c₁ * c₂ * ∏ a, v a (movPt S j hj k z a) := by
  rw [Finset.prod_congr rfl fun a _ => scale_movFn_apply S j hj k c₁ c₂ v z a, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle', Fintype.prod_pi_mulSingle']

theorem isHalf_movPt (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) (e : AE D) (a : Fin D.R.m ⊕ Fin D.R.m) :
    IsHalf e (movPt S j hj k z a) ↔ IsHalf e (z a) := by
  by_cases h2' : a = .inr ⟨j + 1, hj⟩
  · subst h2'
    rw [movPt_two]
    exact GlobalTheory.SchrMove.isHalf_actO_iff _ _ _
  · by_cases h1' : a = .inr ⟨j, by omega⟩
    · subst h1'
      rw [movPt_one]
      exact GlobalTheory.SchrMove.isHalf_actO_iff _ _ _
    · rw [movPt_other S j hj k z a h1' h2']

theorem sum_fn_eq_zero {t : T} (τ : PureDat G t →₀ ℂ) (e : AE D)
    (hsupp : ∀ d ∈ τ.support, (∀ j, (d.1 j).P = locPl G t ∧ (d.1 j).e = e ∧ (d.1 j).z = 1) ∧
      ∀ i, (d.2 i).P = locPl G t ∧ (d.2 i).e = e ∧ (d.2 i).z = 1)
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) (a : Fin D.R.m ⊕ Fin D.R.m)
    (ha : ¬ IsHalf e (z a)) : (τ.sum fun d c => c * ∏ a, fnOf d a (z a)) = 0 := by
  unfold Finsupp.sum
  refine Finset.sum_eq_zero fun d hd => ?_
  beta_reduce
  rw [Finset.prod_eq_zero (Finset.mem_univ a), mul_zero]
  rcases a with j | i
  · by_contra hne
    have h := (d.1 j).sb.1 _ hne
    rw [((hsupp d hd).1 j).2.1] at h
    exact ha h
  · by_contra hne
    have h := (d.2 i).sb.1 _ hne
    rw [((hsupp d hd).2 i).2.1] at h
    exact ha h

theorem sum_fn_of_half (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} (τ : PureDat G t →₀ ℂ) (e : AE D)
    (hexp : ∀ (x : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
      (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))), (∀ j, IsHalf e (x j)) →
      (∀ i, IsHalf e (y i)) → (τ.sum fun d c => c * (∏ j, (d.1 j).fn (x j)) * ∏ i, (d.2 i).fn (y i)) =
        ∏ w, (S.term t Φ β w).datum (S.colAt t w x) (S.rowAt t w y))
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) (h : ∀ a, IsHalf e (z a)) :
    (τ.sum fun d c => c * ∏ a, fnOf d a (z a)) =
      ∏ w, (S.term t Φ β w).datum (S.colAt t w fun j => z (.inl j)) (S.rowAt t w fun i => z (.inr i)) := by
  rw [← hexp (fun j => z (.inl j)) (fun i => z (.inr i)) (fun j => h _) (fun i => h _)]
  refine Finsupp.sum_congr fun d _ => ?_
  rw [Fintype.prod_sum_type, mul_assoc]
  rfl

end GlobalTheory.RowVertexInv

namespace GlobalTheory.RowVertexInv
open GlobalTheory.SplitFlip

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem inl_movPt (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) :
    (fun i => movPt S j hj k z (.inl i)) = fun i => z (.inl i) :=
  funext fun i => movPt_other S j hj k z _ (by simp) (by simp)

theorem inr_movPt (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) :
    (fun i => movPt S j hj k z (.inr i)) = Function.update (Function.update (fun i => z (.inr i)) ⟨j, by omega⟩
        (actO _ _ (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.1 (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.2
          (z (.inr ⟨j, by omega⟩)) : WO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T))))
      ⟨j + 1, hj⟩ (actO _ _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.1
          (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.2 (z (.inr ⟨j + 1, hj⟩)) :
          WO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T))) := by
  funext i
  let B : Fin D.R.m → Type := fun i => WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))
  have hne : (⟨j, by omega⟩ : Fin D.R.m) ≠ ⟨j + 1, hj⟩ := by simp
  by_cases h2' : i = ⟨j + 1, hj⟩
  · subst h2'
    exact (movPt_two S j hj k z).trans (Function.update_self (β := B) (⟨j + 1, hj⟩ : Fin D.R.m) _ _).symm
  · by_cases h1' : i = ⟨j, by omega⟩
    · subst h1'
      exact (movPt_one S j hj k z).trans ((Function.update_of_ne (β := B) hne _ _).trans (Function.update_self (β := B) _ _ _)).symm
    · refine (movPt_other S j hj k z _ (fun h => h1' (Sum.inr_injective h)) (fun h => h2' (Sum.inr_injective h))).trans ?_
      symm
      refine (Function.update_of_ne (β := B) (a := i) h2' _ _).trans ?_
      exact Function.update_of_ne (β := B) (a := i) h1' _ _

theorem local_prod (S : GridChoice W U) {t : T} {Φ : G.Datum} (β : CosFam G t) {μ₀ : T} (hμ : L.Is μ₀)
    (hq : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) (hU : t ∈ U) (j : ℕ) (hj : j + 1 < D.R.m)
    (k : FinPt G (.grid (j + 1) D.R.m)) (hk : finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le) (c₁ c₂ : ℂ)
    (h1 : W.om (.chi j D.R.m) (G.toPair (.chi j D.R.m) 1 (moved S j k)) (S.Z.vac (.chi j D.R.m)) = c₁ • S.Z.vac (.chi j D.R.m))
    (h2 : W.om (.chi (j + 1) D.R.m) (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1) (S.Z.vac (.chi (j + 1) D.R.m)) =
      c₂ • S.Z.vac (.chi (j + 1) D.R.m))
    (x : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
    (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) :
    c₁ * c₂ * ∏ w, (S.term t Φ β w).datum (S.colAt t w x) (S.rowAt t w (Function.update (Function.update y ⟨j, by omega⟩
        (actO _ _ (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.1 (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.2
          (y ⟨j, by omega⟩) : WO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T))))
      ⟨j + 1, hj⟩ (actO _ _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.1
          (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.2 (y ⟨j + 1, hj⟩) :
          WO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T))))) =
      ∏ w, (S.term t Φ β w).datum (S.colAt t w x) (S.rowAt t w y) := by
  have hκ : ∀ w : locPl G t, inBasis (rank_vertex G t w.1 (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w.1
      (finG (G.V (.grid (j + 1) D.R.m)) k) ∈ givenLevel G t w.1 (j + 1, D.R.m) := fun w =>
    Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hk).1 w
  rw [GlobalTheory.T.vacuum_scalars_eq_product_edge_factors_row S hμ hU j hj k hk c₁ c₂ h1 h2, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [GlobalTheory.RowMoveAt.rowAt_move S hU j hj k w.1 w.2 y]
  exact _root_.GlobalTheory.FlatRowMove.term_datum_move S β hμ hq hc hU w j hj _ (hκ w) _ _

end GlobalTheory.RowVertexInv

namespace GlobalTheory.RowVertexInv

theorem sum_prod_scale_movFn_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ → (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)), finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ c₁ c₂ : ℂ, W.om (.chi j D.R.m) (G.toPair (.chi j D.R.m) 1 (moved S j k)) (S.Z.vac (.chi j D.R.m)) = c₁ • S.Z.vac (.chi j D.R.m) → W.om (.chi (j + 1) D.R.m) (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1) (S.Z.vac (.chi (j + 1) D.R.m)) = c₂ • S.Z.vac (.chi (j + 1) D.R.m) → ∀ z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)), (τ.sum fun d c => c * ∏ a, (scaleAt j hj c₁ c₂ a • movFn S j hj k (fnOf d) a) (z a)) = τ.sum fun d c => c * ∏ a, fnOf d a (z a) := by
  intro D T L sc G W U S t Φ β τ μ₀ hμ hq hc hU hβ hE hv j hj k hk c₁ c₂ h1 h2 z
  obtain ⟨e, -, hsupp, hexp⟩ := hE
  have hL : (τ.sum fun d c => c * ∏ a, (scaleAt j hj c₁ c₂ a • movFn S j hj k (fnOf d) a) (z a)) =
      c₁ * c₂ * τ.sum fun d c => c * ∏ a, fnOf d a (movPt S j hj k z a) := by
    rw [Finsupp.mul_sum]
    refine Finsupp.sum_congr fun d _ => ?_
    rw [prod_scale_movFn]
    ring
  rw [hL]
  by_cases hall : ∀ a, IsHalf e (z a)
  · rw [sum_fn_of_half S τ e hexp z hall,
      sum_fn_of_half S τ e hexp _ fun a => (isHalf_movPt S j hj k z e a).2 (hall a), inl_movPt, inr_movPt]
    exact local_prod S β hμ hq hc hU j hj k hk c₁ c₂ h1 h2 (fun i => z (.inl i)) (fun i => z (.inr i))
  · push_neg at hall
    obtain ⟨a, ha⟩ := hall
    rw [sum_fn_eq_zero τ e hsupp z a ha,
      sum_fn_eq_zero τ e hsupp _ a (fun h => ha ((isHalf_movPt S j hj k z e a).1 h)), mul_zero]

end GlobalTheory.RowVertexInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedVacuaAreRealDatumLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped TensorProduct
namespace GlobalTheory.VacRealPf

variable {D : D7}

theorem mem_GfC_of_idemSum {e : AE D} {Q : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e Q) {V : HSp D} {g : GA D V}
    (hs : SuppAt e V g) : g ∈ GfC V := by
  have h0 : infPart D (e + cA D e) = 0 := by
    have h1 := GlobalTheory.FinRestComm.infPart_of_idemSum he
    rw [RingHom.map_add (f := _), h1, GlobalTheory.AdjointPair.infPart_zero e h1, add_zero]
  show g ∈ (infHom V).ker
  rw [MonoidHom.mem_ker]
  apply Units.ext
  ext i j
  have h1 := congrArg (infPart D) (hs i j)
  rw [map_mul, h0, zero_mul] at h1
  have e : (infHom V g).1 i j = infPart D (mt V g i j) := rfl
  change (infHom V g).1 i j = (1 : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)).1 i j
  rw [e, Units.val_one]
  have h2 : infPart D ((mt V g - 1) i j) = infPart D (mt V g i j) - (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j := by
    rw [Matrix.sub_apply, RingHom.map_sub]
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, RingHom.map_zero]
  rw [h2] at h1
  exact sub_eq_zero.1 h1.symm

theorem moves_one (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (P : GlobalTheory.FinPl.Pl D → Prop) : GlobalTheory.FinPl.Moves S 1 L L P := by
  intro y _
  rw [show mt S 1 = 1 from rfl, Matrix.one_mulVec]

theorem mem_idx {j : ℕ} : j ∈ idx D ↔ 1 ≤ j ∧ j + 2 ≤ D.R.m := by
  have := D.R.two_le_m
  simp only [idx, List.mem_range'_1]
  omega

section
variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

theorem base_fin {t : T} {b : Pts ch.G} (hb : IsBase t ch.S.B b) (j : ℕ) : b j ∈ GfC _ := by
  by_cases h0 : j = 0
  · subst h0
    obtain ⟨e, he, hs, -⟩ := hb.1
    exact mem_GfC_of_idemSum he hs
  · by_cases hj : j ∈ idx D
    · obtain ⟨δ, -, hδ⟩ := hb.2.1 j hj
      exact hδ.1
    · rw [hb.2.2 j h0 hj]; exact one_mem _

theorem sd_grid (j : ℕ) (hj : j ≤ D.R.m) : IsSelfDualC _ (ch.G.Λ (.grid D.R.m j)) :=
  (ch.G.isV (X := .grid D.R.m j) ⟨le_rfl, hj⟩ fun i e => by
    have := D.R.two_le_m
    injection e with e1
    omega).sd

theorem sd_top (j : ℕ) (hj : j ≤ D.R.m) : IsSelfDualC _ (ch.G.Λ (.top j)) :=
  (ch.G.isV (X := .top j) hj fun i e => by cases e).sd

theorem fock_vac (t : T) (j : ℕ) (hj : j < D.R.m) (P : PolDown ch.G) {M : GlobalTheory.FinPl.Lat (ch.G.V (.grid D.R.m j))}
    {M' : GlobalTheory.FinPl.Lat (ch.G.V (.grid D.R.m (j + 1)))} (hM : IsSelfDualC _ M) (hM' : IsSelfDualC _ M')
    {g : GA D (ch.G.V (.grid D.R.m j))} {h : GA D (ch.G.V (.grid D.R.m (j + 1)))} (hg : g ∈ GfC _) (hh : h ∈ GfC _)
    (mg : GlobalTheory.FinPl.Moves _ g (ch.G.Λ (.grid D.R.m j)) M fun _ => True)
    (mh : GlobalTheory.FinPl.Moves _ h (ch.G.Λ (.grid D.R.m (j + 1))) M' fun _ => True)
    {x : GA D (ch.G.V (.grid D.R.m j))} {y : GA D (ch.G.V (.grid D.R.m (j + 1)))} (hx : x ∈ GinfC _) (hy : y ∈ GinfC _) :
    GlobalTheory.FinPl.Vac ch.W.ψ (ch.G.V (.grid D.R.m j)) (ch.G.V (.grid D.R.m (j + 1))) M M' (fun _ => True)
      (ch.W.om (.mu t D.R.m j) (x * g, y * h) (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P ⟨j, hj⟩)) :=
  (GlobalTheory.StepMove.gen (ch.W.om_is (.mu t D.R.m j) ⟨le_rfl, hj⟩) (sd_grid ch j hj.le) hM (sd_grid ch (j + 1) hj) hM' hg hh mg mh _ _
    (ch.rm.vT_is t D.R.m j le_rfl hj)).1 _ x hx y hy

theorem real_of {ψ : AddChar (AF D.host.F) ℂ} {X S X' : HSp D} {LA : GlobalTheory.FinPl.Lat X} {LS : GlobalTheory.FinPl.Lat S}
    {LA' : GlobalTheory.FinPl.Lat X'} {C : WO X S → WO S X' → ℂ} (h : IsBiTheta ψ X S X' C)
    (h' : GlobalTheory.FinPl.BiVacAt ψ LA LS LA' (fun _ => True) C) :
    IsBiVac ψ X S X' (LA : Set _) (LS : Set _) (LA' : Set _) C ∧ IsBiSmooth C :=
  ⟨⟨h.cont, h'.1, h'.2⟩, h.smooth⟩

theorem vac_cast {V : HSp D} {LV : GlobalTheory.FinPl.Lat V} {n n' : ℕ} (h : n = n') {f : WO V (ch.G.V (.grid D.R.m n)) → ℂ}
    (hf : GlobalTheory.FinPl.Vac ch.W.ψ V _ LV (ch.G.Λ (.grid D.R.m n)) (fun _ => True) f) :
    GlobalTheory.FinPl.Vac ch.W.ψ V _ LV (ch.G.Λ (.grid D.R.m n')) (fun _ => True) (castSch ch.G h f) := by
  subst h
  exact hf

theorem orth_cast {LZ : GlobalTheory.FinPl.Lat (pLine D)} {v : GlobalTheory.FinPl.Pl D}
    (hor : GlobalTheory.FinPl.OrthAt (topOrth ch.G) (ch.G.Λ (.top D.R.m)) (ch.G.Λ (.grid D.R.m D.R.m)) LZ v) {n : ℕ} (h : D.R.m = n) :
    GlobalTheory.FinPl.OrthAt (topOrthAt ch.G h) (ch.G.Λ (.top n)) (ch.G.Λ (.grid D.R.m D.R.m)) LZ v := by
  subst h
  exact hor

theorem vacReal_of_shape (hsh : ShapeAt ch) : VacReal ch := by
  obtain ⟨N, N₀, LL, LZ, hmv, hLZ, hor, hall⟩ := hsh
  intro t M hM b hb P p hp j hje hjm
  have hm2 := D.R.two_le_m
  obtain ⟨a, ha⟩ := D.R.m_even
  obtain ⟨c, hc⟩ := hje
  have hψ : IsStdChar D ch.W.ψ (-1) := ch.W.ψ_std
  obtain ⟨x₀⟩ := GlobalTheory.SeeSaw.VacShape.nonempty_pl D
  have hFV := _root_.GlobalTheory.FinPl.FlatVacuum.flatVac D ch.W.ψ (fun _ => True)
  have hbf := base_fin ch hb
  have hpi : ∀ k, p k ∈ GinfC _ := hp.1
  unfold conAt
  by_cases h0 : j + 2 * 0 + 2 = D.R.m
  · rw [dite_eq_left h0]
    have hb1 : b (j + 1) = 1 := hb.2.2 (j + 1) (by omega) fun h => by
      have := (mem_idx.1 h).2
      omega
    have hs := hall t M hM j 0 h0 (GlobalTheory.Unf.Inhab.nonempty_volN _).some
    have hg0 := (hs x₀).2.2.1
    have hmv1 := hmv t b hb (j + 1) (by omega)
    rw [hb1] at hmv1
    have v₁ := fock_vac ch t j (by omega) P (M := N j) (M' := N (j + 1)) hg0.sdV hg0.sdW (hbf j) (one_mem _)
      (hmv t b hb j (by omega)) hmv1 (hpi j) (one_mem _)
    rw [one_mul] at v₁
    have v₂ := fock_vac ch t (j + 1) (by omega) P (M := N (j + 1)) (M' := ch.G.Λ (.grid D.R.m (j + 1 + 1))) hg0.sdW
      (sd_grid ch _ (by omega)) (one_mem _) (one_mem _) hmv1 (moves_one _ _ _) (one_mem _) (one_mem _)
    rw [one_mul, one_mul, Prod.mk_one_one, map_one, Module.End.one_apply] at v₂
    have v₃ := vac_cast ch (show j + 1 + 1 = D.R.m by omega) v₂
    have f₁ := hFV.1 0 _ _ (lastAt ch.G ch.W t hM j h0 (GlobalTheory.Unf.Inhab.nonempty_volN _).some).s (N j) (N₀ j) (N (j + 1))
      (ch.G.Λ (.top (j + 1))) (fun x _ => (hs x).2.2.1) _ v₁
    have f₂ := hFV.2.2 _ _ _ (rowJac ch.G (j + 1) (by omega) 0 (by omega)) (N (j + 1)) (ch.G.Λ (.top (j + 1)))
      (ch.G.Λ (.grid D.R.m D.R.m)) hg0.sdW hg0.sdW₀ (sd_grid ch _ le_rfl) (fun x _ => (hs x).2.2.1.monoW) _ v₃
    refine real_of ?_ ?_
    · exact GlobalTheory.LastBiTheta.isBiTheta_lastBi D _ hψ _ _ _ _ _ _ _ _ _ _ GlobalTheory.RowChain.LastSeeSawStep.lastTau_gram _ _ f₁.1 f₂.1
    · exact _root_.GlobalTheory.LastVacPf.lastVac D _ hψ _ _ _ _ _ _ _ _ _ _ rfl rfl GlobalTheory.RowChain.LastSeeSawStep.lastTau_gram (fun _ => True) (N₀ j)
        (ch.G.Λ (.top j)) (ch.G.Λ (.top (j + 1))) (ch.G.Λ (.top (j + 1 + 1))) (ch.G.Λ (.grid D.R.m D.R.m)) hg0.sdV₀
        (sd_top ch _ (by omega)) hg0.sdW₀ (sd_top ch _ (by omega)) (sd_grid ch _ le_rfl)
        (fun x _ => ⟨(hs x).2.2.1.tame, LL j, LZ, (hs x).1, hLZ, (hs x).2.1, orth_cast ch (hor x) _, (hs x).2.2.2.2.1 rfl⟩)
        _ _ f₁ f₂
  · have h1 : j + 2 * ((D.R.m - 4 - j) / 2 + 1) + 2 = D.R.m := by omega
    rw [dite_eq_right h0]
    erw [dite_eq_left h1]
    have hs := hall t M hM j _ h1 (GlobalTheory.Unf.Inhab.nonempty_volN _).some
    have hs' := hall t M hM (j + 1 + 1) ((D.R.m - 4 - j) / 2) (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some
    have had := fun x => (hs' x).2.2.2.1 (j + 1) rfl (by omega)
    have hg0 := (hs x₀).2.2.1
    have hg1 := had x₀
    have v₁ := fock_vac ch t j (by omega) P (M := N j) (M' := N (j + 1)) hg0.sdV hg0.sdW (hbf j) (hbf (j + 1))
      (hmv t b hb j (by omega)) (hmv t b hb (j + 1) (by omega)) (hpi j) (hpi (j + 1))
    have v₂ := fock_vac ch t (j + 1) (by omega) P (M := N (j + 1)) (M' := N (j + 1 + 1)) hg0.sdW hg1.sdW (hbf (j + 1))
      (hbf (j + 1 + 1)) (hmv t b hb (j + 1) (by omega)) (hmv t b hb (j + 1 + 1) (by omega)) (hpi (j + 1)) (hpi (j + 1 + 1))
    have f₁ := hFV.1 _ (besAt ch.G hM j _ h1 (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
      (jacAt ch.G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega)) (stepAt ch.G ch.W t hM j (by omega) (besDecAt ch.G j _ h1)
      (rowJac ch.G (j + 1) (by omega) ((D.R.m - 4 - j) / 2 + 1) (by omega))) (N j) (N₀ j) (N (j + 1))
      (ch.G.Λ (.top (j + 1))) (fun x _ => (hs x).2.2.1) _ v₁
    have f₂ := hFV.2.1 _ (jacAt ch.G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega))
      (besAt ch.G hM (j + 1 + 1) ((D.R.m - 4 - j) / 2) (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some) (stepAt ch.G ch.W t hM (j + 1) (by omega)
      (rowJac ch.G (j + 1) (by omega) ((D.R.m - 4 - j) / 2 + 1) (by omega))
      (besDecAt ch.G (j + 1 + 1) ((D.R.m - 4 - j) / 2) (by omega))) (N (j + 1)) (ch.G.Λ (.top (j + 1))) (N (j + 1 + 1))
      (N₀ (j + 1 + 1)) (fun x _ => had x) _ v₂
    have hCC := _root_.GlobalTheory.ContrComb.contr_comb_main D _ hψ _ _ _ _
      (linkAt hM j _ h1 (GlobalTheory.Unf.Inhab.nonempty_volN _).some (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
      (ch.G.V (.top (j + 1))) ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some) _ _ f₁.1 f₂.1
    exact real_of hCC.1 (hCC.2.2 (fun _ => True) (ch.G.Λ (.top j)) (ch.G.Λ (.top (j + 1))) (ch.G.Λ (.top (j + 1 + 1)))
      (N₀ j) (N₀ (j + 1 + 1)) (sd_top ch _ (by omega)) hg0.sdW₀ (sd_top ch _ (by omega)) hg0.sdV₀ hg1.sdW₀
      (fun x _ => ⟨⟨_, (hs x).2.1⟩, ⟨_, (hs' x).2.1⟩⟩) f₁ f₂)

end

theorem vacReal : Big fun ch => VacReal ch := by
  refine GlobalTheory.RowReal.big_mono ?_ _root_.GlobalTheory.RowShape.shapeAt_big
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch hsh
  exact vacReal_of_shape ch hsh

end GlobalTheory.VacRealPf
end
end

