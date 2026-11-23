module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0643
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0312
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0394
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0613
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0409
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0553
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0629
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0450

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastTwoStepsLocalModelExtendByZeroTopStep
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.LastStepExt0

theorem model_last : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (hChr : ChrP ch) (hArr : ArrP ch) (hJac : JacP ch)
    (t : T) (w : Pl D.host.E) (hw : w ∈ locPl ch.G t) (p : Place D (Kw w)) (hp : IsPlc w p)
    (β : Cosets (G := locGrid ch.G t w) one_le_sLen (givenLevel ch.G t w))
    (M : Vol ch.G) (hM : M.Is t) (φ : EdgeDat ch t w) (v f : SchDown ch.G t)
    (hvf : ∀ j : Fin D.R.m, IsArrVec ch t w p.e φ j j.2 (v j) (f j))
    (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m)
    (h₃ : (locGrid ch.G t w).rank (D.R.m, j + 1 + 1) = (locGrid ch.G t w).rank (D.R.m, D.R.m))
    (h₄ : (locGrid ch.G t w).rank (D.R.m, j + 1) = topRank (locGrid ch.G t w) (j + 1)),
    ∃ T₂ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m))) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)) →ₗ[ℂ]
        (WO (ch.G.V (.top (j + 1))) (ch.G.V (.grid D.R.m D.R.m)) → ℂ),
      p.IsModel ch.W.ψ (frTop ch.S.toGridChoice t w (j + 1) (by omega)) (frRow ch.S.B t w D.R.m le_rfl) T₂ ∧
      (∀ O, IsOne O → T₂ O = fun x => castSch ch.G (show j + 1 + 1 = D.R.m by omega) (v ⟨j + 1, by omega⟩)
        ((rowJac ch.G (j + 1) (by omega) 0 (by omega)).ext0 _ x)) ∧
      ∃ Φ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m))) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)),
        (∀ z, Φ.1 z = phiM (locGrid ch.G t w) (epsV ch.G t w * (repsAt ch.G t w).elt β) ((repsAt ch.G t w).elt β) φ
          (.theta D.R.m (j + 1)) (z.submatrix (Fin.cast h₃) (Fin.cast h₄))ᵀ) ∧
        T₂ Φ = fun x => castSch ch.G (show j + 1 + 1 = D.R.m by omega) (f ⟨j + 1, by omega⟩)
          ((rowJac ch.G (j + 1) (by omega) 0 (by omega)).ext0 _ x) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch hChr hArr hJac t w hw p hp β M hM φ v f hvf j hj h₃ h₄
  suffices key : ∀ (n : ℕ) (hn : j + 1 + 1 = n) (hnm : n ≤ D.R.m)
      (h₃' : (locGrid ch.G t w).rank (D.R.m, j + 1 + 1) = (locGrid ch.G t w).rank (D.R.m, n)),
      ∃ T₂ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, n))) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)) →ₗ[ℂ]
        (WO (ch.G.V (.top (j + 1))) (ch.G.V (.grid D.R.m n)) → ℂ),
      p.IsModel ch.W.ψ (frTop ch.S.toGridChoice t w (j + 1) (by omega)) (frRow ch.S.B t w n hnm) T₂ ∧
      (∀ O, IsOne O → T₂ O = fun x => castSch ch.G hn (v ⟨j + 1, by omega⟩)
        ((rowJac ch.G (j + 1) (by omega) 0 (by omega)).ext0 _ x)) ∧
      ∃ Φ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, n))) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)),
        (∀ z, Φ.1 z = phiM (locGrid ch.G t w) (epsV ch.G t w * (repsAt ch.G t w).elt β) ((repsAt ch.G t w).elt β) φ
          (.theta D.R.m (j + 1)) (z.submatrix (Fin.cast h₃') (Fin.cast h₄))ᵀ) ∧
        T₂ Φ = fun x => castSch ch.G hn (f ⟨j + 1, by omega⟩)
          ((rowJac ch.G (j + 1) (by omega) 0 (by omega)).ext0 _ x)
  · exact key D.R.m (by omega) le_rfl h₃
  intro n hn hnm h₃'
  subst hn
  have hj1 : j + 1 < D.R.m := by omega
  have hc : topRank (locGrid ch.G t w) (j + 1) + 0 = (locGrid ch.G t w).rank (D.R.m, j + 1) := by omega
  have hloc : ∀ i (hi : i ≤ D.R.m), D.R.m ≤ i + 1 →
      p.IsLoc (frRow ch.S.B t w i hi) 1 ((epsV ch.G t w * (repsAt ch.G t w).elt β) (D.R.m, i)) := by
    intro i hi hmi
    rw [Pi.mul_apply, epsV_eq_one t w hmi, elt_eq_one t w β hmi, mul_one]
    refine ⟨fun a b => by simp [Formalism.L2.Theta.mt], ?_⟩
    have : Formalism.L2.Theta.mt (ch.G.V (.grid D.R.m i)) 1 = 1 := by simp [Formalism.L2.Theta.mt]
    rw [this, Matrix.map_one p.π (map_zero _) (map_one _)]
    simp [(frRow ch.S.B t w i hi).βγ]
  obtain ⟨Tm, hTm, hOne, Φ, hΦ, hTΦ⟩ := hArr t w hw p hp φ (j + 1) hj1 (v ⟨j + 1, hj1⟩) (f ⟨j + 1, hj1⟩) (hvf ⟨j + 1, hj1⟩)
    (epsV ch.G t w) ((repsAt ch.G t w).elt β) (fun X => epsV_mem t w X) 1 1 1 1 (hloc (j + 1) hj1.le (by omega))
    (hloc (j + 1 + 1) hj1 (by omega)) (Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin 0)
    (Fin ((locGrid ch.G t w).rank (D.R.m, j + 1 + 1))) (frame hc) (Equiv.refl _)
  have hJ := hJac t w hw p hp M hM j 0 hj (GlobalTheory.Unf.Inhab.nonempty_volN (besDecAt ch.G j 0 hj)).some 1 (Or.inl ⟨rfl, rfl⟩) 0 hc
  have hFT : (mvFr p (1 : GA D (ch.G.V (.grid D.R.m (j + 1 + 1)))) (frRow ch.S.B t w (j + 1 + 1) hj1)
      (epsV ch.G t w (D.R.m, j + 1 + 1)) (Equiv.refl _)).β = (frRow ch.S.B t w (j + 1 + 1) hj1).β := by
    simp only [mvFr]
    rw [epsV_eq_one t w (by omega)]
    have : Formalism.L2.Theta.mt (ch.G.V (.grid D.R.m (j + 1 + 1))) 1 = 1 := by simp [Formalism.L2.Theta.mt]
    rw [this, Matrix.map_one p.π (map_zero _) (map_one _)]
    simp
  obtain ⟨Tm', hTm', hTT⟩ := Place.exists_isModel_chg D (Kw w) p _ _ _ _
    (mvFr p 1 (frRow ch.S.B t w (j + 1) hj1.le) (epsV ch.G t w (D.R.m, j + 1)) (frame hc))
    (mvFr p 1 (frRow ch.S.B t w (j + 1 + 1) hj1) (epsV ch.G t w (D.R.m, j + 1 + 1)) (Equiv.refl _)) _ _
    (mvFr p 1 (frRow ch.S.B t w (j + 1) hj1.le) (epsV ch.G t w (D.R.m, j + 1)) (frame hc))
    (frRow ch.S.B t w (j + 1 + 1) hj1) ch.W.ψ Tm hTm
  have hTT' : ∀ Ψ, Tm' Ψ = Tm Ψ := fun Ψ => hTT Ψ Ψ fun x => by
    rw [hFT, Frame.γβ, Frame.γβ, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨T₂, hT₂, hval⟩ := RankZeroSrc.localModel_rankZeroWitt_source_isModel D (Kw w) p ch.W.ψ ch.W.ψ_std (jacAt ch.G hM (j + 1) 0 (by omega)) _ _ _ _
    (frTop ch.S.toGridChoice t w (j + 1) (by omega)) _ hJ _ (frRow ch.S.B t w (j + 1 + 1) hj1) Tm' hTm'
  haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := Kw w) (n := Fin ((locGrid ch.G t w).rank (D.R.m, j + 1 + 1)))
    (n' := Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin 0)
  haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := Kw w) (n := Fin ((locGrid ch.G t w).rank (D.R.m, j + 1 + 1)))
    (n' := Fin (topRank (locGrid ch.G t w) (j + 1)))
  have hc1 : Continuous fun x : Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, j + 1 + 1)))
      (Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin 0) (Kw w) => x.toCols₁ :=
    continuous_pi fun i => continuous_pi fun j => (continuous_apply (Sum.inl j)).comp (continuous_apply i)
  have hc2 : Continuous fun x : Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, j + 1 + 1)))
      (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w) =>
        (fromCols x 0 : Matrix _ (Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin 0) (Kw w)) :=
    continuous_pi fun i => continuous_pi fun j => by
      rcases j with j | j
      · exact (continuous_apply j).comp (continuous_apply i)
      · exact j.elim0
  refine ⟨T₂, hT₂, fun O hO => ?_, ?_⟩
  · let O' : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, j + 1 + 1)))
        (Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin 0) (Kw w)) :=
      ⟨fun x => O.1 x.toCols₁, GlobalTheory.FinPl.Comm.comp_mem_SB O.2 hc1 hc2 RankZeroSrc.fromCols_toCols₁⟩
    have hO' : IsOne O' := by
      funext x
      show O.1 x.toCols₁ = _
      rw [hO]
      by_cases h2 : ∀ r q, x r q ∈ 𝒪[Kw w]
      · rw [Set.indicator_of_mem (s := {x : Matrix _ _ (Kw w) | ∀ r q, x r q ∈ 𝒪[Kw w]}) (a := x.toCols₁) (fun r q => h2 r (Sum.inl q)),
          Set.indicator_of_mem (s := {x : Matrix _ _ (Kw w) | ∀ r q, x r q ∈ 𝒪[Kw w]}) h2]
      · rw [Set.indicator_of_notMem (s := {x : Matrix _ _ (Kw w) | ∀ r q, x r q ∈ 𝒪[Kw w]}) h2, Set.indicator_of_notMem (a := x.toCols₁)]
        intro h1
        apply h2
        intro r q
        rcases q with q | q
        exacts [h1 r q, q.elim0]
    funext x
    refine (hval O O' (fun y => by simp [O', Matrix.toCols₁_fromCols]) x).trans ?_
    refine (congrFun (hTT' O') _).trans ?_
    refine (congrFun (hOne O' hO') _).trans ?_
    simp only [show ((1 : GA D (ch.G.V (.grid D.R.m (j + 1)))), (1 : GA D (ch.G.V (.grid D.R.m (j + 1 + 1))))) = 1 from rfl,
      map_one, Module.End.one_apply]
    rfl
  · let Φ₂ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, j + 1 + 1))) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)) :=
      ⟨fun x => Φ.1 (fromCols x 0), GlobalTheory.FinPl.Comm.comp_mem_SB Φ.2 hc2 hc1 fun x => Matrix.toCols₁_fromCols x 0⟩
    have hs : ∀ b, (frame hc).symm b = Sum.inl (Fin.cast h₄ b) := fun b => by
      rw [Equiv.symm_apply_eq]
      ext
      rfl
    refine ⟨Φ₂, fun z => ?_, ?_⟩
    · show Φ.1 (fromCols z 0) = _
      rw [hΦ]
      congr 2
      ext a b
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply, hs, Matrix.fromCols_apply_inl]
      rfl
    · funext x
      refine (hval Φ₂ Φ (fun _ => rfl) x).trans ?_
      refine (congrFun (hTT' Φ) _).trans ?_
      refine (congrFun hTΦ _).trans ?_
      simp only [mul_one, show ((1 : GA D (ch.G.V (.grid D.R.m (j + 1)))), (1 : GA D (ch.G.V (.grid D.R.m (j + 1 + 1))))) = 1 from rfl,
        map_one, Module.End.one_apply]
      rfl

end GlobalTheory.LastStepExt0
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastTwoStepsTopVertexFrameAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

namespace GlobalTheory.FlatPlace

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem pr_eq_algebraMap_of_isPlc {w : Pl D.host.E} {p : Place D (Kw w)} (hp : IsPlc w p) :
    (p.pr : D.host.E → Kw w) = algebraMap D.host.E (Kw w) := funext fun a => by
  show p.π (incA D a) = _
  rw [hp.2.1]
  exact congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z w) (GlobalTheory.AdeleBaseChange.map_tmul_one (toAd_spec D) a)

theorem topVertexFrame_renumbered_cast (ch : Choice R) (t : T) (w : Pl D.host.E) (hw : w ∈ locPl ch.G t) (p : Place D (Kw w)) (hp : IsPlc w p)
    (n : ℕ) (hn : D.R.m = n) (hle : n ≤ D.R.m) :
    ∃ e : Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m)) ⊕ Unit ≃ Fin (topRank (locGrid ch.G t w) n),
      (∀ i, (e (Sum.inl i)).val = i.val) ∧ (e (Sum.inr ())).val = topRank (locGrid ch.G t w) n - 1 ∧
      ∃ FX : Frame (Kw w) (ch.G.V (.top n)).rank (Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m)) ⊕ Unit),
        FX.β = fromCols ((topOrthAt ch.G hn).iA.map p.pr * (frRow ch.S.B t w D.R.m le_rfl).β)
          (Matrix.of fun r _ => ((topOrthAt ch.G hn).iB.map p.pr *ᵥ fun _ => (1 : Kw w)) r) ∧
        ∀ r z, FX.β r z = (frTop ch.S.toGridChoice t w n hle).β r (e z) := by
  subst hn
  have hL := ch.S.last t (Set.mem_univ t) w hw
  unfold IsSumFrame at hL
  rw [pr_eq_algebraMap_of_isPlc hp]
  set d := ch.G.sp.topDec with hd
  have h1 : (locGrid ch.G t w).rank (D.R.m, D.R.m) = (ch.G.V (.grid D.R.m D.R.m)).rank :=
    rank_vertex ch.G t w (X := (D.R.m, D.R.m)) ⟨le_rfl, le_rfl⟩
  have h2 : topRank (locGrid ch.G t w) D.R.m = (ch.G.V (.top D.R.m)).rank := topRank_eq ch.G t w hle
  have h3 : (ch.G.V (.grid D.R.m D.R.m)).rank + 1 = (ch.G.V (.top D.R.m)).rank := d.rank
  let e : Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m)) ⊕ Unit ≃ Fin (topRank (locGrid ch.G t w) D.R.m) :=
    ((Equiv.sumCongr (finCongr h1) (⟨fun _ => 0, fun _ => (), fun _ => rfl, fun x => Subsingleton.elim _ _⟩ : Unit ≃ Fin 1)).trans (frame h3)).trans (finCongr h2.symm)
  refine ⟨e, fun i => rfl, ?_, ?_⟩
  · simp [e, frame]
    omega
  let F := frTop ch.S.toGridChoice t w D.R.m hle
  refine ⟨⟨F.β.submatrix id e, F.γ.submatrix e id, ?_, ?_⟩, ?_, fun r z => rfl⟩
  · rw [submatrix_mul_equiv, submatrix_id_id, F.βγ]
  · rw [← submatrix_mul _ _ _ id _ Function.bijective_id, F.γβ, submatrix_one_equiv]
  · refine Matrix.ext fun r z => ?_
    rcases z with i | u
    · have := congrFun (congrFun hL r) (Sum.inl (Fin.cast h1 i))
      refine Eq.trans ?_ (this.trans ?_)
      · rfl
      · simp only [fromCols_apply_inl]
        rfl
    · have := congrFun (congrFun hL r) (Sum.inr 0)
      refine Eq.trans ?_ (this.trans ?_)
      · rfl
      · simp only [fromCols_apply_inr, of_apply, Matrix.mul_diagonal, Matrix.map_apply, mul_one]
        rw [Pi.one_apply, mul_one]
        symm
        show ∑ k : Fin 1, (_ : Kw w) = _
        rw [Fin.sum_univ_one]
        exact mul_one _

theorem frame_top_last : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (t : T) (w : Pl D.host.E) (hw : w ∈ locPl ch.G t) (p : Place D (Kw w)) (hp : IsPlc w p)
    (j : ℕ) (hj : j + 2 = D.R.m),
    ∃ e : Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m)) ⊕ Unit ≃ Fin (topRank (locGrid ch.G t w) (j + 1 + 1)),
      (∀ i, (e (Sum.inl i)).val = i.val) ∧ (e (Sum.inr ())).val = topRank (locGrid ch.G t w) (j + 1 + 1) - 1 ∧
      ∃ FX : Frame (Kw w) (ch.G.V (.top (j + 1 + 1))).rank (Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m)) ⊕ Unit),
        FX.β = fromCols ((topOrthAt ch.G (show D.R.m = j + 1 + 1 by omega)).iA.map p.pr * (frRow ch.S.B t w D.R.m le_rfl).β)
          (Matrix.of fun r _ => ((topOrthAt ch.G (show D.R.m = j + 1 + 1 by omega)).iB.map p.pr *ᵥ fun _ => (1 : Kw w)) r) ∧
        ∀ r z, FX.β r z = (frTop ch.S.toGridChoice t w (j + 1 + 1) (by omega)).β r (e z) :=
  fun ch t w hw p hp j _ => topVertexFrame_renumbered_cast ch t w hw p hp (j + 1 + 1) (by omega) (by omega)

end GlobalTheory.FlatPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeOffS0LastLevelIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.RowShape.OffLat

variable {D : D7}

theorem latV_le_of_smul (S : HSp D) (L M : GlobalTheory.FinPl.Lat S) {v : GlobalTheory.FinPl.Pl D} {t : 𝓞 D.host.F} (ht : t ∉ v.asIdeal)
    (h : ∀ x ∈ L, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • x ∈ M) :
    GlobalTheory.FinPl.latV S L (· = v) ≤ GlobalTheory.FinPl.latV S M (· = v) := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul
  rw [AddSubgroup.closure_le]
  rintro y ⟨α, hα, hsupp, e, he, x, hx, rfl⟩
  rw [Set.mem_singleton_iff] at he
  subst he
  have ht0 : t ≠ 0 := fun h0 => ht (h0 ▸ v.asIdeal.zero_mem)
  have htF : (t : D.host.F) ≠ 0 := by exact_mod_cast ht0
  have hval : v.intValuation t = 1 :=
    le_antisymm (v.intValuation_le_one t) (not_lt.mp fun h => ht ((v.intValuation_lt_one_iff_mem t).mp h))
  have hcv : evalV D.host.F v (algebraMap D.host.F (Af D.host.F) (t : D.host.F)⁻¹) ∈
      v.adicCompletionIntegers D.host.F := by
    rw [AlgHom.commutes, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    change Valued.v ((((t : D.host.F)⁻¹ : D.host.F)) : v.adicCompletion D.host.F) ≤ 1
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀,
      show (t : D.host.F) = algebraMap (𝓞 D.host.F) D.host.F t from rfl,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, hval, inv_one]
  apply AddSubgroup.subset_closure
  refine ⟨α * algebraMap D.host.F (Af D.host.F) (t : D.host.F)⁻¹, ?_, ?_, 1, rfl, _, h x hx, ?_⟩
  · intro w
    rw [map_mul]
    by_cases hw : w = v
    · subst hw
      exact Subring.mul_mem _ (hα w) hcv
    · rw [hsupp w hw, zero_mul]
      exact Subring.zero_mem _
  · intro w hw
    rw [map_mul, hsupp w hw, zero_mul]
  · funext i
    have hx' : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • x i = (t : D.host.F) • x i := by
      rw [Algebra.smul_def, Algebra.smul_def]
      congr 1
    rw [Pi.smul_apply, one_mul, one_mul, hx', ← TensorProduct.smul_tmul]
    congr 1
    refine Prod.ext ?_ ?_
    · change (0 : InfiniteAdeleRing D.host.F) = (t : D.host.F) • (0 : InfiniteAdeleRing D.host.F)
      rw [smul_zero]
    · change α = (t : D.host.F) • (α * algebraMap D.host.F (Af D.host.F) (t : D.host.F)⁻¹)
      rw [Algebra.smul_def, mul_left_comm, ← map_mul, mul_inv_cancel₀ htF, map_one, mul_one]

theorem smul_mem_lat {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) {𝔟 𝔟' : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E}
    (r : 𝓞 D.host.E) (h : ∀ p, ∀ u ∈ 𝔟 p, r • u ∈ 𝔟' p) : ∀ x ∈ d.lat Λ 𝔟, r • x ∈ d.lat Λ 𝔟' := by
  intro x hx
  obtain ⟨y, hy, u, hu, rfl⟩ := hx
  refine ⟨r • y, Λ.smul_mem r hy, r • u, fun p => h p _ (hu p), ?_⟩
  rw [smul_add, Matrix.mulVec_smul, Matrix.mulVec_smul]

theorem smul_mem_of_mul {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (𝔟 : FractionalIdeal R⁰ K) {I J : Ideal R} {s : R} (hJ0 : J ≠ ⊥) (hJ : s ∈ J) {a b n : ℕ} (hn : b ≤ n) {u : K}
    (hu : u ∈ 𝔟 * (I : FractionalIdeal R⁰ K) ^ a * ((J : FractionalIdeal R⁰ K) ^ b)⁻¹) : s ^ n • u ∈ 𝔟 := by
  have hJb : ((J : FractionalIdeal R⁰ K) ^ b) ≠ 0 :=
    pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr hJ0)
  have hsb : algebraMap R K (s ^ b) ∈ (J : FractionalIdeal R⁰ K) ^ b := by
    rw [← FractionalIdeal.coeIdeal_pow, FractionalIdeal.mem_coeIdeal]
    exact ⟨s ^ b, Ideal.pow_mem_pow hJ b, rfl⟩
  have hprod := FractionalIdeal.mul_mem_mul hsb hu
  have hcancel : (J : FractionalIdeal R⁰ K) ^ b * (𝔟 * (I : FractionalIdeal R⁰ K) ^ a * ((J : FractionalIdeal R⁰ K) ^ b)⁻¹)
      = 𝔟 * (I : FractionalIdeal R⁰ K) ^ a := by
    rw [mul_comm, mul_assoc, inv_mul_cancel₀ hJb, mul_one]
  have hle : 𝔟 * (I : FractionalIdeal R⁰ K) ^ a ≤ 𝔟 :=
    mul_le_of_le_one_right' (pow_le_one' FractionalIdeal.coeIdeal_le_one _)
  have hb : s ^ b • u ∈ 𝔟 := by
    rw [Algebra.smul_def]
    exact hle (hcancel ▸ hprod)
  have hsplit : s ^ n • u = s ^ (n - b) • s ^ b • u := by
    rw [smul_smul, ← pow_add, Nat.sub_add_cancel hn]
  rw [hsplit]
  exact Submodule.smul_mem (𝔟 : Submodule R K) _ hb

theorem smul_mem_mul {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (𝔟 : FractionalIdeal R⁰ K) {I J : Ideal R} {s : R} (hI0 : I ≠ ⊥) (hJ0 : J ≠ ⊥) (hI : s ∈ I) {a b n : ℕ} (hn : a ≤ n)
    {u : K} (hu : u ∈ 𝔟) :
    s ^ n • u ∈ 𝔟 * (I : FractionalIdeal R⁰ K) ^ a * ((J : FractionalIdeal R⁰ K) ^ b)⁻¹ := by
  have hsa : algebraMap R K (s ^ a) ∈ (I : FractionalIdeal R⁰ K) ^ a := by
    rw [← FractionalIdeal.coeIdeal_pow, FractionalIdeal.mem_coeIdeal]
    exact ⟨s ^ a, Ideal.pow_mem_pow hI a, rfl⟩
  have hJb : ((J : FractionalIdeal R⁰ K) ^ b) ≠ 0 :=
    pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr hJ0)
  have hone : (1 : FractionalIdeal R⁰ K) ≤ ((J : FractionalIdeal R⁰ K) ^ b)⁻¹ := by
    have := FractionalIdeal.inv_anti_mono hJb (pow_le_one' FractionalIdeal.coeIdeal_le_one _)
    simpa using this
  have hle : 𝔟 * (I : FractionalIdeal R⁰ K) ^ a ≤ 𝔟 * (I : FractionalIdeal R⁰ K) ^ a * ((J : FractionalIdeal R⁰ K) ^ b)⁻¹ :=
    le_mul_of_one_le_right' hone
  have ha : s ^ a • u ∈ 𝔟 * (I : FractionalIdeal R⁰ K) ^ a * ((J : FractionalIdeal R⁰ K) ^ b)⁻¹ := by
    rw [Algebra.smul_def, mul_comm (algebraMap R K (s ^ a)) u]
    exact hle (FractionalIdeal.mul_mem_mul hu hsa)
  have hsplit : s ^ n • u = s ^ (n - a) • s ^ a • u := by
    rw [smul_smul, ← pow_add, Nat.sub_add_cancel hn]
  rw [hsplit]
  exact Submodule.smul_mem ((𝔟 * (I : FractionalIdeal R⁰ K) ^ a * ((J : FractionalIdeal R⁰ K) ^ b)⁻¹ :
    FractionalIdeal R⁰ K) : Submodule R K) _ ha

end GlobalTheory.RowShape.OffLat


open GlobalTheory.RowShape.OffLat in
theorem GlobalTheory.RowShape.latV_grid_iff_rowN_zero : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (v : GlobalTheory.FinPl.Pl D), v ∉ G.pl.S0 → ∀ y : Fin (G.V (.grid D.R.m 0)).rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ GlobalTheory.FinPl.latV _ (G.Λ (.grid D.R.m 0)) (· = v) ↔ y ∈ GlobalTheory.FinPl.latV _ (GlobalTheory.RowShape.rowN G 0) (· = v)) := by
  intro D T L sc G v hv y _
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hgrid : G.Λ (.grid D.R.m 0) =
      (G.rowDec 0 hm).lat (G.Λ (.top 0)) (stairId (G.pl.stA sc) (G.pl.stAbar sc) (D.R.m - 1 - 0)) :=
    G.sp.colLat D.R.m hm le_rfl
  have hrow : GlobalTheory.RowShape.rowN G 0 = (G.rowDec 0 hm).lat (G.Λ (.top 0)) (GlobalTheory.RowShape.rowId D 0) := by
    rw [GlobalTheory.RowShape.rowN, dite_eq_left hm]
  obtain ⟨s, hs, hsI⟩ := GlobalTheory.ModulUnit.exists_mem_modul G.pl sc hv
  obtain ⟨s', hs', hsJ⟩ := GlobalTheory.ModulUnit.exists_mem_modulBar G.pl sc hv
  have hinj : Function.Injective (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
    exact FaithfulSMul.algebraMap_injective _ _
  have hne : ∀ (I : Ideal (𝓞 D.host.E)) (r : 𝓞 D.host.F), r ∉ v.asIdeal →
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r ∈ I → I ≠ ⊥ := by
    intro I r hr hrI hI
    rw [hI, Ideal.mem_bot, ← map_zero (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))] at hrI
    exact hr (hinj hrI ▸ v.asIdeal.zero_mem)
  have hI0 := hne _ s hs hsI
  have hJ0 := hne _ s' hs' hsJ
  have hodd : ¬ Odd (0 : ℕ) := by simp
  have hid : ∀ p : Fin (D.R.m - 1 - 0), stairId (G.pl.stA sc) (G.pl.stAbar sc) (D.R.m - 1 - 0) p =
      GlobalTheory.RowShape.rowId D 0 p * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ (p.1 + 1) *
        (((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ (D.R.m - 1 - 0 - p.1))⁻¹ := by
    intro p
    simp only [stairId, GlobalTheory.RowShape.rowId, GlobalTheory.RowShape.tiltSc, if_neg hodd, FractionalIdeal.spanSingleton_one,
      Places.stA, Places.stAbar, mul_pow, inv_pow, mul_inv, inv_inv, one_mul]
    ac_rfl
  have hA : ∀ x ∈ G.Λ (.grid D.R.m 0),
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (s' ^ (D.R.m - 1 - 0)) • x ∈ GlobalTheory.RowShape.rowN G 0 := by
    intro x hx
    rw [hgrid] at hx
    rw [hrow, map_pow]
    refine smul_mem_lat (G.rowDec 0 hm) (G.Λ (.top 0)) (𝔟 := stairId (G.pl.stA sc) (G.pl.stAbar sc) (D.R.m - 1 - 0))
      (𝔟' := GlobalTheory.RowShape.rowId D 0) _ ?_ x hx
    intro p u hu
    rw [hid p] at hu
    exact smul_mem_of_mul _ hJ0 hsJ (a := p.1 + 1) (b := D.R.m - 1 - 0 - p.1) (n := D.R.m - 1 - 0) (Nat.sub_le _ _) hu
  have hB : ∀ x ∈ GlobalTheory.RowShape.rowN G 0,
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (s ^ (D.R.m - 1 - 0)) • x ∈ G.Λ (.grid D.R.m 0) := by
    intro x hx
    rw [hrow] at hx
    rw [hgrid, map_pow]
    refine smul_mem_lat (G.rowDec 0 hm) (G.Λ (.top 0)) (𝔟 := GlobalTheory.RowShape.rowId D 0)
      (𝔟' := stairId (G.pl.stA sc) (G.pl.stAbar sc) (D.R.m - 1 - 0)) _ ?_ x hx
    intro p u hu
    rw [hid p]
    have hp := p.isLt
    exact smul_mem_mul _ hI0 hJ0 hsI (a := p.1 + 1) (b := D.R.m - 1 - 0 - p.1) (n := D.R.m - 1 - 0) (by omega) hu
  have hpow : ∀ r : 𝓞 D.host.F, r ∉ v.asIdeal → r ^ (D.R.m - 1 - 0) ∉ v.asIdeal :=
    fun r hr h => hr (v.isPrime.mem_of_pow_mem _ h)
  have h1 := latV_le_of_smul _ _ _ (hpow s' hs') hA
  have h2 := latV_le_of_smul _ _ _ (hpow s hs) hB
  exact ⟨fun h => h1 h, fun h => h2 h⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PosNormLineSelfDualAndTopLatticeSplits
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowShape

variable {D : D7}

theorem pLine_gram_eq_one : (pLine D).gram = 1 := by
  rw [pLine_gram]
  ext i j
  fin_cases i; fin_cases j
  simp [antiDiagonalSignGramMatrix]
  rfl

theorem mem_topL_iff (z : Fin (pLine D).rank → D.host.E) : z ∈ topL D ↔ z ∈ GlobalTheory.AdForm.intVec D (pLine D).rank := by
  simp only [topL, latPi, Submodule.mem_pi, Set.mem_univ, true_implies, FractionalIdeal.coe_one, Submodule.mem_one]
  show _ ↔ ∀ k, IsIntegral ℤ (z k)
  refine forall_congr' fun k => ⟨?_, fun h => ⟨⟨z k, h⟩, rfl⟩⟩
  rintro ⟨b, hb⟩
  rw [← hb]
  exact b.2

theorem isSelfDualC_topL : IsSelfDualC (pLine D) (topL D) :=
  GlobalTheory.LocMod.IntFrameStd.isSelfDualC_of_gram_one pLine_gram_eq_one _ mem_topL_iff

variable {T : Type} {L : LevCh D T} {sc : Consts}

theorem topLat_eq_sumLatO (G : GridData L sc) :
    G.Λ (.top D.R.m) = GlobalTheory.Core.Rk.SumBox.sumLatO (topOrth G) (G.Λ (.grid D.R.m D.R.m)) (topL D) := by
  have e : G.Λ (.top D.R.m) = G.sp.topDec.lat (G.Λ (.grid D.R.m D.R.m)) (fun _ => 1) := G.sp.topLat
  rw [e]
  ext x
  rw [GlobalTheory.Core.Rk.SumBox.mem_sumLatO]
  constructor
  · rintro ⟨y, hy, u, hu, rfl⟩
    exact ⟨y, hy, u, Submodule.mem_pi.2 fun p _ => hu p, rfl⟩
  · rintro ⟨y, hy, u, hu, rfl⟩
    exact ⟨y, hy, u, fun p => Submodule.mem_pi.1 hu p (Set.mem_univ _), rfl⟩

theorem topLat_orthAt (G : GridData L sc) (v : Pl D) :
    OrthAt (topOrth G) (G.Λ (.top D.R.m)) (G.Λ (.grid D.R.m D.R.m)) (topL D) v := by
  rw [topLat_eq_sumLatO G]
  exact GlobalTheory.Core.Rk.SumSplit.orthAt_sumLatO D _ _ _ (topOrth G) _ _ v

theorem topL_selfDual_orthAt : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => IsSelfDualC _ (GlobalTheory.RowShape.topL D) ∧
    ∀ v, GlobalTheory.FinPl.OrthAt (topOrth ch.G) (ch.G.Λ (.top D.R.m)) (ch.G.Λ (.grid D.R.m D.R.m)) (GlobalTheory.RowShape.topL D) v :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ =>
    ⟨isSelfDualC_topL, fun v => topLat_orthAt ch.G v⟩⟩⟩

end GlobalTheory.RowShape
end
end

