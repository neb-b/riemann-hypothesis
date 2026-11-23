module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0036
public import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapSecondPlace
public import Formalism.WachLatticeTwists.SplitClassesAll.Statement
public import Formalism.WachLatticeTwists.SplitLocalLifts.Statement
public import Mathlib
public import Formalism.CoboundaryTransfers.Statement
public import Formalism.CoboundaryTransfers.StatementAPI
public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.StatementTop
public import Formalism.WachLatticeTwists.CharacterSplitJumps.WachTwistTheoremFromTorsionBound
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.Bundle0001
public import Formalism.WachLatticeTwists.Statement
public import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.MinimalExponentAttained
public import Formalism.WachLatticeTwists.HodgeTateChains.InvariantsCohomologyData
public import Formalism.CharacterColumnKernels.Statement
public import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.Imports
public import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.Complete
public import Formalism.WachLatticeTwists.TorsionLengthCounts.Bundle0001
public import Formalism.WachLatticeTwists.HodgeTateChains.H2KilledByTateDuality
public import Formalism.WachLatticeTwists.HodgeTateChains.Statement
public import Formalism.WindowSums.AnnihilatorPolynomials.ZpowVal
public import Formalism.WachLatticeTwists.RamifiedBlockRings.ChainFromPrimitiveData
public import Formalism.WachLatticeTwists.RealDisplaySplitting.SurjectionRankOneIdempotent
public import Formalism.WachLatticeTwists.RamifiedBlockRings.Bundle0001
public import Formalism.WachLatticeTwists.SplitLocalLifts.Cocycles1MapOfEquivariant
public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.DualWByLettersExtended
public import Formalism.WachLatticeTwists.SplitLocalLifts.SplitLocalLiftProofs.LocLift
public import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.Bundle0001
public import Formalism.WachLatticeTwists.LatticeDualFibres.Statement
public import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient
public import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
public import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.ExistsPowSmulIntegral
public import Formalism.WachLatticeTwists.LatticeDualFibres.StatDualFibreLattice
public import Formalism.WachLatticeTwists.CharacterSplitJumps.CharacterJumpProofs.MemAnnih
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.Bundle0001
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.TheoremNFiveDeltaClause
public import Formalism.WachLatticeTwists.CharacterSplitJumps.CharacterJumpProofs.PropLocBK
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.Bridge
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.CharacterColumnKernelsOfBlockChiCOfBlockChiOne
public import Formalism.CharacterColumnKernels.CharacterColumnKernelEqualityForm
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.Bundle0001
public import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapProofs.Bundle0002
public import Formalism.LagrangeIdealLifts.Statement
public import Formalism.CoboundaryTransfers.GammaStableTransfers.Bundle0001
public import Formalism.CoboundaryTransfers.GammaStableTransfers.GammaStableOfGammaQUnitHolds
public import Formalism.WachLatticeTwists.RealDisplaySplitting.RealDisplayProofs.IdempotentRankOneAtPoint
public import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapProofs.TheoremNFiveRealAllLiftThird

@[expose] public section

-- bundled from Formalism.AdmissibleDesigns.DesignOfAdmittedObjects
section
noncomputable section

open Formalism.BasicNotions

namespace Formalism.MainNotions.N.RepresentationBoundsCohomology.J8

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Matrix Formalism.RepresentationBoundsCohomology.ringDataObjects Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.MainNotions.N
  Formalism.MainNotions.N.RepresentationBoundsCohomology

section Gen

theorem rank_submatrix_le' {K : Type} [Field K] {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (M : Matrix n n K) (f g : m → n) : (M.submatrix f g).rank ≤ M.rank := by
  exact Matrix.rank_submatrix_le M f g

theorem castAdd_ne_natAdd {r t : ℕ} (b : Fin r) (c : Fin t) : Fin.castAdd t b ≠ Fin.natAdd r c := by
  intro h
  have h1 := congrArg Fin.val h
  simp only [Fin.coe_castAdd, Fin.coe_natAdd] at h1
  omega

theorem lt_rank_of {K : Type} [Field K] {r t : ℕ} (M : Matrix (Fin (r + t)) (Fin (r + t)) K)
    (hc : ∀ c d : Fin t, M (Fin.natAdd r c) (Fin.natAdd r d) = if c = d then 1 else 0)
    (hcb : ∀ (c : Fin t) (b : Fin r), M (Fin.natAdd r c) (Fin.castAdd t b) = 0)
    (hac : ∀ (a : Fin r) (c : Fin t), M (Fin.castAdd t a) (Fin.natAdd r c) = 0)
    (a b : Fin r) (hab : M (Fin.castAdd t a) (Fin.castAdd t b) ≠ 0) : t + 1 ≤ M.rank := by
  classical
  let f : Fin (t + 1) → Fin (r + t) := Fin.cons (Fin.castAdd t a) (Fin.natAdd r)
  let g : Fin (t + 1) → Fin (r + t) := Fin.cons (Fin.castAdd t b) (Fin.natAdd r)
  let w : Fin (t + 1) → K := Fin.cons (M (Fin.castAdd t a) (Fin.castAdd t b)) (fun _ => 1)
  have h1 : M.submatrix f g = Matrix.diagonal w := by
    ext p q
    cases p using Fin.cases with
    | zero =>
      cases q using Fin.cases with
      | zero => simp [f, g, w]
      | succ q => simp [f, g, w, hac, (Fin.succ_ne_zero q).symm]
    | succ p =>
      cases q using Fin.cases with
      | zero => simp [f, g, w, hcb, Fin.succ_ne_zero p]
      | succ q =>
        by_cases hpq : p = q
        · subst hpq
          simp [f, g, w, hc]
        · simp [f, g, w, hc, hpq]
  have h2 := rank_submatrix_le' M f g
  rw [h1, Matrix.rank_diagonal] at h2
  have hw : ∀ p, w p ≠ 0 := by
    intro p
    cases p using Fin.cases with
    | zero => simpa [w] using hab
    | succ p => simp [w]
  have h3 : Fintype.card {p // w p ≠ 0} = t + 1 := by
    rw [Fintype.card_congr (Equiv.subtypeUnivEquiv hw), Fintype.card_fin]
  omega

theorem eq_diag_of {K : Type} [Field K] {r t : ℕ} (M : Matrix (Fin (r + t)) (Fin (r + t)) K)
    (B : Matrix (Fin r) (Fin r) K)
    (hM : ∀ u, eG r t K (M *ᵥ u) = (B *ᵥ (eG r t K u).1, (eG r t K u).2)) (hrk : M.rank = t) :
    M = Matrix.diagonal fun a => if blkG r t a = 0 then (0 : K) else 1 := by
  classical
  have hent : ∀ x y, (M *ᵥ Pi.single y (1 : K)) x = M x y := by
    intro x y
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have h2 : ∀ (d : Fin t) y, M (Fin.natAdd r d) y = if Fin.natAdd r d = y then 1 else 0 := by
    intro d y
    have h := congrFun (congrArg Prod.snd (hM (Pi.single y 1))) d
    simp only [eG_apply] at h
    rw [← hent, h, Pi.single_apply]
  have h1 : ∀ a y, M (Fin.castAdd t a) y = (B *ᵥ fun b => (Pi.single y (1 : K) : Fin (r + t) → K) (Fin.castAdd t b)) a := by
    intro a y
    have h := congrFun (congrArg Prod.fst (hM (Pi.single y 1))) a
    simp only [eG_apply] at h
    rw [← hent, h]
  have hac : ∀ (a : Fin r) (c : Fin t), M (Fin.castAdd t a) (Fin.natAdd r c) = 0 := by
    intro a c
    rw [h1]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, castAdd_ne_natAdd]
  have hc : ∀ c d : Fin t, M (Fin.natAdd r c) (Fin.natAdd r d) = if c = d then 1 else 0 := by
    intro c d
    rw [h2]
    by_cases hcd : c = d
    · subst hcd
      simp
    · rw [if_neg hcd, if_neg]
      intro h
      apply hcd
      have h3 := congrArg Fin.val h
      simp at h3
      exact Fin.ext h3
  have hcb : ∀ (c : Fin t) (b : Fin r), M (Fin.natAdd r c) (Fin.castAdd t b) = 0 := by
    intro c b
    rw [h2, if_neg (fun h => castAdd_ne_natAdd b c h.symm)]
  have hB0 : ∀ a b, M (Fin.castAdd t a) (Fin.castAdd t b) = 0 := by
    intro a b
    by_contra hab
    have := lt_rank_of M hc hcb hac a b hab
    omega
  ext x y
  cases x using Fin.addCases with
  | left a =>
    cases y using Fin.addCases with
    | left b => simp [hB0, Matrix.diagonal_apply, blkG_castAdd]
    | right c => simp [hac, Matrix.diagonal_apply, blkG_castAdd]
  | right c =>
    rw [h2]
    simp [Matrix.diagonal_apply, blkG_natAdd, Fin.succ_ne_zero]

theorem transfer {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (L L' : V ≃ₗ[K] W) (φ : V → V) (F Hm : W → W)
    (h1 : ∀ u, L (φ u) = Hm (L u)) (h2 : ∀ u, L' (φ u) = Hm (L' u)) (h3 : ∀ u, L (φ u) = F (L u)) :
    ∀ u, L' (φ u) = F (L' u) := by
  have hF : ∀ w, Hm w = F w := by
    intro w
    obtain ⟨u, rfl⟩ := L.surjective w
    rw [← h1, h3]
  intro u
  rw [h2, hF]

end Gen

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
  (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (π : N.X i)

def Dg (γ : GE N) (z : (Fin R.r → KK N i) × (Fin R.t → KK N i)) : (Fin R.r → KK N i) × (Fin R.t → KK N i) :=
  ((mapM (toK N i) (rhoO N i ρ π) γ).mulVec z.1,
    fun c : Fin R.t => toK N i ((chiU N i ((c : ℕ) + 1) γ : (N.O i)ˣ) : N.O i) * z.2 c)

theorem act_inR {a : N.X i → MatN N i} (ha : InR N i r a) :
    ∃ Hm : (Fin R.r → KK N i) × (Fin R.t → KK N i) → (Fin R.r → KK N i) × (Fin R.t → KK N i),
      ∀ L : (Fin R.nV → KK N i) ≃ₗ[KK N i] ((Fin R.r → KK N i) × (Fin R.t → KK N i)),
      (∀ γ u, L ((mapM (toK N i) (rO N i r π) γ).mulVec u) = Dg N ρ π γ (L u)) →
      ∀ u, L (((a π).map (toK N i)).mulVec u) = Hm (L u) := by
  obtain ⟨m, f, g, -, rfl⟩ := ha
  refine ⟨fun z => ∑ k, toK N i (f k π) • Dg N ρ π (g k) z, fun L hL u => ?_⟩
  have h : (((∑ k, fun x => f k x • rO N i r x (g k)) π).map (toK N i)).mulVec u =
      ∑ k, toK N i (f k π) • (mapM (toK N i) (rO N i r π) (g k)).mulVec u := by
    rw [Finset.sum_apply]
    change ((toK N i).mapMatrix (∑ k, f k π • rO N i r π (g k))).mulVec u = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Matrix.smul_mulVec]
    congr 1
    ext a b
    simp [mapM, Matrix.smul_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_smul, hL]

theorem tSpan_of_inR {a : N.X i → MatN N i} (ha : InR N i r a) : a ∈ tSpan (N.T i) (repX N r) := by
  have h := Inst.inSpan_tSpan N i (N.T i) (rO N i r) (N.O i) ha
  have e1 : (fun x => (a x).map (algebraMap (N.O i) (N.O i))) = a := by
    funext x
    exact Inst.map_self _
  have e2 : Inst.repF N i (rO N i r) (N.O i) = repX N r := by
    ext γ x : 2
    rw [Inst.repF_apply, Inst.map_self]
    rfl
  rw [e1, e2] at h
  exact h

theorem rr_inj {S : IdempotentChoiceData N i} (hG : GoodCongruenceObjects N r ρ π S) (x' : S.X') :
    Function.Injective (fun c : Fin R.t => S.rr (1 + (c : ℕ)) x') := by
  classical
  obtain ⟨b, hbT, -, hind⟩ := Inst.descent_hyps N hG
  have hG' := hG
  obtain ⟨-, -, -, -, -, -, -, ⟨-, -, -, -, hcard⟩, hroots, -⟩ := hG'
  have hcF : Fintype.card {y // S.p y = S.p x'} = R.t.factorial := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard (S.p x')
  let Φ : {y // S.p y = S.p x'} → (Fin R.t → N.O i) := fun y c => S.rr (1 + (c : ℕ)) y.1
  have hinj : Function.Injective Φ := by
    intro y z hyz
    apply Inst.sep_of_indep hcF (fun k (y : {y // S.p y = S.p x'}) => b k y.1)
      (fun a ha => hind (S.p x') a (fun y hy => ha ⟨y, hy⟩)) y z
    intro k
    refine Inst.T'_eq_of_rr N hG (y.2.trans z.2.symm) (fun c hc => ?_) (b k) (hbT k)
    have hc' := Finset.mem_Icc.mp hc
    have h1 := congrFun hyz ⟨c - 1, by omega⟩
    simpa [Φ, show 1 + (c - 1) = c by omega] using h1
  have hP : ∀ y : {y // S.p y = S.p x'}, ∏ c, (Polynomial.X - Polynomial.C (Φ y c)) =
      ∏ c ∈ Finset.Icc 1 R.t, (Polynomial.X - Polynomial.C (S.rr c x')) := by
    intro y
    have h1 : ∏ c ∈ Finset.Icc 1 R.t, (Polynomial.X - Polynomial.C (S.rr c y.1)) =
        ∏ c ∈ Finset.Icc 1 R.t, (Polynomial.X - Polynomial.C (S.rr c x')) := by
      rw [hroots y.1, hroots x', y.2]
    rw [← h1]
    have h2 : Finset.Icc 1 R.t = Finset.Ico 1 (R.t + 1) := by
      ext c
      simp [Finset.mem_Icc, Finset.mem_Ico]
    rw [h2, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel,
      ← Fin.prod_univ_eq_prod_range
        (fun c => (Polynomial.X : Polynomial (N.O i)) - Polynomial.C (S.rr (1 + c) y.1))]
  exact Inst.inj_of_card Φ hinj _ hP hcF.ge ⟨x', rfl⟩

theorem prod_Icc_fin (t : ℕ) (F : ℕ → Polynomial (N.O i)) :
    ∏ c ∈ Finset.Icc 1 t, F c = ∏ c : Fin t, F (1 + (c : ℕ)) := by
  rw [Fin.prod_univ_eq_prod_range (fun c => F (1 + c)) t, Finset.range_eq_Ico]
  simp_rw [add_comm 1]
  rw [Finset.prod_Ico_add' F 0 t 1, zero_add]
  rfl

section Comp

open Formalism.NG

end Comp

end Formalism.MainNotions.N.RepresentationBoundsCohomology.J8

end
end

-- bundled from Formalism.AdmissibleDesigns.NonemptyPl
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.K

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.MainNotions Formalism.MainNotions.N

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

theorem nonempty_pl : Nonempty (HeightOneSpectrum (𝓞 D.host.E)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.E)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM
    (NumberField.RingOfIntegers.not_isField _)⟩⟩

def plSet : Finset (HeightOneSpectrum (𝓞 D.host.E)) := dc.row ∪ dc.col ∪ D.nd.Q i

def idx (v : HeightOneSpectrum (𝓞 D.host.E)) : ℕ :=
  if h : v ∈ plSet i dc then ((plSet i dc).equivFin ⟨v, h⟩ : ℕ) else (plSet i dc).card

def plOf (n : ℕ) : HeightOneSpectrum (𝓞 D.host.E) :=
  if h : n < (plSet i dc).card then ((plSet i dc).equivFin.symm ⟨n, h⟩ : HeightOneSpectrum (𝓞 D.host.E))
  else Classical.choice nonempty_pl

theorem plOf_idx {v : HeightOneSpectrum (𝓞 D.host.E)} (h : v ∈ plSet i dc) : plOf i dc (idx i dc v) = v := by
  unfold plOf idx
  rw [dite_eq_left h, dite_eq_left ((plSet i dc).equivFin ⟨v, h⟩).isLt]
  simp

theorem idx_inj {v w : HeightOneSpectrum (𝓞 D.host.E)} (hv : v ∈ plSet i dc) (hw : w ∈ plSet i dc)
    (h : idx i dc v = idx i dc w) : v = w := by
  calc v = plOf i dc (idx i dc v) := (plOf_idx i dc hv).symm
    _ = plOf i dc (idx i dc w) := by rw [h]
    _ = w := plOf_idx i dc hw

def rowsN : Finset ℕ := dc.row.image (idx i dc)
def colsN : Finset ℕ := dc.col.image (idx i dc)
def qsN : Finset ℕ := (D.nd.Q i).image (idx i dc)

abbrev Col : Type := {u : HeightOneSpectrum (𝓞 D.host.E) // u ∈ dc.col}

def colIdx (l : Col i dc) : ℕ := idx i dc l.1

theorem colIdx_inj : Function.Injective (colIdx i dc) := by
  intro l₁ l₂ h
  apply Subtype.ext
  have m₁ : l₁.1 ∈ plSet i dc := by
    unfold plSet
    exact Finset.mem_union_left _ (Finset.mem_union_right _ l₁.2)
  have m₂ : l₂.1 ∈ plSet i dc := by
    unfold plSet
    exact Finset.mem_union_left _ (Finset.mem_union_right _ l₂.2)
  exact idx_inj i dc m₁ m₂ h

def Aw (n : ℕ) : ValuationSubring D.nd.Om := D.nd.plOm.1 (plOf i dc n)
def Av (v : HeightOneSpectrum (𝓞 D.host.E)) : ValuationSubring D.nd.Om := D.nd.plOm.1 v

end Formalism.MainNotions.N.K

end
end

