module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2799
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2797
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EventuallyCongOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2612
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2700
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2693
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2712
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2794
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2798
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictHenselisationOfDirectedUnion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2808

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramAtNegOfGramOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)

noncomputable section
namespace GlobalTheory.BottomPairData
variable {D : D7}

theorem sig_of_gram_one {V : HSp D} (hg : V.gram = 1) (hV : V.SigOK) (τ : D.host.E →+* ℂ) :
    (V.sig τ).2 = 0 ∧ (V.sig τ).1 = V.rank := by
  obtain ⟨e, P, hP⟩ := hV τ
  have h1 : (V.gram.map τ).reindex e e = 1 := by
    rw [hg, Matrix.map_one _ (map_zero τ) (map_one τ)]; exact Matrix.submatrix_one_equiv _
  rw [h1, Matrix.mul_one] at hP
  have hP' : (P.1)ᴴ * P.1 = Formalism.UG.Jpq (V.sig τ).1 (V.sig τ).2 := hP
  have hq : (V.sig τ).2 = 0 := by
    by_contra hq
    let k : Fin (V.sig τ).2 := ⟨0, Nat.pos_of_ne_zero hq⟩
    have hk := congrArg (fun M => (M (Sum.inr k) (Sum.inr k)).re) hP'
    simp only [Formalism.UG.Jpq, Matrix.fromBlocks_apply₂₂, Matrix.neg_apply, Matrix.one_apply_eq, Complex.neg_re,
      Complex.one_re] at hk
    have : 0 ≤ (((P.1)ᴴ * P.1) (Sum.inr k) (Sum.inr k)).re := by
      rw [Matrix.mul_apply, Complex.re_sum]
      exact Finset.sum_nonneg fun l _ => by
        rw [Matrix.conjTranspose_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]; exact Complex.normSq_nonneg _
    linarith
  refine ⟨hq, ?_⟩
  have := Fintype.card_congr e
  simp only [Fintype.card_fin, Fintype.card_sum, hq] at this
  omega


open GlobalTheory.Grid (neg neg_gram) in
def negFrame (A : HSp D) : CptF (neg A) := fun τ r c =>
  Sum.elim (fun _ => (0 : ℂ)) (fun k => if (k : ℕ) = (c : ℕ) then 1 else 0) r

open GlobalTheory.Grid (neg) in
theorem negFrame_inl (A : HSp D) (τ : D.what₂.Tau) (a : Fin ((neg A).sig (tauE D τ)).1) (c : Fin (neg A).rank) :
    negFrame A τ (Sum.inl a) c = 0 := rfl

open GlobalTheory.Grid (neg) in
theorem negFrame_inr (A : HSp D) (τ : D.what₂.Tau) (k : Fin ((neg A).sig (tauE D τ)).2) (c : Fin (neg A).rank) :
    negFrame A τ (Sum.inr k) c = if (k : ℕ) = (c : ℕ) then 1 else 0 := rfl

open GlobalTheory.Grid (neg neg_gram) in
theorem jpq_mul_negFrame (A : HSp D) (τ : D.what₂.Tau) :
    Formalism.UG.Jpq ((neg A).sig (tauE D τ)).1 ((neg A).sig (tauE D τ)).2 * negFrame A τ = -negFrame A τ := by
  ext r c
  rcases r with a | b
  · rw [Matrix.neg_apply, show negFrame A τ (Sum.inl a) c = 0 from rfl, neg_zero, Matrix.mul_apply]
    exact Finset.sum_eq_zero fun x _ => by
      rcases x with x | x
      · rw [show negFrame A τ (Sum.inl x) c = 0 from rfl, mul_zero]
      · simp [Formalism.UG.Jpq]
  · simp only [Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      negFrame_inl, negFrame_inr, mul_zero, Finset.sum_const_zero, Matrix.neg_apply, Matrix.zero_apply, zero_mul, zero_add,
      Matrix.one_apply, neg_mul, ite_mul, one_mul, Finset.sum_neg_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]

open GlobalTheory.Grid (neg neg_gram) in
theorem negFrame_conj_mul (A : HSp D) (hg : A.gram = 1) (hA : A.SigOK) (τ : D.what₂.Tau) :
    (negFrame A τ)ᴴ * negFrame A τ = 1 := by
  obtain ⟨hq, hp⟩ := sig_of_gram_one hg hA (tauE D τ)
  ext a b
  rw [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  simp only [Matrix.conjTranspose_apply]
  have e1 : ∀ x, star (negFrame A τ (Sum.inl x) a) * negFrame A τ (Sum.inl x) b = 0 := fun x => by
    rw [show negFrame A τ (Sum.inl x) a = 0 from rfl, star_zero, zero_mul]
  have e2 : ∀ x : Fin ((neg A).sig (tauE D τ)).2, star (negFrame A τ (Sum.inr x) a) * negFrame A τ (Sum.inr x) b =
      if (x : ℕ) = a ∧ (x : ℕ) = b then 1 else 0 := fun x => by
    rw [negFrame_inr, negFrame_inr]
    by_cases h1 : (x : ℕ) = a <;> by_cases h2 : (x : ℕ) = b <;> simp [h1, h2]
  rw [Finset.sum_eq_zero fun x _ => e1 x, zero_add, Finset.sum_congr rfl fun x _ => e2 x]
  have hk : (a : ℕ) < ((neg A).sig (tauE D τ)).2 := by
    show (a : ℕ) < (A.sig (tauE D τ)).1
    rw [hp]; exact a.2
  rw [Finset.sum_eq_single ⟨a, hk⟩]
  · by_cases h : a = b
    · simp [h]
    · rw [if_neg h, if_neg]; rintro ⟨-, h2⟩; exact h (Fin.ext h2)
  · intro x _ hx; rw [if_neg]; rintro ⟨h1, -⟩; exact hx (Fin.ext h1)
  · simp

open GlobalTheory.Grid (neg neg_gram) in
theorem gramAt_neg_of_gram_one {A : HSp D} (hg : A.gram = 1) (τ : D.what₂.Tau) : gramAt D (neg A) τ = -1 := by
  ext a b
  simp only [gramAt, neg_gram, hg, Matrix.map_apply, Matrix.neg_apply, Matrix.one_apply]
  split_ifs <;> simp


open GlobalTheory.Grid (neg neg_gram sigOK_sgn isCartanInv_sgn) in
theorem exists_pair {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {α β : T → ((AE D)ˣ →* Circle)} {νH : T → Formalism.L2.Host.HChar D.host.E} {S}
    (h : X.Is ψ θ α β νH S) (hstd : X.rA.IsStd) (hA : A.SigOK) (h1 : 1 ≤ A.rank) (h1' : 1 ≤ A'.rank) (t : T) :
    ∃ (cA : CptF (neg A)) (a : GL (Fin (neg A).rank) (AE D)) (ν : Measure (WO (neg A) WW)) (𝓕 : Set (WO (neg A) WW)),
      GlobalTheory.Core.Rk.IP.Pair ψ θ (neg A) WW (β t) (β t / α t) (fun τ => -X.rA.s τ) X.rW.s A'.rank cA a ((X.ω t).toSgn true) ν 𝓕 := by
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.Size.exists_isCovolOne (neg A) WW
  have hg := hstd.1
  have hgn : ∀ τ, gramAt D (neg A) τ = -1 := gramAt_neg_of_gram_one hg
  have hs : ∀ τ, X.rA.s τ = 1 := fun τ => (hstd.2.2 τ).1
  refine ⟨negFrame A, 1, ν, 𝓕, ⟨⟨h1, h1', ?_, h.isVac.2.inf, sigOK_sgn true hA, fun τ => ?_,
    fun τ => isCartanInv_sgn true _ τ (h.rigA.2.2 τ).1, fun τ => (h.rigW.2.2 τ).1, fun τ => ?_⟩, ?_, fun τ => ?_, h.weil t, hν⟩⟩
  · exact h.rank.symm
  · rw [Matrix.mul_assoc, jpq_mul_negFrame, Matrix.mul_neg, negFrame_conj_mul A hg hA, hgn]
  · show negFrame A τ * -X.rA.s τ = _
    rw [hs, jpq_mul_negFrame, Matrix.mul_neg, Matrix.mul_one]
  · intro w
    refine ⟨fun _ => false, ?_⟩
    simp only [JR, neg_gram, hg]
    ext i j
    simp [Formalism.UG.cT, Matrix.mul_apply, Matrix.one_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  · rw [hgn, hs]
    simp [compAt]


open GlobalTheory.Grid (neg) in
theorem one_le_bot (i j : Fin D.R.m) : 1 ≤ botBig D i j ∧ 1 ≤ botSmall D i j := by
  obtain ⟨u, hu⟩ := D.R.t_odd
  have h2 : D.R.m ≤ D.R.r := by have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have hr : Odd D.R.r := by
    have := GlobalTheory.ChiGrid.odd_sLen D
    simp only [GlobalTheory.ChiGrid.sLen] at this
    exact (Nat.odd_add.1 this).2 (by decide)
  obtain ⟨w, hw⟩ := hr
  have hi := i.2
  have hj := j.2
  simp only [botBig, botSmall, rankV, GlobalTheory.ChiGrid.sLen]
  constructor <;> omega

end GlobalTheory.BottomPairData


open GlobalTheory.BottomPairData in
theorem GlobalTheory.BottomPairData.pair_data : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → A.SigOK → ∀ t : T, ∃ (cA : CptF (GlobalTheory.Grid.neg A)) (a : GL (Fin (GlobalTheory.Grid.neg A).rank) (AE D)) (νW : Measure (WO (GlobalTheory.Grid.neg A) WW)) (𝓕W : Set (WO (GlobalTheory.Grid.neg A) WW)),
    GlobalTheory.Core.Rk.IP.Pair W.ψ W.θ (GlobalTheory.Grid.neg A) WW (GlobalTheory.BottomIPData.betaB G i j) (GlobalTheory.BottomIPData.betaB G i j / GlobalTheory.BottomIPData.alphaB Lc i j t) (fun τ => -X.rA.s τ) X.rW.s A'.rank cA a ((X.ω t).toSgn true) νW 𝓕W := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro W i j A A' WW X hX hA t
  have hb := one_le_bot (D := D) i j
  exact exists_pair X (GlobalTheory.BottomIPData.isBottomTri_is hX) hX.std hA (hX.rank ▸ hb.1) (hX.rank' ▸ hb.2) t

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridFrameLocalCompactMembership
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

noncomputable section

namespace GlobalTheory.TopFlip.ChKO

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hatL_map {a b : ℕ} {Λ : Submodule (𝓞 E) (Fin a → E)} {Λ' : Submodule (𝓞 E) (Fin b → E)}
    (f : (Fin a → E ⊗[F] Formalism.L2.Herm.Af F) →ₗ[Formalism.L2.Herm.intAf F E] (Fin b → E ⊗[F] Formalism.L2.Herm.Af F))
    (hf : ∀ x ∈ Λ, ∃ y ∈ Λ', (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (y i)) =
      f fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) :
    ∀ x ∈ Formalism.L2.Herm.hatL (F := F) Λ, f x ∈ Formalism.L2.Herm.hatL (F := F) Λ' := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, e⟩ := hf x hx
    exact Submodule.subset_span ⟨y, hy, e⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x z _ _ hx hz => rw [map_add]; exact add_mem hx hz
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx


open GlobalTheory.Doubling in
theorem pairVec_mem_hatL {a b c : ℕ} (e : Fin a ⊕ Fin b ≃ Fin c) {Λ : Submodule (𝓞 E) (Fin a → E)}
    {Λ' : Submodule (𝓞 E) (Fin b → E)} (x : Fin a → E ⊗[F] Formalism.L2.Herm.Af F) (y : Fin b → E ⊗[F] Formalism.L2.Herm.Af F) :
    pairVec e x y ∈ Formalism.L2.Herm.hatL (F := F) (sumLat e Λ Λ') ↔
      x ∈ Formalism.L2.Herm.hatL (F := F) Λ ∧ y ∈ Formalism.L2.Herm.hatL (F := F) Λ' := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ?_⟩
  · have := hatL_map (Λ := sumLat e Λ Λ') (Λ' := Λ) (LinearMap.funLeft _ _ (e ∘ .inl)) (fun x hx => ⟨_, hx.1, rfl⟩) _ h
    convert this using 1
    funext i; simp [LinearMap.funLeft_apply]
  · have := hatL_map (Λ := sumLat e Λ Λ') (Λ' := Λ') (LinearMap.funLeft _ _ (e ∘ .inr)) (fun x hx => ⟨_, hx.2, rfl⟩) _ h
    convert this using 1
    funext i; simp [LinearMap.funLeft_apply]
  · let f₁ : (Fin a → E ⊗[F] Formalism.L2.Herm.Af F) →ₗ[Formalism.L2.Herm.intAf F E] (Fin c → E ⊗[F] Formalism.L2.Herm.Af F) :=
      { toFun := fun u => pairVec e u 0
        map_add' := fun u v => funext fun j => by obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
        map_smul' := fun r v => funext fun j => by obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp }
    let f₂ : (Fin b → E ⊗[F] Formalism.L2.Herm.Af F) →ₗ[Formalism.L2.Herm.intAf F E] (Fin c → E ⊗[F] Formalism.L2.Herm.Af F) :=
      { toFun := fun u => pairVec e 0 u
        map_add' := fun u v => funext fun j => by obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
        map_smul' := fun r v => funext fun j => by obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp }
    have h1 := hatL_map (Λ' := sumLat e Λ Λ') f₁ (fun u hu => ⟨pairVec e u 0, (pairVec_mem_sumLat e).2 ⟨hu, zero_mem _⟩,
      funext fun j => by obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp [f₁]⟩) _ h.1
    have h2 := hatL_map (Λ' := sumLat e Λ Λ') f₂ (fun u hu => ⟨pairVec e 0 u, (pairVec_mem_sumLat e).2 ⟨zero_mem _, hu⟩,
      funext fun j => by obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp [f₂]⟩) _ h.2
    convert add_mem h1 h2 using 1
    funext j
    obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp [f₁, f₂]


open GlobalTheory.Doubling in
theorem isFrame_blkGL {a b c : ℕ} (e : Fin a ⊕ Fin b ≃ Fin c) {Λ : Submodule (𝓞 E) (Fin a → E)}
    {Λ' : Submodule (𝓞 E) (Fin b → E)} {β : GL (Fin a) (E ⊗[F] Formalism.L2.Herm.Af F)} {β' : GL (Fin b) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (h : IsFrame β Λ) (h' : IsFrame β' Λ') : IsFrame (blkGL e (β, β')) (sumLat e Λ Λ') := by
  intro x
  rw [← pairVec_eta e x, pairVec_mem_hatL, h, h']
  change _ ↔ ∀ i, (blkMat e (β⁻¹).val (β'⁻¹).val *ᵥ _) i ∈ _
  rw [blkMat_mulVec]
  refine ⟨fun H j => ?_, fun H => ⟨fun i => ?_, fun i => ?_⟩⟩
  · obtain ⟨i | i, rfl⟩ := e.surjective j
    · rw [pairVec_inl]; exact H.1 i
    · rw [pairVec_inr]; exact H.2 i
  · have := H (e (.inl i)); rwa [pairVec_inl] at this
  · have := H (e (.inr i)); rwa [pairVec_inr] at this

theorem isFrame_neg {a : ℕ} {Λ : Submodule (𝓞 E) (Fin a → E)} {β : GL (Fin a) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (h : IsFrame β Λ) : IsFrame (-β) Λ := by
  intro x
  rw [h, inv_neg, Units.val_neg, neg_mulVec]
  exact forall_congr' fun i => neg_mem_iff.symm

theorem int_change {a : ℕ} {Λ : Submodule (𝓞 E) (Fin a → E)} {β β' : GL (Fin a) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (h : IsFrame β Λ) (h' : IsFrame β' Λ) (i j : Fin a) : (β'⁻¹ * β).val i j ∈ Formalism.L2.Herm.intAf F E := by
  have h1 := (h (β.val *ᵥ Pi.single j 1)).2 fun l => by
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec, Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  have h2 := (h' _).1 h1 i
  rwa [mulVec_mulVec, mulVec_single_one] at h2

end Lat

variable {D : D7}

theorem isEquiv_val (w : Pl D.host.E) :
    (ValuativeRel.valuation (Kw w)).IsEquiv (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))) :=
  haveI : (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  ValuativeRel.isEquiv _ _

theorem change_mem_KO {a : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {β β' : GL (Fin a) (Formalism.IndefR.Lev.EAf D)}
    (h : IsFrame β Λ) (h' : IsFrame β' Λ) (w : Pl D.host.E) : (loc w β')⁻¹ * loc w β ∈ KO (Kw w) (Fin a) := by
  have key : ∀ {β β' : GL (Fin a) (Formalism.IndefR.Lev.EAf D)}, IsFrame β Λ → IsFrame β' Λ → ∀ i j,
      ((loc w β')⁻¹ * loc w β).val i j ∈ (ValuativeRel.valuation (Kw w)).integer := fun {β β'} h h' i j => by
    have h2 := (mem_OA_iff _).1 (int_change h h' i j) w
    rw [← map_inv, ← map_mul]
    exact (isEquiv_val w).le_one_iff_le_one.2 h2
  refine (mem_KO_iff _).2 ⟨key h h', ?_⟩
  rw [_root_.mul_inv_rev, inv_inv]
  exact key h' h

theorem reGL_mem_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b) {g : GL a k} (hg : g ∈ KO k a) :
    GlobalTheory.StepData.reGL e g ∈ KO k b := by
  obtain ⟨h1, h2⟩ := (mem_KO_iff _).1 hg
  refine (mem_KO_iff _).2 ⟨fun i j => h1 _ _, fun i j => ?_⟩
  rw [← map_inv]
  exact h2 _ _

theorem scalar_mem_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a : Type} [Fintype a] [DecidableEq a] (u : kˣ) (hu : ValuativeRel.valuation k u = 1) :
    Units.map (Matrix.scalar a).toMonoidHom u ∈ KO k a := by
  have key : ∀ u : kˣ, ValuativeRel.valuation k u = 1 → ∀ i j,
      (Units.map (Matrix.scalar a).toMonoidHom u).val i j ∈ (ValuativeRel.valuation k).integer := fun u hu i j => by
    change Matrix.diagonal (fun _ => (u : k)) i j ∈ _
    rw [diagonal_apply]
    split_ifs
    exacts [hu.le, zero_mem _]
  refine (mem_KO_iff _).2 ⟨key u hu, ?_⟩
  rw [← map_inv]
  exact key _ (by rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one])

theorem val_xiAt (w : Pl D.host.E)
    (hw : ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) :
    ValuativeRel.valuation (Kw w) (xiAt w) = 1 := by
  have hn : ∀ n : ℕ, n ∣ D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK → w.valuation D.host.E (n : D.host.E) = 1 := by
    rintro n ⟨m, hm⟩
    have : (n : 𝓞 D.host.E) ∉ w.asIdeal := fun h => hw (by rw [hm, Nat.cast_mul]; exact Ideal.mul_mem_right _ _ h)
    have := (w.valuation_eq_one_iff_notMem (K := D.host.E)).2 this
    rwa [map_natCast] at this
  have h1 := hn _ (dvd_mul_left _ _)
  have h2 := hn D.host.d (Dvd.dvd.mul_right (dvd_mul_left _ _) _)
  have h3 : w.valuation D.host.E D.host.sqrtMinusD = 1 := by
    have := congrArg (w.valuation D.host.E) D.host.sqrtMinusD_sq
    rw [map_pow, Valuation.map_neg, h2] at this
    exact (pow_eq_one_iff_of_nonneg zero_le' two_ne_zero).1 this
  have h4 : w.valuation D.host.E D.host.xi0 = 1 := by
    unfold Formalism.BasicNotions.Host.xi0
    rw [map_div₀, map_mul, h1, h3, Valuation.map_neg, map_one, mul_one, div_one]
  refine (isEquiv_val w).eq_one_iff_eq_one.2 ?_
  exact (w.valuedAdicCompletion_eq_valuation' _).trans h4

theorem changes_mem_KO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (B : Frames G) (t : T) (i j : Fin D.R.m) (X : TriG G i j), SquareStanding G t →
      IsFrame X.rA.β (G.Λ (.grid (i + 1) (j + 1))) → IsFrame X.rA'.β (G.Λ (.grid i j)) → IsFrame X.rW.β (latX G i j) →
      ∀ w ∈ locPl G t, chA B t X w ∈ KO (Kw w) _ ∧ chB B t X w ∈ KO (Kw w) _ ∧ chX B t X w ∈ KO (Kw w) _ := by
  intro D T L sc G μ₀ hL B t i j X hS hA hA' hW w hw
  refine ⟨reGL_mem_KO _ (invT_mem_KO (change_mem_KO (B.isFrame_β hL i.2 j.2) hA w)),
    reGL_mem_KO _ (mul_mem (scalar_mem_KO _ (val_xiAt w (hS.2 w hw))) (change_mem_KO (B.isFrame_β hL i.2.le j.2.le) hA' w)),
    reGL_mem_KO _ (change_mem_KO hW (isFrame_blkGL finSumFinEquiv (B.isFrame_β hL i.2.le j.2)
      (isFrame_neg (B.isFrame_β hL i.2 j.2.le))) w)⟩

end GlobalTheory.TopFlip.ChKO

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieTateLociClosedSiegelPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_lie_tate_loci_closed_siegelPullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (πX : X ⟶ S) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (φX : AX.left ⟶ c.A.left) (φ₂X : (G2 AX).left ⟶ (G2 c.A).left) (actX : OActN D.O AX) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)), IsGrpPullback AX c.A πX φX → IsSquare φX φ₂X → RosatiFor D actX (c.P.pull φ₂X) → EtaOK D N actX ηX → ∃ (Z : Scheme.{0}) (j : Z ⟶ X), IsClosedImmersion j ∧ ∀ (T : Scheme.{0}) (g : T ⟶ X), (∃ z : T ⟶ Z, z ≫ j = g) ↔ ((∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ T), x ≫ g ≫ πX ≫ t = spMap β → LieHer b actX β (x ≫ g)) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T) (β : R →+* k), x ≫ g ≫ πX ≫ t = spMap β → GeomAt D N actX (c.P.pull φ₂X) ηX k (x ≫ g)) := by
  first | (exact @GlobalTheory.UPel.HT.lieGeom_locus_closed) | (exact GlobalTheory.UPel.HT.lieGeom_locus_closed) | (intros; apply GlobalTheory.UPel.HT.lieGeom_locus_closed  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianWittIndexEqZeroDefiniteBottom
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

namespace GlobalTheory.BottomWitt

theorem wittIndex_eq_zero :
    GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, wittIndex WW = 0 := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro W i j A A' WW X h _
  exact GlobalTheory.Cusp.wittIndex_eq_zero_iff_isAniso.2 (GlobalTheory.Mem.ColAd.isAniso_of_gram h.stdW.1)

end GlobalTheory.BottomWitt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomDegreeIntegerCombinationIsHomogeneous
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.AV.AbVar.multilinear_quadratic_isHomogeneous' (P : Type*) [AddCommGroup P] (g n : ℕ)
    (M : (Fin g → P) →ₘₗ[ℤ] ℤ) (a : Fin n → Fin n → P) :
    ∃ F : MvPolynomial (Fin n) ℤ, F.IsHomogeneous (2 * g) ∧
      ∀ m : Fin n → ℤ, MvPolynomial.eval m F = M (fun _ => ∑ i, ∑ j, (m i * m j) • a i j) := by
  let φ : (Fin n → Fin n → ℤ) →ₗ[ℤ] P :=
    { toFun := fun x => ∑ i, ∑ j, x i j • a i j
      map_add' := fun x y => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }
  let e : Fin n → Fin n → (Fin n → Fin n → ℤ) := fun i j => Pi.single i (Pi.single j 1)
  have he : ∀ i j, φ (e i j) = a i j := by
    intro i j
    simp only [φ, e, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]
    rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
    simp
  obtain ⟨F, hF, hFe⟩ := GlobalTheory.multilinear_quadratic_isHomogeneous (Fin n → Fin n → ℤ) g n
    (M.compLinearMap (fun _ => φ)) e
  refine ⟨F, hF, fun m => ?_⟩
  rw [hFe m, MultilinearMap.compLinearMap_apply]
  congr 1
  simp only [map_sum, map_smul, he]

theorem GlobalTheory.AV.AbVar.deg_isHomogeneousPoly : ∀ (K : Type) [Field K] (A B : AbVar K), A.dim = B.dim → ∀ (n : ℕ) (f : Fin n → (A ⟶ B)), ∃ F : MvPolynomial (Fin n) ℚ, F.IsHomogeneous (2 * A.dim) ∧ ∀ m : Fin n → ℤ, MvPolynomial.eval (fun i => (m i : ℚ)) F = (deg (∑ i, m i • f i) : ℚ) := by
  intro K _ A B hAB n f
  obtain ⟨c, hamp, hsym⟩ := GlobalTheory.AV.AbVar.exists_symm_ample K B
  obtain ⟨⟨M, hM⟩, -⟩ := GlobalTheory.T.intersection_number_multilinear_symm K A (Fin A.dim) (Fintype.card_fin _)
  set D : ℤ := inter B (fun _ : Fin A.dim => c) with hD
  have hDpos : 0 < D := GlobalTheory.T.abelianVariety_topSelfIntersection_ample_pos K B c hamp (Fin A.dim) (by rw [Fintype.card_fin, hAB])
  obtain ⟨F, hFh, hFe⟩ := GlobalTheory.AV.AbVar.multilinear_quadratic_isHomogeneous' (Pic A.X.left) A.dim n M
    (fun i j => AbVar.lam c (f i).hom (f j).hom)
  refine ⟨MvPolynomial.C ((1 : ℚ) / ((2 : ℚ) ^ A.dim * D)) * MvPolynomial.map (Int.castRingHom ℚ) F, ?_, ?_⟩
  · have := (MvPolynomial.isHomogeneous_C (Fin n) ((1 : ℚ) / ((2 : ℚ) ^ A.dim * D))).mul (hFh.map (Int.castRingHom ℚ))
    rwa [zero_add] at this
  · intro m
    have hq := GlobalTheory.T.two_smul_pullback_symmetric_class_integral_combination K A B c hsym n f m
    have hp := GlobalTheory.T.intersection_pullback_eq_degree_mul_intersection K A B (show A ⟶ B from ∑ i, m i • f i) hAB (Fin A.dim) (Fintype.card_fin _) (fun _ => c)
    have key : MvPolynomial.eval m F = 2 ^ A.dim * ((deg (show A ⟶ B from ∑ i, m i • f i) : ℤ) * D) := by
      rw [hFe m, ← hq, ← hp, ← hM]
      simpa only [RingHom.id_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul, two_smul ℕ, two_smul ℤ] using
        M.map_smul_univ (fun _ => (2 : ℤ))
          (fun _ => CechPic.pull (Hom.hom (show A ⟶ B from ∑ i, m i • f i)).left c)
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_map]
    have e2 : MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun i => (m i : ℚ)) F = ((MvPolynomial.eval m F : ℤ) : ℚ) := by
      rw [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, ← eq_intCast (Int.castRingHom ℚ), MvPolynomial.eval₂_comp_left]
      rfl
    rw [e2, key]
    have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
    push_cast
    field_simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicLocalizationStrictHenselisationNoTorsion
section
open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory

theorem pic_localization_strictHenselisation_no_torsion : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)] (q : ℕ), (IsDomain T ∧ ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) → IsUnit (q : T) → 0 < q → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra (Polynomial T) A) (_ : Algebra.Etale (Polynomial T) A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[(Polynomial T)] Si i)) → ∀ c : CommRing.Pic (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))), c ^ q = 1 → c = 1 := by
  intro T O _ _ _ _ _ _ _ _ _ q hT hq hq0 hSi c hc
  obtain ⟨P, hP, φ, hφ, hsh⟩ := GlobalTheory.StrictHensUnion.isStrictHenselisation_of_directed_union T O hSi
  haveI : IsLocalRing O := hsh.1.toIsLocalRing
  obtain ⟨ζ, hζ, hζu⟩ := GlobalTheory.exists_pow_eq_one_isUnit_one_sub_pow T q hq0 hq hT.2
  refine GlobalTheory.T.picard_torsion_trivial_of_torsors_have_sections _ q hq0 ?_ ⟨algebraMap T _ ζ, ?_, ?_⟩ ?_ c hc
  · simpa using hq.map (algebraMap T (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))))
  · rw [← map_pow, hζ, map_one]
  · intro k hk hkq
    simpa using (hζu k hk hkq).map (algebraMap T (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))))
  · intro D _ _ h1 h2 h3 act hact
    exact GlobalTheory.LocAcyc.torsor_trivial T O hT.2 P φ hφ hsh q hq0 hq D h1 h2 h3 act hact

end GlobalTheory
end

