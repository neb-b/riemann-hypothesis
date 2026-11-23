module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0487
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0117
public import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0586
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0474
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0472
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1468
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2724
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0511
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableThetaLocalSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankSelfDualUnitary
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0585
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightBaseParEqNegLowestKType
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open GlobalTheory.ChiGrid GlobalTheory.RowReal GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal.BaseWeights

theorem mem_tparBlock {c x : ℚ} {n : ℕ} (h : x ∈ GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block c n) : x ∈ TPar.block c n := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 h
  exact Finset.mem_image.2 ⟨a, Finset.mem_range.2 (List.mem_range.1 ha), rfl⟩

theorem basePar_sublist {S : Sizes} (P : Entries S) : P.basePar.Sublist P.orderList := by
  have h1 : ∀ l : List (Fin (S.k - 1)),
      (l.map fun i => (P.v i : ℚ)).Sublist (l.flatMap fun i => [(P.v i : ℚ), P.u i]) := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.flatMap_cons, List.cons_append, List.nil_append]
      exact (ih.cons _).cons₂ _
  unfold Entries.basePar Entries.orderList
  exact List.Sublist.append ((h1 _).trans (List.sublist_append_right _ _)) (List.Sublist.refl _)

theorem base_mem_Dpar (D : D7) (C : ℝ) (τ : D.what₂.Tau) :
    ∀ x ∈ (rowEntries D C τ).basePar, ∃ s, (x, s) ∈ (Ptw D).Dpar D.R.m τ := by
  have hodd : ¬ Odd D.R.m := Nat.not_odd_iff_even.2 D.R.m_even
  obtain ⟨hv, hb, he⟩ := GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D C) (cen D C τ)
  intro x hx
  simp only [Entries.basePar, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons, List.mem_finRange,
    true_and] at hx
  unfold TPar.Dpar
  rcases hx with ⟨i, rfl⟩ | ⟨j, h | h⟩
  · refine ⟨true, Finset.mem_image.2 ⟨((Ptw D).v τ i, true), ?_, ?_⟩⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    · simp only [hodd, if_false, add_zero]
      exact Prod.ext (hv i) rfl
  · refine ⟨decide ((j : ℕ) ≤ D.R.m ∨ Even ((j : ℕ) - D.R.m)), Finset.mem_image.2 ⟨(-(Ptw D).b τ j, decide ((j : ℕ) ≤ D.R.m ∨ Even ((j : ℕ) - D.R.m))), ?_, ?_⟩⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
    · simp only [hodd, if_false, add_zero]
      refine Prod.ext ?_ rfl
      rw [h]
      show -(D.hc τ).b j = _
      rw [hb j]; rfl
  · refine ⟨true, Finset.mem_image.2 ⟨(x, true), ?_, ?_⟩⟩
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, j.2⟩, ?_⟩)
      refine Finset.mem_image.2 ⟨x, ?_, rfl⟩
      have hx' := mem_tparBlock h
      have : (-(Ptw D).e τ j) = -(((rowEntries D C τ).e j : ℤ) : ℚ) := by
        show -(D.hc τ).e j = _
        rw [he j]; rfl
      rw [this]
      exact hx'
    · simp only [hodd, if_false, add_zero]

end GlobalTheory.RowReal.BaseWeights

namespace GlobalTheory.RowReal

open GlobalTheory.RowReal.BaseWeights

theorem hw_basePar_eq_neg_lowK : ∀ (D : D7) (C : ℝ)
    (M : Formalism.IndefR.Mult.DSModel D.sp.X' (Formalism.IndefR.Mult.parB (Ptw D) D.R.m)) (τ : D.what₂.Tau)
    (i : Fin D.sp.X'.rank),
    (hw (rowEntries D C τ).basePar i : ℝ) = -(Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) (Fin.rev i) := by
  intro D C M τ i
  have hlen : (rowEntries D C τ).basePar.length = D.sp.X'.rank := by
    rw [length_base, D.sp.X'_rank]
    simp [Sizes.nC, rowSizes, Ranks.rankX', Ranks.r]
  have hε : M.ε τ = Formalism.MainNotions.S.allPos _ := funext fun a => GlobalTheory.DefiniteMult.allPlus_parB _ (Nat.sub_le _ _) M τ a
  obtain ⟨hanti, q, hq, hS⟩ := M.enum τ
  have hqa : StrictAnti q := fun a b h => by
    have := hanti h
    rw [hq, hq] at this
    exact_mod_cast this
  have hinj : Function.Injective fun a => -q a := fun a b h => hqa.injective (neg_injective h)
  have hE : (Finset.univ.image fun a => -q a).card = D.sp.X'.rank := by
    rw [Finset.card_image_of_injective _ hinj]; simp
  have hpw := (rowEntries_good D C τ).order.sublist (basePar_sublist (rowEntries D C τ))
  let f : Fin D.sp.X'.rank → ℚ := fun j => (rowEntries D C τ).basePar[(j : ℕ)]'(by rw [hlen]; exact j.2)
  have hf : StrictAnti f := fun a b hab => List.pairwise_iff_getElem.1 hpw _ _ _ _ hab
  have hfm : ∀ j, f j ∈ Finset.univ.image fun a => -q a := by
    intro j
    obtain ⟨s, hs⟩ := base_mem_Dpar D C τ _ (List.getElem_mem (by rw [hlen]; exact j.2))
    have h2 : (-(f j), s) ∈ Formalism.IndefR.Mult.parB (Ptw D) D.R.m τ := Finset.mem_image.2 ⟨_, hs, rfl⟩
    rw [hS] at h2
    obtain ⟨a, -, ha⟩ := Finset.mem_image.1 h2
    refine Finset.mem_image.2 ⟨a, Finset.mem_univ _, ?_⟩
    have h3 := congrArg Prod.fst ha
    simp only at h3
    rw [h3, neg_neg]
  let g : Fin D.sp.X'.rank → ℚ := fun j => -q j.rev
  have hg : StrictAnti g := fun a b hab => by
    simp only [g, neg_lt_neg_iff]
    exact hqa (Fin.rev_lt_rev.2 hab)
  have hgm : ∀ j, g j ∈ Finset.univ.image fun a => -q a := fun j => Finset.mem_image.2 ⟨j.rev, Finset.mem_univ _, rfl⟩
  have hfg : f = g := (GlobalTheory.SignedHC.descEnum_unique hE hf hfm).symm.trans (GlobalTheory.SignedHC.descEnum_unique hE hg hgm)
  have hi : (i : ℕ) < (rowEntries D C τ).basePar.length := by rw [hlen]; exact i.2
  have key : (rowEntries D C τ).basePar[(i : ℕ)] = -q i.rev := congrFun hfg i
  have h1 := hw_base _ i hi
  have hl : (((rowEntries D C τ).basePar.length : ℕ) : ℚ) = (D.sp.X'.rank : ℚ) := by rw [hlen]
  rw [hl, key] at h1
  rw [hε, GlobalTheory.ConjTypeW.lowK_allPos, hq]
  have h4 : (hw (rowEntries D C τ).basePar i : ℝ) = (((hw (rowEntries D C τ).basePar i : ℤ) : ℚ) : ℝ) := by push_cast; rfl
  rw [h4, h1, Fin.val_rev]
  have h5 : (i : ℕ) + 1 ≤ D.sp.X'.rank := i.2
  rw [Nat.cast_sub h5]
  push_cast
  ring

end GlobalTheory.RowReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaAtHalfExtensionLatticeIndicatorFn
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.CosetRow

section ThetaExt
variable {D : D7} {m n : ℕ}

theorem isHalf_add_right_iff {e : AE D} {t x : Mx D m n} (hx : IsHalf e x) :
    IsHalf e (t + x) ↔ IsHalf e t := by
  constructor
  · intro h i j
    have h1 := h i j
    have h2 := hx i j
    simp only [Matrix.add_apply, mul_add] at h1
    linear_combination h1 - h2
  · intro h i j
    have h1 := h i j
    have h2 := hx i j
    simp only [Matrix.add_apply, mul_add]
    linear_combination h1 + h2

theorem smul_of_isHalf {e : AE D} {x : Mx D m n} (hx : IsHalf e x) : e • x = x := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact hx i j

theorem smul_eq_zero_of_isHalf {e e' : AE D} (h : e' * e = 0) {x : Mx D m n} (hx : IsHalf e x) : e' • x = 0 := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
  rw [← hx i j, ← mul_assoc, h, zero_mul]

theorem isHalf_smul_idem {e : AE D} (he : e * e = e) (t : Mx D m n) : IsHalf e (e • t) := by
  intro i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [← mul_assoc, he]

def extLin (e₀ e₁ : AE D) (Λ : AddSubgroup (Mx D m n)) : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ) where
  toFun := extFn e₀ e₁ Λ
  map_add' Φ Ψ := by
    funext t
    simp only [extFn, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c Φ := by
    funext t
    simp only [extFn, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem extFn_shift {e₀ e₁ : AE D} (h10 : e₁ * e₀ = 0) (Λ : AddSubgroup (Mx D m n)) (Φ : Mx D m n → ℂ)
    {x : Mx D m n} (hx : IsHalf e₀ x) :
    extFn e₀ e₁ Λ (fun t => Φ (t + x)) = fun t => extFn e₀ e₁ Λ Φ (t + x) := by
  funext t
  have hx' : IsHalf (e₀ + e₁) x := by
    rw [add_comm]; exact GlobalTheory.VecProd.half_add_of_right h10 hx
  simp only [extFn]
  rw [isHalf_add_right_iff hx', smul_add, smul_add, smul_of_isHalf hx, smul_eq_zero_of_isHalf h10 hx, add_zero]

theorem extFn_modul {e₀ e₁ : AE D} (Λ : AddSubgroup (Mx D m n)) (Φ : Mx D m n → ℂ) (g : Mx D m n → ℂ)
    (hg : ∀ t, IsHalf (e₀ + e₁) t → g t = g (e₀ • t)) :
    extFn e₀ e₁ Λ (fun t => g t * Φ t) = fun t => g t * extFn e₀ e₁ Λ Φ t := by
  funext t
  simp only [extFn]
  split_ifs with h
  · rw [hg t h]; ring
  · ring

theorem extFn_halfInd {e₀ e₁ : AE D} (h00 : e₀ * e₀ = e₀) (h11 : e₁ * e₁ = e₁) {Λ : AddSubgroup (Mx D m n)}
    (hΛ0 : ∀ u ∈ Λ, e₀ • u ∈ Λ) (hΛ1 : ∀ u ∈ Λ, e₁ • u ∈ Λ) :
    extFn e₀ e₁ Λ (halfInd e₀ Λ) = halfInd (e₀ + e₁) Λ := by
  funext t
  simp only [extFn, halfInd]
  by_cases ht : IsHalf (e₀ + e₁) t
  · have hdec : t = e₀ • t + e₁ • t := by
      rw [← add_smul, smul_of_isHalf ht]
    have hiff : (e₀ • t ∈ Λ ∧ e₁ • t ∈ Λ) ↔ t ∈ Λ := by
      constructor
      · rintro ⟨h0, h1⟩; rw [hdec]; exact Λ.add_mem h0 h1
      · intro h; exact ⟨hΛ0 t h, hΛ1 t h⟩
    have a0 := isHalf_smul_idem h00 t
    have a1 := isHalf_smul_idem h11 t
    rw [if_pos ht]
    by_cases h0 : e₀ • t ∈ Λ <;> by_cases h1 : e₁ • t ∈ Λ
    · rw [if_pos ⟨h0, a0⟩, if_pos ⟨h1, a1⟩, if_pos ⟨hiff.1 ⟨h0, h1⟩, ht⟩, one_mul]
    · rw [if_pos ⟨h0, a0⟩, if_neg (fun h => h1 h.1), if_neg (fun h => h1 (hiff.2 h.1).2), mul_zero]
    · rw [if_neg (fun h => h0 h.1), if_pos ⟨h1, a1⟩, if_neg (fun h => h0 (hiff.2 h.1).1), zero_mul]
    · rw [if_neg (fun h => h0 h.1), if_neg (fun h => h1 h.1), if_neg (fun h => h0 (hiff.2 h.1).1), zero_mul]
  · simp only [if_neg ht]
    rw [if_neg (fun h => ht h.2)]

theorem isThetaAt_extFn : ∀ {D : D7} {m n : ℕ} {ψ : AddChar (AF D.host.F) ℂ} {B : Mx D m n → Mx D m n → AF D.host.F} {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)} {Λ : AddSubgroup (Mx D m n)} {e₀ e₁ : AE D} {f₀ Φ f : Mx D m n → ℂ}, e₀ * e₀ = e₀ → e₁ * e₁ = e₁ → e₀ * e₁ = 0 → (∀ u ∈ Λ, e₀ • u ∈ Λ) → (∀ u ∈ Λ, e₁ • u ∈ Λ) → (∀ t y, IsHalf (e₀ + e₁) t → IsHalf (cA D e₀) y → B t y = B (e₀ • t) y) → (∃ T, IsPlaceModel ψ B hs (e₀ + e₁) Λ 1 f₀ T) → IsThetaAt ψ B hs e₀ Λ 1 f₀ Φ f → IsThetaAt ψ B hs (e₀ + e₁) Λ 1 f₀ (GlobalTheory.CosetRow.extFn e₀ e₁ Λ Φ) f := by
  intro D m n ψ B hs Λ e₀ e₁ f₀ Φ f h00 h11 h01 hΛ0 hΛ1 hB hex h
  have h10 : e₁ * e₀ = 0 := by rw [mul_comm]; exact h01
  have hsb : ∀ Ψ, IsSBHalf e₀ Λ Ψ → IsSBHalf (e₀ + e₁) Λ (extFn e₀ e₁ Λ Ψ) := fun Ψ hΨ =>
    _root_.GlobalTheory.CosetRow.ExtSB.isSBHalf_extFn h00 h11 h01 hΛ0 hΛ1 hΨ
  refine ⟨hex, fun T hT => ?_⟩
  have hT₀ : IsPlaceModel ψ B hs e₀ Λ 1 f₀ (T ∘ₗ extLin e₀ e₁ Λ) := by
    refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, ?_⟩
    · have hx' : IsHalf (e₀ + e₁) x := by
        rw [add_comm]; exact GlobalTheory.VecProd.half_add_of_right h10 hx
      simp only [LinearMap.comp_apply]
      change T (extFn e₀ e₁ Λ (fun t => Ψ (t + x))) = hs x (T (extFn e₀ e₁ Λ Ψ))
      rw [extFn_shift h10 Λ Ψ hx]
      exact hT.trans _ (hsb Ψ hΨ) x hx'
    · have hy' : IsHalf (cA D (e₀ + e₁)) y := by
        rw [add_comm]; exact GlobalTheory.VecProd.half_conj_add_of_right h10 hy
      simp only [LinearMap.comp_apply]
      change T (extFn e₀ e₁ Λ (fun t => ψ (B t y) * Ψ t)) = hs y (T (extFn e₀ e₁ Λ Ψ))
      rw [extFn_modul Λ Ψ (fun t => ψ (B t y)) (fun t ht => by simp only [hB t y ht hy])]
      exact hT.modul _ (hsb Ψ hΨ) y hy'
    · simp only [LinearMap.comp_apply, one_smul]
      change T (extFn e₀ e₁ Λ (halfInd e₀ Λ)) = f₀
      rw [extFn_halfInd h00 h11 hΛ0 hΛ1]
      simpa using hT.vac
  exact h.2 _ hT₀

end ThetaExt

end GlobalTheory.CosetRow

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetScalarRationalTranslate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.RatMoveJets

theorem unitAt_mul {q : ℕ} [Fact q.Prime] {a b : ℂ} (ha : Mod1All a) (hb : Mod1All b) (hua : GlobalTheory.MovedKappaEx.UnitAt q a)
    (hub : GlobalTheory.MovedKappaEx.UnitAt q b) : GlobalTheory.MovedKappaEx.UnitAt q (a * b) := by
  obtain ⟨ha', -⟩ := ha
  obtain ⟨hb', -⟩ := hb
  intro lam
  have hab : a * b ∈ Qbar := mul_mem ha' hb'
  have e : lamC lam (a * b) = lamC lam a * lamC lam b := by
    unfold lamC
    rw [dite_eq_left hab, dite_eq_left ha', dite_eq_left hb', ← map_mul]
    rfl
  rw [e, norm_mul, hua lam, hub lam, one_mul]

end GlobalTheory.RatMoveJets
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedHomLatticeOfMemLatticeHomCoset
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff

noncomputable section
namespace GlobalTheory.CosLatHalf
open GlobalTheory.RowLatChi Formalism.L2.DIV GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun

theorem smul_mem_latO_of_mem_hatMx' {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) {e : AE D}
    {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P)
    (hAA : ∀ w ∈ P, ∃ a ∈ D.host.AA, Valued.v ((algebraMap D.host.E (Kw w)) a) = 1) {u : WO S T}
    (hm : u ∈ hatMx (homLat ΛS ΛT)) : e • u ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [Finset.sum_smul]
  refine sum_mem fun w hw => ?_
  obtain ⟨a, ha, hv⟩ := hAA w hw
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, Valuation.map_zero] at hv
    exact zero_ne_one hv
  have hc : finPart D (es w * incA D a⁻¹) ∈ intAE D := by
    refine ((comp_toAd D).int (es w * incA D a⁻¹)).2 fun Q => ?_
    show Valued.v (cpt (D := D) Q (toEAf D (es w * incA D a⁻¹))) ≤ 1
    obtain ⟨h1, h2⟩ := cpt_of_isIdemAt (hes w hw)
    rw [RingHom.map_mul, RingHom.map_mul,
      show cpt (D := D) Q (toEAf D (incA D a⁻¹)) = algebraMap D.host.E (Kw Q) a⁻¹ from Comparison₂.cpt_tmul Q a⁻¹]
    rcases eq_or_ne Q w with rfl | hQ
    · rw [h1, one_mul, map_inv₀, map_inv₀, hv, inv_one]
    · rw [h2 Q hQ, zero_mul, Valuation.map_zero]
      exact zero_le
  have e : es w • u = (es w * incA D a⁻¹) • (incA D a • u) := by
    rw [smul_smul, mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ ha0, RingHom.map_one, mul_one]
  rw [e]
  exact GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ hc _ (smul_mem_latO_of_mem_hatMx hS ha hm)

end GlobalTheory.CosLatHalf


open GlobalTheory.CosLatHalf Formalism.L2.DIV in
theorem GlobalTheory.CosLatHalf.mem_latO_of_mem_cosSet : ∀ {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}, IsSelfDualC S ΛS → ∀ {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)}, IsIdemSum e P → (∀ w ∈ P, ∃ a ∈ D.host.AA, Valued.v ((algebraMap D.host.E (Kw w)) a) = 1) → ∀ {𝔪 : Ideal (𝓞 D.host.E)} (κ : Cos ΛS ΛT 𝔪) {t : WO S T}, t ∈ cosSet e κ → t ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  intro D S T ΛS ΛT hS e P he hAA 𝔪 κ t ht
  obtain ⟨hth, x₀, -, hd⟩ := ht
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hinf : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum he
  let u : WO S T := Matrix.of fun i j => pairA D.host.F 0 1 ⊗ₜ[D.host.F] (x₀ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) i j
  have hu : u ∈ hatMx (homLat ΛS ΛT) := AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact (v.adicCompletionIntegers D.host.F).one_mem, x₀, x₀.2, rfl⟩
  have heu : e • (x₀ : Matrix (Fin T.rank) (Fin S.rank) D.host.E).map (incA D) = e • u := by
    refine Matrix.ext fun i j => GlobalTheory.SplitScalar.adele_ext ?_ ?_
    · simp only [Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, hinf, zero_mul]
    · simp only [Matrix.smul_apply, smul_eq_mul, RingHom.map_mul]
      rfl
  have hd' : t - e • (x₀ : Matrix (Fin T.rank) (Fin S.rank) D.host.E).map (incA D) ∈ hatMx (homLat ΛS ΛT) := by
    refine AddSubgroup.closure_mono ?_ hd
    rintro _ ⟨α, hα, x, hx, rfl⟩
    exact ⟨α, hα, x, Submodule.smul_le_right hx, rfl⟩
  have key : t = e • (t - e • (x₀ : Matrix (Fin T.rank) (Fin S.rank) D.host.E).map (incA D)) + e • u := by
    rw [smul_sub, smul_smul, hee, heu, sub_add_cancel]
    exact Matrix.ext fun i j => (hth i j).symm
  rw [key]
  exact add_mem (smul_mem_latO_of_mem_hatMx' hS he hAA hd') (smul_mem_latO_of_mem_hatMx' hS he hAA hu)
end
end

