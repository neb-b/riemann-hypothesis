module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellDef
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0001
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellBru
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellGeo
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0005
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0003
public import Formalism.SharpRestriction.CuspSpanNormBounds.ThresholdCubicInequalitySignPattern
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CriticalLevelLowOfRefined
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaFactorisation
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CmRingIdempotentUnitRatioIdentity
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.StandardHypothesesOfScaleHyp
public import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TopsChoicePartA
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0012

@[expose] public section

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellFin
section
noncomputable section
namespace Formalism.MainNotions.BridgeLemma
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.LatticeGluingRadicals NumberField Module

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem tie_trace {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) (x : E) : algebraMap F E (Algebra.trace F E x) = x + star x := by
  classical

  have hfix : ∀ c : F, star (algebraMap F E c) = algebraMap F E c :=
    fun c => (hc.fixed _).2 ⟨c, rfl⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hc.deg2]; norm_num)
  let s : E ≃ₐ[F] E :=
    { toFun := star
      invFun := star
      left_inv := star_star
      right_inv := star_star
      map_mul' := fun a b => by rw [star_mul, mul_comm]
      map_add' := star_add
      commutes' := hfix }
  have hs1 : s ≠ 1 := by
    intro h
    have hbot : (⊥ : Subalgebra F E) = ⊤ := by
      refine eq_top_iff.2 fun a _ => ?_
      have ha : star a = a := DFunLike.congr_fun h a
      obtain ⟨c, hc'⟩ := RingHom.mem_range.1 ((hc.fixed a).1 ha)
      exact Algebra.mem_bot.2 ⟨c, hc'⟩
    have h1 : Module.finrank F E = 1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 hbot
    rw [hc.deg2] at h1
    exact absurd h1 (by norm_num)
  have hle : Fintype.card (E ≃ₐ[F] E) ≤ Module.finrank F E := by
    first
      | exact AlgEquiv.card_le
      | exact (Fintype.card_congr (algEquivEquivAlgHom F E)).le.trans AlgHom.card_le
  have hpair : ({1, s} : Finset (E ≃ₐ[F] E)).card = 2 := Finset.card_pair (Ne.symm hs1)
  have hcard : Fintype.card (E ≃ₐ[F] E) = 2 := by
    have hge : ({1, s} : Finset (E ≃ₐ[F] E)).card ≤ Fintype.card (E ≃ₐ[F] E) :=
      Finset.card_le_univ _
    rw [hc.deg2] at hle
    omega
  haveI : IsGalois F E := by
    first
      | exact IsGalois.of_card_aut_eq_finrank F E (by rw [Nat.card_eq_fintype_card, hcard, hc.deg2])
      | exact IsGalois.of_card_aut_eq_finrank F E (by rw [hcard, hc.deg2])
  have huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, s} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, hcard, hpair]
  first
    | rw [trace_eq_sum_automorphisms]
    | rw [Algebra.trace_eq_sum_automorphisms]
  rw [huniv, Finset.sum_pair (Ne.symm hs1)]
  try rfl

theorem tie_aniso (D : D7) (T : ℕ) (hT : 0 < T) (F : LFlag (D.sp.Y 0) D.R.rS (T : D.host.E)) (y : (hS D).V)
    (h1 : ∀ a, (hS D).hT (F.fl.fvec a) y = 0) (h2 : (hS D).hT y y = 0) : y ∈ F.fl.X := by
  by_contra hy
  obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  have hmem : y ∈ orth (hS D) (Xplus F) := by
    rw [p_mem_orth]
    intro x hx
    have hle : Xplus F ≤ LinearMap.ker ((hS D).hT.flip y) := by
      refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
      · rintro _ ⟨a, rfl⟩
        have := h1 a.castSucc
        simpa [FlagG.fvec] using this
      · rintro _ rfl
        have := h1 (Fin.last _)
        simpa [FlagG.fvec] using this
    exact hle hx
  have hp := p_posX D T hT F τ y hmem hy
  unfold nrm at hp
  rw [h2, map_zero] at hp
  simp at hp

end Formalism.MainNotions.BridgeLemma
end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.ClauseAOfIdentityFlag
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.LatticeGluingRadicals NumberField Module

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem tie_Xa_mono (F : FlagG S r T) {a b : ℕ} (h : a ≤ b) : F.Xa a ≤ F.Xa b :=
  Submodule.span_mono (by rintro _ ⟨i, hi, rfl⟩; exact ⟨i, lt_of_lt_of_le hi h, rfl⟩)

theorem tie_e_mem_Xa (F : FlagG S r T) (a : Fin r) : F.e a ∈ F.Xa (a.val + 1) :=
  Submodule.subset_span ⟨a, Nat.lt_succ_self _, rfl⟩

theorem tie_Xa_eq (F : FlagG S r T) (F' : FlagG S r T') (h : ∀ a, F'.e a - F.e a ∈ F.Xa a.val) (j : ℕ) :
    F'.Xa j = F.Xa j := by
  have h1 : ∀ j, F'.Xa j ≤ F.Xa j := by
    intro j
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    have h2 : F'.e a = (F'.e a - F.e a) + F.e a := by abel
    rw [h2]
    exact Submodule.add_mem _ (tie_Xa_mono F (le_of_lt ha) (h a)) (tie_Xa_mono F ha (tie_e_mem_Xa F a))
  refine le_antisymm (h1 j) ?_
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    have h2 : F.e a = F'.e a - (F'.e a - F.e a) := by abel
    rw [h2]
    exact Submodule.sub_mem _ (tie_Xa_mono F' ha (tie_e_mem_Xa F' a))
      (tie_Xa_mono F' (le_of_lt ha) (ih a.val ha (h a)))

theorem tie_X_eq_Xa (F : FlagG S r T) : F.X = F.Xa r := by
  unfold FlagG.X FlagG.Xa
  congr 1
  ext x
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨a, a.isLt, rfl⟩
  · rintro ⟨a, _, rfl⟩; exact ⟨a, rfl⟩

end Gen

section Rec

variable {D : D7}

end Rec

end Formalism.MainNotions.BridgeLemma

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.DecayHypothesisOfLargeConstants
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexOrder
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

theorem compact_to_unitary_hermitian (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool)
    (P g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hP : IsCayleyU k r ε P)
    (hg : g ∈ Formalism.REAL.Kset ε) :
    P⁻¹ * g * P ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∩
      (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _) := by
  have a1 : P.conjTranspose * P = 1 := Matrix.mem_unitaryGroup_iff'.1 hP.2
  have a2 : P * P.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.1 hP.2
  have iP : P⁻¹ = P.conjTranspose := Matrix.inv_eq_left_inv a1
  have gJ : g.conjTranspose * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := (Formalism.REAL.maximal_compact_facts _ ε).1 g hg
  rw [iP]
  constructor
  · show (P.conjTranspose * g * P).conjTranspose * Formalism.QuantumDeterminants.Hpk k r * (P.conjTranspose * g * P) = Formalism.QuantumDeterminants.Hpk k r
    rw [← hP.1.2]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc P.conjTranspose * (g.conjTranspose * P) * (P.conjTranspose * Formalism.REAL.Jm ε * P) * (P.conjTranspose * g * P)
        = P.conjTranspose * (g.conjTranspose * ((P * P.conjTranspose) * Formalism.REAL.Jm ε * (P * P.conjTranspose)) * g) * P := by
          simp only [Matrix.mul_assoc]
      _ = P.conjTranspose * Formalism.REAL.Jm ε * P := by
          rw [a2, Matrix.one_mul, Matrix.mul_one, gJ, Matrix.mul_assoc]
  · have hs : P.conjTranspose ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := by
      rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mem hP.2
    exact mul_mem (mul_mem hs hg.1) hP.2

end Formalism.MainNotions.BridgeLemma

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilySeparationBoundOfNorms
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Finset
open scoped nonZeroDivisors NumberField

def SzfNormDD (D : D7) : Prop :=
  ((FractionalIdeal.absNorm (ddE D) : ℚ) : ℝ) = (D.host.rdE ^ D.R.f) ^ 2

theorem szf_card_Tau (D : D7) : Fintype.card D.what₂.Tau = D.R.f := by
  rw [← Nat.card_eq_fintype_card, Nat.card_congr D.eTau]
  exact (factCardPsi D.R D.host).1

end Formalism.MainNotions.BridgeLemma

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SmoothBigCellSectionsExist
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.MainNotions.S.LocalFrameAxioms Formalism.MainNotions.LocalBesselAndTopKernel Formalism.QuantumDeterminants NumberField IsDedekindDomain ValuativeRel
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Steps

variable (D) (large₂ : SizeData₂ D) (X : TermTie D) (Cw : ℝ) (Y : ∀ u u', LoopTie D large₂ X u u' Cw) (Z : TermLocs D X)
  (cN : D.what₂.Word → D.what₂.Word → ℝ) (Vm : ValMap D.R.k D.R.rS)

end Steps

theorem Dstar_pos (D : D7) : 0 < D.what₂.Dstar := by
  rw [← D.Dstar_eq D.u₀]; exact (D.mem D.u₀).A.Dstar_pos

theorem section_exists : ∀ (k r : ℕ) (L : LocBessel k r), 1 ≤ k → ∃ μsec, IsSection k r L.z L.z' μsec
  | 0, _, _, h => absurd h (by norm_num)
  | _ + 1, _, L, _ => Formalism.MainNotions.S.Inh.big_cell_section_of_local_bessel L


section MassDataStep

variable (D) (large₂ : SizeData₂ D) (X : TermTie D) (Cw : ℝ) (Y : ∀ u u', LoopTie D large₂ X u u' Cw) (Z : TermLocs D X)
  (cN : D.what₂.Word → D.what₂.Word → ℝ)


end MassDataStep

section RowsLemmas

open Finset
open scoped ComplexOrder

end RowsLemmas

section RowsAbstract

open Finset
open scoped ComplexOrder

variable {P ι : Type}

variable {Tau : Type} [Fintype Tau] (HSv : Tau → Type) (ip : ∀ v, HSv v → HSv v → ℂ) (n : P → ℝ) (c c0 : ι → P → ℂ)
  (V : ∀ v, P → HSv v) (cW : ℝ)

end RowsAbstract

theorem ptEntry_col {K : Type} [Zero K] : ∀ (bs : List (K × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) →
    ∀ j, j < (bs.map Prod.snd).sum → ∃ i, i < (bs.map Prod.snd).sum ∧ ∃ t : K, t ≠ 0 ∧
      ∀ j', ptEntry bs i j' = if j' = j then t else 0 := by
  intro bs
  induction bs with
  | nil =>
    intro _ j hj
    exact absurd hj (by simp)
  | cons b rest ih =>
    obtain ⟨t, s⟩ := b
    intro h j hj
    simp only [List.map_cons, List.sum_cons] at hj ⊢
    by_cases hjs : j < s
    · refine ⟨s - 1 - j, by omega, t, (h (t, s) (by simp)).1, fun j' => ?_⟩
      simp only [ptEntry]
      by_cases hj' : j' = j
      · subst hj'
        rw [if_pos ⟨by omega, hjs⟩, if_pos (by omega), if_pos rfl]
      · rw [if_neg hj']
        by_cases h2 : j' < s
        · rw [if_pos ⟨by omega, h2⟩, if_neg (by omega)]
        · rw [if_neg (fun hh => h2 hh.2), if_neg (fun hh => by omega)]
    · have hrest : ∀ b ∈ rest, b.1 ≠ 0 ∧ 1 ≤ b.2 :=
        fun b hb => h b (List.mem_cons_of_mem _ hb)
      have hjrest : j - s < (rest.map Prod.snd).sum := by omega
      obtain ⟨i0, hi0, t0, ht0, h0⟩ := ih hrest (j - s) hjrest
      refine ⟨i0 + s, by omega, t0, ht0, fun j' => ?_⟩
      simp only [ptEntry]
      rw [if_neg (fun hh => by omega)]
      by_cases h2 : s ≤ j'
      · rw [if_pos ⟨by omega, h2⟩, Nat.add_sub_cancel, h0]
        by_cases hj' : j' = j
        · rw [if_pos (by omega), if_pos hj']
        · rw [if_neg (by omega), if_neg hj']
      · rw [if_neg (fun hh => h2 hh.2), if_neg (by omega)]

theorem ptMat_det_ne {K : Type} [Field K] {n : ℕ} (p : Point K n) : (ptMat p).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  apply hv
  funext j
  obtain ⟨i, hi, t, ht, hcol⟩ := ptEntry_col p.1 p.2.1 j.val (by rw [p.2.2]; exact j.2)
  have h1 := congrFun h0 ⟨i, by rw [← p.2.2]; exact hi⟩
  simp only [Matrix.mulVec, dotProduct, ptMat, hcol, Pi.zero_apply] at h1
  rw [Finset.sum_eq_single j (fun b _ hb => by rw [if_neg (fun hh => hb (Fin.ext hh)), zero_mul])
    (fun hh => absurd (Finset.mem_univ j) hh), if_pos rfl] at h1
  exact (mul_eq_zero.1 h1).resolve_left ht

theorem Dmin_top_ne (w : Point D.host.E (D.R.rS + 1)) : LocalSplitGroups.Dmin w (D.R.rS + 1) ≠ 0 := by
  unfold LocalSplitGroups.Dmin
  rw [dite_eq_left le_rfl]
  have : (ptMat w).submatrix (Fin.castLE (le_refl (D.R.rS + 1))) (Fin.castLE (le_refl (D.R.rS + 1))) = ptMat w := by
    ext a b; rfl
  rw [this]
  exact ptMat_det_ne w

section RowsStep

open Finset
open scoped ComplexOrder

variable (D) (large₂ : SizeData₂ D) (X : TermTie D) (Cw : ℝ) (Y : ∀ u u', LoopTie D large₂ X u u' Cw) (Z : TermLocs D X)
  (cN : D.what₂.Word → D.what₂.Word → ℝ) (Vm : ValMap D.R.k D.R.rS)

end RowsStep

section Dens

variable (D) (X : TermTie D) (Z : TermLocs D X)

end Dens

end Formalism.MainNotions.BridgeLemma

end
end

