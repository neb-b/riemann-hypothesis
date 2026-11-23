module

public import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0004
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0002
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle0001
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK

@[expose] public section

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.AutLzFiniteOfLoop
section
noncomputable section

section A
open Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.MainNotions.S.Lem.Comparison₂

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem z_mem_orth {T : E} (F : LFlag S r T) : F.fl.z ∈ orth S (Xsp F) := by
  have key : ∀ y ∈ Submodule.span E (Set.range F.fl.e), S.hT y F.fl.z = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨b, rfl⟩ := hw
      exact F.fl.z_orth b
    | zero => simp
    | add w v _ _ h1 h2 => simp [h1, h2]
    | smul c w _ h => simp [h]
  show F.fl.z ∈ ⨅ x ∈ Xsp F, LinearMap.ker (S.hT x)
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  intro x hx
  exact key x hx

end Formalism.MainNotions.S.Lem.Comparison₂

end A

section B
open Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.MainNotions.S.Lem.Comparison₂

theorem one_mem_NLam {D : D7} (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) :
    (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ NLam Λ F := by
  simp only [NLam, IsAutLam, Set.mem_setOf_eq]
  refine ⟨⟨?_, ?_⟩, fun j x _ => by simp, fun x _ => by simp⟩
  · exact (Formalism.HermitianLatticesTheory.isom _).one_mem
  · ext x
    simp [Formalism.HermitianLatticesTheory.gmap]

end Formalism.MainNotions.S.Lem.Comparison₂
end B

section C
open scoped Classical
namespace Formalism.MainNotions.S.Lem.Cnt
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cntSW_eq (D : D7) {T : D.host.E} (T' : D.host.E) (F : LFlag (D.sp.Y 0) D.R.rS T) (Λ : LatV D) (Z : GramM D) :
    cntSW D T' F Λ Z =
      cntCl {F' : LFlag (D.sp.Y 0) D.R.rS T' | IsTerm Λ (gS D) F F' ∧ FrameOK D Λ F' ∧ IsGeneric Λ (gS D) F F' ∧ ZEquiv (ZhatL F F') Z}
        (TEqv D Λ F) := rfl

theorem card_le_cntCl {α ι : Type} (X : Set α) (R : α → α → Prop) (hR : ∀ a ∈ X, R a a) (f : ι → α) (hf : ∀ i, f i ∈ X)
    (hinj : ∀ i j, R (f i) (f j) → i = j) : ENat.card ι ≤ cntCl X R := by
  let g : ι → {O : Set α | ∃ a ∈ X, O = {b | b ∈ X ∧ R a b}} :=
    fun i => ⟨{b | b ∈ X ∧ R (f i) b}, f i, hf i, rfl⟩
  have hg : Function.Injective g := by
    intro i j hij
    have h2 : ({b | b ∈ X ∧ R (f i) b} : Set α) = {b | b ∈ X ∧ R (f j) b} := congrArg Subtype.val hij
    have h3 : f j ∈ ({b | b ∈ X ∧ R (f j) b} : Set α) := ⟨hf j, hR _ (hf j)⟩
    rw [← h2] at h3
    exact hinj i j h3.2
  unfold cntCl
  first
    | exact ENat.card_le_card_of_injective hg
    | (rw [← ENat.card_coe_set_eq]; exact ENat.card_le_card_of_injective hg)

theorem one_mem_NLam (D : D7) (Λ : LatV D) {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) :
    (LinearEquiv.refl D.host.E (hS D).V) ∈ NLam Λ F := by
  simp only [NLam, IsAutLam, Set.mem_setOf_eq]
  refine ⟨⟨?_, ?_⟩, fun j x _ => by simp, fun x _ => by simp⟩
  · first
      | exact (Formalism.HermitianLatticesTheory.isom _).one_mem
      | exact fun _ _ => rfl
  · ext x
    simp [Formalism.HermitianLatticesTheory.gmap]

theorem frameEqv_refl (D : D7) {T' : D.host.E} (F' : LFlag (D.sp.Y 0) D.R.rS T') :
    FrameEqv D (LinearEquiv.refl D.host.E (VS D).V) F' F' := by
  unfold FrameEqv
  refine ⟨1, fun a b hab => Matrix.one_apply_ne (ne_of_lt hab).symm, fun a => Matrix.one_apply_eq a, ?_⟩
  funext b
  simp only [frameAct, LinearEquiv.refl_apply]
  rw [Finset.sum_eq_single b]
  · simp
  · intro a _ hab
    rw [Matrix.one_apply_ne hab]
    simp
  · intro hb
    exact absurd (Finset.mem_univ b) hb

theorem TEqv_refl (D : D7) (Λ : LatV D) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') :
    TEqv D Λ F F' F' := by
  unfold TEqv
  exact ⟨LinearEquiv.refl _ _, one_mem_NLam D Λ F, frameEqv_refl D F'⟩

theorem PEqv_refl (D : D7) (Λ : LatV D) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (p : Trip D T') :
    PEqv D Λ F p p := by
  unfold PEqv
  exact ⟨LinearEquiv.refl _ _, one_mem_NLam D Λ F, LinearEquiv.refl _ _, one_mem_NLam D Λ F,
    frameEqv_refl D _, frameEqv_refl D _, fun x _ => by simp⟩

end Formalism.MainNotions.S.Lem.Cnt
end C

section E

open Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups

namespace Formalism.MainNotions.S.Lem.Glob

variable {D : Formalism.BasicNotions.D7}


end Formalism.MainNotions.S.Lem.Glob
end E

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.FrameFixingOrbitRelation
section
noncomputable section

namespace Formalism.MainNotions.S.TieN

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mass

open Formalism.MainNotions.S.LocalSplitGroups

end Mass

section Cnt

open IsDedekindDomain MeasureTheory Formalism.MainNotions.S.LocalSplitGroups
open scoped BigOperators
open Classical

variable {D : D7} {X : TermTie D} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {u u' : D.what₂.Word}

def IntLow {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E] [TopologicalSpace E]
    [MeasurableSpace E] (Mp : Loc.Model F E) {n : ℕ} (l : Matrix (Fin n) (Fin n) E) : Prop :=
  (∀ a, l a a = 1) ∧ (∀ a b, a < b → l a b = 0) ∧ ∀ a b, l a b ∈ Mp.R

def IntUp {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E] [TopologicalSpace E]
    [MeasurableSpace E] (Mp : Loc.Model F E) {n : ℕ} (ρ : Matrix (Fin n) (Fin n) E) : Prop :=
  (∀ a, ρ a a = 1) ∧ (∀ a b, b < a → ρ a b = 0) ∧ ∀ a b, ρ a b ∈ Mp.R

end Cnt

section Cnt2

open IsDedekindDomain MeasureTheory Formalism.MainNotions.S.LocalSplitGroups
open scoped BigOperators
open Classical

variable {D : D7} {X : TermTie D} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {u u' : D.what₂.Word}

end Cnt2

section FromLoc

open Formalism.MainNotions.S.LocalSplitGroups

end FromLoc

section Orb

open MeasureTheory Matrix Formalism.QuantumDeterminants

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {Cw : ℝ}

end Orb

end Formalism.MainNotions.S.TieN
end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.LocSplitType
section
noncomputable section

namespace Formalism.MainNotions.BridgeRowsGenus

open NumberField Formalism.HermitianLatticesTheory

section Loc

variable {E : Type} [Field E] [NumberField E] [StarRing E]
  {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

end Loc

def LocUnimod : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    Formalism.BasicNotions.CMData F E → ∀ (S : Formalism.BasicNotions.HSpace E) (L M : Submodule (𝓞 E) S.V),
    Submodule.IsLattice E L → Submodule.IsLattice E M →
    ∀ p : Ideal (𝓞 E), p.IsMaximal → IsUnimodularAt S.hT p L → IsUnimodularAt S.hT p M →
      ∃ g ∈ isom S.hT, gmap g (loc (K := E) p L) = loc (K := E) p M

end Formalism.MainNotions.BridgeRowsGenus

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
section
open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Bridge

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB

def orbSqO {k r : ℕ} (L : LocBessel k r) (F : Mx k r → (L.Wq →L[ℂ] L.Wp)) (γ : Point ℂ (r + 1)) : ℝ≥0∞ :=
  ⨆ (g : Mx k r) (μR : Measure (Mt k r)) (ν : Measure (PairSp k r))
    (_ : IsPtRepO L γ g ∧ IsRelStab L g ∧ IsRootMeas L γ g μR ∧ IsOrbQuot L g μR ν),
    ENNReal.ofReal (hsNormSq (OrbInt L F g ν))

def kaS (D : D7) : ℝ := D.host.ka / gg D

section

variable (D : D7) (large₂ : SizeData₂ D)

def AmpIsBessel (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ (W : LocW D.R.k D.R.rS) (hW : GoodW D τ w w' θ W)
    (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (_ : l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3)
    (A : LocS W) (hA : GoodS D lam' A) (hT : 0 < Tr D w) (hT' : 0 < Tr D w'),
    ∃ (f : Mx D.R.k D.R.rS →
        ((toBessel D τ w w' θ W lam' A hW hA hT hT').Wq →L[ℂ] (toBessel D τ w w' θ W lam' A hW hA hT hT').Wp))
      (K : ℝ), 0 < K ∧ IsKFinCoefH (toBessel D τ w w' θ W lam' A hW hA hT hT').σ f ∧
      (∀ μsec, IsSection D.R.k D.R.rS W.z W.z' μsec →
        jNorm2 (toBessel D τ w w' θ W lam' A hW hA hT hT') f μsec ≠ 0 ∧
        ENNReal.ofReal K * jNorm2 (toBessel D τ w w' θ W lam' A hW hA hT hT') f μsec ≤ MMv D w w' A μsec) ∧
      ∀ γ p, RelPt D W.z W.z' γ p → ∀ θ', normWin D large₂ C1 θ' → ∀ νR, RMeas D W γ θ' νR →
        ENNReal.ofReal (hsNormSq (A.J νR γ)) ≤
          ENNReal.ofReal (K * large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 2)) *
            orbSqO (toBessel D τ w w' θ W lam' A hW hA hT hT') f p

def FrameChange (Ch Cs Cn Cf : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (ka b : ℝ),
    Real.exp 1 ≤ b → 0 < ka → ka ≤ b ^ Ch → ka⁻¹ ≤ b ^ Ch → L.c = ((2 * ka : ℝ) : ℂ) → L.κN ≠ ⊤ →
    L.ε = epsSH D.R → 0 < L.κN →
    StdHyp Ch Cs D.R.k D.R.rS L.ε lam0 L.u L.u' (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') ka b →
    l1dist L.lam lam0 ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 →
    IsKFinCoefH L.σ f →
    ∃ (L₁ : LocBessel D.R.k D.R.rS) (f₁ : Mx D.R.k D.R.rS → (L₁.Wq →L[ℂ] L₁.Wp)),
      L₁.ε = L.ε ∧ L₁.lam = L.lam ∧ L₁.u = L.u ∧ L₁.u' = L.u' ∧ L₁.c = cOfDpsi ((1 : ℝ) : ℂ) ∧ 0 < L₁.κN ∧ L₁.κN ≠ ⊤ ∧
      Tz D.R.k D.R.rS L₁.z = Tz D.R.k D.R.rS L.z * ka ^ (2 * D.R.rS) ∧
      Tz D.R.k D.R.rS L₁.z' = Tz D.R.k D.R.rS L.z' * ka ^ (2 * D.R.rS) ∧
      IsKFinCoefH L₁.σ f₁ ∧
      ∀ μsec, IsSection D.R.k D.R.rS L.z L.z' μsec → ∃ μsec₁, IsSection D.R.k D.R.rS L₁.z L₁.z' μsec₁ ∧
        ∃ K₁ : ℝ, 0 < K₁ ∧
        jNorm2 L₁ f₁ μsec₁ ≤ ENNReal.ofReal K₁ * jNorm2 L f μsec ∧
        (jNorm2 L f μsec ≠ 0 → jNorm2 L₁ f₁ μsec₁ ≠ 0) ∧
        ∀ p : Point ℂ (D.R.rS + 1), Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') p ≠ 0 →
          ∃ p₁ : Point ℂ (D.R.rS + 1), Gpt (Tz D.R.k D.R.rS L₁.z) (Tz D.R.k D.R.rS L₁.z') p₁ ≠ 0 ∧
            max 1 (1 / Gpt (Tz D.R.k D.R.rS L₁.z) (Tz D.R.k D.R.rS L₁.z') p₁) ≤
              b ^ (Cf * (D.R.m : ℝ) ^ 2) * max 1 (1 / Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') p) ∧
            ENNReal.ofReal (K₁ * ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') p) * orbSqO L f p ≤
              ENNReal.ofReal (b ^ (Cf * (D.R.m : ℝ) ^ 2) *
                ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L₁.z) (Tz D.R.k D.R.rS L₁.z') p₁) * orbSq L₁ f₁ p₁

def StdOfHyp (C' Cl Cg cb Cu cT CT C0 Ch Cs Cs' Cβ : ℝ) : Prop :=
  Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w', StdHyp Ch Cs D.R.k D.R.rS (epsSH D.R) (lamD D τ) (uS D w τ) (uS D w' τ) (Tr D w) (Tr D w') (kaS D)
      (large₂.sc.b ^ Cβ) ∧
    AllGaps (lamD D τ) (Cs' * D.R.k * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3)

def GfOfRelPt : Prop :=
  ∀ (z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (γ : MatKR D.R.k D.R.rS) (p : Point ℂ (D.R.rS + 1)),
    RelPt D z z' γ p → Gf D.R.k D.R.rS z z' γ = Gpt (Tz D.R.k D.R.rS z) (Tz D.R.k D.R.rS z') p

end

section

variable (D : D7) (large₂ : SizeData₂ D)

end

section

variable (D : D7) (large₂ : SizeData₂ D)

end

theorem sum_castLE {N l : ℕ} (hl : l ≤ N) (f : Fin N → ℂ) (hf : ∀ i : Fin N, l ≤ i.val → f i = 0) :
    ∑ i, f i = ∑ i : Fin l, f (Fin.castLE hl i) := by
  classical
  have h1 : ∑ i ∈ Finset.univ.map (⟨Fin.castLE hl, Fin.castLE_injective hl⟩ : Fin l ↪ Fin N), f i =
      ∑ i, f i := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro i _ hi
    refine hf i ?_
    by_contra h
    exact hi (Finset.mem_map.2 ⟨⟨i.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
  rw [← h1, Finset.sum_map]
  try rfl

theorem leadMinor_cell {N : ℕ} (L P U : Matrix (Fin N) (Fin N) ℂ) (hL : IsLoUni L) (hU : IsUpUni U) (l : ℕ)
    (hl : l ≤ N) : leadMinor (L * P * U) l hl = leadMinor P l hl := by
  unfold leadMinor
  have hLs : ∀ (i : Fin l) (a : Fin N), l ≤ a.val → L (Fin.castLE hl i) a = 0 := fun i a ha =>
    (hL (Fin.castLE hl i) a).1 (Fin.lt_iff_val_lt_val.2 (lt_of_lt_of_le i.isLt ha))
  have hUs : ∀ (b : Fin N) (j : Fin l), l ≤ b.val → U b (Fin.castLE hl j) = 0 := fun b j hb =>
    (hU b (Fin.castLE hl j)).1 (Fin.lt_iff_val_lt_val.2 (lt_of_lt_of_le j.isLt hb))
  have key : (L * P * U).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      L.submatrix (Fin.castLE hl) (Fin.castLE hl) * P.submatrix (Fin.castLE hl) (Fin.castLE hl) *
        U.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    rw [sum_castLE hl]
    · refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [sum_castLE hl]
      intro a ha
      rw [hLs i a ha, zero_mul]
    · intro b hb
      rw [hUs b j hb, mul_zero]
  have hLt : (L.submatrix (Fin.castLE hl) (Fin.castLE hl)).BlockTriangular OrderDual.toDual := by
    intro i j hij
    exact (hL (Fin.castLE hl i) (Fin.castLE hl j)).1 (OrderDual.toDual_lt_toDual.mp hij)
  have hUt : (U.submatrix (Fin.castLE hl) (Fin.castLE hl)).BlockTriangular id := by
    intro i j hij
    exact (hU (Fin.castLE hl i) (Fin.castLE hl j)).1 hij
  have h1 : ∏ i : Fin l, L.submatrix (Fin.castLE hl) (Fin.castLE hl) i i = 1 :=
    Finset.prod_eq_one (fun i _ => (hL (Fin.castLE hl i) (Fin.castLE hl i)).2 rfl)
  have h2 : ∏ i : Fin l, U.submatrix (Fin.castLE hl) (Fin.castLE hl) i i = 1 :=
    Finset.prod_eq_one (fun i _ => (hU (Fin.castLE hl i) (Fin.castLE hl i)).2 rfl)
  rw [key, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_of_lowerTriangular (M := L.submatrix (Fin.castLE hl) (Fin.castLE hl)) hLt,
    Matrix.det_of_upperTriangular (M := U.submatrix (Fin.castLE hl) (Fin.castLE hl)) hUt, h1, h2,
    one_mul, mul_one]

theorem normSq_leadMinor_ZhatO (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mx k r) (l : ℕ) (hl : l ≤ r + 1) :
    Complex.normSq (leadMinor (ZhatO k r z z' g) l hl) = Complex.normSq (leadMinor (Formalism.QuantumDeterminants.Zhat k r z z' g) l hl) := by
  unfold leadMinor
  have e : (ZhatO k r z z' g).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      (Formalism.QuantumDeterminants.Zhat k r z z' g).submatrix (Fin.castLE hl) (Fin.castLE hl) *
        Matrix.diagonal (fun b : Fin l => (-1 : ℂ) ^ (r - (Fin.castLE hl b).val)) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.mul_diagonal, ZhatO]
    ring
  have hp : Complex.normSq (∏ b : Fin l, (-1 : ℂ) ^ (r - (Fin.castLE hl b).val)) = 1 := by
    rw [map_prod]
    exact Finset.prod_eq_one (fun b _ => by rw [map_pow, Complex.normSq_neg, Complex.normSq_one, one_pow])
  rw [e, Matrix.det_mul, Complex.normSq_mul, Matrix.det_diagonal]
  simp only [hp, mul_one]

theorem gfOfRelPt (D : D7) : GfOfRelPt D := by
  unfold GfOfRelPt
  intro z z' γ p hp
  obtain ⟨-, ⟨L, U, hL, hU, hZ⟩, -⟩ := hp
  have hm : ∀ (l : ℕ) (hl : l ≤ D.R.rS + 1),
      Complex.normSq (leadMinor (Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS z z' γ) l hl) =
        Complex.normSq (leadMinor (ptMat p) l hl) := by
    intro l hl
    rw [← normSq_leadMinor_ZhatO, hZ, leadMinor_cell L (ptMat p) U hL hU]
  unfold Gf Gpt
  rw [← hm, ← hm]
  rfl

end Formalism.MainNotions.S.Bridge

end
end

