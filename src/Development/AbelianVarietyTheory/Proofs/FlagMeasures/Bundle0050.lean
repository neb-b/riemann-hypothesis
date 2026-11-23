module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemPerpSpan
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianEichlerProductContinuousOnLattice
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ComplementLatticeOfTermFreeRank
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CompLat

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

def diagGraph (Λ : Submodule L.O S.V) : Submodule L.O S.V where
  carrier := {w | (w, w) ∈ S.graphOf Λ}
  zero_mem' := ⟨0, Λ.zero_mem, 0, Λ.zero_mem, Submodule.zero_mem _, Submodule.zero_mem _,
    by simp, by simp, 0, Λ.zero_mem, by simp⟩
  add_mem' := by
    rintro a b ⟨y', hy', y, hy, p', p, x', x, t, ht, e⟩ ⟨z', hz', z, hz, q', q, u', u, s, hs, e'⟩
    refine ⟨y' + z', Λ.add_mem hy' hz', y + z, Λ.add_mem hy hz, Submodule.add_mem _ p' q',
      Submodule.add_mem _ p q, ?_, ?_, t + s, Λ.add_mem ht hs, ?_⟩
    · have := S.X'.add_mem x' u'
      rwa [sub_add_sub_comm] at this
    · have := S.X.add_mem x u
      rwa [sub_add_sub_comm] at this
    · rw [smul_add, ← e, ← e', sub_add_sub_comm]
  smul_mem' := by
    rintro c a ⟨y', hy', y, hy, p', p, x', x, t, ht, e⟩
    refine ⟨c • y', Λ.smul_mem c hy', c • y, Λ.smul_mem c hy, Submodule.smul_mem _ (c : E) p',
      Submodule.smul_mem _ (c : E) p, ?_, ?_, c • t, Λ.smul_mem c ht, ?_⟩
    · have := S.X'.smul_mem (c : E) x'
      rwa [smul_sub] at this
    · have := S.X.smul_mem (c : E) x
      rwa [smul_sub] at this
    · rw [← smul_sub, e]
      exact smul_comm (c : E) _ t

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
variable [IsNonarchimedeanLocalField F] [CharZero F] in
private theorem exists_integral_smul_mem_of_span_eq_whole (Λ : Submodule L.O S.V)
    (hU : Submodule.span E (Λ : Set S.V) = ⊤) (w : S.V) :
    ∃ c : F, c ≠ 0 ∧ c ∈ (ValuativeRel.valuation F).integer ∧ algebraMap F E c • w ∈ Λ := by
  have hw : w ∈ Submodule.span E (Λ : Set S.V) := hU ▸ Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, Subring.one_mem _, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, Subring.one_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, hcO, hcx⟩ := hx
    obtain ⟨c', hc', hc'O, hcy⟩ := hy
    have h1 := (_root_.GlobalTheory.UnramOrder.algebraMap_mem_iff L c).2 hcO
    have h2 := (_root_.GlobalTheory.UnramOrder.algebraMap_mem_iff L c').2 hc'O
    refine ⟨c * c', mul_ne_zero hc hc', Subring.mul_mem _ hcO hc'O, ?_⟩
    have := Λ.add_mem (Λ.smul_mem (⟨_, h2⟩ : L.O) hcx) (Λ.smul_mem (⟨_, h1⟩ : L.O) hcy)
    convert this using 1
    change algebraMap F E (c * c') • (x + y) =
      algebraMap F E c' • algebraMap F E c • x + algebraMap F E c • algebraMap F E c' • y
    rw [map_mul]
    module
  | smul e x _ hx =>
    obtain ⟨c, hc, hcO, hcx⟩ := hx
    obtain ⟨c', hc', hc'O, he⟩ := _root_.GlobalTheory.HL.StdLat.exists_mul_mem L {e}
    have he' := he e (Finset.mem_singleton_self e)
    refine ⟨c' * c, mul_ne_zero hc' hc, Subring.mul_mem _ hc'O hcO, ?_⟩
    have := Λ.smul_mem (⟨_, he'⟩ : L.O) hcx
    convert this using 1
    change algebraMap F E (c' * c) • e • x = (algebraMap F E c' * e) • algebraMap F E c • x
    rw [map_mul]
    module

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
variable [IsNonarchimedeanLocalField F] [CharZero F] in
private theorem mem_complementLattice_and_tauRel_of_isTerm (d : S.Datum)
    (Λ : Submodule L.O S.V) (hT : S.IsTerm d Λ) (w : S.V)
    (hw : w ∈ S.W0) (hΛ : w ∈ Λ) :
    w ∈ S.complementLatticeOfDatum d ∧ S.TauRel d Λ w 0 := by
  obtain ⟨⟨n, n'⟩, hA, hA', hn, hn', hΛn, hΛn', -, hgr⟩ := hT
  have hME : ∀ x ∈ S.ME, S.h w x = 0 := hw
  have hXo : w ∈ _root_.GlobalTheory.HL.perp L S.Hm S.X := fun x hx =>
    hME x (le_sup_of_le_left (_root_.GlobalTheory.HL.TermBasic.spanTo_mono S S.f (Nat.le_succ r)) hx)
  have hXo' : w ∈ _root_.GlobalTheory.HL.perp L S.Hm S.X' := fun x hx =>
    hME x (le_sup_of_le_right (_root_.GlobalTheory.HL.TermBasic.spanTo_mono S S.f' (Nat.le_succ r)) hx)
  refine ⟨⟨hw, ?_, ?_, ?_⟩, ⟨0, Submodule.zero_mem _, 0, Submodule.zero_mem _, by simpa using hΛ,
    by simpa using hΛ, ⟨0, Λ.zero_mem, by simp⟩, by simpa using Submodule.zero_mem _⟩⟩
  · refine ((_root_.GlobalTheory.HL.StdLat.stdLat_spec L r k S S.f S.es (Or.inl ⟨rfl, rfl⟩) _ hA).2.2 w).2 ?_
    refine (_root_.GlobalTheory.HL.TermBasic.inner_smul S hn w).2 ⟨w, ?_, hXo, by simpa using Submodule.zero_mem _⟩
    rw [← hΛn]; exact hΛ
  · refine ((_root_.GlobalTheory.HL.StdLat.stdLat_spec L r k S S.f' S.es' (Or.inr ⟨rfl, rfl⟩) _ hA').2.2 w).2 ?_
    refine (_root_.GlobalTheory.HL.TermBasic.inner_smul S hn' w).2 ⟨w, ?_, hXo', by simpa using Submodule.zero_mem _⟩
    rw [← hΛn']; exact hΛ
  · rw [hgr]
    exact ⟨w, hΛ, w, hΛ, hXo', hXo, by simpa using Submodule.zero_mem _,
      by simpa using Submodule.zero_mem _, 0, Λ.zero_mem, by simp⟩

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
variable [IsNonarchimedeanLocalField F] [CharZero F] in
private theorem isNoetherianRing_locE_O (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) : IsNoetherianRing L.O := by
  obtain ⟨ω, hω, e, he, hωe⟩ := _root_.GlobalTheory.UnramOrder.exists_sub_cj_mul_eq_one L
  let φ : (ValuativeRel.valuation F).integer →+* L.O :=
    ((algebraMap F E).comp (ValuativeRel.valuation F).integer.subtype).codRestrict L.O
      (fun c => (_root_.GlobalTheory.UnramOrder.algebraMap_mem_iff L c).2 c.2)
  letI : Algebra (ValuativeRel.valuation F).integer L.O := φ.toAlgebra
  let σ : L.O →+* L.O := ((L.cj : E →+* E).comp L.O.subtype).codRestrict L.O
    (fun x => _root_.GlobalTheory.UnramOrder.cj_mem L x.2)
  have key := _root_.GlobalTheory.UnramOrder.exists_eq_add_mul (R₀ := (ValuativeRel.valuation F).integer) σ
    (fun x => Subtype.ext (L.cj_cj x)) (fun c => Subtype.ext (L.cj.commutes _))
    (fun x hx => by
      obtain ⟨c, hc⟩ := _root_.GlobalTheory.UnramOrder.exists_int_of_fixed L x.2 (congrArg Subtype.val hx)
      exact ⟨c, Subtype.ext hc.symm⟩)
    (ω := ⟨ω, hω⟩) (isUnit_iff_exists_inv.2 ⟨⟨e, he⟩, Subtype.ext hωe⟩)
  haveI : Module.Finite (ValuativeRel.valuation F).integer L.O := by
    refine ⟨⟨{1, ⟨ω, hω⟩}, ?_⟩⟩
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, b, rfl⟩ := key x
    refine Submodule.add_mem _ ?_ ?_
    · rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  exact IsNoetherianRing.of_finite (ValuativeRel.valuation F).integer L.O


open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
variable [IsNonarchimedeanLocalField F] [CharZero F] in
theorem _root_.GlobalTheory.HL.CompLat.main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (r k : ℕ) (S : _root_.GlobalTheory.HL.Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∃ b : Fin (k - 1) → S.V, LinearIndependent E b ∧ S.complementLatticeOfDatum d = (Submodule.span L.O (Set.range b) : Set S.V) := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT
  obtain ⟨-, -, -, -, -, -, -, b, hb, hW⟩ := _root_.GlobalTheory.FrameBasic.main L r k S
  have hsd := (_root_.GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT).1
  have hgr : d.2.2 = S.graphOf Λ := by
    obtain ⟨_, -, -, -, -, -, -, -, h⟩ := hT
    exact h
  let Q : Submodule L.O S.V := S.W0.restrictScalars L.O ⊓ d.1 ⊓
    d.2.1 ⊓ _root_.GlobalTheory.HL.CompLat.diagGraph S Λ
  have hQ : (Q : Set S.V) = S.complementLatticeOfDatum d := by
    ext w
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      refine ⟨h1, h2, h3, ?_⟩
      rw [hgr]
      exact h4
    · rintro ⟨h1, h2, h3, h4⟩
      rw [hgr] at h4
      exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  have hspan : Submodule.span E (Q : Set S.V) = Submodule.span E (Set.range b) := by
    rw [← hW]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro w ⟨⟨⟨h1, -⟩, -⟩, -⟩
      exact h1
    · intro w hw
      obtain ⟨c, hc, -, hcw⟩ := exists_integral_smul_mem_of_span_eq_whole S Λ hsd.1.2 w
      have hq : algebraMap F E c • w ∈ (Q : Set S.V) := by
        rw [hQ]
        exact (mem_complementLattice_and_tauRel_of_isTerm S d Λ hT _
          (S.W0.smul_mem _ hw) hcw).1
      have h1 : w = algebraMap F E c⁻¹ • algebraMap F E c • w := by
        rw [smul_smul, ← map_mul, inv_mul_cancel₀ hc, map_one, one_smul]
      rw [h1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hq)
  have hFG : Q.FG := by
    haveI := isNoetherianRing_locE_O L
    obtain ⟨-, hcompl, -⟩ := _root_.GlobalTheory.FrameBasic.main L r k S
    let π : S.V →ₗ[L.O] S.V :=
      (S.W0.subtype.comp
        (Submodule.linearProjOfIsCompl S.W0 S.ME hcompl.symm)).restrictScalars L.O
    refine Submodule.FG.of_le (hsd.1.1.map π) ?_
    rintro w ⟨⟨⟨h1, -⟩, -⟩, h4⟩
    obtain ⟨-, -, y, hy, -, -, -, hx, -⟩ := h4
    have hXME : y - w ∈ S.ME :=
      le_sup_of_le_left (_root_.GlobalTheory.HL.TermBasic.spanTo_mono S S.f (Nat.le_succ r)) hx
    refine ⟨y, hy, ?_⟩
    have hy' : y = w + (y - w) := by abel
    change ((Submodule.linearProjOfIsCompl S.W0 S.ME hcompl.symm y : S.V)) = w
    have e1 := Submodule.linearProjOfIsCompl_apply_left hcompl.symm ⟨w, h1⟩
    have e2 := Submodule.linearProjOfIsCompl_apply_right hcompl.symm ⟨y - w, hXME⟩
    rw [hy', map_add (f := _)]
    erw [e1, e2]
    simp
  obtain ⟨b', hb', hQb⟩ := _root_.GlobalTheory.OrderBasis.order_basis L b hb Q hFG hspan
  exact ⟨b', hb', by rw [← hQ, hQb]⟩

end GlobalTheory.HL.CompLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardUniCosetsLe
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.UniCount

section
variable {E : Type} [CommRing E] {N : ℕ}

theorem isUni_mul {s t : Matrix (Fin N) (Fin N) E} (hs : IsUni s) (ht : IsUni t) :
    IsUni (s * t) := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l i with h1 | h1
    · rw [hs.1 i l h1, zero_mul]
    · rw [ht.1 l j (lt_of_lt_of_le h h1), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hs.2, ht.2, one_mul]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h1 | h1
      · rw [hs.1 i l h1, zero_mul]
      · rw [ht.1 l i h1, mul_zero]
    · simp

def rowM (k : Fin N) (c : Fin N → E) : Matrix (Fin N) (Fin N) E :=
  1 + Matrix.of fun a b => if a = k then c b else 0

theorem mul_rowM (w : Matrix (Fin N) (Fin N) E) (k : Fin N) (c : Fin N → E) (i j : Fin N) :
    (w * rowM k c) i j = w i j + w i k * c j := by
  rw [rowM, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply]
  simp

theorem isUni_rowM (k : Fin N) (c : Fin N → E) (hc : ∀ j, j ≤ k → c j = 0) :
    IsUni (rowM k c) := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · simp only [rowM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply_ne h.ne']
    split_ifs with h1
    · rw [hc j (h1 ▸ h.le), add_zero]
    · simp
  · simp only [rowM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply_eq]
    split_ifs with h1
    · rw [hc i h1.le, add_zero]
    · simp
end

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {N : ℕ}

theorem isIntM_mul (L : LocE F E) {s t : Matrix (Fin N) (Fin N) E} (hs : IsIntM L s)
    (ht : IsIntM L t) : IsIntM L (s * t) := fun i j => by
  rw [Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (hs i l) (ht l j)

theorem isIntM_rowM (L : LocE F E) (k : Fin N) (c : Fin N → E) (hc : ∀ j, c j ∈ L.O) :
    IsIntM L (rowM k c) := fun i j => by
  simp only [rowM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]
  refine add_mem ?_ ?_
  · split_ifs
    exacts [one_mem _, zero_mem _]
  · split_ifs
    exacts [hc j, zero_mem _]

def cos (L : LocE F E) (u : Matrix (Fin N) (Fin N) E) : Set (Matrix (Fin N) (Fin N) E) :=
  {v | ∃ A, IsUni A ∧ IsIntM L A ∧ v = u * A}

theorem cos_mul_subset (L : LocE F E) (u B : Matrix (Fin N) (Fin N) E) (h1 : IsUni B)
    (h2 : IsIntM L B) : cos L (u * B) ⊆ cos L u := by
  rintro v ⟨A, hA, hA', rfl⟩
  exact ⟨B * A, isUni_mul h1 hA, isIntM_mul L h2 hA', Matrix.mul_assoc _ _ _⟩

theorem cos_rowM (L : LocE F E) (u : Matrix (Fin N) (Fin N) E) (k : Fin N) (c : Fin N → E)
    (hc : ∀ j, j ≤ k → c j = 0) (hc' : ∀ j, c j ∈ L.O) : cos L (u * rowM k c) = cos L u := by
  refine (cos_mul_subset L u _ (isUni_rowM k c hc) (isIntM_rowM L k c hc')).antisymm ?_
  have : u = u * rowM k c * rowM k (-c) := by
    ext i j
    rw [mul_rowM, mul_rowM, mul_rowM, hc k le_rfl]
    simp
  conv_lhs => rw [this]
  exact cos_mul_subset L _ _ (isUni_rowM k _ fun j hj => by simp [hc j hj])
    (isIntM_rowM L k _ fun j => neg_mem (hc' j))

theorem exists_rep (L : LocE F E) (δ : E) (R : Set E)
    (hR : ∀ x : E, δ * x ∈ L.O → ∃ r ∈ R, r - x ∈ L.O)
    (u : Matrix (Fin N) (Fin N) E) (hu : IsUni u) (hδ : ∀ i j, δ * u i j ∈ L.O) (m : ℕ) :
    ∃ w : Matrix (Fin N) (Fin N) E, IsUni w ∧ (∀ i j, δ * w i j ∈ L.O) ∧ cos L w = cos L u ∧
      ∀ i j : Fin N, N ≤ i.val + m → i < j → w i j ∈ R := by
  induction m with
  | zero => exact ⟨u, hu, hδ, rfl, fun i j h _ => absurd i.2 (by omega)⟩
  | succ m ih =>
    obtain ⟨w, hw, hwδ, hc, hg⟩ := ih
    by_cases hm : N ≤ m
    · exact ⟨w, hw, hwδ, hc, fun i j _ h => hg i j (by omega) h⟩
    let k : Fin N := ⟨N - 1 - m, by omega⟩
    choose r hrR hr using fun j => hR (w k j) (hwδ k j)
    let c : Fin N → E := fun j => if k < j then r j - w k j else 0
    have hc0 : ∀ j, j ≤ k → c j = 0 := fun j hj => if_neg (not_lt.2 hj)
    have hc1 : ∀ j, c j ∈ L.O := fun j => by
      simp only [c]
      split_ifs
      exacts [hr j, zero_mem _]
    refine ⟨w * rowM k c, isUni_mul hw (isUni_rowM k c hc0), fun i j => ?_,
      (cos_rowM L w k c hc0 hc1).trans hc, fun i j h hij => ?_⟩
    · rw [mul_rowM, mul_add, ← mul_assoc]
      exact add_mem (hwδ i j) (mul_mem (hwδ i k) (hc1 j))
    · rw [mul_rowM]
      by_cases hik : i = k
      · subst hik
        rw [hw.2, one_mul]
        simp only [c, if_pos hij]
        simpa using hrR j
      · have h2 : i.val ≠ N - 1 - m := fun h => hik (Fin.ext h)
        have h3 : k < i := by
          show N - 1 - m < i.val
          omega
        rw [hw.1 i k h3, zero_mul, add_zero]
        exact hg i j (by omega) hij

theorem encard_le (L : LocE F E) (δ : L.O) (hδ : IsUnit (δ : E))
    [Finite (L.O ⧸ Ideal.span {δ})] (N : ℕ) :
    {C : Set (Matrix (Fin N) (Fin N) E) | ∃ u, IsUni u ∧ (∀ i j, (δ : E) * u i j ∈ L.O) ∧
      C = cos L u}.encard ≤
      ((Nat.card (L.O ⧸ Ideal.span {δ}) ^ (N * (N - 1) / 2) : ℕ) : ℕ∞) := by
  obtain ⟨d, hd⟩ := hδ
  let ρ : (L.O ⧸ Ideal.span {δ}) → E := fun q => (d⁻¹ : Eˣ) * (Quotient.out q : L.O)
  have hR : ∀ x : E, (δ : E) * x ∈ L.O → ∃ r ∈ Set.range ρ, r - x ∈ L.O := by
    intro x hx
    let y : L.O := ⟨_, hx⟩
    refine ⟨_, ⟨Ideal.Quotient.mk _ y, rfl⟩, ?_⟩
    have h1 : Quotient.out (Ideal.Quotient.mk (Ideal.span {δ}) y) - y ∈ Ideal.span {δ} :=
      Ideal.Quotient.eq.1 (Ideal.Quotient.mk_out _)
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h1
    have h2 : ((Quotient.out (Ideal.Quotient.mk (Ideal.span {δ}) y) : L.O) : E)
        = (a : E) * d + d * x := by
      have := congrArg (Subtype.val) ha
      push_cast at this
      rw [hd, this]
      simp [y]
    have h3 : ρ (Ideal.Quotient.mk _ y) - x = a := by
      simp only [ρ]
      rw [h2]
      have := d.inv_mul
      linear_combination ((a : E) + x) * this
    rw [h3]
    exact a.2
  let P := {p : Fin N × Fin N // p.1 < p.2}
  let mk : (P → L.O ⧸ Ideal.span {δ}) → Matrix (Fin N) (Fin N) E := fun f =>
    Matrix.of fun i j => if h : i < j then ρ (f ⟨(i, j), h⟩) else if i = j then 1 else 0
  have hsub : {C : Set (Matrix (Fin N) (Fin N) E) | ∃ u, IsUni u ∧
      (∀ i j, (δ : E) * u i j ∈ L.O) ∧ C = cos L u} ⊆ (fun f => cos L (mk f)) '' Set.univ := by
    rintro C ⟨u, hu, huδ, rfl⟩
    obtain ⟨w, hw, -, hc, hg⟩ := exists_rep L δ _ hR u hu huδ N
    choose f hf using fun p : P => hg p.1.1 p.1.2 (by omega) p.2
    refine ⟨f, trivial, ?_⟩
    rw [← hc]
    show cos L (mk f) = _
    congr 1
    ext i j
    simp only [mk, Matrix.of_apply]
    split_ifs with h1 h2
    · exact hf ⟨(i, j), h1⟩
    · rw [h2, hw.2]
    · exact (hw.1 i j (lt_of_le_of_ne (not_lt.1 h1) (Ne.symm h2))).symm
  refine (Set.encard_le_encard hsub).trans ((Set.encard_image_le _ _).trans (le_of_eq ?_))
  have hP : Nat.card P = N * (N - 1) / 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_product_filter_lt,
      Fintype.card_fin, Nat.choose_two_right]
  rw [Set.encard_univ, ENat.card_eq_coe_natCard, Nat.card_fun, hP]

theorem resQ_ne_zero [IsNonarchimedeanLocalField F] (ϖ : 𝒪[F]) (h : Irreducible ϖ) :
    resQ ϖ ≠ 0 := by
  have : Finite (𝒪[F] ⧸ Ideal.span {ϖ}) := by
    rw [← h.maximalIdeal_eq]
    exact inferInstanceAs (Finite 𝓀[F])
  exact Nat.card_pos.ne'

end GlobalTheory.HL.UniCount

theorem GlobalTheory.HL.encard_uniCosets_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ (δ : E), δ ∈ L.O → IsUnit δ → ∀ N : ℕ, ({C : Set (Matrix (Fin N) (Fin N) E) | ∃ u, IsUni u ∧ (∀ i j, δ * u i j ∈ L.O) ∧ C = {v | ∃ A, IsUni A ∧ IsIntM L A ∧ v = u * A}}.encard : ℝ≥0∞) ≤ (resQ ϖ : ℝ≥0∞) ^ ((vE L ϖ (δ * L.cj δ)).toNat * (N * (N - 1) / 2)) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ δ hδ hu N
  have hc := (GlobalTheory.UnramCard.card_quot_eq_pow L ϖ hϖ ⟨δ, hδ⟩ hu).2
  have hfin : Finite (L.O ⧸ Ideal.span {(⟨δ, hδ⟩ : L.O)}) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ (UniCount.resQ_ne_zero ϖ hϖ))
  have h := UniCount.encard_le L ⟨δ, hδ⟩ hu N
  rw [hc, ← pow_mul] at h
  have h2 := ENat.toENNReal_le.2 h
  rw [ENat.toENNReal_coe, Nat.cast_pow] at h2
  exact h2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryTupleMatrixRightMulNearIdentity
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.RStab

theorem gramT_scale {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) {n m : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (x : Fin m → Fin n → E) (t : F) :
    gramT L Hm (fun a => algebraMap F E t • x a)
      = (algebraMap F E t * algebraMap F E t) • gramT L Hm x := by
  ext a b
  simp only [gramT, hf, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul,
    AlgEquiv.commutes, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem rmul_sub {E : Type} [CommRing E] {n m : ℕ} (x : Fin m → Fin n → E)
    (A : Matrix (Fin m) (Fin m) E) (a : Fin m) :
    rmul x A a - x a = ∑ i, (A i a - (1 : Matrix (Fin m) (Fin m) E) i a) • x i := by
  simp only [rmul, sub_smul, Finset.sum_sub_distrib]
  congr 1
  simp [Matrix.one_apply, ite_smul]

theorem exists_isometry_rmul : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ, IsSD L Hm Λ → ∀ (m : ℕ) (Γ : Matrix (Fin m) (Fin m) E), IsUnit Γ.det → ∀ N e : ℕ, ∃ i0 : ℕ, ∀ i ≥ i0, ∀ x : Fin m → Fin n → E, (∀ a, algebraMap F E ((ϖ : F) ^ e) • x a ∈ Λ) → gramT L Hm x = Γ → ∀ A ∈ congK L ϖ m i, cT L A * Γ * A = Γ → ∃ g ∈ isomG L Hm, CongId L ϖ Λ N g ∧ ∀ a, g (x a) = rmul x A a := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm hH Λ hΛ m Γ hΓ N e
  have h0 : ((ϖ : F) ^ e) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hϖ.ne_zero)
  have ht : IsUnit (algebraMap F E ((ϖ : F) ^ e)) := (IsUnit.mk0 _ h0).map _
  set t := algebraMap F E ((ϖ : F) ^ e) with htdef
  have hΓ' : IsUnit ((t * t) • Γ).det := by
    rw [Matrix.det_smul]; exact ((ht.mul ht).pow _).mul hΓ
  obtain ⟨N', hN'⟩ := _root_.GlobalTheory.HL.CloseTuples.exists_isometry_close L ϖ hϖ Hm hH Λ hΛ m _ hΓ' N
  refine ⟨N', fun i hi x hx hG A hA hAΓ => ?_⟩
  have hϖO : algebraMap F E ((ϖ : F) ^ (i - N')) ∈ L.O := by
    rw [L.O_def]
    have h1 : IsIntegral 𝒪[F] ((ϖ : F) ^ (i - N')) :=
      (isIntegral_algebraMap (R := 𝒪[F]) (A := F) (x := ϖ)).pow _
    exact h1.map (IsScalarTower.toAlgHom 𝒪[F] F E)
  obtain ⟨g, hg, hc, hgx⟩ := hN' (fun a => t • x a) (fun a => t • rmul x A a) hx
    (by rw [gramT_scale, hG]) (by rw [gramT_scale, ContModel.gramT_rmul, hG, hAΓ]) (by
      intro a
      choose c hc hc' using hA
      refine ⟨∑ j, (algebraMap F E ((ϖ : F) ^ (i - N')) * c j a) • t • x j, ?_, ?_⟩
      · refine Λ.sum_mem fun j _ => ?_
        exact Λ.smul_mem (⟨_, L.O.mul_mem hϖO (hc j a)⟩ : L.O) (hx j)
      · rw [← smul_sub, rmul_sub, Finset.smul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hc', smul_smul, smul_smul, smul_smul]
        congr 1
        have : (ϖ : F) ^ i = (ϖ : F) ^ N' * (ϖ : F) ^ (i - N') := by
          rw [← pow_add]; congr 1; omega
        rw [this, map_mul]; ring)
  refine ⟨g, hg, hc, fun a => ?_⟩
  have h := hgx a
  simp only [map_smul] at h
  exact ht.smul_left_cancel.1 h

end GlobalTheory.HL.RStab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianEichlerProductContinuousOnLatticeStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianEichlerProduct_continuous_on_lattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (N r : ℕ) (Hm : Matrix (Fin N) (Fin N) E) (X u : Fin r → Fin N → E) (s : Fin r → E) (e : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E)) (he : ∀ i v, e i v = eich L Hm (X i) (u i) (s i) v) (Λ : Submodule L.O (Fin N → E)) (hΛ : IsLat L Λ) (c : Fˣ), ∃ d : Fˣ, ∀ (u' : Fin r → Fin N → E) (s' : Fin r → E) (e' : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E)), (∀ i v, e' i v = eich L Hm (X i) (u' i) (s' i) v) → (∀ i j, ∃ o ∈ L.O, u' i j - u i j = algebraMap F E d * o) → (∀ i, ∃ o ∈ L.O, s' i - s i = algebraMap F E d * o) → ∀ x ∈ Λ, ∃ y ∈ Λ, ((List.ofFn e).prod).symm ((List.ofFn e').prod x) - x = algebraMap F E c • y := by
  first | exact @GlobalTheory.HL.EichCont.prod_eich_cont | exact GlobalTheory.HL.EichCont.prod_eich_cont | (intros; apply GlobalTheory.HL.EichCont.prod_eich_cont <;> assumption)
end

