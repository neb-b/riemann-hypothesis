module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmulColMul
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0427
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0440
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0327
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IncAdjYZeroMulVec
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Matrix ValuativeRel IsLocalRing
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.FinPlLoc GlobalTheory.IwaPlace NumberField Filter
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.GoodPos

variable {D : D7}

theorem incAdj_yZero_mulVec {V₀ W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (r : Fin ρ) (hr : r.1 + 1 = ρ)
    (z : Fin V₀.rank → D.host.E) (a : AE D) (y : Fin V₀.rank → AE D) :
    (show Matrix (Fin W.rank) (Fin V₀.rank) (AE D) from d.incAdj V₀ (a • yZero V₀ ρ z)) *ᵥ y =
      colMul d.jY r (incA D D.host.xi0⁻¹ * hermAt V₀ y (a • ratV z)) := by
  have h1 : (incA D (-D.host.xi0⁻¹) • (adj (a • yZero V₀ ρ z) ⬝ gA V₀)) *ᵥ y =
      Pi.single r (incA D D.host.xi0⁻¹ * hermAt V₀ y (a • ratV z)) := by
    rw [smul_mulVec, ← mulVec_mulVec, herm_eq]
    generalize gA V₀ *ᵥ y = t
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, adj, yZero, zEll, ell, Matrix.transpose_apply,
      Matrix.map_apply, Matrix.smul_apply, Matrix.neg_apply, vecMulVec_apply, RingHom.map_neg]
    by_cases hi : i = r
    · subst hi
      simp only [hr, if_true, mul_one, Pi.single_eq_same, mul_neg, RingHom.map_neg, neg_mul, Finset.sum_neg_distrib, neg_neg]
    · have : ¬ (i.1 + 1 = ρ) := fun h => hi (Fin.ext (by omega))
      simp only [this, if_false, mul_zero, neg_zero, RingHom.map_zero, zero_mul, Finset.sum_const_zero, Pi.single_eq_of_ne hi]
  change (d.jY ⬝ (incA D (-D.host.xi0⁻¹) • (adj (a • yZero V₀ ρ z) ⬝ gA V₀))) *ᵥ y = _
  rw [← mulVec_mulVec, h1, mulVec_single]
  funext k
  exact mul_comm _ _

theorem mxAt_mul {P : Pl D → Prop} {l m n : ℕ} (M : Mx D l m) {N : Mx D m n} (h : MxAt P N) : MxAt P (M ⬝ N) := fun i j => by
  rw [Matrix.mul_apply]; exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (h k j)

theorem mxAt_mul' {P : Pl D → Prop} {l m n : ℕ} {M : Mx D l m} (N : Mx D m n) (h : MxAt P M) : MxAt P (M ⬝ N) := fun i j => by
  rw [Matrix.mul_apply]; exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (h i k)

theorem mxAt_smul {P : Pl D → Prop} {m n : ℕ} (a : AE D) {N : Mx D m n} (h : MxAt P N) : MxAt P (a • N) := fun i j =>
  Ideal.mul_mem_left _ _ (h i j)

theorem mxAt_adj {x : Pl D} {m n : ℕ} {N : Mx D m n} (h : MxAt (· = x) N) : MxAt (· = x) (adj N) := fun i j =>
  id_conj (h j i)

def xiU (D : D7) : (AE D)ˣ := inU D.host.xi0 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)

theorem cA_xi : cA D (incA D D.host.xi0) = -incA D D.host.xi0 := by
  rw [FrameLat.cA_incA, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, RingHom.map_neg]

theorem cA_xi_inv : cA D (incA D D.host.xi0⁻¹) = -incA D D.host.xi0⁻¹ := by
  rw [FrameLat.cA_incA, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, inv_neg, RingHom.map_neg]

theorem last_of {V₀ W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (z : Fin V₀.rank → D.host.E) {M : Lat V₀} {LW : Lat W}
    (hM : IsSelfDualC V₀ M) (hLW : IsSelfDualC W LW) {x : Pl D} {α m : (AE D)ˣ} {b : Fin ρ → (AE D)ˣ}
    (hb : ∀ r : Fin ρ, r.1 + 1 = ρ → b r = xiU D * cU α * m)
    (hα : ∀ y, y ∈ latA W LW (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV W LW (· = x))
    (hW : ∀ i, ∀ a ∈ idAt D (· = x), colMul d.jY i a ∈ latV W LW (· = x) ↔ cA D (b i : AE D) * a ∈ intAt D (· = x))
    (hz : ∀ a ∈ idAt D (· = x), a • ratV z ∈ latV V₀ M (· = x) ↔ ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x))
    (hρ : 0 < ρ) : ∀ a ∈ idAt D (· = x),
      d.incAdj V₀ (a • yZero V₀ ρ z) ∈ latO V₀ W (M : Set _) (LW : Set _) (· = x) ↔ a ∈ intAt D (· = x) := fun a ha => by
  have hsd := LocSD.isSDAt_latV D V₀ M x hM
  have hr : (⟨ρ - 1, by omega⟩ : Fin ρ).1 + 1 = ρ := by simp only; omega
  have hmx : MxAt (· = x) (d.incAdj V₀ (a • yZero V₀ ρ z)) :=
    mxAt_mul _ (mxAt_smul _ (mxAt_mul' _ (mxAt_adj fun i j => Ideal.mul_mem_right _ _ ha)))
  rw [LatMem.mem_latO_iff D V₀ W M LW hM hLW, and_iff_right hmx]
  have h1 := hz _ (Ideal.mul_mem_left _ (m : AE D) ha)
  rw [Units.inv_mul_cancel_left,
    hsd.2.2 (((m : AE D) * a) • ratV z) fun i => Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ha)] at h1
  rw [← h1]
  refine forall₂_congr fun y hy => ?_
  rw [incAdj_yZero_mulVec d _ hr, hα, smul_colMul, hW _ _
    (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (LocSD.hermAt_mem_idAt (hsd.1 y hy) _))), hb _ hr, ← int_neg,
    ← herm_conj V₀ y, int_conj, mul_smul]
  have e1 := herm_smul V₀ 1 m y (a • ratV z)
  rw [one_smul] at e1
  rw [e1, Units.val_mul, Units.val_mul, RingHom.map_mul, RingHom.map_mul, cU_val, cA_cA, xiU, inU_val, cA_xi]
  have e2 := α.mul_inv
  have e3 : incA D D.host.xi0 * incA D D.host.xi0⁻¹ = 1 := (xiU D).mul_inv
  refine iff_of_eq (congrArg (· ∈ _) ?_)
  linear_combination (incA D D.host.xi0 * incA D D.host.xi0⁻¹ * cA D m * hermAt V₀ y (a • ratV z)) * e2 +
    (cA D m * hermAt V₀ y (a • ratV z)) * e3

theorem herm_kap {L L'' S : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (w : WO S L'') (l : Fin L.rank → AE D)
    (s : Fin S.rank → AE D) :
    hermAt S ((show Matrix (Fin S.rank) (Fin L.rank) (AE D) from kap τ S w) *ᵥ l) s =
      incA D (-D.host.xi0⁻¹) * hermAt L l ((rat τ : Mx D _ _) *ᵥ ((show Matrix (Fin L''.rank) (Fin S.rank) (AE D) from w) *ᵥ s)) := by
  rw [mulVec_mulVec]
  change hermAt S ((incA D (-D.host.xi0⁻¹) • (giA S ⬝ (adj (rat τ ⬝ w) ⬝ gA L))) *ᵥ l) s = _
  generalize ((rat τ : Mx D _ _) ⬝ w : Mx D L.rank S.rank) = u
  rw [herm_eq, herm_eq, mulVec_mulVec, Matrix.mul_smul, gA_giA_cancel, smul_mulVec, dotProduct_smul, smul_eq_mul,
    ← mulVec_mulVec, dotProduct_mulVec]
  congr 2
  ext i
  simp [Matrix.vecMul, Matrix.mulVec, dotProduct, adj, map_sum, map_mul, mul_comm]

theorem kap_of {L L'' S : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) {ζ : Fin L.rank → D.host.E}
    {ζ₀ : Fin L''.rank → D.host.E} (hζ : IsLineVec L ζ) (hζ₀ : IsLineVec L'' ζ₀) {lam : D.host.E} (hlam : lam ≠ 0)
    (hτ : τ *ᵥ ζ₀ = lam • ζ) {LL : Lat L} {LZ : Lat L''} {LS : Lat S} (hLL : IsSelfDualC L LL) (hLZ : IsSelfDualC L'' LZ)
    (hLS : IsSelfDualC S LS) {x : Pl D} {α μ : (AE D)ˣ}
    (hα : ∀ (S : HSp D) (L : Lat S) y, y ∈ latA S L (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = x))
    (hμ : ∀ a ∈ idAt D (· = x), a • ratV ζ₀ ∈ latV L'' LZ (· = x) ↔ ((μ⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x))
    (hm : ∀ a ∈ idAt D (· = x), a • ratV ζ ∈ latV L LL (· = x) ↔
      (((α * μ * inU lam hlam * (xiU D * cU α)⁻¹)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) :
    ∀ w ∈ latO S L'' (LS : Set _) (LZ : Set _) (· = x), kap τ S w ∈ latO L S (LL : Set _) (LS : Set _) (· = x) := by
  intro w hw
  rw [LatMem.mem_latO_iff D S L'' LS LZ hLS hLZ] at hw
  have hsd := LocSD.isSDAt_latV D S LS x hLS
  have hmx : MxAt (· = x) (kap τ S w) := mxAt_smul _ (mxAt_mul _ (mxAt_mul' _ (mxAt_adj (mxAt_mul _ hw.1))))
  rw [LatMem.mem_latO_iff D L S LL LS hLL hLS]
  refine ⟨hmx, fun l hl => ?_⟩
  have hn := line_norm hζ hLL hm
  obtain ⟨a, ha, rfl⟩ := line_vec hζ (latV_idAt hl)
  rw [hα]
  refine (hsd.2.2 _ ?_).2 ?_
  · exact fun i => Ideal.mul_mem_left _ _ (mulVec_mem_idAt _ (latV_idAt hl) i)
  intro s hs
  have h1 := (hα _ _ _).1 (hw.2 s hs)
  obtain ⟨a', ha', e'⟩ := line_vec hζ₀ (latV_idAt h1)
  rw [e'] at h1
  have e2 : (show Matrix (Fin L''.rank) (Fin S.rank) (AE D) from w) *ᵥ s = ((α : AE D) * a') • ratV ζ₀ := by
    rw [mul_smul, ← e', smul_smul, Units.mul_inv, one_smul]
  have e1 := herm_smul S ((α⁻¹ : (AE D)ˣ) : AE D) 1 ((show Matrix (Fin S.rank) (Fin L.rank) (AE D) from kap τ S w) *ᵥ a • ratV ζ) s
  rw [one_smul] at e1
  rw [e1, herm_kap, e2, mulVec_smul, rat_mulVec, hτ, ratV_smul, smul_smul, herm_smul, herm_rat]
  have h2 := int_mul ((hm a ha).1 hl) (int_conj.2 ((hμ a' ha').1 h1))
  rw [hn _ h2.1] at h2
  convert h2 using 1
  generalize hm' : α * μ * inU lam hlam * (xiU D * cU α)⁻¹ = m
  have f1 := m.mul_inv
  have f2 : cA D (μ : AE D) * cA D ((μ⁻¹ : (AE D)ˣ) : AE D) = 1 := (cU μ).mul_inv
  have f3 : cA D (m : AE D) = cA D α * cA D μ * cA D (incA D lam) * (-incA D D.host.xi0⁻¹ * (α⁻¹ : (AE D)ˣ)) := by
    rw [← hm', mul_inv]
    simp only [Units.val_mul, RingHom.map_mul, inU_val, cU_inv, cA_cA, xiU, inU_inv, cA_xi_inv]
  rw [f3]
  simp only [RingHom.map_mul, RingHom.map_neg, RingHom.map_one]
  generalize incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ) = h
  linear_combination (cA D α * cA D (incA D lam) * incA D D.host.xi0⁻¹ * (α⁻¹ : (AE D)ˣ) * h * a * cA D a') * f2 +
    (cA D α * cA D (incA D lam) * incA D D.host.xi0⁻¹ * (α⁻¹ : (AE D)ˣ) * h * a * cA D a' * (cA D μ * cA D (μ⁻¹ : (AE D)ˣ))) * f1

section Split

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}

theorem isU_xi (h : p.UnitAA) : IsU p.v (xiU D : AE D) :=
  IsU.of_pres (xiU D).mul_inv (fun a ha => (h.1 a ha).1) fun a ha => (h.1 a ha).2

theorem isU_alpha (h : p.UnitAA) {L : HSp D} {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ) {α : (AE D)ˣ}
    (hα : ∀ (S : HSp D) (L : Lat S) y, y ∈ latA S L (· = p.v) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = p.v)) :
    IsU p.v (α : AE D) := by
  have hgen : ∃ e : D.host.E, e ≠ 0 ∧ ∀ a ∈ idAt D (· = p.v),
      a • ratV ζ ∈ latV L (GlobalTheory.AdelicU.frameLat L) (· = p.v) ↔
        incA D e⁻¹ * a ∈ intAt D (· = p.v) := by
    first
    | exact GlobalTheory.GoodPos.line_gen hζ (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat L) p.v
    | exact GlobalTheory.GoodPos.line_gen hζ (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat L).1 p.v
  obtain ⟨e, he, hg⟩ := hgen
  refine IsU.inv (fun a ha => ?_) α.inv_mul
  have h1 := hα L (GlobalTheory.AdelicU.frameLat L) ((incA D e * a) • ratV ζ)
  have e1 : incA D e⁻¹ * incA D e = 1 := (inU e he).inv_mul
  rw [h.2, smul_smul, hg _ (Ideal.mul_mem_left _ _ ha), hg _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ ha)),
    mul_left_comm (incA D e⁻¹) ((α⁻¹ : (AE D)ˣ) : AE D), ← mul_assoc (incA D e⁻¹), e1, one_mul] at h1
  exact h1

theorem val_le_one {u : AE D} (h : IsU p.v u) : valuation k (p.pr u) ≤ 1 := by
  refine (p.int_iff _).2 ?_
  rw [p.sec_pr, mul_comm]
  exact ((h _ (FrameLat.e_mem_idAt p)).1 (FrameLat.e_mem_intAt p)).2

theorem val_eq_one {u : (AE D)ˣ} (h : IsU p.v (u : AE D)) : valuation k (p.pr u) = 1 := by
  have h1 := val_le_one h
  have h2 := val_le_one (h.inv u.mul_inv)
  have h3 : valuation k (p.pr u) * valuation k (p.pr (u⁻¹ : (AE D)ˣ)) = 1 := by
    rw [← map_mul, ← map_mul, u.mul_inv, map_one, map_one]
  exact le_antisymm h1 (by rw [← h3]; exact mul_le_of_le_one_right' h2)

end Split

end GlobalTheory.GoodPos

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvDiagTorusIntegralBesselJacobiUnramified
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.InvStep

variable {D : D7}

theorem diag_inv {ρ : ℕ} (t : GL (Fin ρ) (AE D)) (ht : ∀ i j, i ≠ j → t.1 i j = 0) :
    t.1 = diagonal (fun k => t.1 k k) ∧ (t⁻¹).1 = diagonal (fun k => (t⁻¹).1 k k) ∧
      ∀ k, t.1 k k * (t⁻¹).1 k k = 1 := by
  have h1 : t.1 = diagonal (fun k => t.1 k k) := by
    ext a b
    by_cases h : a = b
    · subst h; simp
    · rw [diagonal_apply_ne _ h, ht a b h]
  have hm : t.1 * (t⁻¹).1 = 1 := t.mul_inv
  have h3 : ∀ a b, t.1 a a * (t⁻¹).1 a b = (1 : Matrix (Fin ρ) (Fin ρ) (AE D)) a b := by
    intro a b
    have := congrFun (congrFun hm a) b
    rw [h1, diagonal_mul] at this
    exact this
  have h4 : ∀ k, t.1 k k * (t⁻¹).1 k k = 1 := fun k => by
    have := h3 k k; rwa [one_apply_eq] at this
  refine ⟨h1, ?_, h4⟩
  ext a b
  by_cases h : a = b
  · subst h; simp
  · rw [diagonal_apply_ne _ h]
    have e := h3 a b
    rw [one_apply_ne h] at e
    calc (t⁻¹).1 a b = (t⁻¹).1 a a * (t.1 a a * (t⁻¹).1 a b) := by
          rw [← mul_assoc, mul_comm ((t⁻¹).1 a a), h4, one_mul]
      _ = 0 := by rw [e, mul_zero]

theorem mat_mem_idAt {P : Pl D → Prop} {m n k l : ℕ} (A : Mx D m n) (M : Mx D n k) (B : Mx D k l)
    (hM : ∀ a b, M a b ∈ idAt D P) (i : Fin m) (j : Fin l) : (A ⬝ M ⬝ B) i j ∈ idAt D P := by
  rw [Matrix.mul_apply]
  refine Ideal.sum_mem _ fun b _ => Ideal.mul_mem_right _ _ ?_
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (hM a b)

theorem levi_sub_one_mem {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {P : Pl D → Prop} {t : GL (Fin ρ) (AE D)}
    (ht : d.levi t ∈ grpAt S P) (i j : Fin ρ) : t.1 i j - (1 : Mx D ρ ρ) i j ∈ idAt D P := by
  have hm : ∀ a b, (mt S (d.levi t) - 1) a b ∈ idAt D P := by
    intro a b
    have h := (MonoidHom.mem_ker).1 ht
    have h2 := congrArg (fun u : GL (Fin S.rank) (AE D ⧸ idAt D P) => u.1 a b) h
    simp only [Units.val_one] at h2
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
    have e1 : ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (idAt D P))).comp (matHom S) (d.levi t)).1 =
      (mt S (d.levi t)).map (Ideal.Quotient.mk (idAt D P)) := rfl
    rw [e1, Matrix.map_apply] at h2
    rw [h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have e : t.1 - 1 = d.pX ⬝ (mt S (d.levi t) - 1) ⬝ d.jX := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, d.pX_jX, Matrix.mul_assoc, ← blockX, blockX_levi]
  rw [← Matrix.sub_apply, e]
  exact mat_mem_idAt _ _ _ hm i j

theorem symplO_extX_extY {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x y : Mx D T.rank ρ) :
    symplO S T (d.extX T x) (d.extY T y) =
      Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * pairS T x y) := by
  have h := d.hO_ext T x 0 0 y 0 0
  simp only [map_zero, zero_add, add_zero, hO_eq_trace S₀, Matrix.mul_zero, trace_zero] at h
  rw [symplO, h, show pairS T (0 : Mx D T.rank ρ) 0 = 0 by simp [pairS], add_zero]

theorem trace_single_mul {ρ : ℕ} (i : Fin ρ) (β : AE D) (M : Mx D ρ ρ) :
    (Matrix.single i i β ⬝ M).trace = β * M i i := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq]

theorem adj_single {ρ : ℕ} (i : Fin ρ) (β : AE D) : adj (Matrix.single i i β) = Matrix.single i i (cA D β) := by
  ext a b
  simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.single_apply]
  split_ifs with h1 h2 h2 <;> first | rfl | exact absurd ⟨h1.2, h1.1⟩ h2 | exact absurd ⟨h2.2, h2.1⟩ h1 | exact map_zero _


set_option maxHeartbeats 1000000 in
theorem vac_fix_Y : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (LS : Lat S) (LT : Lat T) (v : Pl D), Tame D v → ∀ f, Vac ψ S T LS LT (· = v) f → ∀ y : Mx D T.rank ρ, d.extY T y ∈ latO S T (LS : Set _) (LT : Set _) (· = v) → heisO ψ S T (d.extY T y) f = f := by
  intro D ψ S S₀ T ρ d LS LT v hT f hf y hy
  have hsm : ∀ (c : AE D) (z : Mx D T.rank ρ), c • d.extY T z = d.extY T (c • z) := by
    intro c z
    rw [HypDec.extY_apply, HypDec.extY_apply, Matrix.smul_mul]
  have hadd : ∀ y₁ y₂ : Mx D T.rank ρ, heisO ψ S T (d.extY T (y₁ + y₂)) f =
      heisO ψ S T (d.extY T y₁) (heisO ψ S T (d.extY T y₂) f) := by
    intro y₁ y₂
    funext w
    simp only [heisO, map_add (f := _)]
    rw [GlobalTheory.OrientedHeis.symplOH_add_left, HypDec.symplOH_extY_extY, add_zero, GlobalTheory.OrientedHeis.symplOH_add_right,
      AddChar.map_add_eq_mul, add_assoc]
    ring
  rcases hT.2 with h2 | ⟨e, ε, he, hε, hb⟩
  · have hε : IsPlaceIdem D v (GlobalTheory.SplitIdem.placeHom D.host.F v 1) :=
      ⟨singleV D.host.F v 1, rfl, GlobalTheory.SplitIdem.evalV_singleV_same _ _ _,
        fun w hw => GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ hw⟩
    obtain ⟨a, ha, ha2⟩ : ∃ a : AE D, finPart D a ∈ intAE D ∧
        2 * a = algebraMap (AF D.host.F) (AE D) (GlobalTheory.SplitIdem.placeHom D.host.F v 1) := by
      obtain ⟨yv, hyv⟩ := ((GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v 2).2 h2).exists_right_inv
      rw [map_ofNat] at hyv
      have hy' : (2 : Fv D.host.F v) * yv = 1 := congrArg Subtype.val hyv
      refine ⟨algebraMap (AF D.host.F) (AE D) (GlobalTheory.SplitIdem.placeHom D.host.F v yv), ?_, ?_⟩
      · exact AddSubgroup.subset_closure ⟨_, GlobalTheory.SplitIdem.singleV_mem_intAf D.host.F v yv, 1, rfl⟩
      · rw [two_mul, ← map_add (f := _), ← map_add (f := _), ← two_mul, hy']
    have h1 : 2 • (a • d.extY T y) = d.extY T y := by
      rw [two_nsmul, ← add_smul, ← two_mul, ha2, GlobalTheory.VecInvInert.idem_smul_eq hε hy]
    have h3 := hf.2.1 (a • d.extY T y) (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a ha _ hy)
    rwa [h1] at h3
  · have he' := GlobalTheory.SplitScalar.isSplitIdem_conj he
    have hint : ∀ c : AE D, c * c = c → finPart D c ∈ intAE D := fun c hc =>
      GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hc])
    have hu : d.extY T y = d.extY T (e • y) + d.extY T (cA D e • y) := by
      rw [← hsm, ← hsm, ← add_smul, hb, GlobalTheory.VecInvInert.idem_smul_eq hε hy]
    have f1 : heisO ψ S T (d.extY T (e • y)) f = f := by
      rw [← hsm]
      exact hf.2.2 e he _ (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ e (hint e he.1) _ hy) (fun i j => by rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he.1])
    have f2 : heisO ψ S T (d.extY T (cA D e • y)) f = f := by
      rw [← hsm]
      exact hf.2.2 _ he' _ (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (hint _ he'.1) _ hy) (fun i j => by rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he'.1])
    rw [hu, ← map_add (f := _), hadd, f2, f1]

end GlobalTheory.FinPl.InvStep

namespace GlobalTheory.FinPl.InvStep


set_option maxHeartbeats 1000000 in
theorem inv_int : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → UnrAt s v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → J.d.levi t ∈ grpAt J.W (· = v) → 𝔉 (s.om (1, J.d.levi t) f) ≠ 0 → ∀ i, (t⁻¹).1 i i - 1 ∈ intAt D (· = v) := by
  intro D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 hF f hf t htd ht hne i
  obtain ⟨-, h2, -⟩ := diag_inv t htd
  have hc1 : (t⁻¹).1 i i - 1 ∈ idAt D (· = v) := by
    have := levi_sub_one_mem J.d (P := (· = v)) (t := t⁻¹) (by rw [map_inv]; exact inv_mem ht) i i
    rwa [one_apply_eq] at this
  refine GlobalTheory.T.integral_of_addChar_trivial_on_homLattice_line D ψ s.weil.std B.V B.V₀ J.W J.W₀ ρ B.d J.d LV LV₀ LW LW₀ v hG.tame hG.sdV hG.sdW hG.monoV
    hG.monoW hG.cols i _ hc1 ?_
  intro b hb hY
  have hfix := vac_fix_Y D ψ B.V B.V₀ J.W ρ B.d LV LW v hG.tame f hf _ hY
  have hθ : IsThetaFunO ψ B.V J.W (s.om (1, J.d.levi t) f) := s.weil.om_pres _ _ hf.1
  have hg : heisO ψ B.V J.W (actO B.V J.W 1 (J.d.levi t) (B.d.extY J.W (J.d.jY ⬝ Matrix.single i i b)))
      (s.om (1, J.d.levi t) f) = s.om (1, J.d.levi t) f := by
    rw [← s.weil.om_heis 1 (J.d.levi t) _ f hf.1, hfix]
  have hact : actO B.V J.W 1 (J.d.levi t) (B.d.extY J.W (J.d.jY ⬝ Matrix.single i i b)) =
      B.d.extY J.W (J.d.jY ⬝ (adj (t⁻¹).1 ⬝ Matrix.single i i b)) := by
    rw [actO_eq, inv_one, mt_one, Matrix.mul_one, HypDec.extY_apply, HypDec.extY_apply, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, HypDec.levi_jY, Matrix.mul_assoc J.d.jY]
  have hS : ∀ a c, Matrix.single i i b a c ∈ idAt D (· = v) := by
    intro a c
    rw [Matrix.single_apply]
    split_ifs
    · exact hb
    · exact zero_mem _
  have hMx : MxAt (· = v) (J.d.jY ⬝ (adj (t⁻¹).1 ⬝ Matrix.single i i b)) := by
    intro a c
    have := mat_mem_idAt (J.d.jY ⬝ adj (t⁻¹).1) (Matrix.single i i b) 1 hS a c
    rwa [Matrix.mul_one, Matrix.mul_assoc] at this
  have hpair : ∀ U : Mx D ρ ρ, pairS J.W (J.d.jX ⬝ U) (J.d.jY ⬝ (adj (t⁻¹).1 ⬝ Matrix.single i i b)) =
      cA D b * ((t⁻¹).1 i i * U i i) := by
    intro U
    rw [pairS, adj_mul, adj_mul, adj_adj, adj_single, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc (gA J.W), ← Matrix.mul_assoc (adj J.d.jY), HypDec.gram_YX, Matrix.one_mul,
      ← Matrix.mul_assoc, Matrix.mul_assoc, trace_single_mul]
    congr 1
    conv_lhs => rw [h2]
    rw [diagonal_mul]
  have hUI : UInv J.W (xZero J.d) (J.d.jY ⬝ (adj (t⁻¹).1 ⬝ Matrix.single i i b)) := by
    intro u
    have h1 : u.1.1 i i = 1 := ((mem_UX.1 u.2) i i).2
    have e := hpair 1
    rw [Matrix.mul_one] at e
    rw [xZero, hpair, e, h1, one_apply_eq]
  have hd := hF.Heisenberg₂.dual _ hθ _ hMx hUI
  rw [hact] at hg
  rw [hg] at hd
  have hψ : ψ (symplO B.V J.W (B.d.extX J.W (xZero J.d))
      (B.d.extY J.W (J.d.jY ⬝ (adj (t⁻¹).1 ⬝ Matrix.single i i b)))) = 1 := by
    obtain ⟨w, hw⟩ := Function.ne_iff.1 hne
    have h1 := congrFun hd w
    simp only [Pi.smul_apply, smul_eq_mul] at h1 hw
    exact mul_right_cancel₀ hw (h1.symm.trans (one_mul _).symm)
  rw [← hψ, symplO_extX_extY, symplO_extX_extY]
  congr 3
  have e := hpair 1
  rw [Matrix.mul_one, one_apply_eq, mul_one] at e
  rw [xZero, e, pairS, adj_mul, adj_single, Matrix.mul_assoc, ← Matrix.mul_assoc (gA J.W), ← Matrix.mul_assoc (adj J.d.jY),
    HypDec.gram_YX, Matrix.one_mul, trace_single_mul, Matrix.single_apply, if_pos ⟨rfl, rfl⟩]

end GlobalTheory.FinPl.InvStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsIntegralMulVec
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.XGeoStd

theorem isIntegral_mulVec {E : Type} [Field E] {m n : ℕ} (M : Matrix (Fin m) (Fin n) E)
    (hM : ∀ i j, IsIntegral ℤ (M i j)) (x : Fin n → E) (hx : ∀ k, IsIntegral ℤ (x k)) (k : Fin m) :
    IsIntegral ℤ ((M *ᵥ x) k) := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subalgebra.sum_mem (integralClosure ℤ E) fun l _ => (hM k l).mul (hx l)

theorem isIntegral_ite {E : Type} [Field E] (p : Prop) [Decidable p] :
    IsIntegral ℤ (if p then (1 : E) else 0) := by
  split_ifs
  · exact isIntegral_one
  · exact isIntegral_zero

theorem orthAt_oTop : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} (hI : I.Ok) (n : ℕ) (h : n = (I.rec7 l Z).R.m) (x : GlobalTheory.FinPl.Pl (I.rec7 l Z)), GlobalTheory.FinPl.OrthAt (GlobalTheory.XGeoStd.oTop l Z hI n h) (GlobalTheory.PlaceModel.latFrame ((I.rec7 l Z).sp.X n)) (GlobalTheory.PlaceModel.latFrame (I.rec7 l Z).sp.X') (GlobalTheory.PlaceModel.latFrame (GlobalTheory.XGeoStd.lineZ (I.rec7 l Z))) x := by
  intro B X I l Z hI n h x
  subst h
  obtain ⟨hs, -, h2, -⟩ := hI.spaces
  have hS : ∀ y, y ∈ GlobalTheory.PlaceModel.latFrame ((I.rec7 l Z).sp.X (I.rec7 l Z).R.m) ↔ ∀ k, IsIntegral ℤ (y k) := fun y => by
    rw [← SetLike.mem_coe, GlobalTheory.AdForm.PinInhab.lat_X hI]; rfl
  have hA : ∀ y, y ∈ GlobalTheory.PlaceModel.latFrame (I.rec7 l Z).sp.X' ↔ ∀ k, IsIntegral ℤ (y k) := fun y => by
    rw [← SetLike.mem_coe, GlobalTheory.AdForm.VacStd.coe_latFrame_of_eq _ hs _ h2]; rfl
  have hB : ∀ y, y ∈ GlobalTheory.PlaceModel.latFrame (lineZ (I.rec7 l Z)) ↔ ∀ k, IsIntegral ℤ (y k) := fun y => by
    rw [← SetLike.mem_coe, GlobalTheory.AdForm.VacStd.coe_latFrame_of_eq _ Examples₂.star_isIntegral 1 rfl]; rfl
  have ho : oTop l Z hI _ rfl = GlobalTheory.AdForm.LiveModel.topDec (GlobalTheory.AdForm.PinInhab.gram_X hI _) (gram_X' hI) := rfl
  rw [ho]
  set o := GlobalTheory.AdForm.LiveModel.topDec (GlobalTheory.AdForm.PinInhab.gram_X (l := l) (Z := Z) hI (I.rec7 l Z).R.m) (gram_X' hI)
  have iA_int : ∀ i j, IsIntegral ℤ (o.iA i j) := fun i j => by
    simp only [o, GlobalTheory.AdForm.LiveModel.topDec, Matrix.of_apply]; exact isIntegral_ite _
  have iB_int : ∀ i j, IsIntegral ℤ (o.iB i j) := fun i j => by
    simp only [o, GlobalTheory.AdForm.LiveModel.topDec, Matrix.of_apply]; exact isIntegral_ite _
  have qA_eq : o.qA = o.iAᴴ := by
    rw [OrthDec.qA, gram_X' hI, GlobalTheory.AdForm.PinInhab.gram_X hI, inv_one, Matrix.one_mul, Matrix.mul_one]
  have qB_eq : o.qB = o.iBᴴ := by
    rw [OrthDec.qB, GlobalTheory.AdForm.PinInhab.gram_X hI, GlobalTheory.AdForm.LiveModel.gram_pos, inv_one, Matrix.one_mul, Matrix.mul_one]
  have qA_int : ∀ i j, IsIntegral ℤ (o.qA i j) := fun i j => by
    rw [qA_eq, Matrix.conjTranspose_apply]; exact hs _ (iA_int j i)
  have qB_int : ∀ i j, IsIntegral ℤ (o.qB i j) := fun i j => by
    rw [qB_eq, Matrix.conjTranspose_apply]; exact hs _ (iB_int j i)
  intro y
  constructor
  · intro hy
    refine ⟨GlobalTheory.SeeSaw.SplitLat.rat_mulVec_mem_latV o.qA (fun z hz => ?_) _ hy,
      GlobalTheory.SeeSaw.SplitLat.rat_mulVec_mem_latV o.qB (fun z hz => ?_) _ hy⟩
    · exact (hA _).2 (isIntegral_mulVec _ qA_int z ((hS z).1 hz))
    · exact (hB _).2 (isIntegral_mulVec _ qB_int z ((hS z).1 hz))
  · rintro ⟨hyA, hyB⟩
    have e : y = o.jA *ᵥ (o.pA *ᵥ y) + o.jB *ᵥ (o.pB *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec]
      have := o.sum_eq_one
      rw [show o.jA * o.pA + o.jB * o.pB = 1 from this, Matrix.one_mulVec]
    rw [e]
    refine add_mem (GlobalTheory.SeeSaw.SplitLat.rat_mulVec_mem_latV o.iA (fun z hz => ?_) _ hyA)
      (GlobalTheory.SeeSaw.SplitLat.rat_mulVec_mem_latV o.iB (fun z hz => ?_) _ hyB)
    · exact (hS _).2 (isIntegral_mulVec _ iA_int z ((hA z).1 hz))
    · exact (hS _).2 (isIntegral_mulVec _ iB_int z ((hB z).1 hz))

end GlobalTheory.XGeoStd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepInverseCharacterLocalComponentChainTameStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open NumberField IsDedekindDomain Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LocMod GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.QTw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.step_inverse_character_local_component_chain_tame : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (P : BadPr I a), P.1 ∉ (B.primes X).vGs → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k), Formalism.L2.NTheta.IsIdemAt (D := I.rec7 l Z) q.e P.1 → (∀ x, (ofSplit q).pr x ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt P.1 x) → DenseRange (ofSplit q).pr → ∀ (i : ℕ) (hi : i < B.R.m) (χ : (AE (I.rec7 l Z))ˣ →* Circle), ChrEq (D := I.rec7 l Z) χ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → ∀ μ : kˣ →* ℂˣ, (ofSplit q).IsComp χ⁻¹ μ → (∀ (x : B.fields.E) (u : kˣ), (u : k) = (ofSplit q).pr x → (μ u : ℂ) = B.embLL (Formalism.L2.Col.muAt I.Ch I.sel (I.tup a) (I.cst a) i P x)) ∧ IsTame μ := by
  first | exact @GlobalTheory.QTw.StepChar.comp_eq_muAt_and_tame | exact GlobalTheory.QTw.StepChar.comp_eq_muAt_and_tame | (intros; apply GlobalTheory.QTw.StepChar.comp_eq_muAt_and_tame <;> assumption)
end

