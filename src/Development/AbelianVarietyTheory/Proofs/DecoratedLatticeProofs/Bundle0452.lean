module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0403
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0426
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0414
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0421
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0305
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0425
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0362
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsDoubleLiftPeriodValue
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0424
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0417
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChiPowOfLevG
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemGinfCOfFinM

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticesSameSplitShapeCarriedByCentral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch


set_option maxHeartbeats 1000000 in
theorem sMoves_of_wShape : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S S₀ A Ln : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A Ln) (ζ : Fin Ln.rank → D.host.E) (L L' : Lat S) (N N' : Lat A) (α α' β β' : Fin ρ → k) (γ δ c₀ : k) (a₀ : GA D A), IsLineVec Ln ζ → IsSelfDualC S L → IsSelfDualC S L' → WShape p d o ζ L α α' γ 1 N → WShape p d o ζ L' β β' δ a₀ N' → latV A N (· = p.v) = latV A N' (· = p.v) → c₀ ≠ 0 → (∀ i, valuation k (β i * c₀) = valuation k (α i)) → (∀ i, valuation k (β' i * c₀) = valuation k (α' i)) → valuation k (δ * c₀) = valuation k γ → ∃ (a : GA D A) (c : AE D), CenAt A p.v a ∧ NormOneAt p.v c ∧ SMoves S c (embA d o (a₀ * a)) L L' p.v := by
  intro D k _ _ _ _ p S S₀ A Ln ρ d o ζ L L' N N' α α' β β' γ δ c₀ a₀ hζ hL hL' hW hW' hN hc₀ hb hb' hd
  obtain ⟨c, hc, hpc⟩ := GlobalTheory.T.exists_normOneIdele_with_splitPlace_component D k p c₀ hc₀
  obtain ⟨c', hc', hpc'⟩ := GlobalTheory.T.exists_normOneIdele_with_splitPlace_component D k p c₀⁻¹ (inv_ne_zero hc₀)
  obtain ⟨a, haC, ha⟩ := _root_.GlobalTheory.Core.Mi.LatMatch.exists_cenAt_scalar D A p.v c' hc'
  refine ⟨a, c, haC, hc, ?_⟩
  apply _root_.GlobalTheory.Core.Mi.LatMatch.sMoves_of_wComp D k p S L L' c _ hL hL' hc
  set f : D.host.E →+* k := p.pr.comp (incA D) with hf
  have hatW : ∀ {m n : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E), atW p X = X.map f := fun _ => rfl
  have hrat : ∀ {m n : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E), atW p X = (rat X).map p.pr := fun _ => rfl
  have hkey : ∀ {n m l : ℕ} (M : Matrix (Fin n) (Fin l) (AE D)) (R : Matrix (Fin l) (Fin m) (AE D))
      (u : Fin m → k), M.map p.pr *ᵥ (R.map p.pr *ᵥ u) = (M * R).map p.pr *ᵥ u := by
    intro n m l M R u; rw [Matrix.mulVec_mulVec, Matrix.map_mul]

  have hsum : atW p d.e * atW p d.qX + atW p d.i₀ * atW p d.q0 + atW p d.e' * atW p d.qY = 1 := by
    simp only [hatW]
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add f), ← Matrix.map_add _ (map_add f), d.sum_eq_one_rat,
      Matrix.map_one _ (map_zero f) (map_one f)]
  have hsumA : atW p o.iA * atW p o.qA + atW p o.iB * atW p o.qB = 1 := by
    simp only [hatW]
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add f), o.iA_qA_add, Matrix.map_one _ (map_zero f) (map_one f)]
  have hrk : Ln.rank = 1 := hζ.1
  have j0 : Fin Ln.rank := ⟨0, by omega⟩
  have huniq : ∀ j : Fin Ln.rank, j = j0 := fun j => Fin.ext (by have := j.2; have := j0.2; omega)
  have hζ0 : ζ j0 ≠ 0 := by
    intro h0
    apply hζ.2
    have : ζ = 0 := funext fun j => by rw [huniq j, h0]; rfl
    simp [this]
  have hfζ : f (ζ j0) ≠ 0 := fun h => hζ0 (f.injective (by rw [h, map_zero]))
  set ζk : Fin Ln.rank → k := fun j => f (ζ j) with hζk
  set zv : Fin S.rank → k := fun r' => p.pr (incA D ((d.i₀ *ᵥ vecB o ζ) r')) with hzv
  have hz : zv = atW p (d.i₀ * o.iB) *ᵥ ζk := by
    funext r
    simp only [hzv, vecB, Matrix.mulVec_mulVec]
    exact RingHom.map_mulVec f (d.i₀ * o.iB) ζ r
  have hdec : ∀ x : Fin S.rank → k, ∃ (x1 x2 : Fin ρ → k) (t : k) (y : Fin A.rank → k),
      x = atW p d.e *ᵥ x1 + atW p d.e' *ᵥ x2 + t • zv +
        atW p (d.i₀ * o.iA) *ᵥ ((Formalism.L2.Theta.mt A 1).map p.pr *ᵥ y) := by
   intro x
   set x0 := atW p d.q0 *ᵥ x
   set w := atW p o.qB *ᵥ x0
   set y := atW p o.qA *ᵥ x0
   set t := w j0 / f (ζ j0)
   have hw : w = t • ζk := by
     funext j; rw [huniq j]; simp only [Pi.smul_apply, smul_eq_mul, hζk, t]; field_simp
   have hx : x = atW p d.e *ᵥ (atW p d.qX *ᵥ x) + atW p d.e' *ᵥ (atW p d.qY *ᵥ x) + t • zv +
       atW p (d.i₀ * o.iA) *ᵥ ((Formalism.L2.Theta.mt A 1).map p.pr *ᵥ y) := by
     rw [mt_one, Matrix.map_one _ (map_zero p.pr) (map_one p.pr), Matrix.one_mulVec, hz, ← Matrix.mulVec_smul, ← hw]
     have hm : atW p d.i₀ * (atW p o.iA * atW p o.qA + atW p o.iB * atW p o.qB) * atW p d.q0 =
         atW p d.i₀ * atW p d.q0 := by rw [hsumA, Matrix.mul_one]
     have h0 : atW p (d.i₀ * o.iA) *ᵥ y + atW p (d.i₀ * o.iB) *ᵥ w = atW p d.i₀ *ᵥ x0 := by
       simp only [y, w, x0, hatW, Matrix.map_mul, Matrix.mulVec_mulVec, ← Matrix.add_mulVec]
       simp only [← hatW]
       rw [← hm]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
     calc x = (1 : Matrix (Fin S.rank) (Fin S.rank) k) *ᵥ x := (Matrix.one_mulVec x).symm
       _ = _ := by
         rw [← hsum, Matrix.add_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
           ← Matrix.mulVec_mulVec, ← h0]
         abel
   exact ⟨_, _, _, _, hx⟩
  intro x
  obtain ⟨x1, x2, t, y, rfl⟩ := hdec x
  rw [hW x1 x2 t y]
  have jX : rat d.e = d.jX := rfl
  have jY : rat d.e' = d.jY := rfl
  have jA : rat (d.i₀ * o.iA) = d.j0 * o.jA := rat_mul _ _
  have jB : rat (d.i₀ * o.iB) = d.j0 * o.jB := rat_mul _ _
  have hGX : Formalism.L2.Theta.mt S (embA d o (a₀ ⬝ a)) ⬝ d.jX = d.jX := d.wittDecomp_anisotropicEmbedding_inclX _
  have hGY : Formalism.L2.Theta.mt S (embA d o (a₀ ⬝ a)) ⬝ d.jY = d.jY := d.wittDecomp_anisotropicEmbedding_inclY _
  have hG0' : Formalism.L2.Theta.mt S (embA d o (a₀ ⬝ a)) ⬝ d.j0 = d.j0 ⬝ Formalism.L2.Theta.mt S₀ (o.emb (a₀ ⬝ a, 1)) :=
    d.wittDecomp_anisotropicEmbedding_inclAnisotropic _
  have hG0 : ∀ {m : ℕ} (R : Matrix (Fin S₀.rank) (Fin m) (AE D)), Formalism.L2.Theta.mt S (embA d o (a₀ ⬝ a)) ⬝ (d.j0 ⬝ R) =
      d.j0 ⬝ (Formalism.L2.Theta.mt S₀ (o.emb (a₀ ⬝ a, 1)) ⬝ R) := by
    intro m R; rw [← Matrix.mul_assoc, hG0', Matrix.mul_assoc]
  have hBB : Formalism.L2.Theta.mt S₀ (o.emb (a₀ ⬝ a, 1)) ⬝ o.jB = o.jB := by rw [o.emb_jB, mt_one, Matrix.mul_one]
  have hAA : Formalism.L2.Theta.mt S₀ (o.emb (a₀ ⬝ a, 1)) ⬝ o.jA = o.jA ⬝ (Formalism.L2.Theta.mt A a₀ ⬝ Formalism.L2.Theta.mt A a) := by
    rw [o.emb_jA, mt_mul]
  set G := Formalism.L2.Theta.mt S (embA d o (a₀ * a)) with hG
  have T1 : G.map p.pr *ᵥ (atW p d.e *ᵥ x1) = atW p d.e *ᵥ x1 := by rw [hrat, hkey, jX, hGX]
  have T2 : G.map p.pr *ᵥ (atW p d.e' *ᵥ x2) = atW p d.e' *ᵥ x2 := by rw [hrat, hkey, jY, hGY]
  have hz' : zv = (d.j0 ⬝ o.jB).map p.pr *ᵥ ζk := by
    rw [← jB]; exact hz
  have T3 : G.map p.pr *ᵥ zv = zv := by
    rw [hz', hkey, hG0, hBB]
  have hms : ∀ {m n : ℕ} (r : AE D) (X : Matrix (Fin m) (Fin n) (AE D)), (r • X).map p.pr = p.pr r • X.map p.pr := by
    intro m n r X; ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  have T4 : G.map p.pr *ᵥ (atW p (d.i₀ * o.iA) *ᵥ y) =
      c₀⁻¹ • (atW p (d.i₀ * o.iA) *ᵥ ((Formalism.L2.Theta.mt A a₀).map p.pr *ᵥ y)) := by
    rw [hrat, hkey, hkey, jA, hG0, hAA, ha, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_smul,
      hms, Matrix.smul_mulVec, hpc', Matrix.mul_assoc]
  have himg : p.pr c • (G.map p.pr *ᵥ (atW p d.e *ᵥ x1 + atW p d.e' *ᵥ x2 + t • zv +
      atW p (d.i₀ * o.iA) *ᵥ ((Formalism.L2.Theta.mt A 1).map p.pr *ᵥ y))) =
      atW p d.e *ᵥ (c₀ • x1) + atW p d.e' *ᵥ (c₀ • x2) + (c₀ * t) • zv +
        atW p (d.i₀ * o.iA) *ᵥ ((Formalism.L2.Theta.mt A a₀).map p.pr *ᵥ y) := by
    rw [mt_one, Matrix.map_one _ (map_zero p.pr) (map_one p.pr), Matrix.one_mulVec, Matrix.mulVec_add,
      Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, T1, T2, T3, T4, hpc]
    simp only [smul_add, Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hc₀, one_smul]
  rw [himg, hW' (c₀ • x1) (c₀ • x2) (c₀ * t) y, hN]
  have hval : ∀ u u' z : k, valuation k (u * c₀) = valuation k u' → (u * (c₀ * z) ∈ 𝒪[k] ↔ u' * z ∈ 𝒪[k]) := by
    intro u u' z h
    rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, ← mul_assoc, map_mul, h, ← map_mul]
  refine and_congr (forall_congr' fun i => (hval _ _ _ (hb i)).symm)
    (and_congr (forall_congr' fun i => (hval _ _ _ (hb' i)).symm) (and_congr (hval _ _ _ hd).symm Iff.rfl))

end GlobalTheory.Core.Mi.LatMatch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineMemLatVIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitLine

open GlobalTheory.FinPl GlobalTheory.FinPl.FrameLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_ofSplit (q : SplitPt D k) (x : D.host.E) : (ofSplit q).pr x = q.pr (incA D x) := rfl

theorem eq_sec_add_cA (q : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = q.v)) :
    a = q.sec (q.pr a) + cA D (q.sec (q.pr (cA D a))) := by
  rw [q.sec_pr, q.sec_pr, RingHom.map_mul, cA_cA, ← add_mul, (idem_iff q a).1 ha]

theorem pr_mem_of_int (q : SplitPt D k) {a : AE D} (ha : finPart D a ∈ intAE D) : q.pr a ∈ 𝒪[k] := by
  rw [q.int_iff, q.sec_pr, RingHom.map_mul]
  exact mul_mem_intAE (e_mem_intAt q).2 ha

theorem mem_intAt_iff_pr (q : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = q.v)) :
    a ∈ intAt D (· = q.v) ↔ q.pr a ∈ 𝒪[k] ∧ q.pr (cA D a) ∈ 𝒪[k] := by
  refine ⟨fun h => ⟨pr_mem_of_int q h.2, pr_mem_of_int q ((cA_int_iff a).2 h.2)⟩, fun h => ⟨ha, ?_⟩⟩
  rw [eq_sec_add_cA q ha, RingHom.map_add (f := _)]
  exact add_mem ((q.int_iff _).1 h.1) ((cA_int_iff _).2 ((q.int_iff _).1 h.2))

theorem single_int {Y' : Type} [DecidableEq Y'] (m₁ : Y') (i : Y') : (Pi.single m₁ (1 : k) : Y' → k) i ∈ 𝒪[k] := by
  by_cases hi : i = m₁
  · subst hi; rw [Pi.single_eq_same]; exact one_mem _
  · rw [Pi.single_eq_of_ne hi]; exact zero_mem _

variable {Y : Type} [Fintype Y] [DecidableEq Y]

theorem wpart {q : SplitPt D k} {S : HSp D} {L : Lat S} {F : Frame k S.rank Y} {u : Fin S.rank → D.host.E} {c : k} {m₀ : Y}
    (hI : IntIn q S F L) (hc : valuation k c = 1) (hu : ∀ r, c * (ofSplit q).pr (u r) = F.β r m₀) (x : k) :
    (fun r => q.sec (x * (ofSplit q).pr (u r))) ∈ latV S L (· = q.v) ↔ x ∈ 𝒪[k] := by
  have hc0 : c ≠ 0 := by rintro rfl; rw [map_zero] at hc; exact zero_ne_one hc
  have e : (fun r => q.sec (x * (ofSplit q).pr (u r))) =
      fun r => q.sec ((F.β *ᵥ Pi.single m₀ (x / c)) r) := by
    funext r
    congr 1
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single m₀ (fun b _ hb => by rw [Pi.single_eq_of_ne hb, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h), Pi.single_eq_same, ← hu r]
    field_simp
  rw [e, ← hI (Pi.single m₀ (x / c))]
  constructor
  · intro h
    have h1 := h m₀
    rw [Pi.single_eq_same, Valuation.mem_integer_iff, map_div₀, hc, div_one] at h1
    exact (Valuation.mem_integer_iff _ _).2 h1
  · intro h i
    by_cases hi : i = m₀
    · subst hi
      rw [Pi.single_eq_same, Valuation.mem_integer_iff, map_div₀, hc, div_one]
      exact (Valuation.mem_integer_iff _ _).1 h
    · rw [Pi.single_eq_of_ne hi]; exact zero_mem _

theorem wbar {q : SplitPt D k} {S : HSp D} {L : Lat S} {F : Frame k S.rank Y} {u : Fin S.rank → D.host.E}
    (hL : IsSelfDualC S L) (hI : IntIn q S F L)
    (hb : ∀ m, ∑ r, F.β r m * (ofSplit q).pr (star ((S.gram *ᵥ u) r)) ∈ 𝒪[k])
    (hb1 : ∃ m, valuation k (∑ r, F.β r m * (ofSplit q).pr (star ((S.gram *ᵥ u) r))) = 1) (A : k) :
    (fun r => cA D (q.sec (A * (ofSplit q).pr (star (u r))))) ∈ latV S L (· = q.v) ↔ A ∈ 𝒪[k] := by
  have ht : ∀ i, (ofSplit q).pr (star ((S.gram *ᵥ u) i)) =
      ∑ j, q.pr (cA D (incA D (S.gram i j))) * (ofSplit q).pr (star (u j)) := by
    intro i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [pr_ofSplit, Matrix.mulVec, dotProduct, star_sum, star_mul', map_sum, map_mul, cA_incA]
  have hsum : ∀ x : Fin S.rank → k,
      ∑ i, ∑ j, x i * q.pr (cA D (incA D (S.gram i j))) * (A * (ofSplit q).pr (star (u j))) =
      A * ∑ m, (F.γ *ᵥ x) m * ∑ r, F.β r m * (ofSplit q).pr (star ((S.gram *ᵥ u) r)) := by
    intro x
    have h1 : ∑ i, ∑ j, x i * q.pr (cA D (incA D (S.gram i j))) * (A * (ofSplit q).pr (star (u j))) =
        A * ∑ i, x i * (ofSplit q).pr (star ((S.gram *ᵥ u) i)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ht i, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h1]
    congr 1
    have hx : x = F.β *ᵥ (F.γ *ᵥ x) := by rw [Matrix.mulVec_mulVec, F.βγ, Matrix.one_mulVec]
    generalize F.γ *ᵥ x = y at hx ⊢
    subst hx
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_comm.trans (Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun r _ => ?_)
    ring
  rw [csec_mem_iff hL]
  simp only [hsum]
  obtain ⟨m₁, hm₁⟩ := hb1
  constructor
  · intro h
    have hx : (fun i => q.sec ((F.β *ᵥ Pi.single m₁ (1 : k)) i)) ∈ latV S L (· = q.v) :=
      (hI _).1 (single_int (k := k) m₁)
    have h2 := h _ hx
    rw [Matrix.mulVec_mulVec, F.γβ, Matrix.one_mulVec,
      Finset.sum_eq_single m₁ (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_mul])
        (fun h => absurd (Finset.mem_univ _) h), Pi.single_eq_same, one_mul,
      Valuation.mem_integer_iff, map_mul, hm₁, mul_one] at h2
    exact (Valuation.mem_integer_iff _ _).2 h2
  · intro hA x hx
    have hy := (hI (F.γ *ᵥ x)).2 (by rwa [Matrix.mulVec_mulVec, F.βγ, Matrix.one_mulVec])
    exact mul_mem hA (sum_mem fun m _ => mul_mem (hy m) (hb m))

theorem line_mem_latV_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (Y : Type) [Fintype Y] [DecidableEq Y]
    (F : Frame k S.rank Y) (u : Fin S.rank → D.host.E) (c : k) (m₀ : Y),
    IsSelfDualC S L → IntIn q S F L → valuation k c = 1 → (∀ r, c * (ofSplit q).pr (u r) = F.β r m₀) →
    (∀ m, ∑ r, F.β r m * (ofSplit q).pr (star ((S.gram *ᵥ u) r)) ∈ 𝒪[k]) →
    (∃ m, valuation k (∑ r, F.β r m * (ofSplit q).pr (star ((S.gram *ᵥ u) r))) = 1) →
    ∀ a ∈ GlobalTheory.FinPl.idAt D (· = q.v),
      ((fun r => a * incA D (u r)) ∈ GlobalTheory.FinPl.latV S L (· = q.v) ↔ a ∈ GlobalTheory.FinPl.intAt D (· = q.v)) := by
  intro D k _ _ _ _ q S L Y _ _ F u c m₀ hL hI hc hu hb hb1 a ha
  have hy : (fun r => a * incA D (u r)) = (fun r => q.sec (q.pr a * (ofSplit q).pr (u r))) +
      (fun r => cA D (q.sec (q.pr (cA D a) * (ofSplit q).pr (star (u r))))) := by
    funext r
    rw [Pi.add_apply]
    conv_lhs => rw [eq_sec_add_cA q ha]
    rw [add_mul, sec_mul_right]
    congr 1
    have e : incA D (u r) = cA D (incA D (star (u r))) := by rw [cA_incA, star_star]
    rw [e, ← RingHom.map_mul, sec_mul_right]
    rfl
  rw [hy]
  refine (decomp hL (fun r => q.pr a * (ofSplit q).pr (u r))
    (fun r => q.pr (cA D a) * (ofSplit q).pr (star (u r)))).trans ?_
  rw [mem_intAt_iff_pr q ha]
  exact and_congr (wpart hI hc hu _) (wbar hL hI hb hb1 _)

end GlobalTheory.SplitLine

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ListConvolutionDistinctPlacesSupportedAndComposi
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.ConvDistinct

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ι : Type) (v : ι → GlobalTheory.FinPl.Pl D) (c : ι → WO S T →₀ ℂ), Function.Injective v → (∀ i, GlobalTheory.FinPl.CombAt (· = v i) (c i)) → ∀ L : List ι, L.Nodup → GlobalTheory.FinPl.CombAt (fun p => ∃ i ∈ L, v i = p) (aconv (L.map c)) ∧ ∀ f, comb ψ S T (aconv (L.map c)) f = L.foldr (fun i g => comb ψ S T (c i) g) f := by
  intro D ψ S T ι v c hv hc L
  have hsupp : ∀ L : List ι, GlobalTheory.FinPl.CombAt (fun p => ∃ i ∈ L, v i = p) (aconv (L.map c)) := by
    intro L
    refine GlobalTheory.QFinLaw.combAt_aconv _ (L.map c) (fun e he => ?_)
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 he
    exact fun u hu => GlobalTheory.DisjComb.mxAt_mono (fun p hp => ⟨b, hb, hp.symm⟩) (hc b u hu)
  intro hL
  refine ⟨hsupp L, fun f => ?_⟩
  induction L with
  | nil => exact GlobalTheory.LevelComb.comb_single_zero ψ f
  | cons a L ih =>
    rw [List.map_cons, GlobalTheory.QFinLaw.comb_aconv_cons, ih hL.of_cons, List.foldr_cons]
    intro x hx y hy
    refine GlobalTheory.DisjComb.symplO_disj (P := (· = v a)) (P' := fun p => ∃ b ∈ L, v b = p) ?_ (hc a x hx) (hsupp L y hy)
    rintro _ rfl ⟨b, hb, hab⟩
    exact (List.nodup_cons.1 hL).1 (hv hab ▸ hb)

end GlobalTheory.ConvDistinct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiveChartsKernelEqClassSumJets
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.ClsKLive

theorem kval : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → JetS I l Z R.ψ R.θ s → (∀ j, j ≤ B.R.m → (g.x j).Is) → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → (clsKL R g P r k tl s J A ι).Kval := by
  intro B X I hOk hPins l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ s J hX hS hx P t r a k tl Ch₀ A ι w hP
  intro j hj hab φ hφ Fv hV hval γ a' y'
  have hj1 : j + 1 ≤ B.R.m := hj
  have hinj : Function.Injective (ι j) := hP.live.inj j
  have hram := ((hP.ram j hj.le φ).1 hφ).2
  let Fc : (I.chain l u a).cls j → PY (I.rec7 l Z).what₂.Tau (B.R.N j) := fun c =>
    if h : ∃ β, A.chOf j c = ι j β then Fv h.choose ⟨c, h.choose_spec⟩ else 0
  have hFcEq : ∀ β (c : {c // A.chOf j c = ι j β}), Fc c.1 = Fv β c := by
    intro β c
    have h : ∃ β, A.chOf j c.1 = ι j β := ⟨β, c.2⟩
    have hb : h.choose = β := hinj (h.choose_spec.symm.trans c.2)
    have gen : ∀ β' (hβ' : A.chOf j c.1 = ι j β'), β' = β → Fv β' ⟨c.1, hβ'⟩ = Fv β c := by
      rintro β' hβ' rfl; rfl
    simp only [Fc, dif_pos h]
    exact gen _ _ hb
  have hFc : ∀ c y, φ c y = evalAt y.1 (Fc c) * ∏ τ, (y.1 τ).det ^ (-(I.chain l u a).sSharp j τ) := by
    intro c y
    by_cases h : ∃ β, A.chOf j c = ι j β
    · obtain ⟨β, hβ⟩ := h
      rw [hFcEq β ⟨c, hβ⟩]
      exact hval β ⟨c, hβ⟩ ⟨y.1, y.2⟩
    · have h0 : Fc c = 0 := by simp only [Fc, dif_neg h]
      rw [h0, show φ c y = 0 by rw [hram c (fun ⟨β, hβ⟩ => h ⟨β, hβ.symm⟩)]; rfl]
      have hz : KJInf.evalAt y.1 (0 : PY (I.rec7 l Z).what₂.Tau (B.R.N j)) = 0 := map_zero (MvPolynomial.eval _)
      rw [hz, zero_mul]
  have key := _root_.GlobalTheory.AdForm.KerVal.kernel_classSum I hOk hPins l Z u a Ch₀ A hP.is j hj1 hab φ Fc hFc a'.1 ⟨y'.1, y'.2⟩
  have e0 : (clsKL R g P r k tl s J A ι).val (j + 1) γ ((tupOf R P u g t r k tl).K j φ) a' y' = (I.chain l u a).K j φ a'.1 ⟨y'.1, y'.2⟩ := rfl
  rw [e0, key]
  letI := (I.chain l u a).clsFin j
  letI : Fintype ((tupOf R P u g t r k tl).Ch j) := (tupOf R P u g t r k tl).fin j
  rw [finsum_eq_sum_of_fintype]
  symm
  refine (Fintype.sum_sigma (fun x : (Σ β : (tupOf R P u g t r k tl).Ch j, (clsKL R g P r k tl s J A ι).cl j β) =>
      ((stabOrd (A.U j (ι j x.1)) (A.h j (ι j x.1) x.2) : ℕ) : ℂ)⁻¹ * A.abelian₂ j x.2.1 a'.1 (subY hab y'.1 (Fv x.1 x.2)) *
        ∏ τ, (y'.1 τ).det ^ (-(I.chain l u I.mu0).sDiv j τ))).symm.trans ?_
  refine Fintype.sum_of_injective (fun x => x.2.1) ?_ _ _ ?_ ?_
  · rintro ⟨β, c, hc⟩ ⟨β', c', hc'⟩ h
    simp only at h
    subst h
    have hb : β = β' := hinj (hc.symm.trans hc')
    subst hb
    rfl
  · intro c hc
    have h : ¬ ∃ β, A.chOf j c = ι j β := fun ⟨β, hβ⟩ => hc ⟨⟨β, c, hβ⟩, rfl⟩
    have h0 : Fc c = 0 := by simp only [Fc, dif_neg h]
    rw [h0]
    erw [map_zero (subY hab _), map_zero, mul_zero, zero_mul]
  · rintro ⟨β, c⟩
    have hst := (_root_.GlobalTheory.ChartReps.twDat_reps I hOk hPins l Z u a Ch₀ A hP.is j hj.le (ι j β)).2.2 c
    simp only
    rw [hFcEq β c, hst]
    rfl

end GlobalTheory.AdForm.ClsKLive
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalBimodelTranslation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TriStep.valK_gl₂ : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₁ → Q.Away c₂ → ∀ φ, IsContAut S.B.A φ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ (g : GL Q.n₂ Q.k) (Ξ₁ : SB (Matrix Q.n₁ Q.n₀ Q.k)) (Ξ₂ Ξ₂' : SB (Matrix Q.n₂ Q.n₁ Q.k)), Ξ₂'.1 = om Q.μ₂ 1 g Ξ₂.1 → IsBiTheta ψ S.B.A S.J.W₀ S.B'.A (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂))) → ∀ f ∈ GlobalTheory.TriStep.space Q, GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂') (rTrans (Q.gl₂ (embX (Q.c + 1) g)) f) = ((nabs Q.k (Matrix.GeneralLinearGroup.det g) ^ ((((Q.c + 1 : ℕ) : ℝ) + 1) / 2 - ((σ + 1 : ℕ) : ℝ)) : ℝ) : ℂ) * GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) f := by
  intro D ψ hψ σ S Q c₁ c₂ h₁ h₂ φ hφ Λ hΛ g Ξ₁ Ξ₂ Ξ₂' hΞ hC f hf
  obtain ⟨a₀, ha, hloc⟩ := (_root_.GlobalTheory.QPl.QStep.gl₂_embX_eq_embA) D ψ σ S Q g
  have hop := (_root_.GlobalTheory.LastOmb.weil_last_local) D ψ σ S Q c₁ c₂ h₂ Λ hΛ g a₀ hloc Ξ₁ Ξ₂ Ξ₂' hΞ
  have hf0 : IsContAut S.B'.V f := by
    have := hf.1 1
    rwa [map_one, GlobalTheory.TriStep.rTrans_one] at this
  have hF := GlobalTheory.SeeSawLastValue.contAut_biLift (GlobalTheory.SeeSaw.biAct_all D) S.weila S.weilb S.B.cpt S.J.cpt S.B.vA S.J.v0 hφ hC
  have hB3 := ((GlobalTheory.SeeSaw.biAct_all D) ψ _ _ _ _ _ _ _ S.oma S.omb S.weila S.weilb _ hC).2.2.1
  have hshift : biLift S.oma S.omb S.B.vA S.J.v0 φ (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂'))) =
      rTrans a₀ (biLift S.oma S.omb S.B.vA S.J.v0 φ (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)))) := by
    funext h
    simp only [biLift, rTrans]
    congr 1; funext h₁; congr 1; funext h₀; congr 1
    have e : ((h₁, h * a₀) : GA D S.J.W₀ × GA D S.B'.A) = (h₁, h) * (1, a₀) := by simp
    rw [e, map_mul, Module.End.mul_apply]
    refine congrArg (fun X => S.omb (h₁, h) X 0) ?_
    funext v
    rw [hB3]
    refine congrArg (fun X => S.oma (h₀, h₁) X 0) ?_
    funext u
    rw [hop u]
  have hc : Q.c + 1 = 2 * σ + 1 := Q.F.bes'.1
  have hexp : ((((Q.c + 1 : ℕ) : ℝ) + 1) / 2 - ((σ + 1 : ℕ) : ℝ)) = 0 := by
    rw [hc]; push_cast; ring
  rw [hexp, Real.rpow_zero, Complex.ofReal_one, one_mul]
  unfold GlobalTheory.TriStep.valK
  rw [hshift, ← ha]
  exact GlobalTheory.Core.Mi.per_rTrans D ψ σ S.B' _ f a₀ hψ hF hf0
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RdEmbEvz
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm

theorem rd_emb_evz : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀), A.Is → ∀ θ, IsInfFam θ → ∀ emb : GA (I.rec7 l Z) (I.rec7 l Z).sp.X' →* GA (I.rec7 l Z) ((I.rec7 l Z).sp.X B.R.m), IsEmbTop (D := (I.rec7 l Z)) (TC.z0 X u) emb → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → ∀ β, ((∃ n : ℕ, 0 < n ∧ ∀ κ, K.lev.chi κ ^ n = 1) → ∀ h (κ : K.lev.U), GlobalTheory.Core.Rk.Top.HasMat h κ.1 → ∃ hU : emb h ∈ A.U B.R.m β, A.chi B.R.m β ⟨emb h, hU⟩ = K.lev.chi κ ∧ ‖((K.lev.chi κ : ℂˣ) : ℂ)‖ = 1) ∧ ∀ φ ∈ (I.fm l u a).Fi B.R.m, ∀ c h, GlobalTheory.Core.Rk.Top.HasMat h (K.y c).1 → ∀ y, A.rd θ B.R.m le_rfl β φ y (emb h) = (I.per l u a).evz φ c y := by
  intro B X I hI hP l Z u a Ch₀ A hA θ hθ emb hemb bad K hK β
  refine ⟨fun hfin => GlobalTheory.AdForm.LevChiTop.emb_mem_chi I hI hP l Z u a Ch₀ A hA emb hemb bad K hK hfin β, ?_⟩
  intro φ hφ c h hh y
  have hβ := GlobalTheory.AdForm.TwDat.Is.chOf_top_eq I hI hP l Z u a Ch₀ A hA ((I.perIn u a).tilC c) β
  subst hβ
  obtain ⟨γ, hγ, k, hk, κ, he, hv⟩ := GlobalTheory.AdForm.TwDat.Is.evz_decomp I hI hP l Z u a Ch₀ A hA θ hθ emb hemb bad K hK c h hh
  obtain ⟨y', hy', hval⟩ := hv φ hφ y
  rw [he, (GlobalTheory.AdForm.rd_charts I hI hP l Z u a Ch₀ A hA θ hθ B.R.m le_rfl φ hφ).2 _ y γ hγ ⟨(I.perIn u a).tilC c, rfl⟩ k hk κ y' hy']
  exact hval

end GlobalTheory.AdForm
end

