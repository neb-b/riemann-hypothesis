module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjEqZeroOfSymplO
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalStabiliserScalesRestriction
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SourceUnip

open GlobalTheory.MixModel GlobalTheory.UnipMean

variable {D : D7} {V V' W : HSp D} {r : ℕ}

theorem corner_alg {R a b c : Type} [CommRing R] [Fintype b] [Fintype c] {x1 : Matrix a b R} {m p q : Matrix b b R}
    {C' : Matrix b c R} {B : Matrix c b R} (hq : q = C' * B) (hp : x1 * p = 0)
    (r3 : m = p * m + m * q - p * m * q) : x1 * m = x1 * m * C' * B := by
  have a1 : x1 * (p * m) = 0 := by rw [← Matrix.mul_assoc, hp, Matrix.zero_mul]
  have a2 : x1 * (p * m * q) = 0 := by rw [← Matrix.mul_assoc, a1, Matrix.zero_mul]
  calc x1 * m = x1 * (p * m + m * q - p * m * q) := by rw [← r3]
    _ = x1 * (p * m) + x1 * (m * q) - x1 * (p * m * q) := by rw [Matrix.mul_sub, Matrix.mul_add]
    _ = x1 * m * C' * B := by rw [a1, a2, zero_add, sub_zero, hq]; simp only [Matrix.mul_assoc]

theorem hO_iso (C : Matrix (Fin V.rank) (Fin r) D.host.E) (x : WO V W) (y : Mx D W.rank r) :
    hO V W x (y ⬝ rat (Cᴴ * V.gram)) = (adj y ⬝ (gA W ⬝ (x ⬝ rat C))).trace := by
  rw [hO_eq_trace, rat_mul, rat_conjTranspose, adj_mul, adj_mul, adj_adj, ← gA, adj_gA]
  simp only [Matrix.mul_assoc, giA_gA_cancel]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem symplO_iso_of (C : Matrix (Fin V.rank) (Fin r) D.host.E) {x : WO V W} (hx : x ⬝ rat C = 0)
    (y : Mx D W.rank r) : symplO V W x (y ⬝ rat (Cᴴ * V.gram)) = 0 := by
  rw [symplO_eq, hO_iso, hx, Matrix.mul_zero, Matrix.mul_zero, Matrix.trace_zero, mul_zero, map_zero]

theorem mulC_eq_zero_of_symplO (C : Matrix (Fin V.rank) (Fin r) D.host.E) {x : WO V W}
    (h : ∀ y : Mx D W.rank r, symplO V W x (y ⬝ rat (Cᴴ * V.gram)) = 0) : x ⬝ rat C = 0 := by
  obtain ⟨u, hu⟩ : ∃ u : Mx D W.rank r, u = gA W ⬝ (x ⬝ rat C) := ⟨_, rfl⟩
  have hu0 : u = 0 := by
    ext i j
    have key : ∀ w : AE D, Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * u i j * w) = 0 := fun w => by
      have := h (adj (Matrix.single j i w : Mx D r W.rank))
      rw [symplO_eq, hO_iso, adj_adj, ← hu, trace_single_mul', ← mul_assoc] at this
      exact this
    have hz := eq_zero_of_trace_mul (F := D.host.F) (E := D.host.E) (R := AF D.host.F) _ key
    have hξ : incA D D.host.xi0⁻¹ * incA D D.host.xi0 = 1 := by
      rw [← map_mul, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one]
    have := congrArg (incA D D.host.xi0⁻¹ * ·) hz
    simpa [← mul_assoc, hξ] using this
  have e : giA W ⬝ u = giA W ⬝ (gA W ⬝ (x ⬝ rat C)) := by rw [hu]
  rw [giA_gA_cancel, hu0, Matrix.mul_zero] at e
  exact e.symm

theorem iso_mulC {C : Matrix (Fin V.rank) (Fin r) D.host.E} (hC : IsIsoFrame V C) (y : Mx D W.rank r) :
    y ⬝ rat (Cᴴ * V.gram) ⬝ rat C = 0 := by
  have h : Cᴴ * V.gram * C = 0 := hC.2.2
  rw [Matrix.mul_assoc, ← rat_mul, h, rat_zero, Matrix.mul_zero]

theorem mid_mulC {C : Matrix (Fin V.rank) (Fin r) D.host.E} {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E}
    (hs : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B) (x : WO V' W) :
    x ⬝ rat (V'.gram⁻¹ * Bᴴ * V.gram) ⬝ rat C = 0 := by
  have h0 : Cᴴ * V.gram * B = 0 := hs.orth
  have h1 : Bᴴ * (V.gram * C) = 0 := by
    have := congrArg Matrix.conjTranspose h0
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, gram_conjTranspose,
      Matrix.conjTranspose_zero] at this
  rw [Matrix.mul_assoc, ← rat_mul]
  simp only [Matrix.mul_assoc, h1, Matrix.mul_zero, rat_zero]

section Gen

variable {C : Matrix (Fin V.rank) (Fin r) D.host.E} {C' : Matrix (Fin V.rank) (Fin r) D.host.E}
  {L B₀ : Matrix (Fin r) (Fin V.rank) D.host.E}

theorem gen_fix_iso (h : IsDualPair V C C' L B₀) {g : GA D V} (g2 : rat B₀ ⬝ (mt V g - 1) = 0)
    (y : Mx D W.rank r) : actO V W g 1 (y ⬝ rat (Cᴴ * V.gram)) = y ⬝ rat (Cᴴ * V.gram) := by
  have e1 : rat B₀ ⬝ mt V g = rat B₀ := by
    rwa [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at g2
  have e2 : rat B₀ ⬝ mt V g⁻¹ = rat B₀ := by
    rw [← e1, Matrix.mul_assoc, mt_mul_inv, Matrix.mul_one, e1]
  rw [actO_eq, mt_one, Matrix.one_mul, ← h.hB, Matrix.mul_assoc, e2]

theorem gen_move (h : IsDualPair V C C' L B₀) {g : GA D V} (g1 : (mt V g - 1) ⬝ rat C = 0)
    (r3 : mt V g - 1 = rat (C * L) * (mt V g - 1) + (mt V g - 1) * rat (C' * B₀) -
      rat (C * L) * (mt V g - 1) * rat (C' * B₀))
    {x : WO V W} (hx : x ⬝ rat C = 0) :
    ∃ y : Mx D W.rank r, actO V W g 1 x = x + y ⬝ rat (Cᴴ * V.gram) := by
  have e1 : mt V g ⬝ rat C = rat C := by
    rwa [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at g1
  have e2 : mt V g⁻¹ ⬝ rat C = rat C := by
    rw [← e1, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul, e1]
  obtain ⟨x1, hx1⟩ : ∃ x1 : WO V W, x1 = x ⬝ mt V g⁻¹ := ⟨_, rfl⟩
  have hx1C : x1 ⬝ rat C = 0 := by rw [hx1, Matrix.mul_assoc, e2, hx]
  have hx1p : x1 ⬝ rat (C * L) = 0 := by rw [rat_mul, ← Matrix.mul_assoc, hx1C, Matrix.zero_mul]
  have hx1g : x1 ⬝ mt V g = x := by rw [hx1, Matrix.mul_assoc, mt_inv_mul, Matrix.mul_one]
  have k : x1 ⬝ (mt V g - 1) = x1 ⬝ (mt V g - 1) ⬝ rat C' ⬝ rat B₀ :=
    corner_alg (rat_mul C' B₀) hx1p r3
  refine ⟨-(x1 ⬝ (mt V g - 1) ⬝ rat C'), ?_⟩
  rw [actO_eq, mt_one, Matrix.one_mul, ← h.hB, Matrix.neg_mul, ← k, Matrix.mul_sub, hx1g, Matrix.mul_one, ← hx1]
  abel

end Gen

section Main

variable {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}

theorem weilRepresentation_source_mul (g g' : GA D V) (f : WO V W → ℂ) : ω (g * g', 1) f = ω (g, 1) (ω (g', 1) f) := by
  have : (g * g', (1 : GA D W)) = (g, 1) * (g', 1) := by simp
  rw [this, map_mul]; rfl

theorem weilRepresentation_source_one (f : WO V W → ℂ) : ω (1, 1) f = f := by
  have : ((1 : GA D V), (1 : GA D W)) = 1 := rfl
  rw [this, map_one]; rfl

theorem unit_product_rescale_disjoint_finsets {C : Matrix (Fin V.rank) (Fin r) D.host.E} {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E}
    (hs : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B) (hω : IsWeilDatumO ψ V W χS χT ω)
    {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)}
    (hcov : IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨) {g : GA D V} (hg : g ∈ NI V C) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ f, IsThetaFunO ψ V W f →
      GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (g, 1) f) = c • GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f := by
  have hC := hs.frame
  obtain ⟨C', L, B₀, h⟩ := exists_dualPair hC
  have hP : (1 : Matrix (Fin W.rank) (Fin W.rank) D.host.E).rank = W.rank := by
    rw [Matrix.rank_one, Fintype.card_fin]
  have hQ : (Cᴴ * V.gram).rank = r := by
    refine le_antisymm ?_ ?_
    · simpa using Matrix.rank_le_card_height (Cᴴ * V.gram)
    · have := Matrix.rank_mul_le_left (Cᴴ * V.gram) C'
      rw [← h.hB] at this ⊢
      rwa [h.BC', Matrix.rank_one, Fintype.card_fin] at this
  have eI : ∀ y : Mx D W.rank r, (HMul.hMul (HMul.hMul ((1 : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D))
      (y : Matrix (Fin W.rank) (Fin r) (AE D))) ((Cᴴ * V.gram).map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) =
      y ⬝ rat (Cᴴ * V.gram) := fun y => by
    show rat (1 : Matrix (Fin W.rank) (Fin W.rank) D.host.E) ⬝ y ⬝ rat (Cᴴ * V.gram) = _
    rw [rat_one, Matrix.one_mul]
  unfold NI at hg
  refine Subgroup.closure_induction (p := fun g _ => ∃ c : ℂ, c ≠ 0 ∧ ∀ f, IsThetaFunO ψ V W f →
      GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (g, 1) f) = c • GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f) ?_ ?_ ?_ ?_ hg
  · rintro g ⟨g1, g2, g3⟩
    have g1' : (mt V g - 1) ⬝ rat C = 0 := g1
    obtain ⟨r1, r2, r3⟩ := gen_relations h (x := mt V g - 1) g1' (by rw [h.hB]; exact g2)
      (fun v hv => g3 v (by rw [← h.hB']; exact hv))
    have g2' : rat B₀ ⬝ (mt V g - 1) = 0 := by rw [h.hB]; exact g2
    obtain ⟨c, hc⟩ := _root_.GlobalTheory.IsoMean.mean_scalar D V W W.rank r 1 (Cᴴ * V.gram) hP hQ
      (fun y y' => by rw [eI, eI]; exact symplO_iso_of C (iso_mulC hC y) y') ψ χS χT ω hω μ 𝓨 hcov g 1
      (fun y => by rw [eI]; exact gen_fix_iso h g2' y)
      (fun x hx => by
        obtain ⟨y, hy⟩ := gen_move h g1' r3 (mulC_eq_zero_of_symplO C fun y => by rw [← eI]; exact hx y)
        exact ⟨y, by rw [eI]; exact hy⟩)
    refine ⟨c, Circle.coe_ne_zero c, fun f hf => ?_⟩
    funext x'
    have hm := mid_mulC hs (W := W) x'
    have hh : ∀ (F : WO V W → ℂ) (y : Mx D W.rank r),
        heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x') F
          (HMul.hMul (HMul.hMul ((1 : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D))
            (y : Matrix (Fin W.rank) (Fin r) (AE D))) ((Cᴴ * V.gram).map (incA D)) :
            Matrix (Fin W.rank) (Fin V.rank) (AE D)) =
          F (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x') := fun F y => by
      rw [eI]
      show ψ (symplOH V W _ _) * F _ = _
      have h0 : symplO V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x') (y ⬝ rat (Cᴴ * V.gram)) = 0 := symplO_iso_of C hm y
      rw [symplOH_skew]
      unfold symplOH
      rw [h0, mul_zero, neg_zero, AddChar.map_zero_eq_one, one_mul]
      rfl
    have := hc f hf (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x') (fun y => by rw [eI]; exact symplO_iso_of C hm y)
    simp only [hh] at this
    show ∫ y in 𝓨, ω (g, 1) f _ ∂μ = (c : ℂ) • ∫ y in 𝓨, f _ ∂μ
    rw [this, smul_eq_mul]
  · exact ⟨1, one_ne_zero, fun f _ => by rw [weilRepresentation_source_one, one_smul]⟩
  · rintro a b - - ⟨c, hc, ha⟩ ⟨d, hd, hb⟩
    exact ⟨c * d, mul_ne_zero hc hd, fun f hf => by
      rw [weilRepresentation_source_mul, ha _ (hω.om_pres _ _ hf), hb f hf, smul_smul]⟩
  · rintro a - ⟨c, hc, ha⟩
    refine ⟨c⁻¹, inv_ne_zero hc, fun f hf => ?_⟩
    have := ha _ (hω.om_pres (a⁻¹, 1) f hf)
    rw [← weilRepresentation_source_mul, mul_inv_cancel, weilRepresentation_source_one] at this
    rw [this, smul_smul, inv_mul_cancel₀ hc, one_smul]

end Main

end GlobalTheory.SourceUnip

open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

theorem GlobalTheory.SourceUnip.scal : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ g : GA D V, g ∈ NI V C → ∃ c : ℂ, ∀ f, IsThetaFunO ψ V W f → res V V' W C B μ 𝓨 (ω (g, 1) f) = c • res V V' W C B μ 𝓨 f := by
  intro D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hcov g hg
  obtain ⟨c, -, hc⟩ := GlobalTheory.SourceUnip.unit_product_rescale_disjoint_finsets hs hω hcov hg
  exact ⟨c, hc⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalTargetPreservesIsotropicMean
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnipMean

theorem heisO_zero {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (f : WO V W → ℂ) : heisO ψ V W 0 f = f := by
  funext x
  unfold heisO symplOH symplO hO
  simp

theorem symplO_zero_left {D : D7} (V W : HSp D) (z : WO V W) : symplO V W 0 z = 0 := by
  unfold symplO hO
  simp

theorem mean_target : ∀ (D : D7) (V W : HSp D) (s : ℕ) (L : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W L → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D s V.rank)) (𝓐 : Set (Mx D s V.rank)), IsCovolOne (ratMx D s V.rank) μ 𝓐 → ∀ (n : NI W L) (f : WO V W → ℂ), IsThetaFunO ψ V W f → ∫ a in 𝓐, ω (1, (n : GA D W)) f (HMul.hMul (L.map (incA D)) (a : Matrix (Fin s) (Fin V.rank) (AE D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) ∂μ = ∫ a in 𝓐, f (HMul.hMul (L.map (incA D)) (a : Matrix (Fin s) (Fin V.rank) (AE D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) ∂μ := by
  intro D V W s L hL ψ χS χT ω hω μ 𝓐 hcov n f hf
  have hiso := iso_rat hL
  have e1 : (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hm1 : Formalism.L2.Theta.mt V 1 = 1 := by
    unfold Formalism.L2.Theta.mt
    simp
  have hact : ∀ (g : GA D W) (x : WO V W), actO V W 1 g x = HMul.hMul (Formalism.L2.Theta.mt W g) x := by
    intro g x
    unfold actO
    rw [inv_one, hm1, Matrix.mul_one]
  have hrk : L.rank = s := by
    rw [Matrix.rank_eq_finrank_span_cols]
    exact (finrank_span_eq_card hL.2.1).trans (Fintype.card_fin s)
  have hsym : ∀ y y' : Mx D s V.rank, symplO V W (HMul.hMul (HMul.hMul (L.map (incA D)) y) ((1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D))) (HMul.hMul (HMul.hMul (L.map (incA D)) y') ((1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D))) = 0 := by
    intro y y'
    rw [e1, Matrix.mul_one, Matrix.mul_one]
    exact symplO_frame hiso y y'
  have hsc : ∀ g : GA D W,
      (∀ y : Mx D s V.rank, HMul.hMul (mt W g) (HMul.hMul (GlobalTheory.MixModel.rat L) y) = HMul.hMul (GlobalTheory.MixModel.rat L) y) →
      (∀ x : WO V W, HMul.hMul (GlobalTheory.MixModel.adj (GlobalTheory.MixModel.rat L)) (HMul.hMul (GlobalTheory.MixModel.gA W) x) = 0 →
        ∃ y : Mx D s V.rank, HMul.hMul (mt W g) x = x + HMul.hMul (GlobalTheory.MixModel.rat L) y) →
      ∃ c : ℂ, c ≠ 0 ∧ Sc ψ ω (GlobalTheory.MixModel.rat L) μ 𝓐 g c := by
    intro g hg1 hg2
    have hfix : ∀ y : Mx D s V.rank, actO V W 1 g (HMul.hMul (HMul.hMul (L.map (incA D)) y) ((1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D))) = HMul.hMul (HMul.hMul (L.map (incA D)) y) ((1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D)) := by
      intro y
      rw [e1, Matrix.mul_one, hact]
      exact hg1 y
    have hmov : ∀ x : WO V W, (∀ y : Mx D s V.rank, symplO V W x (HMul.hMul (HMul.hMul (L.map (incA D)) y) ((1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D))) = 0) → ∃ y : Mx D s V.rank, actO V W 1 g x = x + HMul.hMul (HMul.hMul (L.map (incA D)) y) ((1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D)) := by
      intro x hx
      rw [e1] at hx
      simp only [Matrix.mul_one] at hx
      obtain ⟨y, hy⟩ := hg2 x (adj_eq_zero_of_symplO (C := GlobalTheory.MixModel.rat L) hx)
      refine ⟨y, ?_⟩
      rw [e1, Matrix.mul_one, hact]
      exact hy
    obtain ⟨c, hc⟩ := _root_.GlobalTheory.IsoMean.mean_scalar D V W s V.rank L 1 hrk (Matrix.rank_one.trans (Fintype.card_fin _)) hsym ψ χS χT ω hω μ 𝓐 hcov 1 g hfix hmov
    refine ⟨c, Circle.coe_ne_zero c, ?_⟩
    intro f' hf'
    have h0 := hc f' hf' 0 (fun y => symplO_zero_left V W _)
    simp only [heisO_zero, e1, Matrix.mul_one] at h0
    exact h0
  have key := mean_unip hL hω hcov hsc n.2 f hf
  unfold meanL at key
  rw [one_mul] at key
  exact key

end GlobalTheory.UnipMean

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightWittEmbeddingLeConstMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.EmbHeight

open scoped NNReal
open GlobalTheory.AdelicU Formalism.UG

section Generic

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

theorem htOf_le_mul {R : Type} [CommRing R] {N : Matrix n n R → ℝ≥0} {N₁ : Matrix m m R → ℝ≥0} {c : ℝ≥0}
    (hc : 1 ≤ c) (X : GL n R) (x : GL m R) (h1 : N (X : Matrix n n R) ≤ c * max 1 (N₁ (x : Matrix m m R)))
    (h2 : N ((X⁻¹ : GL n R) : Matrix n n R) ≤ c * max 1 (N₁ ((x⁻¹ : GL m R) : Matrix m m R))) :
    htOf N X ≤ c * htOf N₁ x := by
  refine max_le (one_le_mul_of_one_le_of_one_le hc (one_le_htOf _ _)) (max_le ?_ ?_)
  · exact h1.trans (mul_le_mul' le_rfl (max_le (one_le_htOf _ _) (le_htOf _ _)))
  · exact h2.trans (mul_le_mul' le_rfl (max_le (one_le_htOf _ _) (inv_le_htOf _ _)))

theorem bc_val_aff {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (A : Matrix n n R) (B : Matrix n m R)
    (C : Matrix m n R) {X : GL n R} {x : GL m R} (h : (X : Matrix n n R) = A + B * (x : Matrix m m R) * C) :
    ((bc φ X : GL n R') : Matrix n n R') = A.map φ + B.map φ * ((bc φ x : GL m R') : Matrix m m R') * C.map φ := by
  show (X : Matrix n n R).map φ = A.map φ + B.map φ * (x : Matrix m m R).map φ * C.map φ
  rw [h, Matrix.map_add _ (map_add φ), Matrix.map_mul, Matrix.map_mul]

theorem bc_inv_aff {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (A : Matrix n n R) (B : Matrix n m R)
    (C : Matrix m n R) {X : GL n R} {x : GL m R}
    (h : ((X⁻¹ : GL n R) : Matrix n n R) = A + B * ((x⁻¹ : GL m R) : Matrix m m R) * C) :
    (((bc φ X)⁻¹ : GL n R') : Matrix n n R') =
      A.map φ + B.map φ * (((bc φ x)⁻¹ : GL m R') : Matrix m m R') * C.map φ := by
  simp only [← map_inv]
  exact bc_val_aff φ A B C h

theorem map_aff {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (A : Matrix n n R) (B : Matrix n m R)
    (C : Matrix m n R) (y : Matrix m m R) : (A + B * y * C).map φ = A.map φ + B.map φ * y.map φ * C.map φ := by
  rw [Matrix.map_add _ (map_add φ), Matrix.map_mul, Matrix.map_mul]

theorem opNorm_add_le (a b : Matrix n n ℂ) : opNorm (a + b) ≤ opNorm a + opNorm b := by
  unfold opNorm; rw [map_add (f := _)]; exact nnnorm_add_le _ _

theorem exists_opNorm_mul_mul_le (B : Matrix n m ℂ) (C : Matrix m n ℂ) :
    ∃ K : ℝ≥0, ∀ y : Matrix m m ℂ, opNorm (B * y * C) ≤ K * opNorm y := by
  let L : (EuclideanSpace ℂ m →L[ℂ] EuclideanSpace ℂ m) →ₗ[ℂ] (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :=
    { toFun := fun T => Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (B * (Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ)).symm T * C)
      map_add' := fun S T => by simp only [map_add (f := _), Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun r T => by simp only [map_smul, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  let Lc := LinearMap.toContinuousLinearMap L
  refine ⟨‖Lc‖₊, fun y => ?_⟩
  have e : opNorm (B * y * C) = ‖Lc (Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) y)‖₊ := by
    show _ = ‖L _‖₊
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, StarAlgEquiv.symm_apply_apply]
    rfl
  rw [e]
  exact Lc.le_opNNNorm _

end Generic

variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

theorem normFin_add_le (v : HeightOneSpectrum (𝓞 F)) {p q : Type} [Fintype p] [Fintype q]
    (a b : Matrix p q (Fv F v ⊗[F] E)) : normFin F v (a + b) ≤ max (normFin F v a) (normFin F v b) :=
  (normFin_le_iff F v).2 fun i j =>
    (absFin_add_le F v _ _).trans (max_le_max (absFin_le_normFin F v a i j) (absFin_le_normFin F v b i j))

theorem normFin_aff_le (v : HeightOneSpectrum (𝓞 F)) (A : Matrix n n (Fv F v ⊗[F] E)) (B : Matrix n m (Fv F v ⊗[F] E))
    (C : Matrix m n (Fv F v ⊗[F] E)) (y : Matrix m m (Fv F v ⊗[F] E)) :
    normFin F v (A + B * y * C) ≤
      max 1 (max (normFin F v A) (normFin F v B * normFin F v C)) * max 1 (normFin F v y) := by
  set M := max 1 (max (normFin F v A) (normFin F v B * normFin F v C))
  have h1 : (1 : ℝ≥0) ≤ M := le_max_left _ _
  refine (normFin_add_le F v _ _).trans (max_le ?_ ?_)
  · exact (le_max_left _ _ |>.trans (le_max_right 1 _) : normFin F v A ≤ M).trans (le_mul_of_one_le_right' (le_max_left _ _))
  · calc normFin F v (B * y * C) ≤ normFin F v B * normFin F v y * normFin F v C :=
          (normFin_mul_le F v _ _).trans (mul_le_mul' (normFin_mul_le F v _ _) le_rfl)
      _ = (normFin F v B * normFin F v C) * normFin F v y := by ring
      _ ≤ M * max 1 (normFin F v y) :=
          mul_le_mul' ((le_max_right _ _).trans (le_max_right _ _)) (le_max_right _ _)

theorem exists_normInf_aff_le (w : InfinitePlace F) (A : Matrix n n (w.Completion ⊗[F] E))
    (B : Matrix n m (w.Completion ⊗[F] E)) (C : Matrix m n (w.Completion ⊗[F] E)) :
    ∃ c : ℝ≥0, 1 ≤ c ∧ ∀ y : Matrix m m (w.Completion ⊗[F] E),
      normInf F w (A + B * y * C) ≤ c * max 1 (normInf F w y) := by
  classical
  have hK : ∀ τ : EmbOver E w, ∃ K : ℝ≥0, ∀ y : Matrix m m ℂ,
      opNorm (B.map (infEmb τ) * y * C.map (infEmb τ)) ≤ K * opNorm y := fun τ =>
    exists_opNorm_mul_mul_le _ _
  choose K hK using hK
  refine ⟨1 + ∑ τ, (opNorm (A.map (infEmb τ)) + K τ), le_self_add, fun y => (normInf_le_iff F w).2 fun τ => ?_⟩
  have hy : opNorm (y.map (infEmb τ)) ≤ max 1 (normInf F w y) :=
    ((normInf_le_iff F w).1 le_rfl τ).trans (le_max_right _ _)
  have hs : opNorm (A.map (infEmb τ)) + K τ ≤ 1 + ∑ τ, (opNorm (A.map (infEmb τ)) + K τ) :=
    (Finset.single_le_sum (f := fun τ => opNorm (A.map (infEmb τ)) + K τ) (fun _ _ => zero_le)
      (Finset.mem_univ τ)).trans le_add_self
  have e := map_aff (infEmb τ) A B C y
  rw [e]
  refine (opNorm_add_le _ _).trans ?_
  have h3 := hK τ (y.map (infEmb τ))
  refine (add_le_add le_rfl h3).trans ?_
  calc opNorm (A.map (infEmb τ)) + K τ * opNorm (y.map (infEmb τ))
      ≤ opNorm (A.map (infEmb τ)) * max 1 (normInf F w y) + K τ * max 1 (normInf F w y) :=
        add_le_add (le_mul_of_one_le_right' (le_max_left _ _)) (mul_le_mul' le_rfl hy)
    _ = (opNorm (A.map (infEmb τ)) + K τ) * max 1 (normInf F w y) := by rw [add_mul]
    _ ≤ _ := mul_le_mul' hs le_rfl

theorem eventually_normFin_rect_le_one {p q : Type} [Fintype p] [Fintype q] (y : Matrix p q (AF F ⊗[F] E)) :
    ∀ᶠ v in Filter.cofinite, normFin F v (y.map (compFin F E v)) ≤ 1 := by
  simp only [normFin_le_iff, Filter.eventually_all]
  exact fun i j => eventually_absFin_le_one F (y i j)

theorem exists_heightGL_aff_le (A : Matrix n n (AF F ⊗[F] E)) (B : Matrix n m (AF F ⊗[F] E))
    (C : Matrix m n (AF F ⊗[F] E)) :
    ∃ K : ℝ≥0, ∀ (X : GL n (AF F ⊗[F] E)) (x : GL m (AF F ⊗[F] E)),
      (X : Matrix n n (AF F ⊗[F] E)) = A + B * (x : Matrix m m (AF F ⊗[F] E)) * C →
      ((X⁻¹ : GL n (AF F ⊗[F] E)) : Matrix n n (AF F ⊗[F] E)) =
        A + B * ((x⁻¹ : GL m (AF F ⊗[F] E)) : Matrix m m (AF F ⊗[F] E)) * C →
      heightGL F X ≤ K * heightGL F x := by
  have hw := fun w : InfinitePlace F =>
    exists_normInf_aff_le F w (A.map (compInf F E w)) (B.map (compInf F E w)) (C.map (compInf F E w))
  choose cw hcw1 hcw using hw
  set cv : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => max 1 (max (normFin F v (A.map (compFin F E v)))
    (normFin F v (B.map (compFin F E v)) * normFin F v (C.map (compFin F E v)))) with hcv
  have hfin : (Function.mulSupport cv).Finite := by
    have h := ((eventually_normFin_rect_le_one F A).and (eventually_normFin_rect_le_one F B)).and
      (eventually_normFin_rect_le_one F C)
    refine (Filter.eventually_cofinite.1 h).subset fun v hv hv' => hv ?_
    refine max_eq_left (max_le hv'.1.1 ?_)
    exact mul_le_one' hv'.1.2 hv'.2
  refine ⟨(∏ w, cw w) * ∏ᶠ v, cv v, fun X x h1 h2 => ?_⟩
  unfold heightGL
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib,
    ← finprod_mul_distrib hfin (finite_mulSupport_htFin F x)]
  refine mul_le_mul' (Finset.prod_le_prod' fun w _ => ?_)
    (finprod_le_finprod' (finite_mulSupport_htFin F _) (hfin.union (finite_mulSupport_htFin F x) |>.subset
      (Function.mulSupport_mul _ _)) fun v => ?_)
  · refine htOf_le_mul (hcw1 w) _ _ ?_ ?_
    · rw [bc_val_aff _ _ _ _ h1]; exact hcw w _
    · rw [bc_inv_aff _ _ _ _ h2]; exact hcw w _
  · refine htOf_le_mul (le_max_left _ _) _ _ ?_ ?_
    · rw [bc_val_aff _ _ _ _ h1]; exact normFin_aff_le F v _ _ _ _
    · rw [bc_inv_aff _ _ _ _ h2]; exact normFin_aff_le F v _ _ _ _

end GlobalTheory.EmbHeight

namespace GlobalTheory.EmbHeight

open scoped NNReal
open GlobalTheory.AdelicU

theorem unitaryAdelicHeight_wittEmbedding_le : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ C : ℝ, ∀ g : GA D S₀,
    height S (d.emb0 g) ≤ C * height S₀ g := by
  intro D S S₀ ρ d
  obtain ⟨K, hK⟩ := exists_heightGL_aff_le D.host.F (d.jX ⬝ d.pX + d.jY ⬝ d.pY) d.j0 d.p0
  refine ⟨K, fun g => ?_⟩
  have h1 : ∀ g : GA D S₀, mt S (d.emb0 g) = (d.jX ⬝ d.pX + d.jY ⬝ d.pY) + d.j0 ⬝ mt S₀ g ⬝ d.p0 := fun g => by
    rw [d.unitaryMatrix_wittCoreEmbedding, add_right_comm]
  have h := hK (matHom S (d.emb0 g)) (matHom S₀ g) (h1 g) (by
    rw [← map_inv, ← map_inv]
    exact h1 g⁻¹)
  show ((heightGL D.host.F _ : ℝ≥0) : ℝ) ≤ (K : ℝ) * ((heightGL D.host.F _ : ℝ≥0) : ℝ)
  exact_mod_cast h

end GlobalTheory.EmbHeight

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorRightIntertwinesHeisenbergDerivativeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
open GlobalTheory.HeisOrbit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_operator_right_intertwines_heisenberg_derivative : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsStd ψ → M.IsWeil ψ χX χW om → ∀ (h : UA σ W.J) (Th : SInf F (Fin n × Fin d) → SInf F (Fin n × Fin d)),
    (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (1, h)) f (Th f)) → ∀ u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u →
    ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ → ∀ y,
      Th f₁ y = GlobalTheory.HeisOrbit.dOp (GlobalTheory.HeisOrbit.archCo M.co (u * (mat h)ᵀ)).1 (GlobalTheory.HeisOrbit.archCo M.co (u * (mat h)ᵀ)).2 (Th f) y := by
  first | exact @GlobalTheory.HeisOrbit.weil_heisDeriv_intertw | exact GlobalTheory.HeisOrbit.weil_heisDeriv_intertw | (intros; apply GlobalTheory.HeisOrbit.weil_heisDeriv_intertw <;> assumption)
end

