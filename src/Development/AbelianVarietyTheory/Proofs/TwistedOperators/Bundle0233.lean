module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0218
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0013
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0935
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterOfSpherical
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitInclMemExtSubIff
section
noncomputable section

namespace GlobalTheory.SplitFlag

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions GlobalTheory.AdelicU GlobalTheory.Cusp
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp extSub coordR act)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {V : Formalism.BasicNotions.HSpace E} {v : HeightOneSpectrum (𝓞 F)}

def wPart (τ : E →ₐ[F] Fv F v) (W : Submodule E V.V) : Submodule (Fv F v) (Fin V.rank → Fv F v) where
  carrier := splitVec τ '' (extSub (F := F) V (Fv F v) W : Set (Fin V.rank → Fv F v ⊗[F] E))
  zero_mem' := ⟨0, zero_mem _, funext fun _ => map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩
    exact ⟨y + z, add_mem hy hz, splitVec_add τ y z⟩
  smul_mem' := by
    rintro c _ ⟨y, hy, rfl⟩
    refine ⟨algebraMap (Fv F v) (Fv F v ⊗[F] E) c • y, Submodule.smul_mem _ _ hy, ?_⟩
    rw [splitVec_smul, AlgHom.commutes]
    rfl

theorem wPart_mono (τ : E →ₐ[F] Fv F v) {A B : Submodule E V.V} (h : A ≤ B) : wPart τ A ≤ wPart τ B := by
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, GlobalTheory.Cusp.extSub_mono V _ h hy, rfl⟩

section Perp

theorem le_perp_perp (W : Submodule E V.V) : W ≤ perp V (perp V W) := fun y hy =>
  GlobalTheory.Cusp.mem_perp.2 fun x hx => by
    have := GlobalTheory.Cusp.mem_perp.1 hx y hy
    simp only [HSpace.hD] at this ⊢
    rw [← V.herm.eq, this, map_zero]

theorem perp_perp (W : Submodule E V.V) : perp V (perp V W) = W := by
  refine (Submodule.eq_of_le_of_finrank_eq (le_perp_perp W) ?_).symm
  have h1 := GlobalTheory.IsoDim.finrank_perp_add V W
  have h2 := GlobalTheory.IsoDim.finrank_perp_add V (perp V W)
  omega

end Perp

section Split

variable (hc : CMData F E) (h : IsCMExt F E hc.sig) (τ : E →ₐ[F] Fv F v)


include h in
theorem mem_extSub_iff_split {W : Submodule E V.V} {y : Fin V.rank → Fv F v ⊗[F] E} :
    y ∈ extSub (F := F) V (Fv F v) W ↔
      splitVec τ y ∈ wPart τ W ∧ splitVec (τ.comp hc.sig) y ∈ wPart (τ.comp hc.sig) W := by
  refine ⟨fun hy => ⟨⟨y, hy, rfl⟩, ⟨y, hy, rfl⟩⟩, fun ⟨⟨y₁, h₁, e₁⟩, ⟨y₂, h₂, e₂⟩⟩ => ?_⟩
  rw [← (splitVecEquiv h τ).symm_apply_apply y]
  change splitIncl h τ (splitVec τ y) + splitIncl h (τ.comp hc.sig) (splitVec (τ.comp hc.sig) y) ∈ _
  rw [← e₁, ← e₂, splitIncl_splitVec, splitIncl_splitVec]
  exact add_mem (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)

include h in
theorem splitIncl_mem_extSub_iff {W : Submodule E V.V} {u : Fin V.rank → Fv F v} :
    splitIncl h τ u ∈ extSub (F := F) V (Fv F v) W ↔ u ∈ wPart τ W := by
  rw [mem_extSub_iff_split hc h τ, splitVec_splitIncl, splitVec_comp_splitIncl]
  exact and_iff_left (zero_mem _)

end Split

section Dual

variable (hc : CMData F E) (h : IsCMExt F E hc.sig) (hJ : IsHermND hc.sig V.gram) (τ : E →ₐ[F] Fv F v)


include h hJ in
theorem mem_wPart_comp_iff {W : Submodule E V.V} {u' : Fin V.rank → Fv F v} :
    u' ∈ wPart (τ.comp hc.sig) W ↔ ∀ u ∈ wPart τ (perp V W), u' ⬝ᵥ V.gram.map τ *ᵥ u = 0 := by
  rw [← splitIncl_mem_extSub_iff hc h (τ.comp hc.sig)]
  conv_lhs => rw [← perp_perp W]
  rw [GlobalTheory.Cusp.mem_extSub_perp hc V]
  constructor
  · rintro H _ ⟨x, hx, rfl⟩
    have := congrArg (splitProj (τ.comp hc.sig)) (H x hx)
    change splitProj (τ.comp hc.sig) (hLin hc.sig V.gram (Fv F v) (splitIncl h (τ.comp hc.sig) u') x) = _ at this
    rwa [splitProj_comp_hLin h hJ, splitVec_splitIncl, map_zero] at this
  · intro H x hx
    change hLin hc.sig V.gram (Fv F v) (splitIncl h (τ.comp hc.sig) u') x = 0
    refine split_ext h τ ?_ ?_
    · rw [splitProj_hLin, splitVec_splitIncl_comp, map_zero, Matrix.mulVec_zero, dotProduct_zero]
    · rw [splitProj_comp_hLin h hJ, splitVec_splitIncl, map_zero]
      exact H _ ⟨x, hx, rfl⟩

end Dual

section Chain

def flagChain (𝔉 : IsoFlag V) (τ : E →ₐ[F] Fv F v) (j : Fin (2 * 𝔉.k + 2)) :
    Submodule (Fv F v) (Fin V.rank → Fv F v) :=
  if hj : (j : ℕ) ≤ 𝔉.k then wPart τ (𝔉.X ⟨j, by omega⟩)
  else wPart τ (perp V (𝔉.X ⟨2 * 𝔉.k + 1 - j, by omega⟩))

variable (𝔉 : IsoFlag V) (τ : E →ₐ[F] Fv F v)

theorem flagChain_of_le {j : Fin (2 * 𝔉.k + 2)} (hj : (j : ℕ) ≤ 𝔉.k) :
    flagChain 𝔉 τ j = wPart τ (𝔉.X ⟨j, by omega⟩) := dif_pos hj

theorem flagChain_of_lt {j : Fin (2 * 𝔉.k + 2)} (hj : 𝔉.k < (j : ℕ)) :
    flagChain 𝔉 τ j = wPart τ (perp V (𝔉.X ⟨2 * 𝔉.k + 1 - j, by omega⟩)) := dif_neg (not_le.2 hj)

theorem flagChain_mono : Monotone (flagChain 𝔉 τ) := by
  intro i j hij
  have hij' : (i : ℕ) ≤ j := hij
  rcases le_or_gt (i : ℕ) 𝔉.k with hi | hi <;> rcases le_or_gt (j : ℕ) 𝔉.k with hj | hj
  · rw [flagChain_of_le 𝔉 τ hi, flagChain_of_le 𝔉 τ hj]
    exact wPart_mono τ (𝔉.strictMono.monotone (Fin.mk_le_mk.2 hij'))
  · rw [flagChain_of_le 𝔉 τ hi, flagChain_of_lt 𝔉 τ hj]
    exact wPart_mono τ (𝔉.le_perp _ _)
  · omega
  · rw [flagChain_of_lt 𝔉 τ hi, flagChain_of_lt 𝔉 τ hj]
    exact wPart_mono τ (GlobalTheory.Cusp.perp_anti (𝔉.strictMono.monotone (Fin.mk_le_mk.2 (by omega))))

theorem wPart_bot : wPart τ (⊥ : Submodule E V.V) = ⊥ := by
  refine eq_bot_iff.2 ?_
  rintro _ ⟨y, hy, rfl⟩
  rw [SetLike.mem_coe, GlobalTheory.Cusp.extSub_bot, Submodule.mem_bot] at hy
  rw [hy, Submodule.mem_bot]
  exact funext fun _ => map_zero _

theorem wPart_top {hc : CMData F E} (h : IsCMExt F E hc.sig) : wPart τ (⊤ : Submodule E V.V) = ⊤ :=
  eq_top_iff.2 fun u _ => ⟨splitIncl h τ u, by rw [GlobalTheory.Cusp.extSub_top]; trivial, splitVec_splitIncl h τ u⟩

theorem flagChain_zero : flagChain 𝔉 τ 0 = ⊥ := by
  rw [flagChain_of_le 𝔉 τ (Nat.zero_le _)]
  convert wPart_bot τ
  exact 𝔉.zero

theorem flagChain_last {hc : CMData F E} (h : IsCMExt F E hc.sig) : flagChain 𝔉 τ (Fin.last _) = ⊤ := by
  rw [flagChain_of_lt 𝔉 τ (by simp; omega)]
  convert wPart_top τ h
  have : (⟨2 * 𝔉.k + 1 - (Fin.last (2 * 𝔉.k + 1) : ℕ), by simp⟩ : Fin (𝔉.k + 1)) = 0 := Fin.ext (by simp)
  rw [this, 𝔉.zero, GlobalTheory.Cusp.perp_bot]

end Chain

end GlobalTheory.SplitFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticFormIsotropicPartAddMiddlePart
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TowerForm

variable {D : D7}

def ad {m n : ℕ} (A : Mx D m n) : Mx D n m := Formalism.UG.cT (cA D) A

theorem ad_mul {l m n : ℕ} (A : Mx D l m) (B : Mx D m n) :
    ad (HMul.hMul A B : Mx D l n) = HMul.hMul (ad B) (ad A) := by
  unfold ad Formalism.UG.cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem cA_incA_sig (e : D.host.E) : cA D (incA D e) = incA D (D.sp.cm.sig e) := by
  simp only [cA, sigR, incA, inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, map_one]

theorem ad_map {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) :
    ad (A.map (incA D) : Mx D m n) = (adj D A).map (incA D) := by
  unfold ad adj Formalism.UG.cT
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, cA_incA_sig]
  rfl

theorem adj_mul {l m n : ℕ} (A : Matrix (Fin l) (Fin m) D.host.E) (B : Matrix (Fin m) (Fin n) D.host.E) :
    adj D (A * B) = adj D B * adj D A := by
  unfold adj Formalism.UG.cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem adj_adj {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) : adj D (adj D A) = A := by
  unfold adj Formalism.UG.cT
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply]
  exact star_star (A i j)

theorem adj_gram (V : HSp D) : adj D V.gram = V.gram := by
  unfold adj Formalism.UG.cT
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply]
  exact GlobalTheory.LatVac.gram_star V j i

theorem adj_gram_inv (V : HSp D) : adj D V.gram⁻¹ = V.gram⁻¹ := by
  have hu := GlobalTheory.LatVac.gram_det_isUnit V
  symm
  apply Matrix.inv_eq_left_inv
  calc adj D V.gram⁻¹ * V.gram = adj D V.gram⁻¹ * adj D V.gram := by rw [adj_gram]
    _ = adj D (V.gram * V.gram⁻¹) := (adj_mul _ _).symm
    _ = 1 := by
      rw [Matrix.mul_nonsing_inv (h := hu)]
      unfold adj Formalism.UG.cT
      simp

theorem hO_eq_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace ((S.gram⁻¹.map (incA D) * ad y) * T.gram.map (incA D) * x) := by
  unfold hO
  rw [Matrix.mul_assoc, Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, ad, Formalism.UG.cT, Matrix.transpose_apply,
    Matrix.map_apply, Finset.mul_sum, mul_assoc]

theorem hO_add_left (S T : HSp D) (x x' y : WO S T) : hO S T (x + x') y = hO S T x y + hO S T x' y := by
  unfold hO
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem hO_add_right (S T : HSp D) (x y y' : WO S T) : hO S T x (y + y') = hO S T x y + hO S T x y' := by
  unfold hO
  simp only [Matrix.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]

theorem hO_mul_mul (V W : HSp D) {m n : ℕ} (y₁ : Mx D W.rank m) (y₂ : Mx D W.rank n)
    (P₁ : Matrix (Fin m) (Fin V.rank) D.host.E) (P₂ : Matrix (Fin n) (Fin V.rank) D.host.E) :
    hO V W (HMul.hMul y₁ (P₁.map (incA D))) (HMul.hMul y₂ (P₂.map (incA D))) =
      Matrix.trace (ad y₂ * W.gram.map (incA D) * y₁ * (P₁ * V.gram⁻¹ * adj D P₂).map (incA D)) := by
  rw [hO_eq_trace, ad_mul, ad_map, Matrix.map_mul, Matrix.map_mul]
  have key := Matrix.trace_mul_comm (V.gram⁻¹.map (incA D) * (adj D P₂).map (incA D))
    (ad y₂ * W.gram.map (incA D) * y₁ * P₁.map (incA D))
  simpa only [Matrix.mul_assoc] using key

theorem adj_zero {m n : ℕ} : adj D (0 : Matrix (Fin m) (Fin n) D.host.E) = 0 := by
  unfold adj Formalism.UG.cT
  simp

section Split

variable {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
  {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E}

theorem coef_iso_iso (hs : IsIsoSplit V V' C B) :
    adj D C * V.gram * V.gram⁻¹ * adj D (adj D C * V.gram) = 0 := by
  have hC : adj D C * V.gram * C = 0 := hs.frame.2.2
  rw [adj_mul, adj_adj, adj_gram, Matrix.mul_nonsing_inv_cancel_right (h := GlobalTheory.LatVac.gram_det_isUnit V),
    ← Matrix.mul_assoc]
  exact hC

theorem coef_iso_mid (hs : IsIsoSplit V V' C B) :
    adj D C * V.gram * V.gram⁻¹ * adj D (V'.gram⁻¹ * adj D B * V.gram) = 0 := by
  rw [adj_mul, adj_mul, adj_adj, adj_gram, adj_gram_inv,
    Matrix.mul_nonsing_inv_cancel_right (h := GlobalTheory.LatVac.gram_det_isUnit V), ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    hs.orth, Matrix.zero_mul]

theorem coef_mid_iso (hs : IsIsoSplit V V' C B) :
    V'.gram⁻¹ * adj D B * V.gram * V.gram⁻¹ * adj D (adj D C * V.gram) = 0 := by
  have hBC : adj D B * (V.gram * C) = 0 := by
    have h := congrArg (adj D) hs.orth
    rwa [adj_mul, adj_mul, adj_adj, adj_gram, adj_zero] at h
  rw [adj_mul, adj_adj, adj_gram, Matrix.mul_nonsing_inv_cancel_right (h := GlobalTheory.LatVac.gram_det_isUnit V),
    Matrix.mul_assoc, hBC, Matrix.mul_zero]

theorem coef_mid_mid (hs : IsIsoSplit V V' C B) :
    V'.gram⁻¹ * adj D B * V.gram * V.gram⁻¹ * adj D (V'.gram⁻¹ * adj D B * V.gram) = V'.gram⁻¹ := by
  rw [adj_mul, adj_mul, adj_adj, adj_gram, adj_gram_inv,
    Matrix.mul_nonsing_inv_cancel_right (h := GlobalTheory.LatVac.gram_det_isUnit V)]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (adj D B), ← Matrix.mul_assoc (adj D B * V.gram), hs.isom,
    Matrix.mul_nonsing_inv (h := GlobalTheory.LatVac.gram_det_isUnit V'), Matrix.mul_one]

theorem trace_swap {m n : ℕ} (Z : Mx D m m) (A : Mx D m n) (Y : Mx D n n) (X : Mx D n m) :
    Matrix.trace (Z * A * Y * X) = Matrix.trace (A * Y * X * Z) := by
  have key := Matrix.trace_mul_comm Z (A * Y * X)
  simpa only [Matrix.mul_assoc] using key

theorem hO_isoPart_add_midPart (hs : IsIsoSplit V V' C B) (y y' : Mx D W.rank r) (x x' : WO V' W) :
    hO V W (isoPart V W C y + midPart V V' W B x) (isoPart V W C y' + midPart V V' W B x') = hO V' W x x' := by
  rw [hO_add_left, hO_add_right, hO_add_right]
  unfold isoPart midPart
  rw [hO_mul_mul, hO_mul_mul, hO_mul_mul, hO_mul_mul, coef_iso_iso hs, coef_iso_mid hs, coef_mid_iso hs,
    coef_mid_mid hs]
  simp only [Matrix.map_zero, map_zero, Matrix.mul_zero, Matrix.trace_zero, zero_add]
  rw [hO_eq_trace, trace_swap]

end Split

theorem symplOH_isoPart_add_midPart : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (y y' : Mx D W.rank r) (x x' : WO V' W),
    symplOH V W (isoPart V W C y + midPart V V' W B x) (isoPart V W C y' + midPart V V' W B x') = symplOH V' W x x' := by
  intro D V V' W r C B hs y y' x x'
  unfold symplOH symplO
  rw [hO_isoPart_add_midPart hs]

end GlobalTheory.TowerForm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
section
noncomputable section

namespace GlobalTheory.LPositivity

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.UnitarySphericalReps
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)

section Analysis

theorem isPosReal_iff {z : ℂ} : IsPosReal z ↔ ∃ r : ℝ, 0 < r ∧ z = r :=
  ⟨fun h => ⟨z.re, h.2, Complex.ext rfl (by simpa using h.1)⟩, by rintro ⟨r, hr, rfl⟩; exact ⟨rfl, hr⟩⟩

theorem isPosReal_prod {ι : Type} (s : Finset ι) {f : ι → ℂ} (h : ∀ i ∈ s, IsPosReal (f i)) :
    IsPosReal (∏ i ∈ s, f i) := by
  refine Finset.prod_induction f IsPosReal (fun a b ha hb => ?_) ⟨rfl, one_pos⟩ h
  obtain ⟨x, hx, rfl⟩ := isPosReal_iff.1 ha
  obtain ⟨y, hy, rfl⟩ := isPosReal_iff.1 hb
  exact isPosReal_iff.2 ⟨x * y, mul_pos hx hy, by simp⟩

theorem isPosReal_of_hasProd {ι : Type} {f : ι → ℂ} {a : ℂ} (ha : HasProd f a) (h0 : a ≠ 0)
    (h : ∀ i, IsPosReal (f i)) : IsPosReal a := by
  have hc : IsClosed {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} :=
    (isClosed_eq Complex.continuous_im continuous_const).inter (isClosed_le continuous_const Complex.continuous_re)
  have := hc.mem_of_tendsto ha (Eventually.of_forall fun s =>
    ⟨(isPosReal_prod s fun i _ => h i).1, (isPosReal_prod s fun i _ => h i).2.le⟩)
  exact ⟨this.1, this.2.lt_of_ne fun e => h0 (Complex.ext e.symm this.1)⟩

theorem isPosReal_eulerFac {B : Multiset ℂˣ} {x : ℂ} (hB : B.map star = B) (hx : star x = x)
    (h : ∀ b ∈ B, ‖(b : ℂ) * x‖ < 1) : IsPosReal (eulerFac B x) := by
  have hre : ∀ b ∈ B, 0 < (1 - (b : ℂ) * x).re := fun b hb => by
    have := (Complex.re_le_norm _).trans_lt (h b hb)
    rw [Complex.sub_re, Complex.one_re]
    linarith
  set u : ℂ := (B.map fun b : ℂˣ => Complex.log (1 - (b : ℂ) * x)).sum with hu
  have h1 : eulerPoly B x = Complex.exp u := by
    rw [hu, Complex.exp_multiset_sum, Multiset.map_map, eulerPoly]
    refine congrArg _ (Multiset.map_congr rfl fun b hb => (Complex.exp_log fun e => ?_).symm)
    simpa [e] using hre b hb
  have h2 : starRingEnd ℂ u = u := by
    conv_rhs => rw [hu, ← hB, Multiset.map_map]
    rw [hu, map_multiset_sum, Multiset.map_map]
    refine congrArg _ (Multiset.map_congr rfl fun b hb => ?_)
    have h3 : (1 - (b : ℂ) * x).arg ≠ Real.pi := fun e => by
      have := (Complex.arg_eq_pi_iff.1 e).1
      linarith [hre b hb]
    simp only [Function.comp_apply, Units.coe_star]
    rw [← Complex.log_conj _ h3, map_sub, map_one, map_mul, show starRingEnd ℂ x = x from hx]
    rfl
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h2
  exact isPosReal_iff.2 ⟨(Real.exp r)⁻¹, by positivity, by rw [eulerFac, h1, hr]; simp⟩

variable {K : Type} [Field K] [NumberField K]

theorem star_npow (w : HeightOneSpectrum (𝓞 K)) (s : ℝ) : star (npow w (-(s : ℂ))) = npow w (-(s : ℂ)) := by
  rw [npow, ← Complex.ofReal_neg, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg _)]
  exact Complex.conj_ofReal _

theorem norm_lt_one_of_bounded {T : Set (HeightOneSpectrum (𝓞 K))} {c : Fam K} {r : ℕ} {κ : ℝ} (h : Bounded T c r κ)
    {s : ℂ} (hs : κ < s.re) {w : HeightOneSpectrum (𝓞 K)} (hw : w ∉ T) :
    ∀ b ∈ c w, ‖(b : ℂ) * npow w (-s)‖ < 1 := fun _ hb =>
  (h.norm_le le_rfl hw hb).trans_lt
    (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast one_lt_absNorm w) (by linarith))

end Analysis

section Normalising

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end Normalising

section Transport

variable {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

end Transport

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {h : w.under (𝓞 F) = v}
  {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GLoc σ J v) V} {B : Multiset ℂˣ}
  (hc : IsCMExt F E σ) (hJ : IsHermND σ J) (hL : Submodule.IsFullLattice E L) (hd : IsSelfDualAt σ J L v)

include hc hJ hL hd

theorem exists_inert_chart (h : w.under (𝓞 F) = v) (hv : IsInertAt F E v w) :
    ∃ c ϖ e, IsUnramInv ϖ c (qV F v) ∧ IsInertChart σ J L h c e ∧ Continuous e ∧ Continuous e.symm := by
  obtain ⟨-, ⟨c, hcj, -⟩, -, -, H⟩ := (exists_isInertChart σ hc v).2 w h hv
  obtain ⟨⟨ϖ, hU⟩, H⟩ := H c hcj
  obtain ⟨e, he⟩ := H n J L hJ hL.fg hL.span_eq_top hd
  exact ⟨c, ϖ, e, hU, he⟩


end Local

section Global

open Formalism.BasicNotions Formalism.BasicNotions.TH

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem split_or_inert (D : D7) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) ∨ IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w := by
  haveI := D.host.isCMField_hostE
  haveI := GlobalTheory.PlaceComp.unramified (E := D.host.E) D.sp.cm
  set v := w.under (𝓞 D.host.F) with hv
  rcases (GlobalTheory.quadratic_unramified_iff_inert_or_split D.host.F D.host.E (isCMExt_host D).2.2.1 v).1
    (fun u _ => Algebra.unramified_iff_forall.1 inferInstance ⟨u.asIdeal, u.isPrime⟩) with h | h
  · exact Or.inr ((h.isMaximal (Ideal.map_ne_bot_of_ne_bot v.ne_bot)).eq_of_le w.isPrime.ne_top Ideal.map_comap_le)
  · obtain ⟨P, Q, hne, e⟩ := Set.ncard_eq_two.1 h
    have hP : P ∈ v.asIdeal.primesOver (𝓞 D.host.E) := by simp [e]
    have hQ : Q ∈ v.asIdeal.primesOver (𝓞 D.host.E) := by simp [e]
    have := hP.2
    have := hQ.2
    exact Or.inl ⟨⟨P, hP.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩,
      ⟨Q, hQ.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, fun e => hne (congrArg (·.asIdeal) e),
      hP.2.over.symm, hQ.2.over.symm⟩

variable {D : D7} {V : HSp D}

theorem star_eq_inv {z : ℂˣ} (h : ‖(z : ℂ)‖ = 1) : star z = z⁻¹ :=
  Units.ext (by simpa using (Complex.inv_eq_conj h).symm)

end Global

end GlobalTheory.LPositivity

end
end

