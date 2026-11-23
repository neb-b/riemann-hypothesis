module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1581
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1570
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.PieriBlockIdeals.Bundle0003
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastMapNorm
public import Formalism.LocalToGlobal.Divisibility.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0423
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1571
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasRationalWeilOperatorLeviBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1543

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixTrivialOffInertPlaceUnitaryAtPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertBigCell

theorem idem_split_mul {R S : Type} [CommRing R] [Ring S] (e : R) (ι : S →+ R)
    (he : (1 - e) * (1 - e) = 1 - e) (hι : ∀ x, (1 - e) * ι x = 0) (hmul : ∀ x y, ι (x * y) = ι x * ι y)
    {l m n : Type} [Fintype m] (A : Matrix l m R) (B : Matrix m n R) (X : Matrix l m S) (Y : Matrix m n S) :
    ((1 - e) • A + X.map ι) * ((1 - e) • B + Y.map ι) = (1 - e) • (A * B) + (X * Y).map ι := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hmul]
  linear_combination (A i k * B k j) * he + A i k * hι (Y k j) + B k j * hι (X i k)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)}

theorem iotaW_apply (hw : Formalism.UG.IsInertAt F E v w) (x : w.adicCompletion E) :
    iotaW hw x = GlobalTheory.InertLocField.liftT E v ((InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm x) := rfl

theorem iotaW_injective (hw : Formalism.UG.IsInertAt F E v w) : Function.Injective (iotaW hw) :=
  (GlobalTheory.InertLocField.liftT_injective v).comp (InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm.injective

theorem iotaW_mul (hw : Formalism.UG.IsInertAt F E v w) (x y : w.adicCompletion E) :
    iotaW hw (x * y) = iotaW hw x * iotaW hw y := by
  rw [iotaW_apply, iotaW_apply, iotaW_apply, map_mul, GlobalTheory.InertLocField.liftT_mul]

theorem idem_mul_iotaW (hw : Formalism.UG.IsInertAt F E v w) (x : w.adicCompletion E) :
    algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) * iotaW hw x = iotaW hw x := by
  rw [← Algebra.smul_def, GlobalTheory.InertLocField.liftV_one_smul, iotaW_apply, GlobalTheory.InertLocField.evT_liftT]

theorem one_sub_mul_iotaW (hw : Formalism.UG.IsInertAt F E v w) (x : w.adicCompletion E) :
    (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) * iotaW hw x = 0 := by
  rw [sub_mul, one_mul, idem_mul_iotaW, sub_self]

theorem one_sub_idem (v : Pl (F := F)) :
    (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) * (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) =
      1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) := by
  have h : algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) * algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) =
      algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) := by
    rw [← map_mul, ← GlobalTheory.InertLocField.liftV_mul, mul_one]
  linear_combination h

theorem complEquiv_symm_algebraMap' (hw : Formalism.UG.IsInertAt F E v w) (x : E) :
    (InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm (algebraMap E _ x) = (1 : Fv F v) ⊗ₜ[F] x := by
  rw [RingEquiv.symm_apply_eq]
  change _ = toCompl (under_eq_of_isInertAt hw) ((1 : Fv F v) ⊗ₜ[F] x)
  rw [toCompl_tmul, map_one, one_mul]

theorem iotaW_algebraMap (hw : Formalism.UG.IsInertAt F E v w) (x : E) :
    iotaW hw (algebraMap E _ x) = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) * inclR (F := F) (AF F) x := by
  rw [iotaW_apply, complEquiv_symm_algebraMap', GlobalTheory.InertLocField.liftT_tmul]
  change _ = (GlobalTheory.LatVac.liftV v 1 ⊗ₜ[F] (1 : E)) * ((1 : AF F) ⊗ₜ[F] x)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem iotaW_conjW (σ : E →ₐ[F] E) (hw : Formalism.UG.IsInertAt F E v w) (x : w.adicCompletion E) :
    iotaW hw (conjW σ hw x) = cA σ (iotaW hw x) := by
  rw [iotaW_apply, iotaW_apply, ← GlobalTheory.InertLocField.liftT_sigR]
  congr 1
  exact (InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm_apply_apply _

theorem incM_split (hw : Formalism.UG.IsInertAt F E v w) {l m : Type} (J : Matrix l m E) :
    incM F J = (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) • incM F J +
      (J.map (algebraMap E (w.adicCompletion E))).map (iotaW hw) := by
  ext i j
  simp only [incM, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, iotaW_algebraMap]
  ring

end GlobalTheory.InertBigCell

namespace GlobalTheory.InertBigCell

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)}

theorem iotaW_one (hw : Formalism.UG.IsInertAt F E v w) :
    iotaW hw 1 = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) := by
  rw [← map_one (algebraMap E (w.adicCompletion E)), iotaW_algebraMap]
  change _ * inclR (F := F) (AF F) 1 = _
  rw [(inclR (F := F) (AF F)).map_one, mul_one]

theorem diagCols_split (hw : Formalism.UG.IsInertAt F E v w) (ι : Type) [DecidableEq ι] :
    (diagCols ι : Matrix (ι ⊕ ι) ι (AE F E)) =
      (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) • (diagCols ι : Matrix (ι ⊕ ι) ι (AE F E)) +
        (diagCols ι : Matrix (ι ⊕ ι) ι (w.adicCompletion E)).map (iotaW hw) := by
  ext i j
  rcases i with i | i <;>
  · simp only [diagCols, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr, Matrix.one_apply]
    split_ifs
    · rw [iotaW_one]; ring
    · rw [map_zero]; ring

theorem invOf_two_smul_add_iotaW (hw : Formalism.UG.IsInertAt F E v w) (t : AE F E) (x : w.adicCompletion E) :
    ⅟(2 : AF F) • (t + t + iotaW hw x) = t + iotaW hw ((2 : w.adicCompletion E)⁻¹ * x) := by
  have h2 : (2 : w.adicCompletion E) ≠ 0 := by
    rw [← map_ofNat (algebraMap E (w.adicCompletion E)) 2]
    exact (map_ne_zero _).2 two_ne_zero
  have hx : iotaW hw x = iotaW hw (2⁻¹ * x) + iotaW hw (2⁻¹ * x) := by
    rw [← map_add (f := _), ← add_mul, ← two_mul, mul_inv_cancel₀ h2, one_mul]
  rw [hx, show t + t + (iotaW hw (2⁻¹ * x) + iotaW hw (2⁻¹ * x)) =
      (2 : AF F) • (t + iotaW hw (2⁻¹ * x)) by rw [two_smul]; abel, smul_smul, invOf_mul_self, one_smul]

theorem glueW_transpose (hw : Formalism.UG.IsInertAt F E v w) {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι (w.adicCompletion E)) : (glueW hw P)ᵀ = glueW hw Pᵀ := by
  rw [glueW, glueW, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, Matrix.transpose_map]

theorem glueW_map_cA (σ : E →ₐ[F] E) (hw : Formalism.UG.IsInertAt F E v w) {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι (w.adicCompletion E)) : (glueW hw P).map (cA σ) = glueW hw (P.map (conjW σ hw)) := by
  ext i j
  simp only [glueW, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul, map_sub,
    map_one, AlgHom.commutes, iotaW_conjW]
  congr 2
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem glueW_read_at_place (σ : E →ₐ[F] E) (hw : Formalism.UG.IsInertAt F E v w) {ι : Type} [Fintype ι] [DecidableEq ι] :
  (∀ (J : Matrix ι ι E) (P : Matrix ι ι (w.adicCompletion E)),
    (GlobalTheory.InertBigCell.glueW hw P)ᵀ * incM F J * (GlobalTheory.InertBigCell.glueW hw P).map (cA σ) = incM F J ↔
      Pᵀ * J.map (algebraMap E (w.adicCompletion E)) * P.map (GlobalTheory.InertBigCell.conjW σ hw) = J.map (algebraMap E (w.adicCompletion E))) ∧
  (∀ P : Matrix (ι ⊕ ι) (ι ⊕ ι) (w.adicCompletion E), P * diagCols ι = diagCols ι →
    GlobalTheory.InertBigCell.glueW hw P * (diagCols ι : Matrix (ι ⊕ ι) ι (AE F E)) = diagCols ι) ∧
  (∀ P : Matrix (ι ⊕ ι) (ι ⊕ ι) (w.adicCompletion E),
    ⅟(2 : AF F) • ((GlobalTheory.InertBigCell.glueW hw P).toBlocks₁₁ + (GlobalTheory.InertBigCell.glueW hw P).toBlocks₁₂ +
      (GlobalTheory.InertBigCell.glueW hw P).toBlocks₂₁ + (GlobalTheory.InertBigCell.glueW hw P).toBlocks₂₂) =
    GlobalTheory.InertBigCell.glueW hw ((2 : w.adicCompletion E)⁻¹ • (P.toBlocks₁₁ + P.toBlocks₁₂ + P.toBlocks₂₁ + P.toBlocks₂₂))) := by
  set e := algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) with he_def
  refine ⟨fun J P => ?_, fun P hP => ?_, fun P => ?_⟩
  · rw [glueW_transpose, glueW_map_cA, glueW, glueW, incM_split hw J, idem_split_mul e (iotaW hw) (one_sub_idem v) (one_sub_mul_iotaW hw) (iotaW_mul hw), idem_split_mul e (iotaW hw) (one_sub_idem v) (one_sub_mul_iotaW hw) (iotaW_mul hw), Matrix.one_mul, Matrix.mul_one,
      add_right_inj]
    exact (Matrix.map_injective (iotaW_injective hw)).eq_iff
  · rw [diagCols_split hw ι, glueW, idem_split_mul e (iotaW hw) (one_sub_idem v) (one_sub_mul_iotaW hw) (iotaW_mul hw),
      Matrix.one_mul]
    exact congrArg (fun M => (1 - e) • (diagCols ι : Matrix (ι ⊕ ι) ι (AE F E)) + M.map (iotaW hw)) hP
  · ext i j
    simp only [glueW, Matrix.smul_apply, Matrix.add_apply, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁,
      Matrix.toBlocks₂₂, Matrix.of_apply, Matrix.map_apply, smul_eq_mul, Matrix.one_apply, Sum.inl.injEq,
      Sum.inr.injEq, reduceCtorEq, if_false, mul_zero, add_zero]
    rw [← invOf_two_smul_add_iotaW hw, map_add (f := _), map_add (f := _), map_add (f := _)]
    congr 1
    abel

end GlobalTheory.InertBigCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BddMemSpanShortGen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.SupFull

theorem isBddSec_smul {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {la : Wt X.Ψ r}
    {P : Frame X.Ψ r → ℂ} (t : ℂ) (h : X.IsBddSec la P) : X.IsBddSec la (t • P) := by
  obtain ⟨⟨h1, h2, h3⟩, C, hC⟩ := h
  refine ⟨⟨h1.const_smul t, fun x hx b hb => ?_, fun g hg x hx => ?_⟩, ‖t‖ * C, fun x hx => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, h2 x hx b hb]; ring
  · simp only [Pi.smul_apply, smul_eq_mul, h3 g hg x hx]; ring
  · rw [Formalism.L2.PjFree.pnorm_smul]
    exact mul_le_mul_of_nonneg_left (hC x hx) (norm_nonneg _)


set_option maxHeartbeats 800000 in
theorem bdd_mem_span_shortGen : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → l.A = 1 → (∀ k k', (U.X k).Gm = (U.X k').Gm ∧ (U.X k).ξ0 = (U.X k').ξ0) → (∀ k, HasPrinc (U.X k) l.M) → d.IsLev → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → UnitC d → ¬ 3 ∣ d.pd → (Dw.p + Dw.q ≤ n → ∃ ph ψ x₀, d.PhiPin ph ψ x₀) → ∀ (nab : NabV Xo c) (bad nV : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < bad → Dom a n → 4 * (Module.finrank ℚ E * r) + 4 ≤ n → (∀ k, ChiOne (U.X k) (Formalism.L2.PjFree.laU U a n k)) → ShortValTot Xo c nab bad nV a n d → ∀ P : Formalism.L2.PjFree.FDSec U.X, (∀ k, (U.X k).IsBddSec (Formalism.L2.PjFree.laU U a n k) (P k)) → (∀ k x, x ∉ (U.X k).dom → P k x = 0) → P ∈ Submodule.span ℂ (Formalism.L2.PjFree.rdU U '' shortGen Xo c nab bad nV a n d) := by
  intro hci E _ _ _ H Dw l Xo c n d σ r U hσ hU hr1 hA hG hpr hlev hnab huc h3 hpin nab bad nV a hbad hdom hbig
    hchi htot P hP1 hP0
  rcases isEmpty_or_nonempty U.Comp with hemp | ⟨⟨k₀⟩⟩
  · have : P = 0 := funext fun k => (hemp.false k).elim
    rw [this]
    exact Submodule.zero_mem _
  obtain ⟨W⟩ := nonempty_uw hU
  have hrpq : r = Dw.p + Dw.q := hU.1
  have hn : r ≤ n := by
    have := Module.finrank_pos (R := ℚ) (M := E)
    nlinarith
  have hev : Even n := by
    unfold Formalism.L2.Pj.Dom at hdom
    tauto
  have huw := _root_.GlobalTheory.Dict.uw_lattice E H Dw l Xo c σ r U hσ hU hr1 W
  have hsame : ∀ k, SameSp (U.X k) (U.X k₀) := fun k =>
    ⟨Finset.ext fun τ => ((hU.2.1 k).2 τ).trans ((hU.2.1 k₀).2 τ).symm, (hG k k₀).1,
      (hU.2.1 k).1.trans (hU.2.1 k₀).1.symm, (hG k k₀).2, by rw [(huw k).1, (huw k₀).1, (hG k k₀).2]⟩
  obtain ⟨ph, ψ, x₀, hph⟩ := hpin (hrpq ▸ hn)
  obtain ⟨Dc, hDe, -⟩ := _root_.GlobalTheory.Dict.exists_dic E H Dw l c σ r W.g n (U.X k₀) a W.e hσ hrpq (hU.2.1 k₀).1 (hU.2.1 k₀).2
    (huw k₀).2.1 hdom
  obtain ⟨D, hD⟩ := _root_.GlobalTheory.LevelTied.exists_levTie E H Dw l Xo c n d σ r (U.X k₀) hn hrpq (huw k₀).2.1 hlev h3 ph ψ x₀ hph
  obtain ⟨v₀, mu, hv₀, hmu⟩ := GlobalTheory.SW.exists_vacua_and_multipliers E r (U.X k₀) W.g Dc.bas Dc.idx n Dc.sympl hev D
  obtain ⟨x0, ga, δ, hadm, hset, hsep⟩ := GlobalTheory.T.exists_components_lattices_moved_to_level_family E H Dw l Xo c n d σ r U hσ hU hr1 hA hlev W k₀ hsame ph D hn hD
  obtain ⟨u, hu, hread⟩ := _root_.GlobalTheory.Dict.rdU_short_eq_thP hci E H Dw l Xo c n d σ r U hσ hU hr1 hlev hnab huc ph ψ x₀ hph W (U.X k₀) a
    hdom Dc D hn hDe hD v₀ hv₀ x0
  choose C hC hrd using fun k => hread k (hsame k) (ga k) (δ k) (hset k).1 (hset k).2.1 (hset k).2.2.1
    (hset k).2.2.2.1 (hset k).2.2.2.2
  have hmu1 := _root_.GlobalTheory.Dict.mult_eq_one_on_stab E H Dw l Xo c n d σ r W.g (U.X k₀) Dc.bas Dc.idx D hn ph Dc.sympl hev hD
    (W.F.Di (W.ik k₀)) (W.emb k₀) (huw k₀).2.2.2.1 (huw k₀).2.2.2.2.1 (huw k₀).2.2.2.2.2.1 (huw k₀).2.2.2.2.2.2
    v₀ hv₀ mu hmu
  have hgrp := (GlobalTheory.SW.level_laws E r (U.X k₀) W.g Dc.bas Dc.idx n Dc.sympl hev D hn).2.2.1
  have hpull := fun k => _root_.GlobalTheory.Dict.isStabForm_pull E r (U.X k) (U.X k₀) (hsame k) (ga k) (Formalism.L2.PjFree.laU U a n k)
    (wtOf (U.X k₀) Dc.hr Dc.k Dc.k' n) D.grp l.M ((C k)⁻¹ • P k) (hset k).1
    (fun τ i => by
      rw [Dc.wt_eq]
      simp only [wtX, Formalism.L2.PjFree.laU, (hsame k).p0])
    (fun g' hg' => ⟨((hgrp g').1 hg').1, fun hfix => (hmu1 _ (hset k).2.1 g' hg' hfix).2⟩)
    (hpr k) (hchi k) (isBddSec_smul _ (hP1 k))
  have hM2 : 0 < d.l₂.M := lt_of_lt_of_le (by norm_num) d.l₂.three_le
  have hMm : ((2 * bad * d.l₂.M : ℕ) : 𝓞 E) ∈ D.𝔪 := by
    rw [hD.m, Nat.cast_mul]
    refine Ideal.mul_mem_left _ _ ?_
    have h1 : (d.l₂.M : 𝓞 E) ∈ d.l₂.Mb * d.l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [d.l₂.prod]
      exact Ideal.mem_span_singleton_self _
    unfold Mfr
    exact (Submodule.mem_inf.1 (Ideal.mul_le_inf h1)).2
  obtain ⟨m, Λ, Pj, hΛ, hQ⟩ := _root_.GlobalTheory.Dict.stabForms_eq_sum_thP E r (U.X k₀) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hev hbig D hn
    (2 * bad * d.l₂.M) (Mfr l) (Jd d) (by positivity) hMm hD.prod hD.cop v₀ hv₀ mu hmu Dc.k Dc.k' U.Comp
    (fun k => mapL (ga k) (U.X k).Λ) _ (fun k => (hset k).2.1) hsep
    (fun k g' hg' hfix => (hmu1 _ (hset k).2.1 g' hg' hfix).1) (fun k => (hpull k).1)
  have hgl := fun j => GlobalTheory.Dict.GenLatCmp.genLat_vset E n (Λ j)
  have hg1 := fun j => (hgl j).1 bad d.l₂.M hbad d.l₂.odd (hΛ j).1
  choose N hN using fun j => (hg1 j).2.2.2
  have hV : ∀ j, Λ j ∈ Vset E n d.l₂.M := fun j => (hgl j).2.2.1 _ _ (Dvd.intro_left _ rfl) (hΛ j).1
  choose mj t R hR hPj using fun j => _root_.GlobalTheory.Dict.rowHighest_eq_sum_harmL E H Dw l c σ r W.g Dw.p n (U.X k₀) a Dc (Λ j) (N j)
    (hN j).1.pos ((hN j).2.2.trans inf_le_left) (Pj j) (hΛ j).2
  choose f hf hfr using fun j i => (htot ⟨Λ j⟩ (N j) x0 (R j i) (hg1 j).1 (hg1 j).2.1 (hg1 j).2.2.1 (hN j)
    (hadm _) (hR j i)).2
  have hPe : P = ∑ j, ∑ i, (t j i * (u (Λ j) (N j))⁻¹) • Formalism.L2.PjFree.rdU U (f j i) := by
    funext k x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hx : x ∈ (U.X k).dom
    · obtain ⟨hx1, hx2, -⟩ := ((hpull k).2 0 (differentiableOn_const 0) (by simp)).2 x hx
      have e1 := hQ k _ hx1
      rw [hx2, Pi.smul_apply, smul_eq_mul, inv_mul_eq_iff_eq_mul₀ (hC k)] at e1
      rw [e1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hPj j, theta_sum_smul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hrd k (Λ j) (hV j) (N j) (hN j) (R j i) (hR j i).1 (f j i) (hf j i) (hfr j i) x hx]
      have := hu (Λ j) (hV j) (N j) (hN j)
      field_simp
    · rw [hP0 k x hx]
      refine (Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun i _ => ?_).symm
      have : Formalism.L2.PjFree.rdU U (f j i) k x = 0 := dif_neg hx
      rw [this, mul_zero]
  rw [hPe]
  refine Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨f j i, ⟨hf j i, ⟨Λ j⟩, N j, x0, R j i, (hg1 j).1, (hg1 j).2.1, (hg1 j).2.2.1, hN j,
    hadm _, hR j i, hfr j i⟩, rfl⟩


set_option maxHeartbeats 1000000 in
theorem exists_datum_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ r), 1 ≤ r → l.A = 1 → Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ k k', (U.X k).Gm = (U.X k').Gm ∧ (U.X k).ξ0 = (U.X k').ξ0) → (∀ k, HasPrinc (U.X k) l.M) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → 4 * (Module.finrank ℚ E * r) + 4 ≤ n → (∀ k, ChiOne (U.X k) (Formalism.L2.PjFree.laU U a n k)) → ∃ (d : DeltaDat Xo c n) (nab : NabV Xo c), d.IsLev ∧ (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) ∧ (∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ y₂ ^ 1 = 1) ∧ d.l₂ = l ∧ (∃ ph ψ x₀, d.PhiPin ph ψ x₀) ∧ ∀ f ∈ sec Xo c a n, (∀ k, (U.X k).IsBddSec (Formalism.L2.PjFree.laU U a n k) (Formalism.L2.PjFree.rdU U f k)) → f ∈ Submodule.span c.F (shortGen Xo c nab 1 0 a n d) := by
  intro E _ _ _ H Dw l Xo c r σ U hr hA hσ hU hG hP a n hdom hn hχ
  have hC : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 := GlobalTheory.ChartFree.chartIndep
  have hrk : r = Dw.p + Dw.q := hU.1
  have h1 : 1 ≤ Dw.p + Dw.q := hrk ▸ hr
  have hL : Out.Laws := GlobalTheory.firstFiveLaws.1
  have hB : Out.SecBaseChangeSt := hL.secBaseChange
  have hnr : Dw.p + Dw.q ≤ n := by
    have h0 : 0 < Module.finrank ℚ E := Module.finrank_pos
    have : r ≤ Module.finrank ℚ E * r := Nat.le_mul_of_pos_left r h0
    omega
  have hd : ∃ d : DeltaDat Xo c n, d.IsLev ∧ (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) ∧ d.cδ = 1 ∧
      d.pd = 1 ∧ d.l₂ = l ∧ ∃ ph x₀, d.PhiPin ph 1 x₀ := by
    obtain ⟨d, e1, -, e2, -, -, hδ, hlev, hnab⟩ :=
      GlobalTheory.LevelCover.exists_deltaDat_isLev E H Dw l Xo c h1 n 1 ⊤ l Xo c rfl
        ⟨dvd_rfl, le_rfl, dvd_rfl⟩ (Nat.mul_one _).symm (Nat.coprime_one_left _) (Ideal.mul_top _).symm
        (top_sup_eq _)
    obtain ⟨f, ph, x₀, hpin⟩ := GlobalTheory.exists_phiPin_of_character E H Dw l Xo c n d hlev hnr 1
    exact ⟨{ d with φδ := f }, hlev, hnab, hδ, e1, e2, ph, x₀, hpin⟩
  obtain ⟨d, hlev, hnab, hδ, hpe, hle, ph, x₀, hpin⟩ := hd
  have hAe : d.l₂.A = l.A := congrArg (·.A) hle
  have hT : AllTest d.Xo₂ d.c₂ := GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw d.l₂ d.Xo₂ d.c₂
  obtain ⟨_, nab, -⟩ := GlobalTheory.CanonConn.exists_isNab hL E H Dw l Xo c
  have hunit : UnitC d := fun A y => by
    have : evR d.Xo₂ d.c₂ d.cδ y = 1 := by
      rw [hδ]
      exact evalAt_one _ _ _ (hT _ _)
    rw [this, norm_one]
  have h3 : ¬ 3 ∣ d.pd := by rw [hpe]; decide
  have htie : d.PsiTie 1 := by
    intro k g ρ _ _ _ _ K _ _ _ y y' _
    have h : ∀ z : FrPt d.Xo₂ d.c₂ K, evR d.Xo₂ d.c₂ d.cδ z = 1 := fun z => by
      rw [hδ]
      exact evalAt_one _ _ _ (hT _ _)
    change evR d.Xo₂ d.c₂ d.cδ y' =
      algebraMap d.c₂.F K (d.eF ((1 : c.Fˣ) : c.F)) * evR d.Xo₂ d.c₂ d.cδ y
    rw [h y, h y']
    simp
  have htot : ShortValTot Xo c nab 1 0 a n d :=
    GlobalTheory.shortValTot_of_pinned hL hC E H Dw l Xo c n d (GlobalTheory.levelMaps_closed hL E H Dw h1)
      (GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c).2.2.1 (GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c)
      (GlobalTheory.Frames.algebraic_laws hB E H Dw _ _ _).2.2.1 hT hlev hAe hnab (fun _ => ⟨ph, 1, x₀, hpin, htie⟩)
      nab 1 0 a
  refine ⟨d, nab, hlev, hnab, fun k _ _ y => ?_, hle, ⟨ph, 1, x₀, hpin⟩, fun f hf hb => ?_⟩
  · rw [pow_one, hδ]
    exact evalAt_one _ _ _ (hT _ _)
  · exact mem_span_of_map_mem_span_image (Formalism.L2.PjFree.rdU U) (sec Xo c a n)
      (GlobalTheory.reading_linearIndependent_and_injective hB E H Dw l Xo c σ r U hU a n).1
      (shortGen Xo c nab 1 0 a n d) (fun g hg => hg.1) hf
      (bdd_mem_span_shortGen hC E H Dw l Xo c n d σ r U hσ hU hr hA hG hP hlev hnab hunit h3
        (fun _ => ⟨ph, 1, x₀, hpin⟩) nab 1 0 a Nat.one_pos hdom hn hχ htot _ hb fun k x hx => dif_neg hx)

end GlobalTheory.SupFull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingMapHermitianNormLeProdBounds
section
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.BranchNormBound

open GlobalTheory.BranchFormula GlobalTheory.BranchNorm GlobalTheory.IndefiniteRowSideFullHecke.ScaledCoisometryNorms

theorem const_le {n : ℕ} {lam : DomWeight (n + 1)} {sg : DomWeight n} (hI : Interlace rfl lam sg) (hS : SameShift lam sg) :
    ((cBr rfl lam sg : ℤ) : ℝ) ^ 2 * kapBr ℝ rfl lam sg ≤ Formalism.MainNotions.PrimeDegreeVariant.brBd rfl lam sg ^ 2 := by
  have hx : xiBr ℂ rfl lam sg ∈ delSq ℂ (n + 1) lam := nablaSq_eq_delSq ℂ lam ▸ xi_mem hI hS
  have h := (onePlace Formalism.L2.DIV.BrJ.branching_interlacing_pairs (n + 1) n rfl lam sg hI hS).2.2.2.2.2 _ hx
  have hk : normFock lam (xiBr ℂ rfl lam sg) (xiBr ℂ rfl lam sg) = kapBr ℂ rfl lam sg := by
    rw [kapBr, normFock, fockF_eq, fockF_eq, GlobalTheory.Proof.TensorMapDescent.xiBr_map, Formalism.L2.DIV.map_extremal]
  have e1 : ((kapBr ℝ rfl lam sg : ℝ) : ℂ) = kapBr ℂ rfl lam sg := kapBr_map Complex.ofRealHom
  obtain ⟨s1, -⟩ := fockF_self_ne (f := extremal ℂ n sg) (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl sg.natW)
  have h5 : normFock sg (extremal ℂ n sg) (extremal ℂ n sg) = 1 := div_self s1
  rw [brOne_xi rfl hI hS, normFock_smul, h5, hk, ← e1] at h
  simp only [map_mul, map_intCast, Complex.conj_ofReal, mul_one, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im, mul_zero, zero_mul, sub_zero, add_zero] at h
  have hp := kapBr_pos hI hS
  refine le_of_mul_le_mul_right ?_ hp
  nlinarith

theorem sumGram_one (n : ℕ) : sumGram (n + 1) (1 : Matrix (Fin n) (Fin n) ℂ) 1 = 1 := by
  ext a b
  have := a.2
  have := b.2
  simp only [sumGram, Matrix.of_apply, Matrix.one_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem brStd_norm_le {ι : Type} [Fintype ι] {n N : ℕ} (hN : N = n + 1) (Λ : ι → DomWeight N) (σ : ι → DomWeight n)
    (hI : ∀ τ, Interlace hN (Λ τ) (σ τ)) (hS : ∀ τ, SameShift (Λ τ) (σ τ)) (x : VV ℂ Λ) :
    (pairK σ (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) (brStd hN Λ σ x) (brStd hN Λ σ x)).re ≤
      (∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd hN.symm (Λ τ) (σ τ) ^ 2) *
        (pairK Λ (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) x x).re := by
  subst hN
  have h1 : ∀ m : ℕ, ((1 : Matrix (Fin m) (Fin m) ℂ).map (RingHom.id ℂ)).PosDef := fun m => by
    simpa using (Matrix.PosDef.one : (1 : Matrix (Fin m) (Fin m) ℂ).PosDef)
  have h := (brNorm ℂ (RingHom.id ℂ) (fun _ => rfl) ι (n + 1) n rfl Λ σ hI hS (fun _ => 1) (fun _ => h1 n)
    (fun _ => 1) (fun _ => 1) 1 one_pos (fun _ => by simp)).2.2.1 x
  simp only [nrmSq, sumGram_one, brAt, one_zpow, Finset.prod_const_one, one_smul, RingHom.id_apply, brSq, one_mul] at h
  have hp := pairK_pos (RingHom.id ℂ) (fun _ => rfl) Λ (G := fun _ => 1) (fun _ => h1 _) x
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hp)
  exact Finset.prod_le_prod₀ (fun τ _ => mul_nonneg (sq_nonneg _) (kapBr_pos (hI τ) (hS τ)).le)
    fun τ _ => const_le (hI τ) (hS τ)

end GlobalTheory.BranchNormBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingPairingExtendScalars
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BrPairF

theorem funEquiv_symm_mapVV {K ι : Type} [Field K] [CharZero K] [Fintype ι] {n : ℕ} (φ : K →+* ℂ)
    (σ : ι → DomWeight n) (v : VV K fun τ => (σ τ).dual) :
    (GlobalTheory.FunObj.funEquiv σ).symm (GlobalTheory.CoefModel.mapVV φ (fun τ => (σ τ).dual) v) =
      GlobalTheory.CoefModel.mapVV φ σ ((GlobalTheory.FunObj.funEquiv σ).symm v) := by
  have h1 : IsFunForm σ ((funEquiv σ).symm v) v := by
    have := isFunForm_funEquiv σ ((funEquiv σ).symm v)
    rwa [LinearEquiv.apply_symm_apply] at this
  have h2 := GlobalTheory.BrRat.isFunForm_map φ σ h1
  have h3 := (isFunForm_iff_eq σ _ _).1 h2
  rw [LinearEquiv.symm_apply_eq]
  exact h3

theorem brPair_mapVV : ∀ {K ι : Type} [Field K] [CharZero K] [Fintype ι] {n N : ℕ} (φ : K →+* ℂ) (σ : ι → DomWeight n) (hN : N = n + 1)
    (Λ : ι → DomWeight N) (u : VV K Λ) (v : VV K fun τ => (σ τ).dual),
    GlobalTheory.FunObj.brPair σ hN Λ (GlobalTheory.CoefModel.mapVV φ Λ u) (GlobalTheory.CoefModel.mapVV φ (fun τ => (σ τ).dual) v) =
      φ (GlobalTheory.BrPairF.brPairF σ hN Λ u v) := by
  intro K ι _ _ _ n N φ σ hN Λ u v
  rw [brPair, LinearMap.compl₁₂_apply, pairBK_apply, pairB_apply, brPairF_apply, pairBK_apply, pairB_apply,
    GlobalTheory.BrRat.covOf_eq, funEquiv_symm_mapVV, GlobalTheory.CoefModel.mapVV_coe, Formalism.L2.Col.Br.brStd, LinearMap.comp_apply,
    Submodule.subtype_apply, Formalism.L2.Col.Br.brStd, LinearMap.comp_apply, Submodule.subtype_apply, GlobalTheory.CoefModel.mapVV_coe,
    GlobalTheory.Proof.TensorMapDescent.branchingProjection_map, GlobalTheory.Proof.TensorMapDescent.fockB_map, map_mul, map_inv₀]
  congr 2
  unfold extNormB
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← GlobalTheory.Proof.TensorMapDescent.fockB_map, Formalism.L2.DIV.map_extremal]

end GlobalTheory.BrPairF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxSchrodingerCompatibilityStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.darboux_schrodinger_compatibility : GlobalTheory.FunPr.Hypotheses₂ → DerEx → VacLine →
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → IsStd ψ →
    Framed τ JA JB a b A C → IsFockMap ψ τ d A C Φ →
    ∃ (ω₀ : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)) (c₀ : InfinitePlace F → ℂ),
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ φ ∈ schA F κ, ω₀ g φ ∈ schA F κ) ∧
        (∀ w, ∀ φ ∈ schA F κ, ω₀ g (d.rho ψ w φ) = d.rho ψ (actB (cA σ) g w) (ω₀ g φ)) ∧
        ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
          ∀ φ ∈ schA F κ, ∫⁻ x, ‖ω₀ g φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) ∧
      (∀ l ∈ (adeleClass F).adm κ, ∀ φ ∈ schA F κ,
        ContinuousOn (fun g => l (ω₀ g φ)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) ∧
      ActsBy τ C ω₀ Φ (fockAct2 P Q R S) c₀ := by
  first | exact @GlobalTheory.GenRep.genRep | exact GlobalTheory.GenRep.genRep | (intros; apply GlobalTheory.GenRep.genRep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasRationalWeilOperatorLeviBlockStatement
section
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasRationalWeilOperator_leviBlock : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (κ : Type) [Fintype κ] [DecidableEq κ] (g h : Matrix κ κ F), gᵀ * h = 1 →
    HasOp ψ (Matrix.fromBlocks g 0 0 h) := by
  first | exact @GlobalTheory.RatWeilOp.hasOp_levi | exact GlobalTheory.RatWeilOp.hasOp_levi | (intros; apply GlobalTheory.RatWeilOp.hasOp_levi <;> assumption)
end

