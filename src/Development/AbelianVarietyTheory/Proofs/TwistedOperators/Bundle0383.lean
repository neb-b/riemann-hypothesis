module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FramesDifferByIsometryAndTriangularOfPeriods
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0866
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0369
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0337

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FramesDifferByIsometryOfTriangularPeriods
section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix ComplexConjugate

noncomputable section

namespace GlobalTheory.PeriodBorelQ

open GlobalTheory.FramePeriod GlobalTheory.PeriodBorel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem natPer_move_q {X X' : Data E r} {N : ℕ} {a : GL (Fin r) E} (h : QMatch X X' N a) (τ : E →+* ℂ) (q : ℕ)
    (M : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → E) (n : ℕ) :
    natPer τ X'.Gm q ((a : Matrix (Fin r) (Fin r) E).map τ * M)
      (Data.emb τ ((a : Matrix (Fin r) (Fin r) E) *ᵥ v)) n = natPer τ X.Gm q M (Data.emb τ v) n := by
  have he : Data.emb τ ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      (a : Matrix (Fin r) (Fin r) E).map τ *ᵥ Data.emb τ v := by
    funext k; simp [Data.emb, Matrix.mulVec, dotProduct, map_sum, map_mul]
  have hu : IsUnit ((a : Matrix (Fin r) (Fin r) E).map τ).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 a.isUnit).map τ
  unfold natPer
  split_ifs with hn
  · rw [he, locPer_apply, locPer_apply]
    split_ifs
    · exact h.hermC_eq τ (col M ⟨n, hn⟩) _
    · rw [Matrix.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul_cancel_right _ _ hu]
  · rfl

theorem natPer_natCast_smul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (q : ℕ) (M : Matrix (Fin r) (Fin r) ℂ)
    (N : ℕ) (v : Fin r → E) (n : ℕ) :
    natPer τ G q M (Data.emb τ ((N : E) • v)) n = (N : ℂ) * natPer τ G q M (Data.emb τ v) n := by
  have he : Data.emb τ ((N : E) • v) = (N : ℂ) • Data.emb τ v := by
    funext k; simp [Data.emb]
  unfold natPer
  split_ifs with hn
  · rw [he, locPer_apply, locPer_apply]
    split_ifs
    · rw [FD.hermC_smul_right, Complex.conj_natCast]
    · rw [Matrix.mulVec_smul]; rfl
  · simp

theorem borel_of_periods_q : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (N : ℕ) (a : GL (Fin r) E) (h : QMatch X X' N a), 0 < N → ∀ (m : (E →+* ℂ) → ℕ), (∀ τ ∈ X.Ψ, m τ = r - X.p0) → (∀ τ ∉ X.Ψ, m τ = X.p0) → ∀ x ∈ X.dom, ∀ x' ∈ X'.dom, ∀ (A : (E →+* ℂ) → ℕ → ℕ → ℂ), (∀ τ i j, j < i → A τ i j = 0) → (∀ τ, ∀ i < m τ, ∀ v ∈ X.Λ, Formalism.L2.PjFree.perFr X' x' ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i = ∑ j ∈ Finset.range (m τ), A τ i j * Formalism.L2.PjFree.perFr X x v τ j) → ∃ b ∈ Bor X'.Ψ r, x' = rmul (lact a (castFr h.psi x)) b ∧ (IsUnitFr X x → IsUnitFr X' x' → (∀ τ i, ‖b τ i i‖ = 1) ∧ ∀ τ, ∀ i < m τ, ‖A τ i i‖ = 1) := by
  intro E _ _ _ r X X' N a h hN0 m hm1 hm2 x hx x' hx' A hA hper
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN0.ne'
  have hz := h.mem_dom hx
  set z := lact a (castFr h.psi x) with hzd
  have hlat : ∀ w ∈ X'.Λ, ∃ v ∈ X.Λ, (a : Matrix (Fin r) (Fin r) E) *ᵥ v = (N : E) • w := by
    intro w hw
    refine ⟨_, h.lat' w hw, ?_⟩
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hloc := fun τ : X'.Ψ => loc_borel X' τ.1 (mat z τ) (mat x' τ) (hz τ).1 (hx' τ).1 (A τ.1) (A (conjEmb τ.1))
    (hA _) (hA _)
    (fun i hi w hw => by
      obtain ⟨v, hv, hav⟩ := hlat w hw
      have hm := hm1 τ.1 (h.mem τ)
      rw [h.p0] at hm
      refine mul_left_cancel₀ hN ?_
      rw [← natPer_natCast_smul, ← hav, ← perFr_mem X' x' _ τ.1 τ.2, hper τ.1 i (hm ▸ hi) v hv, hm,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [perFr_mem X x v τ.1 (h.mem τ), ← natPer_move_q h, h.p0, hav, natPer_natCast_smul, mul_left_comm]
      rfl)
    (fun i hi w hw => by
      obtain ⟨v, hv, hav⟩ := hlat w hw
      have hm := hm2 _ (conjEmb_not_mem X (h.mem τ))
      rw [h.p0] at hm
      refine mul_left_cancel₀ hN ?_
      rw [← natPer_natCast_smul, ← hav, ← perFr_conj X' x' _ τ.1 τ.2 i hi, hper _ i (hm ▸ hi) v hv, hm,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [perFr_conj X x v τ.1 (h.mem τ) j (h.p0 ▸ Finset.mem_range.1 hj), ← natPer_move_q h, h.p0, hav,
        natPer_natCast_smul, mul_left_comm]
      rfl)
  let b : Frame X'.Ψ r := fun τ => ((mat z τ)⁻¹ * mat x' τ : Matrix (Fin r) (Fin r) ℂ)
  have hb : b ∈ Bor X'.Ψ r := fun τ => by
    refine ⟨?_, (hloc τ).1⟩
    show ((mat z τ)⁻¹ * mat x' τ).det ≠ 0
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact mul_ne_zero (inv_ne_zero (hz τ).1) (hx' τ).1
  have hxb : x' = rmul z b := by
    funext τ
    exact (Matrix.mul_nonsing_inv_cancel_left (mat z τ) (mat x' τ) (isUnit_iff_ne_zero.2 (hz τ).1)).symm
  refine ⟨b, hb, hxb, fun hu hu' => ?_⟩
  have hbd : ∀ τ i, ‖b τ i i‖ = 1 := by
    intro τ i
    have e := FrameDegreeData.ratio_rmul X' z hz hb τ i
    rw [← hxb, norm_div, norm_div, hu', hu', hzd, h.dmin_eq, h.dmin_eq, hu, hu, div_one, _root_.mul_one] at e
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 e.symm
  refine ⟨hbd, fun τ i hi => ?_⟩
  by_cases hτ : τ ∈ X.Ψ
  · rw [hm1 τ hτ, h.p0] at hi
    exact ((hloc ⟨τ, h.psi ▸ hτ⟩).2 (hbd _)).1 i hi
  · rw [hm2 τ hτ, h.p0] at hi
    have := ((hloc ⟨conjEmb τ, h.psi ▸ conjEmb_mem X hτ⟩).2 (hbd _)).2 i hi
    rwa [conjEmb_conjEmb] at this

end GlobalTheory.PeriodBorelQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeElementKeepsOneSubIdempotentPartLattice
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

namespace GlobalTheory.HeckeOffParts
open scoped Matrix

theorem mulVec_one_sub_idempotent_of_split_sum_identity {A : Type} [CommRing A] {n : ℕ} (a b : A) (h1 : a * a = a) (h2 : a * b = 0)
    (M : Matrix (Fin n) (Fin n) A) (z : Fin n → A) (h6 : M *ᵥ z = (a + b) • M *ᵥ z + z - (a + b) • z) :
    M *ᵥ ((1 - a) • z) = b • M *ᵥ z + z - a • z - b • z := by
  have hP : (1 - a) * (a + b) = b := by linear_combination -h1 - h2
  rw [Matrix.mulVec_smul]
  conv_lhs => rw [h6]
  rw [smul_sub, smul_add, smul_smul, smul_smul, hP, sub_smul, one_smul]
  abel

open GlobalTheory.SplitPlace in
theorem inv_part_mem {D : D7} {e : AE D} (he : IsSplitIdem D e) {V : HSp D} {ϖ : D.host.E} {k : ℕ} {a₀ : GA D V}
    (ha : Formalism.L2.NTheta.IsHeckeElt V e ϖ k a₀) :
    ∀ z ∈ Formalism.L2.NTheta.LamHat V,
      fm V a₀⁻¹ *ᵥ ((1 - finPart D e) • z) ∈ Formalism.L2.NTheta.LamHat V := by
  intro z hz
  obtain ⟨-, hs, h3, -⟩ := ha
  have hi := idem_mem he.1
  have hci := cf_mem hi
  have h3' : ∀ y ∈ Formalism.L2.NTheta.LamHat V, finPart D e • fm V a₀ *ᵥ y ∈ Formalism.L2.NTheta.LamHat V := h3
  have hadj := adj_mem V (finPart D e) a₀ h3' z hz
  have h6 := mulVec_parts (finPart D) ((suppAt_iff e V a₀⁻¹).1 (suppAt_inv hs)) z
  rw [RingHom.map_add (f := _), fin_cA, ← fm_eq] at h6
  have e1 : finPart D e * finPart D e = finPart D e := by rw [← map_mul, he.1]
  have e2 : finPart D e * cf D (finPart D e) = 0 := by rw [← fin_cA, ← map_mul, he.2.1, map_zero]
  rw [mulVec_one_sub_idempotent_of_split_sum_identity _ _ e1 e2 _ z h6]
  have m1 : finPart D e • z ∈ Formalism.L2.NTheta.LamHat V := smul_mem V hi hz
  have m2 : cf D (finPart D e) • z ∈ Formalism.L2.NTheta.LamHat V := smul_mem V hci hz
  have m3 := (Formalism.L2.NTheta.LamHat V).add_mem hadj hz
  have m4 := (Formalism.L2.NTheta.LamHat V).sub_mem m3 m1
  exact (Formalism.L2.NTheta.LamHat V).sub_mem m4 m2

open GlobalTheory.SplitPlace in
theorem hat_one_mem {D : D7} {e : AE D} (he : IsSplitIdem D e) {V : HSp D} {ϖ : D.host.E} {k : ℕ} {a₀ : GA D V}
    (ha : Formalism.L2.NTheta.IsHeckeElt V e ϖ k a₀) :
    ∀ w ∈ latGHat V 1, fm V a₀⁻¹ *ᵥ ((1 - finPart D e) • w) ∈ latGHat V 1 := by
  intro w hw
  let f : (Fin V.rank → RF D) →+ (Fin V.rank → RF D) :=
    (Matrix.mulVecLin (fm V a₀⁻¹)).toAddMonoidHom.comp (DistribSMul.toAddMonoidHom _ (1 - finPart D e))
  change f w ∈ latGHat V 1
  unfold latGHat at hw ⊢
  refine AddSubgroup.mem_comap.1 ((AddSubgroup.closure_le (K := AddSubgroup.comap f _)).2 ?_ hw)
  rintro _ ⟨a, haA, x, ⟨x', hx', rfl⟩, rfl⟩
  rw [SetLike.mem_coe, AddSubgroup.mem_comap]
  refine AddSubgroup.subset_closure ⟨a, haA, _, ⟨fm V a₀⁻¹ *ᵥ ((1 - finPart D e) • x'), ?_, rfl⟩, ?_⟩
  · have hx'' : x' ∈ Formalism.L2.NTheta.LamHat V := by
      rw [← GlobalTheory.LatReflection.latHat_eq_lamHat]; exact hx'
    have := inv_part_mem he ha x' hx''
    rw [← GlobalTheory.LatReflection.latHat_eq_lamHat] at this
    exact this
  · simp only [map_one, Units.val_one, Matrix.one_mulVec]
    change fm V a₀⁻¹ *ᵥ ((1 - finPart D e) • (((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] a) • x')) =
      ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] a) • (fm V a₀⁻¹ *ᵥ ((1 - finPart D e) • x'))
    rw [smul_comm (1 - finPart D e), Matrix.mulVec_smul]

open GlobalTheory.SplitPlace in
theorem off_parts : ∀ (D : D7) (V : HSp D) (e : AE D) (ϖ : D.host.E) (k : ℕ) (g a₀ : GA D V),
    Formalism.L2.Theta.IsSplitIdem D e → Formalism.L2.NTheta.IsHeckeElt V e ϖ k a₀ →
    ∀ y ∈ latGHat V g, (1 - finPart D e) • y ∈ latGHat V (g * a₀) := by
  intro D V e ϖ k g a₀ he ha y hy
  obtain ⟨z, hz, rfl⟩ := ((GlobalTheory.MarkCoset.latG_spec D V g).2 y).1 hy
  refine ((GlobalTheory.MarkCoset.latG_spec D V (g * a₀)).2 _).2
    ⟨fm V a₀⁻¹ *ᵥ ((1 - finPart D e) • z), hat_one_mem he ha z hz, ?_⟩
  rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
  change (finHom V g).1 *ᵥ (fm V a₀ *ᵥ (fm V a₀⁻¹ *ᵥ ((1 - finPart D e) • z))) = _
  rw [fm_vec_inv, Matrix.mulVec_smul]

end GlobalTheory.HeckeOffParts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSelfDualLatticeSplitPlaceDictionaryStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_selfDual_lattice_split_place_dictionary : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (V : Spc F E d) (r s : ℕ), B.IsGood σ → V.IsHerm σ B r s →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v →
    ∃ (π₁ π₂ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
      ((∀ z, π₁ (cA σ z) = π₂ z) ∧ (∀ z, π₂ (cA σ z) = π₁ z) ∧
      (∀ a : AF F, π₁ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = evFin F v a) ∧
      (∀ a : AF F, π₂ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = evFin F v a) ∧
      (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) ∧
      (∀ x₁ x₂ : Fv F v, ∃ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) ∧
      (∀ z : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), z ∈ GlobalTheory.InertSph.latAt V v ↔ At (evFin F v) z ∧
        (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₁ (z j)) i ∈
          v.adicCompletionIntegers F) ∧
        (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₂ (z j)) i ∈
          v.adicCompletionIntegers F))) ∧
      ∃ S : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), IsUnit S.det ∧
        S.map (fun x => (x : Fv F v)) =
          (b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F V.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) := by
  first | exact @GlobalTheory.SplitDictHerm.split_dict_herm | exact GlobalTheory.SplitDictHerm.split_dict_herm | (intros; apply GlobalTheory.SplitDictHerm.split_dict_herm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentCutUnitaryPointStabilizesLattices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.FinDecomp
open scoped Classical

noncomputable section
namespace GlobalTheory.IdemCut

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem smul_phi_of_mul_eq_zero {a e : AF F} (h : a * e = 0) (M : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    a • phi e M = a • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
  simp only [phi, smul_add, smul_smul, mul_sub, mul_one, h, sub_zero, zero_smul, add_zero]

theorem smul_phi_of_mul_eq_self {a e : AF F} (h : a * e = a) (M : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    a • phi e M = a • M := by
  simp only [phi, smul_add, smul_smul, mul_sub, mul_one, h, sub_self, zero_smul, zero_add]

theorem idempotentCut_latticeStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a'), G.IsGood B →
    ∀ h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J, ∃ S₁ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∀ (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) (e : AF F) (he : e * e = e), S₁ ⊆ S →
      (∀ w ∉ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u * e = 0 ∨ u * e = u) →
      (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.FinDecomp.loc e he h))ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w ↔
        γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w) ∧
      (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.FinDecomp.loc e he h))ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w ↔
        γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w) := by
  intro F E _ _ _ _ _ σ B a a' G hG h
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.exists_finset_integral_adele_mulVec_mem_lattice_closure F E _ (mat h) G.W.L hG.hW.lat
  obtain ⟨S₂, hS₂⟩ := GlobalTheory.T.exists_finset_integral_adele_mulVec_mem_lattice_closure F E _ (mat h⁻¹) G.W.L hG.hW.lat
  refine ⟨S₁ ∪ S₂, fun S e he hS hcut => ?_⟩
  have key : ∀ w ∉ S, ∀ (X : ℕ) (Xs : Spc F E X), ∀ γ,
      γ * (mat (loc e he h))ᵀ ∈ latAtV Xs G.W w ↔ γ ∈ latAtV Xs G.W w := by
    intro w hw X Xs γ
    have hw1 : w ∉ S₁ := fun h' => hw (hS (Finset.mem_union_left _ h'))
    have hw2 : w ∉ S₂ := fun h' => hw (hS (Finset.mem_union_right _ h'))
    refine GlobalTheory.T.tensorLattice_mul_transpose_stable_iff F E X _ Xs G.W w _ _ (mat_inv_mul (loc e he h)) ?_ ?_ γ
    · intro u hu hint y hy
      rw [← Matrix.smul_mulVec, mat_loc]
      rcases hcut w hw u hu with h0 | h1
      · rw [smul_phi_of_mul_eq_zero h0, Matrix.smul_mulVec, Matrix.one_mulVec]
        exact AddSubgroup.subset_closure ⟨u, hu, hint, y, hy, rfl⟩
      · rw [smul_phi_of_mul_eq_self h1, Matrix.smul_mulVec]
        exact hS₁ w hw1 u hu hint y hy
    · intro u hu hint y hy
      rw [← Matrix.smul_mulVec, mat_loc_inv]
      rcases hcut w hw u hu with h0 | h1
      · rw [smul_phi_of_mul_eq_zero h0, Matrix.smul_mulVec, Matrix.one_mulVec]
        exact AddSubgroup.subset_closure ⟨u, hu, hint, y, hy, rfl⟩
      · rw [smul_phi_of_mul_eq_self h1, Matrix.smul_mulVec]
        exact hS₂ w hw2 u hu hint y hy
  exact ⟨fun w hw => key w hw _ G.V, fun w hw => key w hw _ G.V'⟩

end GlobalTheory.IdemCut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableGaussianExpLinearNormTermComplexMatrixStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_gaussian_exp_linear_norm_term_complex_matrix : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ), (∀ τ, 0 < c τ) → ∀ z₀ : VCx ι a b, Integrable fun z : VCx ι a b => Real.exp ((∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) - gq c z / 2) := by
  first | exact @GlobalTheory.FockTransl.integrable_exp_lin_sub_gq | exact GlobalTheory.FockTransl.integrable_exp_lin_sub_gq | (intros; apply GlobalTheory.FockTransl.integrable_exp_lin_sub_gq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralBargmannEqZeroOfMoments
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransl

section BargmannUnique

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem bk_smul_left (c : ι → ℝ) (u : ℂ) (z₀ z : VCx ι a b) : bk c (u • z₀) z = u * bk c z₀ z := by
  unfold bk
  simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem conjMono_add (m m' : DVar ι a b →₀ ℕ) (z : VCx ι a b) :
    conjMono (m + m') z = conjMono m z * conjMono m' z := by
  unfold conjMono
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

theorem conjMono_single_one (k : DVar ι a b) (z : VCx ι a b) :
    conjMono (Finsupp.single k 1) z = conj (z k.1 k.2.1 k.2.2) := by
  unfold conjMono; simp [Finsupp.prod_single_index]

abbrev monoSpan (ι : Type) [Fintype ι] (a b : ℕ) : Submodule ℂ (VCx ι a b → ℂ) :=
  Submodule.span ℂ (Set.range fun m : DVar ι a b →₀ ℕ => conjMono m)

theorem monoSpan_mul {P Q : VCx ι a b → ℂ} (hP : P ∈ monoSpan ι a b) (hQ : Q ∈ monoSpan ι a b) :
    P * Q ∈ monoSpan ι a b := by
  have h := Submodule.mul_mem_mul hP hQ
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨m, rfl⟩, _, ⟨m', rfl⟩, rfl⟩
  exact ⟨m + m', funext fun z => conjMono_add m m' z⟩

theorem bk_mem_monoSpan (c : ι → ℝ) (z₀ : VCx ι a b) : (fun z => bk c z₀ z) ∈ monoSpan ι a b := by
  have : (fun z => bk c z₀ z) = ∑ τ, ∑ i, ∑ j,
      ((c τ : ℂ) * z₀ τ i j) • conjMono (Finsupp.single (τ, i, j) 1) := by
    funext z
    simp only [bk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, conjMono_single_one]
  rw [this]
  exact Submodule.sum_mem _ fun τ _ => Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem bk_pow_mem_monoSpan (c : ι → ℝ) (z₀ : VCx ι a b) (n : ℕ) :
    (fun z => bk c z₀ z ^ n) ∈ monoSpan ι a b := by
  induction n with
  | zero =>
    have : (fun z : VCx ι a b => bk c z₀ z ^ 0) = conjMono 0 := by funext z; simp [conjMono]
    rw [this]; exact Submodule.subset_span ⟨0, rfl⟩
  | succ n ih =>
    have := monoSpan_mul ih (bk_mem_monoSpan c z₀)
    convert this using 1
    funext z; simp [pow_succ]

theorem exp_norm_le_four (w : ℂ) : Real.exp ‖w‖ ≤ Real.exp ((1 - Complex.I) * w).re +
    Real.exp ((1 + Complex.I) * w).re + Real.exp ((-1 - Complex.I) * w).re + Real.exp ((-1 + Complex.I) * w).re := by
  have h1 : ((1 - Complex.I) * w).re = w.re + w.im := by simp [Complex.mul_re] <;> ring
  have h2 : ((1 + Complex.I) * w).re = w.re + -w.im := by simp [Complex.mul_re] <;> ring
  have h3 : ((-1 - Complex.I) * w).re = -w.re + w.im := by simp [Complex.mul_re] <;> ring
  have h4 : ((-1 + Complex.I) * w).re = -w.re + -w.im := by simp [Complex.mul_re] <;> ring
  rw [h1, h2, h3, h4]
  have key : Real.exp ‖w‖ ≤ Real.exp |w.re| * Real.exp |w.im| := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (Complex.norm_le_abs_re_add_abs_im w)
  have hre : Real.exp |w.re| ≤ Real.exp w.re + Real.exp (-w.re) := by
    rcases abs_cases w.re with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith [Real.exp_pos w.re, Real.exp_pos (-w.re)]
  have him : Real.exp |w.im| ≤ Real.exp w.im + Real.exp (-w.im) := by
    rcases abs_cases w.im with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith [Real.exp_pos w.im, Real.exp_pos (-w.im)]
  calc Real.exp ‖w‖ ≤ (Real.exp w.re + Real.exp (-w.re)) * (Real.exp w.im + Real.exp (-w.im)) :=
        key.trans (mul_le_mul hre him (by positivity) (by positivity))
    _ = _ := by simp only [add_mul, mul_add, ← Real.exp_add]; ring

theorem integral_moment_span_eq_zero {c : ι → ℝ} (hc : ∀ τ, 0 < c τ) {F : VCx ι a b → ℂ}
    (hF : Continuous F) {M : ℝ} (hM : ∀ z, ‖F z‖ ≤ M)
    (hmom : ∀ m : DVar ι a b →₀ ℕ, ∫ z, conjMono m z * (Real.exp (-gq c z / 2) : ℂ) * F z = 0)
    {P : VCx ι a b → ℂ} (hP : P ∈ monoSpan ι a b) :
    Integrable (fun z => P z * (Real.exp (-gq c z / 2) : ℂ) * F z) ∧
      ∫ z, P z * (Real.exp (-gq c z / 2) : ℂ) * F z = 0 := by
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    exact ⟨((_root_.GlobalTheory.FockTransl.integrable_conjMono_bargmann_gauss ι a b c hc).1 m).mul_bdd hF.aestronglyMeasurable
      (Filter.Eventually.of_forall hM), hmom m⟩
  | zero => simp
  | add x y _ _ hx hy =>
    have e : (fun z => (x + y) z * (Real.exp (-gq c z / 2) : ℂ) * F z) =
        fun z => x z * (Real.exp (-gq c z / 2) : ℂ) * F z + y z * (Real.exp (-gq c z / 2) : ℂ) * F z := by
      funext z; simp only [Pi.add_apply]; ring
    rw [e]
    exact ⟨hx.1.add hy.1, by rw [integral_add hx.1 hy.1, hx.2, hy.2, add_zero]⟩
  | smul r x _ hx =>
    have e : (fun z => (r • x) z * (Real.exp (-gq c z / 2) : ℂ) * F z) =
        fun z => r * (x z * (Real.exp (-gq c z / 2) : ℂ) * F z) := by
      funext z; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [e]
    exact ⟨hx.1.const_mul r, by rw [integral_const_mul, hx.2, mul_zero]⟩

theorem integral_bargmann_eq_zero_of_moments : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ), (∀ τ, 0 < c τ) → ∀ F : VCx ι a b → ℂ, Continuous F → (∃ M : ℝ, ∀ z, ‖F z‖ ≤ M) → (∀ m : DVar ι a b →₀ ℕ, ∫ z, conjMono m z * (Real.exp (-gq c z / 2) : ℂ) * F z = 0) → ∀ z₀, ∫ z, Complex.exp (bk c z₀ z) * (Real.exp (-gq c z / 2) : ℂ) * F z = 0 := by
  intro ι _ a b c hc F hF hMex hmom z₀
  obtain ⟨M, hM⟩ := hMex
  have hexpR : ∀ x : ℝ, HasSum (fun n : ℕ => x ^ n / (Nat.factorial n : ℝ)) (Real.exp x) := fun x => by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp _
  have hexpC : ∀ x : ℂ, HasSum (fun n : ℕ => x ^ n / (Nat.factorial n : ℂ)) (Complex.exp x) := fun x => by
    rw [Complex.exp_eq_exp_ℂ]; exact NormedSpace.expSeries_div_hasSum_exp _
  have hgq : Continuous (fun z : VCx ι a b => gq c z) := by unfold gq; fun_prop
  have hbk : Continuous (fun z : VCx ι a b => bk c z₀ z) := by unfold bk; fun_prop
  have hg : Continuous (fun z : VCx ι a b => ((Real.exp (-gq c z / 2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp (hgq.neg.div_const 2))
  have hsum := hasSum_integral_of_dominated_convergence (μ := volume)
    (F := fun (n : ℕ) z => bk c z₀ z ^ n / (Nat.factorial n : ℂ) * (Real.exp (-gq c z / 2) : ℂ) * F z)
    (f := fun z => Complex.exp (bk c z₀ z) * (Real.exp (-gq c z / 2) : ℂ) * F z)
    (fun n z => ‖bk c z₀ z‖ ^ n / (Nat.factorial n : ℝ) * (Real.exp (-gq c z / 2) * M))
    (fun n => ((((hbk.pow n).div_const _).mul hg).mul hF).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun z => by
      simp only [norm_mul, norm_div, norm_pow, Complex.norm_natCast, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [mul_assoc]
      gcongr
      exact hM z)
    (Filter.Eventually.of_forall fun z => (hexpR ‖bk c z₀ z‖).summable.mul_right _)
    (by
      have htsum : (fun z => ∑' n : ℕ, ‖bk c z₀ z‖ ^ n / (Nat.factorial n : ℝ) * (Real.exp (-gq c z / 2) * M)) =
          fun z => Real.exp ‖bk c z₀ z‖ * (Real.exp (-gq c z / 2) * M) := by
        funext z; rw [tsum_mul_right, (hexpR _).tsum_eq]
      rw [htsum]
      have hI : ∀ u : ℂ, Integrable fun z : VCx ι a b =>
          ‖Complex.exp (bk c (u • z₀) z) * (Real.exp (-gq c z / 2) : ℂ)‖ :=
        fun u => ((_root_.GlobalTheory.FockTransl.integrable_conjMono_bargmann_gauss ι a b c hc).2 (u • z₀)).norm
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
      refine Integrable.mono' ((((hI (1 - Complex.I)).add (hI (1 + Complex.I))).add
        (hI (-1 - Complex.I))).add (hI (-1 + Complex.I)) |>.const_mul M)
        ((Real.continuous_exp.comp (continuous_norm.comp hbk)).mul
          ((Real.continuous_exp.comp (hgq.neg.div_const 2)).mul continuous_const)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => ?_)
      simp only [Pi.add_apply, bk_smul_left, norm_mul, Complex.norm_exp, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [abs_of_nonneg (by positivity)]
      have h4 := exp_norm_le_four (bk c z₀ z)
      have he := Real.exp_pos (-gq c z / 2)
      calc Real.exp ‖bk c z₀ z‖ * (Real.exp (-gq c z / 2) * M)
          = (M * Real.exp (-gq c z / 2)) * Real.exp ‖bk c z₀ z‖ := by ring
        _ ≤ (M * Real.exp (-gq c z / 2)) * (Real.exp ((1 - Complex.I) * bk c z₀ z).re +
            Real.exp ((1 + Complex.I) * bk c z₀ z).re + Real.exp ((-1 - Complex.I) * bk c z₀ z).re +
            Real.exp ((-1 + Complex.I) * bk c z₀ z).re) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = _ := by ring)
    (Filter.Eventually.of_forall fun z => by
      simpa only [mul_assoc] using (hexpC (bk c z₀ z)).mul_right ((Real.exp (-gq c z / 2) : ℂ) * F z))
  have h0 : ∀ n : ℕ, ∫ z, bk c z₀ z ^ n / (Nat.factorial n : ℂ) * (Real.exp (-gq c z / 2) : ℂ) * F z = 0 := by
    intro n
    have := (integral_moment_span_eq_zero hc hF hM hmom
      (Submodule.smul_mem _ ((Nat.factorial n : ℂ)⁻¹) (bk_pow_mem_monoSpan c z₀ n))).2
    have e : (fun z => bk c z₀ z ^ n / (Nat.factorial n : ℂ) * (Real.exp (-gq c z / 2) : ℂ) * F z) =
        fun z => ((Nat.factorial n : ℂ)⁻¹ • fun z => bk c z₀ z ^ n) z * (Real.exp (-gq c z / 2) : ℂ) * F z := by
      funext z; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [e]; exact this
  simp only [h0] at hsum
  exact hsum.unique hasSum_zero

end BargmannUnique

end GlobalTheory.FockTransl

end
end

