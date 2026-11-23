module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0634
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0644
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0672
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0657

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NpowHalfAddHalf
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Cell

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SetCell

variable {D : D7} {p : ℕ}

theorem mem_K_of_mem_KOff {S : Finset (Pl D)} {u : G D p} (hu : u ∈ KOff D p S) : u ∈ K D p := by
  obtain ⟨hf, h1, h2⟩ := mem_levelOff.1 hu
  refine mem_levelAll.2 ⟨fun v => ?_, fun w => ?_⟩
  · by_cases hv : v ∈ S
    · rw [h1 v hv]; exact one_mem _
    · exact h2 v hv
  · rw [mem_finPts_iff_forall.1 hf w]; exact one_mem _

theorem height_mul_K {H : G D p → ℝ≥0} (hH : IsHeight H) {k : G D p} (hk : k ∈ K D p) (g : G D p) :
    H (g * k) = H g := by
  obtain ⟨q, hq, k', hk', rfl⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D p g
  rw [mul_assoc, GlobalTheory.CompanionTheory.HtEx.height_eq hH ⟨q, hq⟩ (mul_mem hk' hk), GlobalTheory.CompanionTheory.HtEx.height_eq hH ⟨q, hq⟩ hk']

theorem w_mem_GF {w : G D p} (hw : IsW w) : w ∈ GF D p := by
  have hY : mat w⁻¹ = blk4 0 (-1) 1 0 := by
    have e2 : mat w⁻¹ * mat w = 1 :=
      (show mat (w⁻¹ * w) = mat w⁻¹ * mat w from rfl).symm.trans (by rw [inv_mul_cancel]; rfl)
    have e3 : mat w * blk4 0 (-1) 1 0 = 1 := by
      rw [show mat w = _ from hw, GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul]
      simp [GlobalTheory.StdUnn.Model.block_matrix_one]
    calc mat w⁻¹ = mat w⁻¹ * (mat w * blk4 0 (-1) 1 0) := by rw [e3, mul_one]
      _ = blk4 0 (-1) 1 0 := by rw [← mul_assoc, e2, one_mul]
  refine GlobalTheory.CompanionTheory.PcB.mem_GF w (blk4 0 1 (-1) 0) (blk4 0 (-1) 1 0) ?_ ?_
  · rw [show mat w = _ from hw, GlobalTheory.CompanionTheory.PcB.rational_map_block_matrix, GlobalTheory.CompanionTheory.PcB.rat_zero', GlobalTheory.CompanionTheory.PcB.rat_one', GlobalTheory.CompanionTheory.PcB.rat_neg',
      GlobalTheory.CompanionTheory.PcB.rat_one']
  · rw [hY, GlobalTheory.CompanionTheory.PcB.rational_map_block_matrix, GlobalTheory.CompanionTheory.PcB.rat_zero', GlobalTheory.CompanionTheory.PcB.rat_one', GlobalTheory.CompanionTheory.PcB.rat_neg',
      GlobalTheory.CompanionTheory.PcB.rat_one']

theorem npow_half_add_half (r : ℝ≥0) : npow r ((p : ℂ) / 2 + (p : ℂ) / 2) = (((r : ℝ) ^ p : ℝ) : ℂ) := by
  have e : (p : ℂ) / 2 + (p : ℂ) / 2 = (p : ℂ) := by ring
  rw [e, npow, Complex.cpow_natCast]
  push_cast
  rfl

def hp (H : G D p → ℝ≥0) (g : G D p) : ℝ := (H g : ℝ) ^ p

theorem hp_law {H : G D p → ℝ≥0} (hH : IsHt H) {q : G D p} (hq : q ∈ P D p) {a : GL (Fin p) (AE D)}
    (ha : blkA (mat q) = a.1) (g : G D p) :
    hp H (q * g) = (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ p * hp H g := by
  simp only [hp]
  rw [hH.2.2 q hq a ha g, NNReal.coe_mul, mul_pow]

theorem hp_pos {H : G D p → ℝ≥0} (hH : IsHt H) (g : G D p) : 0 < hp H g :=
  pow_pos (by exact_mod_cast hH.2.1 g) _

theorem exists_block {q : G D p} (hq : q ∈ P D p) : ∃ a : GL (Fin p) (AE D), blkA (mat q) = a.1 :=
  ⟨GlobalTheory.StdUnn.HeightExists.leviBlock (D := D) (n := p) ⟨q, hq⟩, rfl⟩

theorem isRho_iff_sec {H : G D p → ℝ≥0} (hH : IsHt H) (f : G D p → ℂ) : IsRho f ↔ Sec (P D p) (hp H) f := by
  constructor
  · rintro ⟨c, l⟩
    refine ⟨c, fun q hq g => ?_⟩
    obtain ⟨a, ha⟩ := exists_block hq
    rw [l q hq a ha g, hp_law hH hq ha g, npow_half_add_half]
    simp only [MonoidHom.one_apply, Circle.coe_one, one_mul]
    push_cast
    ring
  · rintro ⟨c, l⟩
    refine ⟨c, fun q hq a ha g => ?_⟩
    have h1 := l q hq g
    rw [hp_law hH hq ha g] at h1
    have h0 : ((hp H g : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hp_pos hH g).ne'
    rw [npow_half_add_half]
    simp only [MonoidHom.one_apply, Circle.coe_one, one_mul]
    apply mul_right_cancel₀ h0
    rw [h1]
    push_cast
    ring

theorem setC : HtExist → PositivityTheory.Rg.Rsw.Cell.SetC := by
  intro hEx D p mu hmu
  obtain ⟨H, hH⟩ := GlobalTheory.StdUnn.exists_height D p
  have hI : IsHt H := GlobalTheory.CompanionTheory.HtEx.isHt_of_isHeight hH
  have hS := isRho_iff_sec hI
  refine ⟨hp H, ?_, hS, ?_, ?_⟩
  · refine ⟨GlobalTheory.StdUnn.HeightExists.isClosed_P, (hEx D p).2, ?_, hp_pos hI, ?_, ?_, ?_, ?_⟩
    · exact (NNReal.continuous_coe.comp hI.1).pow p
    · intro q hq g g'
      obtain ⟨a, ha⟩ := exists_block hq
      rw [hp_law hI hq ha g, hp_law hI hq ha g']
      ring
    · exact fun f f' hf hf' => hmu.add f f' ((hS f).2 hf) ((hS f').2 hf')
    · exact fun c f hf => hmu.smul c f ((hS f).2 hf)
    · exact fun f hf h0 => hmu.pos f ((hS f).2 hf) h0
  · intro S u hu g
    simp only [hp]
    rw [height_mul_K hH (mem_K_of_mem_KOff hu) g]
  · intro nb hnb w hw y
    have hN : ∀ f, IsRho f → mu (fun g => f (g * nb y)) = mu f := fun f hf => hmu.inv_n (nb y) y.1 (hnb y) f hf
    have hW := w_mem_GF hw
    refine ⟨fun f hf => hN f ((hS f).2 hf), fun f hf => ?_⟩
    have hf' := (hS f).2 hf
    have r1 := GlobalTheory.CompanionTheory.MuC.isRho_right hf' w⁻¹
    have r2 := GlobalTheory.CompanionTheory.MuC.isRho_right r1 (nb y)
    have e3 := hmu.inv_rat w hW _ r2
    have e2 := hN _ r1
    have e1 := hmu.inv_rat w⁻¹ ((GF D p).inv_mem hW) f hf'
    calc mu (fun g => f (g * (w * nb y * w⁻¹))) = mu (fun g => f (g * w * nb y * w⁻¹)) := by
          simp only [mul_assoc]
      _ = mu f := by rw [e3, e2, e1]

end GlobalTheory.CompanionTheory.SetCell

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdNonnegReal
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.EisE

variable {D : D7} {n r t a b : ℕ}

theorem good_rows {S : Finset (Pl D)} {e : AE D} {η : Fin a → Mx D 1 b → ℂ} (h : ∀ i, Good S e (η i)) :
    Good S e (fun y : Mx D a b => ∏ i, η i (y.submatrix (fun _ => i) id)) := by
  intro y
  by_cases hy : IntOff S y
  · rw [if_pos hy]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hi : IntOff S (y.submatrix (fun _ : Fin 1 => i) id) := fun v hv _ j => hy v hv i j
    have := h i (y.submatrix (fun _ : Fin 1 => i) id)
    rw [if_pos hi] at this
    exact this
  · rw [if_neg hy]
    simp only [IntOff] at hy
    push Not at hy
    obtain ⟨v, hv, i, j, hij⟩ := hy
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    have := h i (y.submatrix (fun _ : Fin 1 => i) id)
    rw [if_neg (fun hi => hij (hi v hv 0 j))] at this
    exact this

theorem prod_nonneg_real {ι : Type} (s : Finset ι) (w : ι → ℂ) (h : ∀ i, 0 ≤ (w i).re ∧ (w i).im = 0) :
    0 ≤ (∏ i ∈ s, w i).re ∧ (∏ i ∈ s, w i).im = 0 := by
  refine Finset.prod_induction w (fun x : ℂ => 0 ≤ x.re ∧ x.im = 0) ?_ (by simp) fun i _ => h i
  rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
  simp [Complex.mul_re, Complex.mul_im, hx', hy', mul_nonneg hx hy]

theorem blockMatrix_add_zero {R : Type} (A : Matrix (Fin t) (Fin t) R) (b' : Matrix (Fin t) (Fin 0) R) (c : Matrix (Fin 0) (Fin t) R)
    (d : Matrix (Fin 0) (Fin 0) R) : bl (add_zero t) A b' c d = A := by
  have h : ∀ i : Fin t, (finSumFinEquiv.trans (finCongr (add_zero t))).symm i = Sum.inl i := by
    intro i
    rw [Equiv.symm_apply_eq]
    ext
    simp only [Equiv.trans_apply, finSumFinEquiv_apply_left]
    rfl
  ext i j
  simp only [bl, Matrix.submatrix_apply, h, Matrix.fromBlocks_apply₁₁]

theorem exists_isW (D : D7) (t : ℕ) : ∃ w : G D t, IsW w := by
  obtain ⟨⟨M⟩, -⟩ := GlobalTheory.CompanionTheory.JacobiMaps.mapsExist D t t 0 (add_zero t)
  refine ⟨M.w, ?_⟩
  have := M.w_mat
  simp only [blockMatrix_add_zero] at this
  exact this

theorem rsec_inv {hn : r + t = n} (M : Maps D hn) (m : Meas D r t) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D r)
    {θ : InfFam D} (ω : G D n →* Module.End ℂ (schwartzA θ a n)) (Φ : schwartzA θ a n) {Ω : G D t → Mx D r t → ℂ} (u : G D t)
    (h1 : ω (M.emb u) Φ = Φ) (h2 : ∀ h, Ω (h * u) = Ω h) (g : G D t) :
    Rsec M m ψ b₀ (fun g => (ω g Φ).1 0) 1 Ω (g * u) = Rsec M m ψ b₀ (fun g => (ω g Φ).1 0) 1 Ω g := by
  have hf : ∀ x, (ω (x * M.emb u) Φ).1 0 = (ω x Φ).1 0 := fun x => by
    rw [map_mul, Module.End.mul_apply, h1]
  have e1 : ∀ y z, M.w * M.nzx z 0 * (M.sh y * M.emb (g * u) * 1) =
      (M.w * M.nzx z 0 * (M.sh y * M.emb g * 1)) * M.emb u := fun y z => by
    rw [map_mul]
    simp only [mul_one, mul_assoc]
  simp only [Rsec, Wz, h2, e1, hf]

section Xi

variable (V : HSp D) (b₀ : HermE D r) (hn : r + t = n)

def xiP (Φ : Mx D V.rank n → ℂ) (η : Mx D r t → ℂ) (z : Mx D V.rank r × Mx D V.rank t) : ℂ :=
  Φ (jn hn z.1 z.2) * conj (η (yv V b₀ z))

variable {V b₀ hn}

theorem continuous_xiP {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {Φ : Mx D V.rank n → ℂ} {η : Mx D r t → ℂ}
    (hΦ : Continuous Φ) (hη : Continuous η) : Continuous (xiP V b₀ hn Φ η) := by
  have hy := (GlobalTheory.CompanionTheory.RCellCont.continuity_characters_projection (t := t) hψ V b₀ (0 : hermA D t)).2.1
  exact (hΦ.comp (continuous_jn hn)).mul (Complex.continuous_conj.comp (hη.comp hy))

theorem xiP_cond {S : Finset (Pl D)} {e : AE D} (he : e * e = e) (hc : cA D e = e) {Φ : Mx D V.rank n → ℂ} {η : Mx D r t → ℂ}
    (hΦ : Good S e Φ) (hη : Good S e η)
    (hy : ∀ z : Mx D V.rank r × Mx D V.rank t, IntOff S z.1 → IntOff S z.2 → IntOff S (yv V b₀ z))
    (p : Mx D V.rank r × Mx D V.rank t → ℂ) (hp : ∀ z, p (e • z.1, e • z.2) = p z) (z : Mx D V.rank r × Mx D V.rank t) :
    (IntOff S z.1 ∧ IntOff S z.2 → xiP V b₀ hn Φ η z * p z = xiP V b₀ hn Φ η (e • z.1, e • z.2) * p (e • z.1, e • z.2)) ∧
      (¬ (IntOff S z.1 ∧ IntOff S z.2) → xiP V b₀ hn Φ η z * p z = 0) := by
  refine ⟨fun ⟨h1, h2⟩ => ?_, fun h => ?_⟩
  · have a1 := hΦ (jn hn z.1 z.2)
    rw [if_pos ((intOff_jn hn _ _).2 ⟨h1, h2⟩), jn_smul] at a1
    have a2 := hη (yv V b₀ z)
    rw [if_pos (hy z h1 h2), ← yv_smul he hc] at a2
    rw [hp]
    simp only [xiP]
    rw [a1, a2]
  · have a1 := hΦ (jn hn z.1 z.2)
    rw [if_neg (fun hh => h ((intOff_jn hn _ _).1 hh))] at a1
    simp [xiP, a1]


set_option synthInstance.maxHeartbeats 400000 in
theorem cell_id {S : Finset (Pl D)} {e : AE D} (he : e * e = e) (hc : cA D e = e) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsCharAF D.host.F ψ) [BorelSpace (Mx D V.rank r × Mx D V.rank t)]
    {P : Measure (Mx D V.rank r × Mx D V.rank t)} {σ : Measure (XS D V.rank r t e)}
    (hL : ∀ Ξ : Mx D V.rank r × Mx D V.rank t → ℂ, Continuous Ξ →
      (∀ z, (IntOff S z.1 ∧ IntOff S z.2 → Ξ z = Ξ (e • z.1, e • z.2)) ∧ (¬ (IntOff S z.1 ∧ IntOff S z.2) → Ξ z = 0)) →
      (Integrable Ξ P → Integrable (fun z : XS D V.rank r t e => Ξ z.1) σ) ∧ ∫ z, Ξ z ∂P = ∫ z : XS D V.rank r t e, Ξ z.1 ∂σ)
    (hy : ∀ z : Mx D V.rank r × Mx D V.rank t, IntOff S z.1 → IntOff S z.2 → IntOff S (yv V b₀ z))
    {Φ : Mx D V.rank n → ℂ} {η : Mx D r t → ℂ} (hΦc : Continuous Φ) (hηc : Continuous η) (hΦ : Good S e Φ) (hη : Good S e η)
    {B : ℝ} (hB : ∀ y, ‖η y‖ ≤ B) (hI : Integrable (fun z : Mx D V.rank r × Mx D V.rank t => Φ (jn hn z.1 z.2)) P) :
    Integrable (fun z : XS D V.rank r t e => xiP V b₀ hn Φ η z.1) σ ∧
      ∀ x : hermS D t e, ∫ z, xiP V b₀ hn Φ η z * pch ψ x.1.1 (qv V b₀ z) ∂P =
        ∫ z : XS D V.rank r t e, xiP V b₀ hn Φ η z.1 * pch ψ x.1.1 (qv V b₀ z.1) ∂σ := by
  have hx := continuous_xiP (b₀ := b₀) (hn := hn) hψ hΦc hηc
  haveI : OpensMeasurableSpace (Mx D V.rank r × Mx D V.rank t) := BorelSpace.opensMeasurable
  constructor
  · have hc1 := xiP_cond (hn := hn) he hc hΦ hη hy (fun _ => 1) (fun _ => rfl)
    simp only [mul_one] at hc1
    refine (hL _ hx hc1).1 ?_
    refine (hI.norm.const_mul B).mono' hx.aestronglyMeasurable (ae_of_all _ fun z => ?_)
    simp only [xiP, norm_mul, RCLike.norm_conj]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
  · intro x
    have hcp := (GlobalTheory.CompanionTheory.RCellCont.continuity_characters_projection (t := t) hψ V b₀ x.1).2.2.2.1
    refine (hL (fun z => xiP V b₀ hn Φ η z * pch ψ x.1.1 (qv V b₀ z)) (hx.mul hcp) ?_).2
    refine xiP_cond (hn := hn) he hc hΦ hη hy _ fun z => ?_
    rw [qv_smul he hc]
    exact pch_smul x.2 _

end Xi

end GlobalTheory.CompanionTheory.EisE

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftCommutesLeviEmbedding
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn.Model

namespace GlobalTheory.CompanionTheory.PcB

open GlobalTheory.CompanionTheory.FourierN (mat_injective)

theorem blockMatrix_zero' {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) :
    bl hn (0 : Matrix (Fin ρ) (Fin ρ) R) 0 0 0 = 0 := by
  simp only [bl]
  rw [Matrix.fromBlocks_zero]
  rfl

theorem lowerUnipotent_mul_blockDiagonal {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) (c : Matrix (Fin p) (Fin ρ) R)
    (d : Matrix (Fin p) (Fin p) R) :
    HMul.hMul (bl hn 1 0 c 1) (bl hn 1 0 0 d) = bl hn 1 0 c d := by
  simp only [bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  congr 1 <;> simp

theorem blockMatrix_diagonal_mul_lowerUnipotent {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) (c : Matrix (Fin p) (Fin ρ) R)
    (d : Matrix (Fin p) (Fin p) R) :
    HMul.hMul (bl hn 1 0 0 d) (bl hn 1 0 c 1) = bl hn 1 0 (HMul.hMul d c) d := by
  simp only [bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  congr 1 <;> simp

theorem upperUnipotent_mul_blockDiagonal {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) (y : Matrix (Fin ρ) (Fin p) R)
    (d : Matrix (Fin p) (Fin p) R) :
    HMul.hMul (bl hn 1 y 0 1) (bl hn 1 0 0 d) = bl hn 1 (HMul.hMul y d) 0 d := by
  simp only [bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  congr 1 <;> simp

theorem blockMatrix_diagonal_mul_upperUnipotent {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) (y : Matrix (Fin ρ) (Fin p) R)
    (d : Matrix (Fin p) (Fin p) R) :
    HMul.hMul (bl hn 1 0 0 d) (bl hn 1 y 0 1) = bl hn 1 y 0 d := by
  simp only [bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  congr 1 <;> simp

theorem sh_emb_levi (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (g₀ : G D p)
    (a : GL (Fin p) (AE D)) (h : mat g₀ = blk4 a.1 0 0 (adj (a⁻¹).1)) (y : Mx D ρ p) :
    M.sh y * M.emb g₀ = M.emb g₀ * M.sh (HMul.hMul y a.1 : Mx D ρ p) := by
  have hinv : HMul.hMul (adj (a⁻¹).1 : Mx D p p) (adj a.1 : Mx D p p) = (1 : Mx D p p) := by
    have h1 : HMul.hMul (a.1 : Mx D p p) ((a⁻¹).1 : Mx D p p) = (1 : Mx D p p) := by
      exact congrArg Units.val (mul_inv_cancel a)
    rw [← adj_mul, h1]
    exact adj_one
  have diag_mul (A A' B B' : Mx D n n) :
      blk4 A 0 0 A' * blk4 B 0 0 B' = blk4 (A * B) 0 0 (A' * B') := by
    rw [submatrix_fromBlocks_mul]
    congr 1 <;> simp
  apply mat_injective
  rw [mat_mul', mat_mul', M.sh_mat, M.sh_mat, M.emb_mat g₀ _ _ _ _ h, blockMatrix_zero', diag_mul, diag_mul]
  congr 1
  · rw [upperUnipotent_mul_blockDiagonal, blockMatrix_diagonal_mul_upperUnipotent]
  · have hk : HMul.hMul (adj (a⁻¹).1 : Mx D p p) (adj (HMul.hMul y a.1 : Mx D ρ p)) = adj y := by
      rw [adj_mul, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
    have hk' : HMul.hMul (adj (a⁻¹).1 : Mx D p p) (-adj (HMul.hMul y a.1 : Mx D ρ p)) = -adj y := by
      rw [Matrix.mul_neg, hk]
    rw [lowerUnipotent_mul_blockDiagonal, blockMatrix_diagonal_mul_lowerUnipotent, hk']

end GlobalTheory.CompanionTheory.PcB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftConjHeisenberg
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem sh_mul_nzx {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (y : Mx D ρ p)
    (z : hermA D ρ) (x : Mx D ρ p) :
    M.sh y * M.nzx z x = M.nzx (z + GlobalTheory.CompanionTheory.FJE.jc y x) x * M.sh y := by
  apply GlobalTheory.CompanionTheory.FourierN.mat_injective
  rw [GlobalTheory.CompanionTheory.PcB.mat_mul', GlobalTheory.CompanionTheory.PcB.mat_mul',
    M.nzx_mat, M.nzx_mat, M.sh_mat]
  simp only [blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add]
  simp only [bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add]
  congr 2
  simp only [jc]
  congr 2
  rw [Matrix.mul_neg]
  change z.1 + y * adj x = (z.1 + (y * adj x + x * adj y)) + -(x * adj y)
  abel

end GlobalTheory.CompanionTheory.FJE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentAdditiveLaw
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.NzxAdd

theorem nzx_add : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (z z' : hermA D ρ) (x x' : Mx D ρ p), M.nzx z x * M.nzx z' x' = M.nzx (z + z') (x + x') := by
  intro D n ρ p hn M z z' x x'
  exact GlobalTheory.CompanionTheory.PcB.nzx_mul M z z' x x'

end GlobalTheory.CompanionTheory.NzxAdd
end
end

