module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0293
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.ExhaustionFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0212
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBallLeadingGramMinorLowerBoundLast
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall.MinorLast

open Matrix
open scoped ComplexOrder

theorem det_sub_bound {p m : ℕ} (N : Matrix (Fin p) (Fin m) ℂ) (q : Fin p → ℂ) :
    (1 - ∑ c, ‖q c‖ ^ 2) * ‖(Nᴴ * N).det‖ ≤
      ‖(Nᴴ * N - vecMulVec (star (q ᵥ* N)) (q ᵥ* N)).det‖ := by
  set A := Nᴴ * N with hAdef
  set u := q ᵥ* N with hu
  by_cases hA : A.det = 0
  · rw [hA]; simp
  have hU : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have hsplit : A - vecMulVec (star u) u = A + replicateCol Unit (-star u) * replicateRow Unit u := by
    ext i j
    simp [vecMulVec, replicateCol, replicateRow, Matrix.mul_apply, sub_eq_add_neg]
  have key : (A - vecMulVec (star u) u).det = A.det * (1 - u ⬝ᵥ A⁻¹ *ᵥ star u) := by
    rw [hsplit, Matrix.det_add_mul _ _ hU]
    congr 1
    rw [Matrix.det_unique]
    simp [Matrix.mul_apply, replicateRow, replicateCol, dotProduct, mulVec, sub_eq_add_neg,
      Finset.mul_sum]
    simp only [Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  set P := N * A⁻¹ * Nᴴ with hPdef
  have hs : u ⬝ᵥ A⁻¹ *ᵥ star u = q ⬝ᵥ P *ᵥ star q := by
    rw [hu, Matrix.star_vecMul, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec]
  have hAh : Aᴴ = A := by rw [hAdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hPh : Pᴴ = P := by
    rw [hPdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_nonsing_inv, hAh, Matrix.mul_assoc]
  have hPP : P * P = P := by
    have h1 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hU
    calc P * P = N * (A⁻¹ * (Nᴴ * N) * A⁻¹) * Nᴴ := by simp only [hPdef, Matrix.mul_assoc]
      _ = P := by rw [← hAdef, h1, Matrix.one_mul, hPdef, Matrix.mul_assoc]
  have hQ : (1 - P) = (1 - P)ᴴ * (1 - P) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPh, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub, hPP]
    simp
  have hpsd : (1 - P).PosSemidef := by rw [hQ]; exact Matrix.posSemidef_conjTranspose_mul_self _
  have ht := hpsd.dotProduct_mulVec_nonneg (star q)
  rw [star_star, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub] at ht
  have hqq : q ⬝ᵥ star q = ((∑ c, ‖q c‖ ^ 2 : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.ofReal_sum,
      Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have ha := (Matrix.posSemidef_conjTranspose_mul_self N).det_nonneg
  rw [← hAdef] at ha
  rw [key, hs]
  set a := A.det
  set t := q ⬝ᵥ star q - q ⬝ᵥ P *ᵥ star q with htdef
  have hsq : q ⬝ᵥ P *ᵥ star q = ((∑ c, ‖q c‖ ^ 2 : ℝ) : ℂ) - t := by rw [htdef, hqq]; ring
  rw [hsq]
  obtain ⟨ha1, ha2⟩ := Complex.nonneg_iff.1 ha
  obtain ⟨ht1, ht2⟩ := Complex.nonneg_iff.1 ht
  have hae : a = (a.re : ℂ) := Complex.ext rfl (by simp [← ha2])
  have hte : t = (t.re : ℂ) := Complex.ext rfl (by simp [← ht2])
  rw [hae, hte, Complex.norm_real, Real.norm_of_nonneg ha1]
  rw [show (a.re : ℂ) * (1 - (((∑ c, ‖q c‖ ^ 2 : ℝ) : ℂ) - (t.re : ℂ))) = ((a.re * (1 - ∑ c, ‖q c‖ ^ 2 + t.re) : ℝ) : ℂ) by push_cast; ring]
  rw [Complex.norm_real]
  calc (1 - ∑ c, ‖q c‖ ^ 2) * a.re ≤ a.re * (1 - ∑ c, ‖q c‖ ^ 2 + t.re) := by nlinarith
    _ ≤ _ := Real.le_norm_self _

end GlobalTheory.IntBall.MinorLast

namespace GlobalTheory.IntBall.MinorLast

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem gram_eq_mul {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem gram_mul {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x y : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ G (x * y) = yᵀ * ReciprocityTheory.ChartRestriction.G.FD.gram τ G x * y.map (starRingEnd ℂ) := by
  rw [gram_eq_mul, gram_eq_mul, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

theorem entry_tdm {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (d : Fin r → ℂ) (i j : Fin r) :
    (Mᵀ * Matrix.diagonal d * M.map (starRingEnd ℂ)) i j = ∑ l, M l i * d l * starRingEnd ℂ (M l j) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply]

variable {p : ℕ} (X : Data E (p + 1))

theorem nmat_eq (z : V (nd X)) (τ : X.Ψ) (a b : Fin (p + 1)) :
    nmat X z τ a b = lowMat (zOf X z τ) a b := rfl

theorem n_top (hp : X.p0 = p) (z : V (nd X)) (τ : X.Ψ) (i a : Fin p) :
    mat (nFrame X z) τ i.castSucc a.castSucc = lowMat (zOf X z τ) i.castSucc a.castSucc := by
  show (∑ c, zFrame X z τ i.castSucc c * leviFrame X z τ c a.castSucc) = _
  rw [Fin.sum_univ_castSucc]
  have hl : zFrame X z τ i.castSucc (Fin.last p) = 0 := by
    simp [zFrame, hp, Fin.ext_iff]; omega
  rw [hl, zero_mul, add_zero]
  rw [Finset.sum_eq_single i]
  · simp [zFrame, leviFrame, hp, nmat_eq]
    rw [if_neg (by omega), if_neg (by omega)]
  · intro b _ hb
    have : i.castSucc ≠ b.castSucc := fun h => hb (Fin.castSucc_injective _ h).symm
    simp [zFrame, hp, this]
  · simp

theorem n_last (hp : X.p0 = p) (z : V (nd X)) (τ : X.Ψ) (a : Fin p) :
    mat (nFrame X z) τ (Fin.last p) a.castSucc =
      ∑ c : Fin p, lowMat (zOf X z τ) (Fin.last p) c.castSucc * lowMat (zOf X z τ) c.castSucc a.castSucc := by
  show (∑ c, zFrame X z τ (Fin.last p) c * leviFrame X z τ c a.castSucc) = _
  simp [zFrame, leviFrame, hp, nmat_eq, Fin.sum_univ_castSucc]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [if_neg (by omega)]

end GlobalTheory.IntBall.MinorLast

namespace GlobalTheory.IntBall.MinorLast

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {p : ℕ}

theorem finiteRing_sq_sub_mul_sq_eq_of_card (X : Data E (p + 1)) (hp : X.p0 = p) (x0 : Base X) (z : V (nd X)) (τ : X.Ψ)
    (k : Fin p) :
    zDet X z τ * colGram (blkW X.p0 (zOf X z τ)) k.succ ≤
      ‖dmin X.Gm (point X x0 z) τ ⟨(k : ℕ) + 1, by omega⟩‖ := by
  set w := zOf X z τ with hw
  let N : Matrix (Fin p) (Fin ((k : ℕ) + 1)) ℂ := fun i a => lowMat w i.castSucc (Fin.castSucc ⟨a, by omega⟩)
  let q : Fin p → ℂ := fun c => lowMat w (Fin.last p) c.castSucc
  have hA : colGram (blkW X.p0 w) k.succ = ‖(Nᴴ * N).det‖ := by
    have hB : blkW X.p0 w = fun (i j : Fin (p + 1 - 1)) => lowMat w ⟨i, by omega⟩ ⟨j, by omega⟩ := by
      funext i j
      unfold blkW
      split_ifs with h
      · have hi : (i : ℕ) = 0 := by omega
        have hj : (j : ℕ) = 0 := by omega
        simp [lowMat, hi, hj, Fin.ext_iff]
      · rfl
    rw [hB]
    rfl
  have hZ : zDet X z τ = 1 - ∑ c, ‖q c‖ ^ 2 := by
    unfold zDet
    rw [Matrix.det_one_sub_mul_comm]
    letI hU : Unique {a : Fin (p + 1) // X.p0 ≤ (a : ℕ)} :=
      { default := ⟨Fin.last p, by simp [hp]⟩
        uniq := fun a => Subtype.ext (Fin.ext (by have := a.2; have := a.1.2; simp; omega)) }
    rw [Matrix.det_unique]
    let e : Fin p ≃ {b : Fin (p + 1) // (b : ℕ) < X.p0} :=
      { toFun := fun c => ⟨c.castSucc, by simp [hp]⟩
        invFun := fun b => ⟨b.1, by have := b.2; omega⟩
        left_inv := fun c => rfl
        right_inv := fun b => rfl }
    have hs : ∑ b : {b : Fin (p + 1) // (b : ℕ) < X.p0},
        zBlock X z τ default b * star (zBlock X z τ default b) = ((∑ c, ‖q c‖ ^ 2 : ℝ) : ℂ) := by
      rw [← Fintype.sum_equiv e (fun c => zBlock X z τ default (e c) * star (zBlock X z τ default (e c)))
        _ (fun _ => rfl)]
      push_cast
      refine Finset.sum_congr rfl fun c _ => ?_
      change q c * star (q c) = _
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast; rfl
    simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [hs]
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
  have hD : dmin X.Gm (point X x0 z) τ ⟨(k : ℕ) + 1, by omega⟩ =
      (Nᴴ * N - Matrix.vecMulVec (star (q ᵥ* N)) (q ᵥ* N)).det := by
    have hg : ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (mat (point X x0 z) τ) =
        (mat (nFrame X z) τ)ᵀ * Matrix.diagonal (fun a : Fin (p + 1) => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) *
          (mat (nFrame X z) τ).map (starRingEnd ℂ) := by
      rw [show mat (point X x0 z) τ = mat x0.1 τ * mat (nFrame X z) τ from rfl, gram_mul, x0.2 τ]
    unfold dmin lminor
    rw [hg, ← Matrix.det_transpose (Nᴴ * N - _)]
    congr 1
    ext a b
    have hc : ∀ a : Fin ((k : ℕ) + 1), (Fin.castLE (by omega) a : Fin (p + 1)) =
        Fin.castSucc (⟨a, by omega⟩ : Fin p) := fun a => Fin.ext rfl
    rw [Matrix.submatrix_apply, hc, hc, entry_tdm, Fin.sum_univ_castSucc]
    simp only [n_top X hp, n_last X hp, Fin.val_castSucc, Fin.val_last, sgn, hp, Fin.is_lt, if_true,
      lt_irrefl, if_false, Matrix.transpose_apply, Matrix.sub_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, Matrix.vecMul, dotProduct, Pi.star_apply, N, q, ← hw]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.ofReal_one, Complex.ofReal_neg,
      mul_one, Complex.star_def]
    rw [sub_eq_add_neg]
    congr 1
    · exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    · ring
  rw [hA, hZ, hD]
  exact det_sub_bound N q

end GlobalTheory.IntBall.MinorLast

namespace GlobalTheory.IntBall.MinorLast

theorem zDet_mul_colGram_le_dmin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), X.p0 + 1 = r → ∀ (x0 : Base X) (z : V (nd X)), z ∈ Om X → ∀ (τ : X.Ψ) (k : Fin (r - 1)), zDet X z τ * colGram (blkW X.p0 (zOf X z τ)) k.succ ≤ ‖dmin X.Gm (point X x0 z) τ ⟨(k : ℕ) + 1, by omega⟩‖ := by
  intro E _ _ _ r X hr x0 z _ τ k
  obtain ⟨p, rfl⟩ : ∃ p, r = p + 1 := ⟨X.p0, hr.symm⟩
  exact finiteRing_sq_sub_mul_sq_eq_of_card X (by omega) x0 z τ k

end GlobalTheory.IntBall.MinorLast
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharacterAbsScalarEventuallyEqOne
section
noncomputable section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary ValuativeRel Filter
open scoped Topology
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem sc_eventually_eq_one : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E]
    (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (m : ℕ) (χ : Eˣ →* Circle) (_ : Continuous χ),
    ∀ᶠ z in nhds (1 : E), sc F χ m z = 1 := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE m χ hχ
  obtain ⟨hfd, htr, hinv, ht2, -, hN, -, -⟩ := _root_.GlobalTheory.quadExt_topology F E c δ hE
  obtain ⟨L, hL, hLc, hLo⟩ := GlobalTheory.T.exists_compactOpen_normClosedBall_quadratic F E c δ hE 1

  have h0 : {t : Eˣ | ‖(χ t : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (1 : Eˣ) :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp)
  rw [Units.isEmbedding_val₀.nhds_eq_comap, mem_comap] at h0
  obtain ⟨U, hU, hUV⟩ := h0

  have h1 : ∀ᶠ π in 𝓝 (0 : F), ∀ a ∈ (L : Set E), 1 + π • a ∈ U := by
    refine hLc.eventually_forall_of_forall_eventually fun a _ => ?_
    have : Tendsto (fun q : F × E => 1 + q.1 • q.2) (𝓝 (0, a)) (𝓝 1) :=
      Continuous.tendsto' (by fun_prop) _ _ (by simp)
    exact this hU
  have h2 : {x : F | valuation F x < 1} ∈ 𝓝 (0 : F) := (IsValuativeTopology.mem_nhds_zero_iff _).mpr ⟨1, fun _ h => h⟩
  obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset (inter_mem h1 h2)
  obtain ⟨hsU, hsv⟩ := hs (show (s : F) ∈ GlobalTheory.SplitWeil.cball s from show valuation F (s : F) ≤ valuation F (s : F) from le_rfl)
  set π : F := (s : F) with hπdef
  have hπ : π ≠ 0 := s.ne_zero

  have hmul : ∀ a ∈ (L : Set E), ∀ b ∈ (L : Set E), a * b ∈ (L : Set E) := by
    intro a ha b hb
    rw [hL] at ha hb ⊢
    show valuation F (Algebra.norm F (a * b)) ≤ valuation F ((1 : Fˣ) : F)
    have ha' : valuation F (Algebra.norm F a) ≤ 1 := by simpa [GlobalTheory.SplitWeil.cball] using ha
    have hb' : valuation F (Algebra.norm F b) ≤ 1 := by simpa [GlobalTheory.SplitWeil.cball] using hb
    rw [map_mul, map_mul]
    simpa using mul_le_one' ha' hb'
  have hsm : ∀ a ∈ (L : Set E), π • a ∈ (L : Set E) := by
    intro a ha
    rw [hL] at ha ⊢
    show valuation F (Algebra.norm F (π • a)) ≤ valuation F ((1 : Fˣ) : F)
    have ha' : valuation F (Algebra.norm F a) ≤ 1 := by simpa [GlobalTheory.SplitWeil.cball] using ha
    rw [Algebra.smul_def, map_mul, Algebra.norm_algebraMap, map_mul, map_pow]
    simpa using mul_le_one' (pow_le_one' hsv.le _) ha'

  set V : Set E := {z | π⁻¹ • (z - 1) ∈ (L : Set E)} with hVdef
  have hVo : IsOpen V := hLo.preimage (by fun_prop)
  have hV1 : (1 : E) ∈ V := by simp [V, L.zero_mem]
  have hVU : V ⊆ U := by
    intro z hz
    have := hsU _ hz
    rwa [smul_smul, mul_inv_cancel₀ hπ, one_smul, add_sub_cancel] at this
  have hVpow : ∀ z ∈ V, ∀ n : ℕ, z ^ n ∈ V := by
    intro z hz n
    induction n with
    | zero => simpa using hV1
    | succ n ih =>
      show π⁻¹ • (z ^ (n + 1) - 1) ∈ (L : Set E)
      have hz' : z = 1 + π • (π⁻¹ • (z - 1)) := by
        rw [smul_smul, mul_inv_cancel₀ hπ, one_smul, add_sub_cancel]
      have e : π⁻¹ • (z ^ (n + 1) - 1) =
          π⁻¹ • (z ^ n - 1) + π • ((π⁻¹ • (z - 1)) * (π⁻¹ • (z ^ n - 1))) + π⁻¹ • (z - 1) := by
        have hp : algebraMap F E π ≠ 0 := (map_ne_zero _).mpr hπ
        simp only [Algebra.smul_def, map_inv₀]
        field_simp
        ring
      rw [e]
      exact L.add_mem (L.add_mem ih (hsm _ (hmul _ hz _ ih))) hz

  have h3 : Tendsto (fun z : E => Algebra.norm F z - 1) (𝓝 1) (𝓝 0) :=
    Continuous.tendsto' (by fun_prop) _ _ (by simp)
  filter_upwards [hVo.mem_nhds hV1, eventually_ne_nhds (one_ne_zero : (1 : E) ≠ 0), h3.eventually h2] with z hz hz0 hzN
  have hv : valuation F (Algebra.norm F z) = 1 := by
    simpa using (valuation F).map_one_add_of_lt hzN
  have hχz : χ (Units.mk0 z hz0) = 1 := by
    refine Circle.coe_eq_one.mp (GlobalTheory.WeilM.eq_one_of_forall_pow_near fun n => ?_)
    have : (Units.mk0 z hz0) ^ n ∈ Units.val ⁻¹' U := by simpa using hVU (hVpow z hz n)
    simpa using hUV this
  have hn : nabs F (Units.map (Algebra.norm F : E →* F) (Units.mk0 z hz0)) = 1 :=
    GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one (by simpa using hv)
  simp [sc, hz0, hχz, hn]

end GlobalTheory.KSp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeChartChange
section
set_option autoImplicit false

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR

namespace GlobalTheory.PD

section Alt

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem altMap_add_smul_self {n : ℕ} (f : M [⋀^Fin n]→ₗ[R] N) (v : Fin n → M) (k : Fin n) (c : Fin n → R)
    (hc : c k = 0) : f (fun j => v j + c j • v k) = f v := by
  classical
  have key : ∀ s : Finset (Fin n), f (fun j => v j + if j ∈ s then c j • v k else 0) = f v := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      by_cases hak : a = k
      · subst hak
        have e : (fun j => v j + if j ∈ insert a s then c j • v a else 0) =
            (fun j => v j + if j ∈ s then c j • v a else 0) := by
          funext j
          by_cases hj : j = a
          · subst hj; simp [hc]
          · simp [Finset.mem_insert, hj]
        rw [e, ih]
      · set g : Fin n → M := fun j => v j + if j ∈ s then c j • v k else 0 with hg
        have e1 : (fun j => v j + if j ∈ insert a s then c j • v k else 0) = Function.update g a (v a + c a • v k) := by
          funext j
          by_cases hj : j = a
          · subst hj; simp
          · simp [hg, Function.update_of_ne hj, Finset.mem_insert, hj]
        have e2 : Function.update g a (v a) = g := by
          funext j
          by_cases hj : j = a
          · subst hj; simp [hg, ha]
          · simp [Function.update_of_ne hj]
        have e3 : f (Function.update g a (v k)) = 0 := by
          refine f.map_eq_zero_of_eq _ (i := a) (j := k) ?_ hak
          simp [Function.update_of_ne (Ne.symm hak), hg, hc]
        rw [e1, f.map_update_add, f.map_update_smul, e2, ih, e3, smul_zero, add_zero]
  simpa using key Finset.univ

theorem exists_perm_succ {d : ℕ} (τ : Fin d → Fin (d + 1)) (hinj : Function.Injective τ) (hne : ∀ j, τ j ≠ 0) :
    ∃ π : Equiv.Perm (Fin d), τ = Fin.succ ∘ π := by
  let p : Fin d → Fin d := fun j => (τ j).pred (hne j)
  have hp : Function.Injective p := by
    intro a b hab
    apply hinj
    simpa [p] using congrArg Fin.succ hab
  refine ⟨Equiv.ofBijective p (Finite.injective_iff_bijective.1 hp), ?_⟩
  funext j
  simp [p]

theorem altMap_sub_succAbove {d : ℕ} (f : M [⋀^Fin d]→ₗ[R] N) (θ : Fin (d + 1) → M) (h0 : θ 0 = 0)
    (i : Fin (d + 1)) : ∃ ε : ℤˣ, f (fun j => θ (i.succAbove j) - θ i) = ε • f (fun j => θ j.succ) := by
  classical
  cases i using Fin.cases with
  | zero => exact ⟨1, by simp [h0]⟩
  | succ i' =>
    have hd : 0 < d := Nat.lt_of_le_of_lt (Nat.zero_le _) i'.isLt
    set i : Fin (d + 1) := i'.succ with hi
    set j0 : Fin d := ⟨0, hd⟩ with hj0
    have hσ0 : i.succAbove j0 = 0 := by
      rw [Fin.succAbove_of_castSucc_lt]
      · rfl
      · rw [Fin.lt_def]; simp [hi, hj0]
    set w : Fin d → M := fun j => θ (i.succAbove j) - θ i with hw
    set c : Fin d → R := fun j => if j = j0 then 0 else -1 with hc
    have k1 := altMap_add_smul_self f w j0 c (by simp [hc])
    have e1 : (fun j => w j + c j • w j0) = Function.update (θ ∘ i.succAbove) j0 ((-1 : R) • θ i) := by
      funext j
      by_cases hj : j = j0
      · subst hj; simp [hw, hc, hσ0, h0]
      · simp [hw, hc, hj, hσ0, h0, Function.update_of_ne hj]
    set τ : Fin d → Fin (d + 1) := Function.update i.succAbove j0 i with hτ
    have e2 : Function.update (θ ∘ i.succAbove) j0 (θ i) = θ ∘ τ := by
      funext j
      by_cases hj : j = j0
      · subst hj; simp [hτ]
      · simp [hτ, Function.update_of_ne hj]
    have hτinj : Function.Injective τ := by
      intro a b hab
      by_cases ha : a = j0 <;> by_cases hb : b = j0
      · rw [ha, hb]
      · simp [hτ, ha, Function.update_of_ne hb] at hab
      · simp [hτ, hb, Function.update_of_ne ha] at hab
      · simp only [hτ, Function.update_of_ne ha, Function.update_of_ne hb] at hab
        exact Fin.succAbove_right_injective hab
    have hτne : ∀ j, τ j ≠ 0 := by
      intro j
      by_cases hj : j = j0
      · subst hj; simp [hτ, hi]
      · rw [hτ, Function.update_of_ne hj, ← hσ0]
        exact fun h => hj (Fin.succAbove_right_injective h)
    obtain ⟨π, hπ⟩ := exists_perm_succ τ hτinj hτne
    refine ⟨-Equiv.Perm.sign π, ?_⟩
    rw [← k1, e1, f.map_update_smul, e2, hπ]
    have e3 : θ ∘ (Fin.succ ∘ ⇑π) = (fun j => θ j.succ) ∘ ⇑π := rfl
    rw [e3, f.map_perm, Units.neg_smul, neg_one_smul]

end Alt

theorem volume_chart_change (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F]
    [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F) (h : IsFinCover k K x)
    (i : Fin (d + 1)) : ∃ ε : ℤˣ, (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (x (i.succAbove j) / x i))) =
      ε • algebraMap F K (∏ j, x j / x i) • vol0 k K x := by
  have hx := h.pd.ne
  set y : Fin (d + 1) → K := fun a => algebraMap F K (x a / x 0) with hy
  have hy0 : ∀ a, y a ≠ 0 := fun a => (map_ne_zero _).2 (div_ne_zero (hx a) (hx 0))
  set θ : Fin (d + 1) → Ω[K⁄k] := fun a => (y a)⁻¹ • D k K (y a) with hθ
  have hθ0 : θ 0 = 0 := by
    show (algebraMap F K (x 0 / x 0))⁻¹ • D k K (algebraMap F K (x 0 / x 0)) = 0
    rw [div_self (hx 0), map_one, Derivation.map_one_eq_zero, smul_zero]
  have hD : ∀ a, D k K (algebraMap F K (x a / x i)) = algebraMap F K (x a / x i) • (θ a - θ i) := by
    intro a
    have e : algebraMap F K (x a / x i) = y a / y i := by
      simp only [hy, ← map_div₀]
      congr 1
      field_simp [hx 0, hx i]
    have ha := hy0 a
    have hi := hy0 i
    rw [e, Derivation.leibniz_div, hθ]
    simp only [smul_sub, smul_smul]
    congr 2 <;> field_simp
  obtain ⟨ε, hε⟩ := altMap_sub_succAbove (ExteriorAlgebra.ιMulti K d) θ hθ0 i
  refine ⟨ε, ?_⟩
  have hprod : algebraMap F K (∏ j, x j / x i) = ∏ j, algebraMap F K (x (i.succAbove j) / x i) := by
    rw [Fin.prod_univ_succAbove _ i, div_self (hx i), one_mul, map_prod]
  simp only [hD]
  rw [AlternatingMap.map_smul_univ, hε, hprod]
  rw [smul_comm]
  rfl

end GlobalTheory.PD
end
end

