module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0317
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0249

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinkedLineVectorsInvertibleOnThetaFunctions
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct Matrix GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.LinkInvTheta

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj starAdj starAdj_ofAdj)

variable {D : D7}

theorem star_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) : star (ψ a) = ψ (-a) := by
  have h1 : ‖ψ a‖ = 1 := hψ.1.2.1 a
  have h2 : ψ a * star (ψ a) = 1 := by
    rw [Complex.star_def, Complex.mul_conj', h1]; simp
  have h3 : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h0 : ψ a ≠ 0 := by intro h; rw [h, zero_mul] at h3; exact zero_ne_one h3
  exact mul_left_cancel₀ h0 (h2.trans h3.symm)

theorem map_starAdj_eq_zero {B : Type} [CommRing B] (φ : AE D →+* B) (hφ : ∀ z, φ z = 0 → φ (cA D z) = 0)
    (L S : HSp D) {x : WO L S} (hx : x.map φ = 0) : (starAdj L S x).map φ = 0 := by
  have h1 : (adj x).map φ = 0 := by
    funext i j
    exact hφ (x j i) (congrFun (congrFun hx j) i)
  have h2 := map_mul_eq_zero_right φ (giA L) (map_mul_eq_zero_left φ h1 (gA S))
  funext i j
  have h3 : φ ((giA L ⬝ (adj x ⬝ gA S) : Mx D L.rank S.rank) i j) = 0 := congrFun (congrFun h2 i) j
  show φ (incA D D.host.xi0 * (giA L ⬝ (adj x ⬝ gA S) : Mx D L.rank S.rank) i j) = 0
  rw [map_mul, h3, mul_zero]

theorem continuous_starAdj (L S : HSp D) : Continuous (starAdj L S) := by
  have h1 : Continuous fun x : WO L S => (adj x ⬝ gA S : Mx D L.rank S.rank) :=
    continuous_adj.matrix_mul continuous_const
  have h2 : Continuous fun x : WO L S => (giA L ⬝ (adj x ⬝ gA S) : Mx D L.rank S.rank) :=
    continuous_const.matrix_mul h1
  exact h2.const_smul (incA D D.host.xi0)

theorem starAdj_mem (L S : HSp D) {x : WO L S} (hx : x ∈ ratMx D S.rank L.rank) :
    starAdj L S x ∈ ratMx D L.rank S.rank := by
  obtain ⟨γ, hγ⟩ := mem_ratMx.1 hx
  rw [← hγ, starAdj, giA, gA, ← rat_conjTranspose, ← rat_mul, ← rat_mul, ← rat_smul]
  exact rat_mem _

theorem lnk_simil {L L' : HSp D} {ζ : Fin L.rank → D.host.E} {ζ' : Fin L'.rank → D.host.E} (h : IsLineVec L' ζ')
    (l : Lnk L ζ L' ζ') : l.τᴴ ⬝ (L.gram ⬝ l.τ) = (D.host.xi0 * star D.host.xi0) • L'.gram := by
  have e : star ζ' ⬝ᵥ (l.τᴴ ⬝ (L.gram ⬝ l.τ)) *ᵥ ζ' =
      star ζ' ⬝ᵥ ((D.host.xi0 * star D.host.xi0) • L'.gram) *ᵥ ζ' := by
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.star_mulVec, ← Matrix.mulVec_mulVec, l.map, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, ← l.norm, star_neg, Matrix.mulVec_neg, neg_dotProduct_neg]
  have hu : Unique (Fin L'.rank) := by rw [h.1]; infer_instance
  have h2 := h.2
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_unique] at e h2
  funext i j
  rw [Subsingleton.elim i default, Subsingleton.elim j default]
  have a : star ζ' default ≠ 0 := left_ne_zero_of_mul h2
  have b : ζ' default ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul h2)
  have c := mul_left_cancel₀ a e
  have c' := mul_right_cancel₀ b c
  exact c'

theorem link_inv_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (L L' S : HSp D) (ζ : Fin L.rank → D.host.E) (ζ' : Fin L'.rank → D.host.E), IsLineVec L ζ → IsLineVec L' ζ' → ∀ l : Lnk L ζ L' ζ', l.τᴴ ⬝ (L.gram ⬝ l.τ) = (D.host.xi0 * star D.host.xi0) • L'.gram ∧ ∀ Φ₀, IsThetaFunO ψ S L' Φ₀ → ∃ Ξ, IsThetaFunO ψ L S Ξ ∧ Φ₀ = fun w => star (Ξ (l.κ S w)) := by
  intro D ψ hψ L L' S ζ ζ' hL hL' l
  have hτ := lnk_simil hL' l
  refine ⟨hτ, fun Φ₀ hΦ => ?_⟩
  have hτ' : l.τᴴ ⬝ (L.gram ⬝ l.τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram := by
    rw [Int.cast_one, one_mul]; exact hτ
  obtain ⟨hadd, -, -, -, hsym, -⟩ := GlobalTheory.LinkKappa.kappa_props D L L' S l.τ 1 hτ' (l.κ S) (fun _ => rfl)
  have hH : ∀ w w', symplOH L S (l.κ S w) (l.κ S w') = -symplOH S L' w w' := fun w w' => by
    unfold symplOH; rw [hsym]; push_cast; ring
  have hτ0 : l.τ ≠ 0 := by
    intro h0
    have e := l.map
    rw [h0, Matrix.zero_mulVec] at e
    have hz : ζ = 0 := neg_eq_zero.mp e.symm
    apply hL.2
    rw [hz]; simp
  obtain ⟨σ, hστ, hτσ⟩ := GlobalTheory.Unf.LinkGram.exists_inv_of_rank_one hL.1 hL'.1 l.τ hτ0
  let g : WO L S → WO S L' := fun x => (rat σ : Mx D L'.rank L.rank) ⬝ starAdj L S x
  have hgk : ∀ w, g (l.κ S w) = w := by
    intro w
    show (rat σ : Mx D L'.rank L.rank) ⬝ starAdj L S (l.κ S w) = w
    rw [Lnk.κ, starAdj_ofAdj, ← Matrix.mul_assoc, ← rat_mul, hστ, rat_one, Matrix.one_mul]
  have hkg : ∀ x, l.κ S (g x) = x := by
    intro x
    show l.κ S ((rat σ : Mx D L'.rank L.rank) ⬝ starAdj L S x) = x
    rw [Lnk.κ, ← Matrix.mul_assoc, ← rat_mul, hτσ, rat_one, Matrix.one_mul, GlobalTheory.Unf.LinkGram.ofAdj_starAdj]
  have gadd : ∀ x y, g (x + y) = g x + g y := fun x y => by
    conv_lhs => rw [← hkg x, ← hkg y, ← hadd, hgk]
  have gH : ∀ x y, symplOH S L' (g x) (g y) = -symplOH L S x y := fun x y => by
    conv_rhs => rw [← hkg x, ← hkg y, hH, neg_neg]
  have gcont : Continuous g := continuous_const.matrix_mul (continuous_starAdj L S)
  have grat : ∀ x ∈ ratMx D S.rank L.rank, g x ∈ ratMx D L'.rank S.rank := fun x hx =>
    ratMx_mul (rat_mem σ) (starAdj_mem L S hx)
  have gfin : ∀ x : WO L S, x.map (finPart D) = 0 → (g x).map (finPart D) = 0 := fun x h =>
    map_mul_eq_zero_right (finPart D) _
      (map_starAdj_eq_zero (finPart D) (fun z hz => by rw [GlobalTheory.LinkKappa.finPart_conj, hz, map_zero]) L S h)
  have ginf : ∀ x : WO L S, x.map (infPart D) = 0 → (g x).map (infPart D) = 0 := fun x h =>
    map_mul_eq_zero_right (infPart D) _
      (map_starAdj_eq_zero (infPart D) (fun z hz => by rw [GlobalTheory.LinkKappa.infPart_conj, hz, map_zero]) L S h)
  let A : WO L S →+ WO S L' := AddMonoidHom.mk' g gadd
  refine ⟨fun x => star (Φ₀ (g x)), ⟨fun γ x => ?_, ?_, continuous_star.comp (hΦ.cont.comp gcont), fun k M h1 h2 x => ?_⟩, ?_⟩
  · obtain ⟨γ', hγ'⟩ := grat (ratW S L γ) ⟨γ, rfl⟩
    have e : g (ratW S L γ) = ratW L' S γ' := hγ'.symm
    show star (Φ₀ (g (ratW S L γ + x))) = ψ (-(symplOH L S (ratW S L γ) x)) * star (Φ₀ (g x))
    rw [gadd, e, hΦ.quasi, star_mul', star_psi hψ, ← e, gH, neg_neg]
  · obtain ⟨U, hU, h⟩ := hΦ.level
    refine ⟨U.comap A, hU.preimage gcont, fun u hu h0 => ?_⟩
    funext x
    have e := congrFun (h _ hu (ginf u h0)) (g x)
    unfold heisO at e ⊢
    show ψ (symplOH L S x u) * star (Φ₀ (g (x + u))) = star (Φ₀ (g x))
    rw [← e, star_mul', star_psi hψ]
    show ψ (symplOH L S x u) * star (Φ₀ (g (x + u))) = ψ (-symplOH S L' (g x) (g u)) * star (Φ₀ (g x + g u))
    rw [gH, neg_neg, gadd]
  · have h3 : ∀ t, (A (M t)).map (finPart D) = 0 := fun t => gfin (M t) (h2 t)
    have := hΦ.smooth k (A.comp M) (gcont.comp h1) h3 (g x)
    have heq : (fun t => Φ₀ (g (x + M t))) = fun t => Φ₀ (g x + A (M t)) :=
      funext fun t => congrArg Φ₀ (gadd x (M t))
    have h4 := (congrArg (ContDiff ℝ _) heq).mpr this
    exact Complex.conjCLE.contDiff.comp h4
  · funext w
    show Φ₀ w = star (star (Φ₀ (g (l.κ S w))))
    rw [hgk, star_star]
end GlobalTheory.LinkInvTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixCoefficientDecayInFrameOfTranslateDecay
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameDecay

section Frob
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedRing

theorem hs_eq_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) = ‖A‖ := by
  rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact (Real.rpow_natCast _ 2).symm

theorem hsn_mul_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    GlobalTheory.SepPer.hsn (A * B) ≤ GlobalTheory.SepPer.hsn A * GlobalTheory.SepPer.hsn B := by
  unfold GlobalTheory.SepPer.hsn
  rw [hs_eq_norm, hs_eq_norm, hs_eq_norm]
  exact Matrix.frobenius_norm_mul A B

end Frob

theorem hsn_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ GlobalTheory.SepPer.hsn A := Real.sqrt_nonneg _

theorem one_le_hsn_of_mem {n : ℕ} (ε : Fin n → Bool) (i : Fin n) (y : Matrix (Fin n) (Fin n) ℂ)
    (hy : y ∈ Formalism.MainNotions.S.UJset ε) : 1 ≤ GlobalTheory.SepPer.hsn y := by
  have hy' : yᴴ * Formalism.REAL.Jm ε * y = Formalism.REAL.Jm ε := hy
  have h := congrFun (congrFun hy' i) i
  have e1 : (yᴴ * Formalism.REAL.Jm ε * y) i i = ∑ k, star (y k i) * ((if ε k then 1 else -1) * y k i) := by
    simp only [Formalism.REAL.Jm]
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
    ring
  have e2 : ‖Formalism.REAL.Jm ε i i‖ = 1 := by
    by_cases hi : ε i = true <;> simp [Formalism.REAL.Jm, hi]
  have hcol : 1 ≤ ∑ k, ‖y k i‖ ^ 2 := by
    rw [← e2, ← h, e1]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
    by_cases hk : ε k = true <;> simp [hk, norm_mul, sq]
  have hall : ∑ k, ‖y k i‖ ^ 2 ≤ ∑ a, ∑ b, ‖y a b‖ ^ 2 :=
    Finset.sum_le_sum fun a _ =>
      Finset.single_le_sum (f := fun b => ‖y a b‖ ^ 2) (fun b _ => by positivity) (Finset.mem_univ i)
  unfold GlobalTheory.SepPer.hsn
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt (hcol.trans hall)

end GlobalTheory.FrameDecay

namespace GlobalTheory.FrameDecay

theorem coef_frame_decay : ∀ (m N : ℕ), N = m + 1 → ∀ (ε : Fin N → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (π : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (v₀ : H) (g₀ F G : Matrix (Fin N) (Fin N) ℂ) (A₀ : ℝ),
  Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) π → g₀ ∈ Formalism.MainNotions.S.UJset ε → IsUnit F → Fᴴ * Formalism.REAL.Jm ε * F = G →
  (∀ g ∈ Formalism.MainNotions.S.UJset ε, ‖⟪π g₀ v₀, π g (π g₀ v₀)⟫_ℂ‖ ≤ A₀ * GlobalTheory.SepReal.hsn g ^ (-(20 * ((m : ℝ) + 1) ^ 2))) →
  ∃ C : ℝ, ∀ g ∈ Formalism.QuantumDeterminants.UH G, ‖⟪v₀, π (F * g * F⁻¹) v₀⟫_ℂ‖ * (1 + GlobalTheory.SepPer.hsn g) ^ (2 * N ^ 2 + 1) ≤ C := by
  intro m N hN ε H instH instI π v₀ g₀ F G A₀ hπ hg₀ hF hG hdec
  obtain ⟨⟨_, hmul⟩, hiso, -⟩ := hπ
  have hg₀' : g₀ᴴ * Formalism.REAL.Jm ε * g₀ = Formalism.REAL.Jm ε := hg₀
  have hJJ := Formalism.REAL.Jm_mul_self ε

  have hleft : (Formalism.REAL.Jm ε * g₀ᴴ * Formalism.REAL.Jm ε) * g₀ = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc g₀ᴴ, hg₀', hJJ]
  have hinv : g₀⁻¹ = Formalism.REAL.Jm ε * g₀ᴴ * Formalism.REAL.Jm ε := Matrix.inv_eq_left_inv hleft
  have hl : g₀⁻¹ * g₀ = 1 := by rw [hinv, hleft]
  have hr : g₀ * g₀⁻¹ = 1 := Matrix.mul_nonsing_inv g₀ (Matrix.isUnit_det_of_left_inverse hleft)
  have hmemMul : ∀ a ∈ Formalism.MainNotions.S.UJset ε, ∀ b ∈ Formalism.MainNotions.S.UJset ε, a * b ∈ Formalism.MainNotions.S.UJset ε := by
    intro a ha b hb
    have ha' : aᴴ * Formalism.REAL.Jm ε * a = Formalism.REAL.Jm ε := ha
    have hb' : bᴴ * Formalism.REAL.Jm ε * b = Formalism.REAL.Jm ε := hb
    show (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = Formalism.REAL.Jm ε
    calc (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [ha', hb']
  have hinvMem : g₀⁻¹ ∈ Formalism.MainNotions.S.UJset ε := by
    show (g₀⁻¹)ᴴ * Formalism.REAL.Jm ε * g₀⁻¹ = Formalism.REAL.Jm ε
    conv_lhs => rw [← hg₀']
    rw [show (g₀⁻¹)ᴴ * (g₀ᴴ * Formalism.REAL.Jm ε * g₀) * g₀⁻¹ = (g₀ * g₀⁻¹)ᴴ * Formalism.REAL.Jm ε * (g₀ * g₀⁻¹) by
      rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc], hr]
    simp

  have hFd : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det F).mp hF
  have hFl : F⁻¹ * F = 1 := Matrix.nonsing_inv_mul F hFd
  have hFr : F * F⁻¹ = 1 := Matrix.mul_nonsing_inv F hFd

  have hkeep : ∀ u w : H, ⟪π g₀ u, π g₀ w⟫_ℂ = ⟪u, w⟫_ℂ := by
    intro u w
    let T : H →ₗᵢ[ℂ] H := ⟨(π g₀ : H →ₗ[ℂ] H), fun v => hiso g₀ hg₀ v⟩
    exact T.inner_map_map u w
  set k : ℝ := 20 * ((m : ℝ) + 1) ^ 2 with hk
  set e : ℕ := 2 * N ^ 2 + 1 with he
  have hek : (e : ℝ) ≤ k := by
    have h1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    rw [he, hk, hN]; push_cast; nlinarith
  set c₁ : ℝ := GlobalTheory.SepPer.hsn (F⁻¹ * g₀⁻¹) * GlobalTheory.SepPer.hsn (g₀ * F) with hc₁
  have hc₁0 : 0 ≤ c₁ := mul_nonneg (hsn_nonneg _) (hsn_nonneg _)
  refine ⟨|A₀| * (1 + c₁) ^ e, fun g hg => ?_⟩
  have hg' : gᴴ * G * g = G := hg
  set x := F * g * F⁻¹ with hx
  have hxMem : x ∈ Formalism.MainNotions.S.UJset ε := by
    show xᴴ * Formalism.REAL.Jm ε * x = Formalism.REAL.Jm ε
    have : xᴴ * Formalism.REAL.Jm ε * x = (F⁻¹)ᴴ * (gᴴ * (Fᴴ * Formalism.REAL.Jm ε * F) * g) * F⁻¹ := by
      rw [hx, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [this, hG, hg', ← hG]
    have hFH : (F⁻¹)ᴴ * Fᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hFr, Matrix.conjTranspose_one]
    calc (F⁻¹)ᴴ * (Fᴴ * Formalism.REAL.Jm ε * F) * F⁻¹ = ((F⁻¹)ᴴ * Fᴴ) * Formalism.REAL.Jm ε * (F * F⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [hFH, hFr, Matrix.one_mul, Matrix.mul_one]
  set y := g₀ * x * g₀⁻¹ with hy
  have hyMem : y ∈ Formalism.MainNotions.S.UJset ε := hmemMul _ (hmemMul _ hg₀ _ hxMem) _ hinvMem

  have hco : ⟪v₀, π x v₀⟫_ℂ = ⟪π g₀ v₀, π y (π g₀ v₀)⟫_ℂ := by
    have h1 : π y (π g₀ v₀) = π g₀ (π x v₀) := by
      have h2 : y * g₀ = g₀ * x := by rw [hy, Matrix.mul_assoc, hl, Matrix.mul_one]
      rw [← ContinuousLinearMap.comp_apply, ← hmul _ hyMem _ hg₀, h2, hmul _ hg₀ _ hxMem,
        ContinuousLinearMap.comp_apply]
    rw [h1, hkeep]

  set s := GlobalTheory.SepPer.hsn y with hs
  set t := GlobalTheory.SepPer.hsn g with ht
  have hs1 : 1 ≤ s := one_le_hsn_of_mem ε ⟨0, by omega⟩ y hyMem
  have hs0 : 0 < s := by linarith
  have hts : t ≤ c₁ * s := by
    have hgeq : g = (F⁻¹ * g₀⁻¹) * y * (g₀ * F) := by
      have : (F⁻¹ * g₀⁻¹) * y * (g₀ * F) = (F⁻¹ * F) * g * (F⁻¹ * F) := by
        rw [hy, hx]; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc g₀⁻¹ g₀, hl, Matrix.one_mul,
          ← Matrix.mul_assoc g₀⁻¹ g₀, hl, Matrix.one_mul]
      rw [this, hFl, Matrix.one_mul, Matrix.mul_one]
    rw [ht, hgeq, hc₁]
    calc GlobalTheory.SepPer.hsn ((F⁻¹ * g₀⁻¹) * y * (g₀ * F))
        ≤ GlobalTheory.SepPer.hsn ((F⁻¹ * g₀⁻¹) * y) * GlobalTheory.SepPer.hsn (g₀ * F) := hsn_mul_le _ _
      _ ≤ (GlobalTheory.SepPer.hsn (F⁻¹ * g₀⁻¹) * s) * GlobalTheory.SepPer.hsn (g₀ * F) :=
          mul_le_mul_of_nonneg_right (hsn_mul_le _ _) (hsn_nonneg _)
      _ = GlobalTheory.SepPer.hsn (F⁻¹ * g₀⁻¹) * GlobalTheory.SepPer.hsn (g₀ * F) * s := by ring
  have hbd := hdec y hyMem
  have hsame : GlobalTheory.SepReal.hsn y = s := rfl
  rw [hsame, ← hco] at hbd
  have hpow : s ^ (-k) ≤ (s ^ e)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hs0.le]
    exact Real.rpow_le_rpow_of_exponent_le hs1 (by linarith)
  have hz : ‖⟪v₀, π x v₀⟫_ℂ‖ ≤ |A₀| * (s ^ e)⁻¹ :=
    hbd.trans ((mul_le_mul_of_nonneg_right (le_abs_self A₀) (Real.rpow_nonneg hs0.le _)).trans
      (mul_le_mul_of_nonneg_left hpow (abs_nonneg _)))
  have hT : (1 + t) ^ e ≤ (1 + c₁) ^ e * s ^ e := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by linarith [hsn_nonneg g]) ?_ e
    nlinarith
  have hse : 0 < s ^ e := pow_pos hs0 e
  calc ‖⟪v₀, π x v₀⟫_ℂ‖ * (1 + t) ^ e ≤ (|A₀| * (s ^ e)⁻¹) * ((1 + c₁) ^ e * s ^ e) :=
        mul_le_mul hz hT (pow_nonneg (by linarith [hsn_nonneg g]) _)
          (mul_nonneg (abs_nonneg _) (inv_nonneg.mpr hse.le))
    _ = |A₀| * (1 + c₁) ^ e := by field_simp

end GlobalTheory.FrameDecay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixCoefficientLipschitzAtRealPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.PackLoc.lipAt : ∀ (D : D7) (θ : InfFam D) (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (S S' : D.what₂.Tau → SPar) (M₀ : DSModel Y S')
  (MP : DSModel V S) (τ : D.what₂.Tau) (e : Option (Fin Y.rank) ≃ Fin V.rank) (v₀ v : MP.H τ)
  (g₀ : Matrix (Fin V.rank) (Fin V.rank) ℂ) (A : Matrix (Fin Y.rank) (Fin Y.rank) ℂ) (K lam q : ℝ) (c : ℂ),
  (∀ u, GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)) =
    ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) v⟫_ℂ) →
  (∀ X ∈ lieAt Y τ, ∀ (s : ℝ) u,
    GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * GlobalTheory.PackLoc.ptY M₀ τ u)) =
      ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • (A * X * A⁻¹)) * GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) v⟫_ℂ) →
  (∀ X ∈ lieAt Y τ, A * X * A⁻¹ ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) →
  (∀ X ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((GlobalTheory.ConjDS.conjModel M₀).ε τ)), ∀ s : ℝ,
    Integrable (fun h => ‖⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • X) * Formalism.MainNotions.S.umat h)) v⟫_ℂ -
      ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖) (Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) ∧
    ∫ h, ‖⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • X) * Formalism.MainNotions.S.umat h)) v⟫_ℂ -
      ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) ≤
        K * |s| * GlobalTheory.SepReal.hsn X) →
  (∀ F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℝ,
    (Integrable (fun u : Formalism.REAL.UJ (M₀.ε τ) => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) (Formalism.REAL.muG (M₀.ε τ)) ↔
      Integrable (fun h => F (Formalism.MainNotions.S.umat h)) (Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) ∧
    ∫ u, F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) ∂(Formalism.REAL.muG (M₀.ε τ)) =
      lam • ∫ h, F (Formalism.MainNotions.S.umat h) ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) →
  0 < lam → lam * K ≤ Real.exp q * ‖c‖ →
  ∀ X ∈ lieAt Y τ, ∀ s : ℝ,
    Integrable (fun u => ‖GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * GlobalTheory.PackLoc.ptY M₀ τ u)) -
      GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u))‖) (Formalism.REAL.muG (M₀.ε τ)) ∧
    ∫ u, ‖GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * GlobalTheory.PackLoc.ptY M₀ τ u)) -
      GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u))‖ ∂(Formalism.REAL.muG (M₀.ε τ)) ≤
      Real.exp q * ‖c‖ * |s| * hsn (A * X * A⁻¹) := by
  intro D θ Y V d S S' M₀ MP τ e v₀ v g₀ A K lam q c hB hA hL hK hH hlam hlk X hX s
  set X' := A * X * A⁻¹ with hX'
  have hX'L := hL X hX
  set F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℝ := fun x =>
    ‖⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • X') * x)) v⟫_ℂ -
      ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e x) v⟫_ℂ‖ with hF
  have hfun : (fun u => ‖GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * GlobalTheory.PackLoc.ptY M₀ τ u)) -
      GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u))‖) =
      fun u => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) := by
    funext u
    rw [hA X hX s u, hB u]
  obtain ⟨hint, hbd⟩ := hK X' hX'L s
  obtain ⟨hiff, heq⟩ := hH F
  have hsnEq : GlobalTheory.SepReal.hsn X' = hsn X' := rfl
  have hsn0 : 0 ≤ hsn X' := Real.sqrt_nonneg _
  rw [hfun]
  refine ⟨hiff.2 hint, ?_⟩
  rw [heq, smul_eq_mul]
  have h1 : lam * ∫ h, F (Formalism.MainNotions.S.umat h) ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) ≤
      lam * (K * |s| * hsn X') := by
    rw [← hsnEq]
    exact mul_le_mul_of_nonneg_left hbd hlam.le
  have h2 : lam * (K * |s| * hsn X') ≤ Real.exp q * ‖c‖ * |s| * hsn X' := by
    have hm : 0 ≤ |s| * hsn X' := mul_nonneg (abs_nonneg s) hsn0
    calc lam * (K * |s| * hsn X') = (lam * K) * (|s| * hsn X') := by ring
      _ ≤ (Real.exp q * ‖c‖) * (|s| * hsn X') := mul_le_mul_of_nonneg_right hlk hm
      _ = Real.exp q * ‖c‖ * |s| * hsn X' := by ring
  exact h1.trans h2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurableLevelIndicatorCoefficientTestFunction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepPer.CoefMeas

theorem measurable_coef : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ (v a : ∀ τ, M.H τ), Measurable (coef θ M (congLev D.sp.cm V.gram Λ 𝔪) v a) := by
  intro D θ hθ V S M Λ 𝔪 hΛ h𝔪 v a
  classical
  have h1 := GlobalTheory.SepPer.CoefCont.continuous_coefR D θ hθ V S M v a
  have hfull : Submodule.IsFullLattice D.host.E Λ := by
    haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
    refine ⟨?_⟩
    obtain ⟨s, hs⟩ := hΛ.1.fg
    apply eq_top_iff.mpr
    intro y _
    let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
      ∑ i, ∑ j, star (x i) * V.gram i j * y j
    obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
    have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
      exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
    let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
      carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
      zero_mem' := by refine ⟨0, ?_⟩; simp [f]
      add_mem' := by
        rintro x z ⟨b, hb⟩ ⟨c, hc⟩
        refine ⟨b + c, ?_⟩
        change (b : D.host.E) + c = _
        rw [hb, hc]
        simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
      smul_mem' := by
        rintro c x ⟨b, hb⟩
        refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
        simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        change star (c : D.host.E) * _ = _
        ring }
    have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
      intro x hx
      obtain ⟨b, hb⟩ := ha x hx
      exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
    have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
      apply (hΛ.2 _).2
      intro x hx
      have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
      obtain ⟨b, hb⟩ := hxP
      refine ⟨b, ?_⟩
      rw [hb]
      dsimp only [f, Pi.smul_apply]
      simp only [smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
      Submodule.subset_span hy
    have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
      (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
    change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
      ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
    rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
    exact this
  have h2 := (congLev_open_compact V hfull h𝔪).1
  unfold coef
  exact Measurable.ite h2.measurableSet h1.measurable measurable_const

end GlobalTheory.SepPer.CoefMeas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceEigenvalueIsSqrtNormStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_place_eigenvalue_is_sqrt_norm : ∀ (D : D7) (lam : ℕ →* ℂ), (∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ)) → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → IsSplit (E := D.host.E) v → ∀ m : ℕ, lam (qV D.host.E w ^ m) = (Real.sqrt ((qV D.host.E w ^ m : ℕ) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.FinZeta.SplitNorm.lam_qV_pow | exact GlobalTheory.FinZeta.SplitNorm.lam_qV_pow | (intros; apply GlobalTheory.FinZeta.SplitNorm.lam_qV_pow <;> assumption)
end

