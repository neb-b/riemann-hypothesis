module

public import Formalism.HermitianCurvature.StatementTL
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0030
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleOfPlaces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0058
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0020
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormOfMemRootSetOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0006
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0057

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftOfXOfParts
section
namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TL Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr

noncomputable section

theorem lift_of_x_of_parts : TL.LiftXOfParts := by
  intro hZ _hC hX Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 hD Y
  obtain ⟨_, _, hAct, hQQ, _, _, _, hLS⟩ := hD
  obtain ⟨B0, _, hB⟩ := hX Wp Wq P Bs X
  obtain ⟨hFB, hEq, hRad⟩ := hB Y
  set E := xFib Bs B0 (Y + ((P.k : ℂ) - 2) / 2) with hE
  set s : ℂ := M.sgn P l0 with hs
  have hx : st.x Y = L.GGi * st.QQ Y 1 1 := by
    rw [hLS.tau, ← mul_assoc, L.GGi_GG, one_mul]
  have hx1 : (st.x Y).1 = X.fn 5 * (s • X.t Y 1 1) := by
    rw [hx, hQQ Y, hAct.2.2.2.2.2.2.2.2.2.2.2.1]
    rfl
  refine hZ Wp Wq P Bs 0 0 0 0 (fun _ => s) E (st.x Y) ?_ hFB ?_ ?_
  · refine ⟨MvPolynomial.C s, by simp, fun g => by simp⟩
  · intro p hp g hg J
    simp only [pow_zero, mul_one, smul_apply]
    rw [hEq p hp g hg J, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  · intro Φ x hx'
    simp only [pow_zero, mul_one, smul_apply]
    rw [hx1, Module.End.mul_apply, X.fn_apply 5 _ x hx', LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply,
      Pi.smul_apply, hRad Φ x hx', smul_smul, smul_smul]
    have hG : (0 : ℝ) < Q.GGl P.k P.r Bs.z Bs.z' x.2 := hx'.2.2
    simp only [Q.fnVal]
    congr 1
    have hG' : ((Q.GGl P.k P.r Bs.z Bs.z' x.2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hG.ne'
    field_simp

end

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.OmpCofLPd
section
open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.TLC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TL Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

variable {k r : ℕ}

theorem omp_adj_pd (z z' : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 1)) :
    U.IsPolyDeg r (fun g => star (adjugate (Zhat k r z z' g) a b)) := by
  have e : (fun g => star (adjugate (Zhat k r z z' g) a b)) = fun g =>
      (fun _ => ((-1 : ℂ) ^ ((b : ℕ) + (a : ℕ)))) g *
        (((Zhat k r z z' g).submatrix b.succAbove a.succAbove)ᴴ).det := by
    funext g
    rw [adjugate_fin_succ_eq_det_submatrix, star_mul', det_conjTranspose, star_pow, star_neg, star_one]
  rw [e]
  have := pd_mul (pd_const (N := 2 * r + k + 1) ((-1 : ℂ) ^ ((b : ℕ) + (a : ℕ))) 0)
    (pd_det (l := r) (fun g => ((Zhat k r z z' g).submatrix b.succAbove a.succAbove)ᴴ) fun c d => by
      simpa [conjTranspose_apply] using zhat_star_pd k r z z' _ _)
  simpa using this

theorem omp_cofL_pd {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (s : Fin (2 * r + k + 1)) :
    U.IsPolyDeg r (fun g => D.cofL Bs g s) := by
  unfold D.cofL
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact pd_sum _ fun a _ => pd_mono (show r + 0 ≤ r by omega) (pd_mul (omp_adj_pd Bs.z Bs.z' (Fin.last r) a) (pd_const _ 0))

theorem omp_inv_pd (q s : Fin (2 * r + k + 1)) :
    U.IsPolyDeg 1 (fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => (Hpk k r * gᴴ * Hpk k r) q s) := by
  simp only [Matrix.mul_apply, conjTranspose_apply]
  refine pd_sum _ fun u _ => pd_mono (show 1 + 0 ≤ 1 by omega) (pd_mul ?_ (pd_const _ 0))
  exact pd_sum _ fun t _ => pd_mono (show 0 + 1 ≤ 1 by omega) (pd_mul (pd_const _ 0) (pd_star_entry _ _))

theorem omp_poly {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (B0 : Fin k → Fin (2 * r + k + 1) → ℂ) (j : Fin k) :
    U.IsPolyDeg (r + 1) (fun g => omC Bs B0 g j) := by
  unfold omC herm
  simp only [dotProduct, mulVec]
  refine pd_sum _ fun i _ => pd_mono (show 0 + (r + 1) ≤ r + 1 by omega) (pd_mul (pd_const _ 0) ?_)
  refine pd_sum _ fun q _ => pd_mono (show 0 + (r + 1) ≤ r + 1 by omega) (pd_mul (pd_const _ 0) ?_)
  exact pd_sum _ fun s _ => pd_mono (show 1 + r ≤ r + 1 by omega) (pd_mul (omp_inv_pd q s) (omp_cofL_pd Bs s))

end Formalism.FourierDecayAlt.P.TLC
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SizeAtNonneg
section
open Finset NumberField
open scoped ComplexConjugate ComplexOrder

namespace Formalism.FourierDecayAlt.P.PBA

open Formalism.FourierDecayAlt

noncomputable section

theorem pair_prob {W : Type} {s t : Finset W} {a b : W → ℝ} (ha : TB.IsProb s a) (hb : TB.IsProb t b) :
    TB.IsProb (s ×ˢ t) (fun x => a x.1 * b x.2) := by
  refine ⟨fun x => mul_nonneg (ha.1 _) (hb.1 _), fun x hx => ?_, ?_⟩
  · rw [Finset.mem_product, not_and_or] at hx
    rcases hx with h | h
    · simp [ha.2.1 _ h]
    · simp [hb.2.1 _ h]
  · rw [Finset.sum_product]
    simp_rw [← Finset.mul_sum, hb.2.2, mul_one]
    exact ha.2.2

theorem sum_pair {W : Type} (s t : Finset W) (a b f g : W → ℝ) (hb : ∑ y ∈ t, b y = 1)
    (ha : ∑ x ∈ s, a x = 1) :
    ∑ x ∈ s ×ˢ t, a x.1 * b x.2 * ((f x.1 + g x.2) / 2) =
      ((∑ x ∈ s, a x * f x) + ∑ y ∈ t, b y * g y) / 2 := by
  have key : ∀ x, ∑ y ∈ t, a x * b y * ((f x + g y) / 2) =
      (a x * f x + a x * ∑ y ∈ t, b y * g y) / 2 := by
    intro x
    have split : ∀ y, a x * b y * ((f x + g y) / 2) =
        (a x * f x / 2) * b y + (a x / 2) * (b y * g y) := by
      intro y; ring
    simp_rw [split, Finset.sum_add_distrib, ← Finset.mul_sum, hb]
    ring
  rw [Finset.sum_product]
  simp_rw [key]
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul, ha]
  ring

theorem mix_sum {X W : Type} (Y : Finset X) (Ws : Finset W) (κ : X → X → ℂ) (c : ℂ) (p : W → ℂ)
    (G : W → X → X → ℂ) :
    ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * (c * ∑ w ∈ Ws, p w * G w h h') =
      c * ∑ w ∈ Ws, p w * ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * G w h h' := by
  simp_rw [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun h' _ => ?_
  ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)

theorem av_eq (v : Fin S.f) (x : E) : S.base.av v x = ‖S.σ v x‖ := by
  show (S.pl v) x = ‖S.emb v x‖
  rw [← S.hemb v]
  rfl

theorem loc_join (σ : E →+* ℂ) (h : TB.Pt E) (s : ℕ) (t : E) :
    C.loc σ (TB.join h s t) = C.loc σ h ++ [(s, σ t)] := by
  simp only [C.loc, TB.join, List.map_append, List.map_cons, List.map_nil]

theorem ptSize_loc (σ : E →+* ℂ) (h : TB.Pt E) : D.ptSize (C.loc σ h) = TB.level h := by
  simp only [D.ptSize, C.loc, TB.level, List.map_map]
  rfl

theorem sizeAt_nonneg (v : Fin S.f) (a : List C.Letter) : 0 ≤ S.sizeAt v a := by
  unfold C.HidaSetting.sizeAt
  apply List.prod_nonneg
  intro x hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
  exact abs_nonneg _

theorem gN_psd (hpos : C.ThmPPos S) (v : Fin S.f) {ε : ℝ} (hε : 0 < ε) {i : ℕ} (hi : i ≤ S.G.r + 1) (w0 : S.W)
    (Y : Finset C.LPt) : TB.PSDOn Y (KB.gN S v ε i (w0.1 v)) := by
  have h := hpos v ε hε i hi w0 Y
  unfold TB.PSDOn at h ⊢
  have heq : (Matrix.of fun x y : Y => KB.gN S v ε i (w0.1 v) x y) =
      (((S.sizeAt v (w0.1 v))⁻¹ : ℝ) : ℂ) • Matrix.of fun x y : Y => S.gramLoc v ε i (w0.1 v) x y := by
    ext x y
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, KB.gN, div_eq_inv_mul,
      Complex.ofReal_inv]
  rw [heq]
  exact h.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr (sizeAt_nonneg S v _)))

theorem Nst_eq {ε : ℝ} {i : ℕ} (hi : i ≤ S.G.r + 1) (s : ℕ) (w : S.W) (Y : Finset (TB.Pt E))
    (κ : TB.Pt E → TB.Pt E → ℂ) (t t' : E) :
    S.base.Nst ε i s w Y κ t t' = ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, KB.gN S v ε i (w.1 v)
      (C.loc (S.σ v) h ++ [(s, S.σ v t)]) (C.loc (S.σ v) h' ++ [(s, S.σ v t')]) := by
  have hsz : ((C.Word.size S.P w.1 : ℝ) : ℂ) = ∏ v, ((S.sizeAt v (w.1 v) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_prod]
    rfl
  show (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * S.gram ε i w.1 (TB.join h s t) (TB.join h' s t')) /
      ((C.Word.size S.P w.1 : ℝ) : ℂ) = _
  simp only [C.HidaSetting.gram, if_pos hi, loc_join, KB.gN, Finset.prod_div_distrib, hsz,
    Finset.sum_div, mul_div_assoc]

end

end Formalism.FourierDecayAlt.P.PBA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TendstoSmulCocompact
section
namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section main

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def mainD (s : ℕ) (β ε : ℂ) (bt : ℂ → H) (x D : ℂ) : H :=
  ∑ z ∈ G.rootSet s (ε * D), G.psi β ((s : ℂ) * z * x) • bt z

def bz (s : ℕ) (bt : ℂ → H) (z : ℂ) : H := (((s : ℝ) * ‖z‖ ^ (s - 1) : ℝ) : ℂ) • bt z

def pairD (s : ℕ) (β ε : ℂ) (bt bt' : ℂ → H) (x x' ρ : ℂ) : ℂ :=
  ∫ D, ⟪mainD s β ε bt x D, ((‖ρ‖ ^ s : ℝ) : ℂ) • mainD s β ε bt' x' (ρ ^ s * D)⟫_ℂ

theorem psi_conj_mul (β a b : ℂ) : conj (G.psi β a) * G.psi β b = G.psi β (b - a) := by
  unfold G.psi
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, mul_sub, Complex.sub_re]
  push_cast
  ring

def termZ (s : ℕ) (β : ℂ) (bt bt' : ℂ → H) (x x' ρ ζ z : ℂ) : ℂ :=
  G.psi β ((s : ℂ) * (ζ * ρ * x' - x) * z) • ⟪bz s bt z, ((‖ρ‖ : ℝ) : ℂ) • bz s bt' (ζ * ρ * z)⟫_ℂ

theorem integrable_termZ {s : ℕ} (_hs : s ≠ 0) (β : ℂ) {bt bt' : ℂ → H} (hb : MemLp (bz s bt) 2 volume)
    (hb' : MemLp (bz s bt') 2 volume) (x x' ρ ζ : ℂ) (hρ : ρ ≠ 0) (hζ : ζ ≠ 0) :
    Integrable (termZ s β bt bt' x x' ρ ζ) := by
  have hd : MemLp (fun z => ((‖ρ‖ : ℝ) : ℂ) • bz s bt' (ζ * ρ * z)) 2 volume :=
    (memLp_comp_mul hb' (ζ * ρ) (mul_ne_zero hζ hρ)).const_smul _
  have hi := integrable_inner_of_memLp hb hd
  refine hi.bdd_smul 1 ?_ (Eventually.of_forall fun z => (norm_psi β _).le)
  exact ((continuous_psi β).comp (continuous_const.mul continuous_id)).aestronglyMeasurable

theorem pairD_eq {s : ℕ} (hs : s ≠ 0) (β : ℂ) {ε : ℂ} (hε : ‖ε‖ = 1) {bt bt' : ℂ → H}
    (hb : MemLp (bz s bt) 2 volume) (hb' : MemLp (bz s bt') 2 volume) (x x' ρ : ℂ) (hρ : ρ ≠ 0) :
    pairD s β ε bt bt' x x' ρ = ∑ ζ ∈ G.rootSet s 1, ∫ z, termZ s β bt bt' x x' ρ ζ z := by
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
  have hζ0 : ∀ ζ ∈ G.rootSet s 1, ζ ≠ 0 := fun ζ hζ h0 => by
    have := norm_of_mem_rootSet_one hs hζ; rw [h0, norm_zero] at this; exact zero_ne_one this

  set Φ : ℂ → ℂ := fun z => ∑ ζ ∈ G.rootSet s 1,
    (conj (G.psi β ((s : ℂ) * z * x)) * G.psi β ((s : ℂ) * (ζ * ρ * z) * x')) *
      (((‖ρ‖ ^ s : ℝ) : ℂ) * ⟪bt z, bt' (ζ * ρ * z)⟫_ℂ) with hΦ
  have hjac : ∀ z : ℂ, ‖ε⁻¹ * ((s : ℂ) * z ^ (s - 1))‖ ^ 2 • Φ z =
      ∑ ζ ∈ G.rootSet s 1, termZ s β bt bt' x x' ρ ζ z := by
    intro z
    rw [hΦ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun ζ hζ => ?_
    have hζn := norm_of_mem_rootSet_one hs hζ
    have hn : ‖ζ * ρ * z‖ = ‖ρ‖ * ‖z‖ := by rw [norm_mul, norm_mul, hζn, one_mul]
    have hj : ‖ε⁻¹ * ((s : ℂ) * z ^ (s - 1))‖ ^ 2 = ((s : ℝ) * ‖z‖ ^ (s - 1)) ^ 2 := by
      rw [norm_mul, norm_inv, hε, inv_one, one_mul, norm_mul, norm_pow, Complex.norm_natCast]
    have hps : conj (G.psi β ((s : ℂ) * z * x)) * G.psi β ((s : ℂ) * (ζ * ρ * z) * x') =
        G.psi β ((s : ℂ) * (ζ * ρ * x' - x) * z) := by
      rw [psi_conj_mul]; congr 1; ring
    have hρs : ‖ρ‖ ^ s = ‖ρ‖ * ‖ρ‖ ^ (s - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hj, hps]
    simp only [termZ, bz, inner_smul_left, inner_smul_right, Complex.conj_ofReal, smul_eq_mul, hn, hρs, mul_pow,
      Complex.real_smul]
    push_cast
    ring
  have hint : Integrable (fun z => ‖ε⁻¹ * ((s : ℂ) * z ^ (s - 1))‖ ^ 2 • Φ z) := by
    simp_rw [hjac]
    exact integrable_finsetSum _ fun ζ hζ => integrable_termZ hs β hb hb' x x' ρ ζ hρ (hζ0 ζ hζ)
  obtain ⟨-, hch⟩ := integral_sum_rootSet s hs ε hε0 Φ hint

  have hD : ∀ D : ℂ, D ≠ 0 → ⟪mainD s β ε bt x D, ((‖ρ‖ ^ s : ℝ) : ℂ) • mainD s β ε bt' x' (ρ ^ s * D)⟫_ℂ =
      ∑ z ∈ G.rootSet s (ε * D), Φ z := by
    intro D hD0
    rw [inner_smul_right, mainD, sum_inner, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z hz => ?_
    have hzs : z ^ s = ε * D := (mem_rootSet' hs).1 hz
    have hw : ε * D ≠ 0 := mul_ne_zero hε0 hD0
    have hrD : ε * (ρ ^ s * D) = ρ ^ s * (ε * D) := by ring
    rw [mainD, hrD, sum_rootSet_mul hs hw hzs rfl (pow_ne_zero _ hρ), inner_sum, Finset.mul_sum, hΦ]
    refine Finset.sum_congr rfl fun ζ _ => ?_
    rw [inner_smul_left, inner_smul_right]
    ring
  have hDae : (fun D => ⟪mainD s β ε bt x D, ((‖ρ‖ ^ s : ℝ) : ℂ) • mainD s β ε bt' x' (ρ ^ s * D)⟫_ℂ) =ᵐ[volume]
      fun D => ∑ z ∈ G.rootSet s (ε * D), Φ z := by
    filter_upwards [Measure.ae_ne volume (0 : ℂ)] with D hD0
    exact hD D hD0
  rw [pairD, integral_congr_ae hDae, hch]
  simp_rw [hjac]
  exact integral_finsetSum _ fun ζ hζ => integrable_termZ hs β hb hb' x x' ρ ζ hρ (hζ0 ζ hζ)

theorem tendsto_smul_cocompact {α : Type} {l : Filter α} (c : ℂ) (hc : c ≠ 0) (y : α → ℂ)
    (hy : Tendsto y l (cocompact ℂ)) : Tendsto (fun a => c * y a) l (cocompact ℂ) := by
  rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded] at hy ⊢
  simp only [norm_mul]
  exact hy.const_mul_atTop (norm_pos_iff.mpr hc)

theorem tendsto_pairD {s : ℕ} (hs : s ≠ 0) {β : ℂ} (hβ : β ≠ 0) {ε : ℂ} (hε : ‖ε‖ = 1) {bt bt' : ℂ → H}
    (hb : MemLp (bz s bt) 2 volume) (hb' : MemLp (bz s bt') 2 volume) {α : Type} {l : Filter α}
    (x x' ρ : α → ℂ) (σ : ℂ) (hρ0 : ∀ᶠ a in l, ρ a ≠ 0) (hρ : Tendsto ρ l (𝓝 1))
    (hsh : Tendsto (fun a => (s : ℂ) * (ρ a * x' a - x a)) l (𝓝 σ))
    (hne : ∀ ζ ∈ G.rootSet s 1, ζ ≠ 1 → Tendsto (fun a => ζ * ρ a * x' a - x a) l (cocompact ℂ)) :
    Tendsto (fun a => pairD s β ε bt bt' (x a) (x' a) (ρ a)) l
      (𝓝 (∫ z, G.psi β (σ * z) • ⟪bz s bt z, bz s bt' z⟫_ℂ)) := by
  set L : ℂ := ∫ z, G.psi β (σ * z) • ⟪bz s bt z, bz s bt' z⟫_ℂ with hL
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hlim : ∀ ζ ∈ G.rootSet s 1, Tendsto (fun a => ∫ z, termZ s β bt bt' (x a) (x' a) (ρ a) ζ z) l
      (𝓝 (if ζ = 1 then L else 0)) := by
    intro ζ hζ
    have hζn := norm_of_mem_rootSet_one hs hζ
    have hζ0 : ζ ≠ 0 := fun h0 => by rw [h0, norm_zero] at hζn; exact zero_ne_one hζn
    have hf0 : Integrable (fun z => ⟪bz s bt z, bz s bt' (ζ * z)⟫_ℂ) :=
      integrable_inner_of_memLp hb (memLp_comp_mul hb' ζ hζ0)
    have hfi : ∀ᶠ a in l, Integrable (fun z => ⟪bz s bt z, ((‖ρ a‖ : ℝ) : ℂ) • bz s bt' (ζ * ρ a * z)⟫_ℂ) := by
      filter_upwards [hρ0] with a ha
      exact integrable_inner_of_memLp hb ((memLp_comp_mul hb' (ζ * ρ a) (mul_ne_zero hζ0 ha)).const_smul _)
    have hL1 : Tendsto (fun a => ∫ z, ‖⟪bz s bt z, ((‖ρ a‖ : ℝ) : ℂ) • bz s bt' (ζ * ρ a * z)⟫_ℂ -
        ⟪bz s bt z, bz s bt' (ζ * z)⟫_ℂ‖) l (𝓝 0) := by
      have hζρ : Tendsto (fun a => ζ * ρ a) l (𝓝 ζ) := by
        simpa using (tendsto_const_nhds (x := ζ)).mul hρ
      have h1 := (tendsto_inner_dil (bz s bt) (bz s bt') hb hb' ζ hζ0).comp hζρ
      refine h1.congr fun a => ?_
      simp only [Function.comp_apply, norm_mul, hζn, one_mul, Complex.ofReal_one, one_smul]
    by_cases h1 : ζ = 1
    · subst h1
      rw [if_pos rfl]
      have hw : Tendsto (fun a => (s : ℂ) * (1 * ρ a * x' a - x a)) l (𝓝 σ) := by simpa using hsh
      have := tendsto_integral_psi_conv β _ _ hf0 hfi hL1 _ σ hw
      simpa [termZ, hL] using this
    · rw [if_neg h1]
      have hw := tendsto_smul_cocompact (s : ℂ) hs0 _ (hne ζ hζ h1)
      have := tendsto_integral_psi_moving β hβ _ _ hf0 hfi hL1 _ hw
      simpa [termZ, mul_assoc] using this
  have hsum := tendsto_finsetSum (G.rootSet s 1) hlim
  rw [Finset.sum_ite_eq' (G.rootSet s 1) 1 (fun _ => L), if_pos (one_mem_rootSet_one hs)] at hsum
  refine hsum.congr' ?_
  filter_upwards [hρ0] with a ha
  exact (pairD_eq hs β hε hb hb' (x a) (x' a) (ρ a) ha).symm

end main

end

end Formalism.FourierDecayAlt.P.PBK
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_GCore_GenTransferKapCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section preds

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def KapPt (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (Qr : M.Ty P → (Wq →L[ℂ] Wq)) : Prop :=
  (∀ ρ σ, (Qr ρ).comp (Qr σ) = if ρ = σ then Qr ρ else 0) ∧ (∑ ρ, Qr ρ = 1) ∧
  (∀ ρ (v w : Wq), inner ℂ (Qr ρ v) w = inner ℂ v (Qr ρ w)) ∧
  ∀ (f : M.Ty P → ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : MA.Qp P.r P.TT),
    (((d.κ f).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1
        (NF.muZ P.k P.r Bs.μsec q.1.2) =
      ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2)).comp (∑ ρ, f ρ • Qr ρ)

end preds

def GTKPt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∃ Qr : M.Ty P → (Wq →L[ℂ] Wq), KapPt P Bs d Qr

def GTKLine : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ Qr : M.Ty P → (Wq →L[ℂ] Wq), KapPt P Bs d Qr →
    ∀ ζ : ℂ, P.TT < Complex.normSq ζ → ∀ ρ : M.Ty P,
      ∃ E ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ, E.comp (Qr ρ) = E ∧
        inner ℂ (B.hsVec E) (B.hsVec E) = (1 : ℂ) ∧
        ∀ Z ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ, Z.comp (Qr ρ) = Z →
          Z = inner ℂ (B.hsVec E) (B.hsVec Z) • E

def GTKapOfCut : Prop := GTKPt → GTKLine → GTKap

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

