module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0122
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointNearCuspScale
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0121
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0112

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicGLCircleCharacterTrivialOnDetOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory

theorem glChar_transvection {R : Type} [CommRing R] (h2 : IsUnit (2 : R)) {n : ℕ}
    (α : GL (Fin n) R →* Circle) (i j : Fin n) (hij : i ≠ j) (t : R)
    (u : GL (Fin n) R) (hu : u.1 = Matrix.transvection i j t) : α u = 1 := by
  obtain ⟨w, hw⟩ := h2
  let f : Fin n → R := Function.update 1 i 2
  let g : Fin n → R := Function.update 1 i (↑w⁻¹ : R)
  have hfg : ∀ k, f k * g k = 1 := by
    intro k
    by_cases hk : k = i
    · subst hk; simp [f, g, ← hw]
    · simp [f, g, hk]
  have hgf : ∀ k, g k * f k = 1 := fun k => by rw [mul_comm]; exact hfg k
  let d : GL (Fin n) R :=
    ⟨Matrix.diagonal f, Matrix.diagonal g,
      by rw [Matrix.diagonal_mul_diagonal]; simp [hfg],
      by rw [Matrix.diagonal_mul_diagonal]; simp [hgf]⟩
  have hcomm : d * u = u * u * d := by
    apply Units.ext
    have hfi : f i = 2 := by simp [f]
    have hfj : f j = 1 := by simp [f, hij.symm]
    change Matrix.diagonal f * u.1 = u.1 * u.1 * Matrix.diagonal f
    rw [hu, Matrix.transvection_mul_transvection_same _ _ hij]
    ext a b
    simp only [Matrix.transvection, Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul,
      Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply,
      Matrix.diagonal_apply, Matrix.one_apply]
    clear_value f g d
    clear hfg hgf
    split_ifs <;> subst_vars <;> simp_all <;> ring
  have h := congrArg α hcomm
  simp only [map_mul] at h
  have h' : α d * α u = α d * (α u * α u) := by rw [h]; exact mul_comm _ _ |>.trans (by rfl)
  have h'' := mul_left_cancel h'
  exact (mul_eq_left.mp h''.symm)

theorem glChar_eq_one_of_det_eq_one : ∀ (D : D7) (n : ℕ) (α : GL (Fin n) (AE D) →* Circle),
    Continuous α → ∀ a, Matrix.GeneralLinearGroup.det a = 1 → α a = 1 := by
  intro D n α _ a ha
  have h2 : IsUnit (2 : AE D) := by
    have h := (IsUnit.mk0 (2 : D.host.F) two_ne_zero).map (algebraMap D.host.F (AE D))
    rwa [map_ofNat] at h
  have := _root_.GlobalTheory.GLGen.mem_of_det_eq_one (AE D) (_root_.GlobalTheory.StableRange.adeles_stableRange_one D) n α.ker
    (fun i j hij t u hu => MonoidHom.mem_ker.mpr (glChar_transvection h2 α i j hij t u hu)) a ha
  exact MonoidHom.mem_ker.mp this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicUnitaryEveryPointHasCuspScale
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CuspGeo

open Formalism.IndefR.Eqv

theorem norm_mul_mul_apply_le {n : ℕ} (P A Q : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) (hA : ∀ k l, ‖A k l‖ ≤ c)
    (i j : Fin n) : ‖(P * A * Q) i j‖ ≤ (∑ k, ∑ l, ‖P i k‖ * ‖Q l j‖) * c := by
  simp only [Matrix.mul_apply]
  calc ‖∑ l, (∑ k, P i k * A k l) * Q l j‖ ≤ ∑ l, ∑ k, ‖P i k‖ * c * ‖Q l j‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        rw [norm_mul, ← Finset.sum_mul]
        refine mul_le_mul_of_nonneg_right ((norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)) (norm_nonneg _)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hA k l) (norm_nonneg _)
    _ = (∑ k, ∑ l, ‖P i k‖ * ‖Q l j‖) * c := by
        rw [Finset.sum_comm, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring

theorem norm_uMat_inv_apply {n : ℕ} {ε : Fin n → Bool} (y : Formalism.REAL.UJ ε) (i j : Fin n) :
    ‖uMat y⁻¹ i j‖ = ‖uMat y j i‖ := by
  have hy : (uMat y)ᴴ * Formalism.REAL.Jm ε * uMat y = Formalism.REAL.Jm ε := y.2
  have h1 : uMat y⁻¹ = Formalism.REAL.Jm ε * (uMat y)ᴴ * Formalism.REAL.Jm ε := by
    show (((y : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = _
    refine Units.inv_eq_of_mul_eq_one_left ?_
    calc Formalism.REAL.Jm ε * (uMat y)ᴴ * Formalism.REAL.Jm ε * uMat y
        = Formalism.REAL.Jm ε * ((uMat y)ᴴ * Formalism.REAL.Jm ε * uMat y) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hy, Formalism.REAL.Jm_mul_self]
  rw [h1]
  by_cases hi : ε i <;> by_cases hj : ε j <;>
    simp [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, hi, hj]

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

def frameBound (fr : UI.Frames D V) (τ : D.what₂.Tau) (i j : Fin V.rank) : ℝ :=
  ∑ k, ∑ l, ‖fr.P (Formalism.L2.Host.tauPl D τ) i k‖ * ‖(fr.P (Formalism.L2.Host.tauPl D τ))⁻¹ l j‖

theorem frameBound_nonneg (fr : UI.Frames D V) (τ : D.what₂.Tau) (i j : Fin V.rank) : 0 ≤ frameBound fr τ i j :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)

def brgFin (fr : UI.Frames D V) : (UI.instV fr).Gf →* GA D V :=
  (UI.brg fr : (UI.instV fr).GA →* GA D V).comp (MonoidHom.inr _ _)

theorem brgFin_apply (fr : UI.Frames D V) (k : (UI.instV fr).Gf) : brgFin fr k = UI.brg fr (1, k) := rfl

theorem continuous_brgFin (fr : UI.Frames D V) : Continuous (brgFin fr) :=
  (UI.brg fr).continuous.comp (continuous_const.prodMk continuous_id)

theorem brg_entry_bounds (fr : UI.Frames D V)
    (h2 : ∀ (x : (UI.instV fr).GA) (τ : D.what₂.Tau) (A : Matrix (Fin V.rank) (Fin V.rank) ℂ),
      A = uMat (x.1 (Formalism.L2.Host.tauPl D τ)) → infMat D.sp.cm.sig V.gram (θ τ) (UI.brg fr x) =
        fr.P (Formalism.L2.Host.tauPl D τ) * A * (fr.P (Formalism.L2.Host.tauPl D τ))⁻¹) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ (y : (UI.instV fr).Ginf) (c : ℝ),
      ((∀ v i j, ‖uMat (y v) i j‖ ≤ c) → normInf θ V (UI.brg fr (y, 1)) ≤ S * c) ∧
      ((∀ v i j, ‖(uMat (y v) - 1) i j‖ ≤ c) →
        ∀ τ i j, ‖(infMat D.sp.cm.sig V.gram (θ τ) (UI.brg fr (y, 1)) - 1) i j‖ ≤ S * c) := by
  have hle : ∀ τ i j, frameBound fr τ i j ≤ ∑ τ, ∑ i, ∑ j, 2 * frameBound fr τ i j := fun τ i j => by
    have h0 := frameBound_nonneg fr
    calc frameBound fr τ i j ≤ 2 * frameBound fr τ i j := by linarith [h0 τ i j]
      _ ≤ ∑ j', 2 * frameBound fr τ i j' :=
          Finset.single_le_sum (f := fun j' => 2 * frameBound fr τ i j') (fun j' _ => by linarith [h0 τ i j'])
            (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', 2 * frameBound fr τ i' j' :=
          Finset.single_le_sum (f := fun i' => ∑ j', 2 * frameBound fr τ i' j')
            (fun i' _ => Finset.sum_nonneg fun j' _ => by linarith [h0 τ i' j']) (Finset.mem_univ i)
      _ ≤ _ :=
          Finset.single_le_sum (f := fun τ' => ∑ i', ∑ j', 2 * frameBound fr τ' i' j')
            (fun τ' _ => Finset.sum_nonneg fun i' _ => Finset.sum_nonneg fun j' _ => by linarith [h0 τ' i' j'])
            (Finset.mem_univ τ)
  refine ⟨∑ τ, ∑ i, ∑ j, 2 * frameBound fr τ i j,
    Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg zero_le_two (frameBound_nonneg fr τ i j), fun y c => ⟨fun hc => ?_, fun hc τ i j => ?_⟩⟩
  · unfold normInf
    simp only [Finset.sum_mul]
    refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have e1 := norm_mul_mul_apply_le (fr.P (Formalism.L2.Host.tauPl D τ))
      (uMat (y (Formalism.L2.Host.tauPl D τ)) : Matrix (Fin V.rank) (Fin V.rank) ℂ) (fr.P (Formalism.L2.Host.tauPl D τ))⁻¹ c (fun k l => hc (Formalism.L2.Host.tauPl D τ) k l) i j
    have e2 := norm_mul_mul_apply_le (fr.P (Formalism.L2.Host.tauPl D τ))
      (uMat ((y (Formalism.L2.Host.tauPl D τ))⁻¹) : Matrix (Fin V.rank) (Fin V.rank) ℂ)
      (fr.P (Formalism.L2.Host.tauPl D τ))⁻¹ c
      (fun k l => (norm_uMat_inv_apply _ k l).trans_le (hc _ l k)) i j
    rw [← map_inv, h2 _ τ (uMat (y (Formalism.L2.Host.tauPl D τ)) : Matrix (Fin V.rank) (Fin V.rank) ℂ) rfl,
      h2 _ τ (uMat ((y (Formalism.L2.Host.tauPl D τ))⁻¹) : Matrix (Fin V.rank) (Fin V.rank) ℂ) rfl]
    unfold frameBound
    linarith
  · have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc (Formalism.L2.Host.tauPl D τ) i j)
    have hdet : IsUnit (fr.P (Formalism.L2.Host.tauPl D τ)).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 (fr.unit (Formalism.L2.Host.tauPl D τ))
    rw [h2 _ τ (uMat (y (Formalism.L2.Host.tauPl D τ)) : Matrix (Fin V.rank) (Fin V.rank) ℂ) rfl]
    have e : fr.P (Formalism.L2.Host.tauPl D τ) * (uMat (y (Formalism.L2.Host.tauPl D τ)) : Matrix (Fin V.rank) (Fin V.rank) ℂ) *
        (fr.P (Formalism.L2.Host.tauPl D τ))⁻¹ - 1 = fr.P (Formalism.L2.Host.tauPl D τ) *
        ((uMat (y (Formalism.L2.Host.tauPl D τ)) : Matrix (Fin V.rank) (Fin V.rank) ℂ) - 1) *
        (fr.P (Formalism.L2.Host.tauPl D τ))⁻¹ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_nonsing_inv _ hdet]
    rw [e]
    exact (norm_mul_mul_apply_le _ _ _ c (hc _) i j).trans (mul_le_mul_of_nonneg_right (hle τ i j) hc0)

theorem near (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ) (V : HSp D) :
    Near θ V := by
  intro U hU
  obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.BridgeDict.bridge_dict D θ hθ V (UI.framesV D V)
  obtain ⟨S, hS0, hS⟩ := brg_entry_bounds (θ := θ) (UI.framesV D V) h2
  obtain ⟨d, hd⟩ := GlobalTheory.Grow.height_le_normInf_pow (θ := θ) V hθ
  have hKp : IsOpen ((U.comap (brgFin (UI.framesV D V)) : Subgroup _) : Set (UI.instV (UI.framesV D V)).Gf) :=
    hU.preimage (continuous_brgFin _)
  obtain ⟨b, C, δ₀, K, hδ₀, hK, hx⟩ := _root_.GlobalTheory.CuspGeo.nearInst (UI.instV (UI.framesV D V)) _ hKp
  obtain ⟨Ck, hCk⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact V (hK.image (continuous_brgFin (UI.framesV D V)))
  refine ⟨b * d, max (Ck * (S * C) ^ d) (S * C), δ₀, hδ₀, fun g => ?_⟩
  set fr := UI.framesV D V with hfr
  set x := (UI.brg fr).symm g with hxdef
  have hgx : UI.brg fr x = g := (UI.brg fr).apply_symm_apply g
  obtain ⟨δ, hδ, hδ1, ⟨γ, hγ, hγK, hγb⟩, halt⟩ := hx x
  refine ⟨δ, hδ, hδ1, ?_, ?_⟩
  · have hsplit : γ * x = ((γ * x).1, 1) * (1, (γ * x).2) := Prod.ext (by simp) (by simp)
    have e : UI.brg fr γ * g = UI.brg fr ((γ * x).1, 1) * brgFin fr (γ * x).2 := by
      calc UI.brg fr γ * g = UI.brg fr (γ * x) := by rw [map_mul, hgx]
        _ = UI.brg fr (((γ * x).1, 1) * (1, (γ * x).2)) := congrArg _ hsplit
        _ = _ := map_mul _ _ _
    have hkb := hCk _ ⟨_, hγK, rfl⟩
    have hq : GlobalTheory.Grow.quotHeight V g ≤ GlobalTheory.Grow.height V (UI.brg fr ((γ * x).1, 1)) * Ck := by
      have := GlobalTheory.Grow.quotHeight_le V g ((h1 γ).2 hγ)
      rw [e] at this
      exact this.trans ((GlobalTheory.Grow.height_mul_le V _ _).trans
        (mul_le_mul_of_nonneg_left hkb (GlobalTheory.Grow.height_pos V _).le))
    have hy : ∀ v i j, ‖uMat ((γ * x).1 v) i j‖ ≤ C / δ ^ b := fun v i j =>
      (le_div_iff₀ (pow_pos hδ b)).2 (hγb v i j)
    have hN := (hS (γ * x).1 (C / δ ^ b)).1 hy
    have hN0 : 0 ≤ normInf θ V (UI.brg fr ((γ * x).1, 1)) := by unfold normInf; positivity
    have hNb : normInf θ V (UI.brg fr ((γ * x).1, 1)) * δ ^ b ≤ S * C := by
      calc _ ≤ S * (C / δ ^ b) * δ ^ b := mul_le_mul_of_nonneg_right hN (pow_pos hδ b).le
        _ = S * C := by rw [mul_assoc, div_mul_cancel₀ _ (pow_pos hδ b).ne']
    have hH := hd _ ((brg_mem_GinfC fr ((γ * x).1, 1)).2 rfl)
    have hHb : GlobalTheory.Grow.height V (UI.brg fr ((γ * x).1, 1)) * δ ^ (b * d) ≤ (S * C) ^ d := by
      rw [pow_mul]
      calc _ ≤ normInf θ V (UI.brg fr ((γ * x).1, 1)) ^ d * (δ ^ b) ^ d :=
            mul_le_mul_of_nonneg_right hH (by positivity)
        _ = (normInf θ V (UI.brg fr ((γ * x).1, 1)) * δ ^ b) ^ d := (mul_pow _ _ _).symm
        _ ≤ (S * C) ^ d := pow_le_pow_left₀ (by positivity) hNb d
    have hCk0 : 0 ≤ Ck := zero_le_one.trans ((GlobalTheory.Grow.one_le_height V _).trans hkb)
    calc GlobalTheory.Grow.quotHeight V g * δ ^ (b * d)
        ≤ GlobalTheory.Grow.height V (UI.brg fr ((γ * x).1, 1)) * Ck * δ ^ (b * d) :=
          mul_le_mul_of_nonneg_right hq (by positivity)
      _ = Ck * (GlobalTheory.Grow.height V (UI.brg fr ((γ * x).1, 1)) * δ ^ (b * d)) := by ring
      _ ≤ Ck * (S * C) ^ d := mul_le_mul_of_nonneg_left hHb hCk0
      _ ≤ _ := le_max_left _ _
  · rcases halt with h | ⟨W, hW, hWm⟩
    · exact Or.inl h
    · obtain ⟨r, C₀, hC₀, hNI⟩ := h3 W hW
      refine Or.inr ⟨r, C₀, hC₀, fun m hm => ?_⟩
      have hm' : (UI.brg fr).symm m ∈ (UI.instV fr).NA W :=
        hNI _ (by rwa [(UI.brg fr).apply_symm_apply])
      obtain ⟨γ', hγ', u, k, hk, he, hu⟩ := hWm _ hm'
      refine ⟨UI.brg fr γ', (h1 γ').2 hγ', UI.brg fr (u, 1), brgFin fr k,
        ⟨(brg_mem_GinfC fr (u, 1)).2 rfl, fun τ i j => ?_⟩, hk, (brg_mem_GfC fr (1, k)).2 rfl, ?_⟩
      · calc _ ≤ S * (C * δ) := (hS u (C * δ)).2 hu τ i j
          _ ≤ max (Ck * (S * C) ^ d) (S * C) * δ := by
            rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) hδ.le
      · calc m * g = UI.brg fr ((UI.brg fr).symm m * x) := by rw [map_mul, (UI.brg fr).apply_symm_apply, hgx]
          _ = UI.brg fr (γ' * x * ((u, 1) * (1, k))) := by
            rw [he]; exact congrArg (fun z => UI.brg fr (γ' * x * z)) (Prod.ext (by simp) (by simp))
          _ = UI.brg fr γ' * g * UI.brg fr (u, 1) * brgFin fr k := by
            rw [map_mul, map_mul, map_mul, hgx, ← mul_assoc]; rfl

end GlobalTheory.CuspGeo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupActionFourierBesselBasePoint
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB

theorem snocCols_uni_iff : ∀ (R : Type) [CommRing R] (n σ : ℕ) (M : Matrix (Fin n) (Fin σ) R) (w : Fin n → R) (Y : Matrix (Fin n) (Fin n) R), (∃ U ∈ GlobalTheory.UniIndexPrime.uniSub (σ + 1) R, Y * Matrix.of (fun k => Fin.snoc (α := fun _ => R) (M k) (w k)) = Matrix.of (fun k => Fin.snoc (α := fun _ => R) (M k) (w k)) * (U : Matrix (Fin (σ + 1)) (Fin (σ + 1)) R)) ↔ ∃ u ∈ GlobalTheory.UniIndexPrime.uniSub σ R, ∃ v : Fin σ → R, Y * M = M * (u : Matrix (Fin σ) (Fin σ) R) ∧ Y *ᵥ w = w + M *ᵥ v := GlobalTheory.T.snocColumns_moved_by_upperUnitriangular_iff

theorem fix_lineVec_emb : ∀ (D : D7) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ k : GA D S, mt S k *ᵥ ratV (o.iB *ᵥ ζ) = ratV (o.iB *ᵥ ζ) → ∃ h : GA D A, k = o.emb (h, 1) := GlobalTheory.T.exists_unitaryEmbedding_preimage_of_fixes_anisotropicLine

theorem fourierBesselBasePoint_leftInverse_rational : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), (∃ P ∈ ratMx D (σ + 1) B.V.rank, P ⬝ x0 B = 1) ∧ x0 B ∈ ratMx D B.V.rank (σ + 1) := _root_.GlobalTheory.Unf.FB.fourierBesselBasePoint_rational_with_rational_leftInverse

variable {D : D7} {σ : ℕ}

theorem ratV_mulVec_rat {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (v : Fin n → D.host.E) :
    ratV (M *ᵥ v) = rat M *ᵥ ratV v := by
  funext i; simp only [ratV, rat, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]

def actUni (B : BesLev D σ) : Subgroup (GA D B.V) where
  carrier := {g | ∃ u ∈ UX D (σ + 1), mt B.V g ⬝ x0 B = x0 B ⬝ u.1}
  one_mem' := ⟨1, one_mem _, by rw [mt_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]⟩
  mul_mem' := by
    rintro a b ⟨u, hu, ha⟩ ⟨u', hu', hb⟩
    refine ⟨u * u', mul_mem hu hu', ?_⟩
    rw [mt_mul, Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Units.val_mul, Matrix.mul_assoc]
  inv_mem' := by
    rintro a ⟨u, hu, ha⟩
    refine ⟨u⁻¹, inv_mem hu, ?_⟩
    have h1 : mt B.V a⁻¹ ⬝ (x0 B ⬝ u.1) ⬝ (u⁻¹).1 = x0 B ⬝ (u⁻¹).1 := by
      rw [← ha, ← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul]
    rw [← h1, Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem mem_actUni_iff (B : BesLev D σ) (g : GA D B.V) : g ∈ actUni B ↔ ∃ u ∈ UX D σ, ∃ v : Fin σ → AE D,
    mt B.V g ⬝ B.d.jX = B.d.jX ⬝ u.1 ∧
      mt B.V g *ᵥ (B.d.j0 *ᵥ ratV (vecB B.o B.ζ)) = B.d.j0 *ᵥ ratV (vecB B.o B.ζ) + B.d.jX *ᵥ v :=
  snocCols_uni_iff (AE D) B.V.rank σ B.d.jX _ (mt B.V g)

theorem flagN_le_actUni (B : BesLev D σ) : flagN B.d ≤ actUni B := by
  intro n hn
  obtain ⟨u, hu, b, c, rfl⟩ := ((flag_jacobi_structure D B.V B.V₀ σ B.d).1 n).1 hn
  rw [mem_actUni_iff]
  have hm : mt B.V (B.d.levi u * (B.d.nB b * B.d.nC c)) ⬝ B.d.j0 = B.d.j0 + B.d.jX ⬝ (u.1 ⬝ b) := by
    rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, B.d.nC_j0, B.d.nB_j0, Matrix.mul_add, B.d.wittDecomp_levi_inclAnisotropic,
      ← Matrix.mul_assoc, B.d.levi_jX, Matrix.mul_assoc]
  refine ⟨u, hu, (u.1 ⬝ b) *ᵥ ratV (vecB B.o B.ζ), ?_, ?_⟩
  · rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, B.d.nC_jX, B.d.nB_jX, B.d.levi_jX]
  · rw [Matrix.mulVec_mulVec, hm, Matrix.add_mulVec, Matrix.mulVec_mulVec]

theorem embA_mem_actUni (B : BesLev D σ) (h : GA D B.A) : embA B.d B.o h ∈ actUni B := by
  rw [mem_actUni_iff]
  refine ⟨1, one_mem _, 0, ?_, ?_⟩
  · rw [embA_apply, B.d.wittDecomp_anisotropicEmbedding_inclX, Units.val_one, Matrix.mul_one]
  · rw [Matrix.mulVec_zero, add_zero, Matrix.mulVec_mulVec, embA_apply, B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mulVec_mulVec,
      vecB, ratV_mulVec_rat]
    change B.d.j0 *ᵥ (mt B.V₀ (B.o.emb (h, 1)) *ᵥ (B.o.jB *ᵥ ratV B.ζ)) = B.d.j0 *ᵥ (B.o.jB *ᵥ ratV B.ζ)
    congr 1
    rw [Matrix.mulVec_mulVec, B.o.emb_jB, mt_one, Matrix.mul_one]

theorem besGrp_le_actUni (B : BesLev D σ) : besGrp B.d B.o ≤ actUni B :=
  sup_le (flagN_le_actUni B) (by rintro _ ⟨h, rfl⟩; exact embA_mem_actUni B h)

theorem mem_besGrp_of_actUni (B : BesLev D σ) (g : GA D B.V) (hg : g ∈ actUni B) : g ∈ besGrp B.d B.o := by
  obtain ⟨u, hu, v, hX, h0⟩ := (mem_actUni_iff B g).1 hg
  have hst : B.d.levi u⁻¹ * g ∈ stabX B.d := by
    show mt B.V (B.d.levi u⁻¹ * g) ⬝ B.d.jX = B.d.jX
    rw [mt_mul, Matrix.mul_assoc, hX, ← Matrix.mul_assoc, B.d.levi_jX, Matrix.mul_assoc, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.mul_one]
  obtain ⟨n, hn, k, hk⟩ := ((flag_jacobi_structure D B.V B.V₀ σ B.d).2.2.1 _).1 hst
  obtain ⟨b, c, rfl⟩ := ((flag_jacobi_structure D B.V B.V₀ σ B.d).2.1 n).1 hn
  have hp : B.d.p0 ⬝ mt B.V (B.d.levi u⁻¹ * g) ⬝ B.d.j0 = mt B.V₀ k := by
    rw [hk, mt_mul, mt_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, B.d.wittDecomp_projAnisotropic_unipotentMixed, Matrix.sub_mul, B.d.wittDecomp_projAnisotropic_unipotentSkew,
      Matrix.mul_assoc _ B.d.pY, B.d.pY_nC, Matrix.sub_mul, B.d.wittDecomp_projAnisotropic_anisotropicEmbedding, Matrix.mul_assoc _ B.d.pY, B.d.wittDecomp_projY_anisotropicEmbedding,
      Matrix.sub_mul, Matrix.mul_assoc, B.d.p0_j0, Matrix.mul_one, Matrix.mul_assoc _ B.d.pY, B.d.pY_j0,
      Matrix.mul_zero, sub_zero]
  have hz : mt B.V₀ k *ᵥ ratV (B.o.iB *ᵥ B.ζ) = ratV (B.o.iB *ᵥ B.ζ) := by
    have e1 : B.d.p0 ⬝ mt B.V (B.d.levi u⁻¹ * g) = B.d.p0 ⬝ mt B.V g := by
      rw [mt_mul, ← Matrix.mul_assoc, B.d.wittDecomp_projAnisotropic_levi]
    rw [← hp, e1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    change B.d.p0 *ᵥ (mt B.V g *ᵥ (B.d.j0 *ᵥ ratV (vecB B.o B.ζ))) = _
    rw [h0, Matrix.mulVec_add, Matrix.mulVec_mulVec, B.d.p0_j0, Matrix.one_mulVec, Matrix.mulVec_mulVec, B.d.p0_jX,
      Matrix.zero_mulVec, add_zero]
    rfl
  obtain ⟨h, rfl⟩ := fix_lineVec_emb D B.V₀ B.A B.L B.o B.ζ B.line k hz
  have hg' : g = (B.d.levi u * (B.d.nB b * B.d.nC c)) * embA B.d B.o h := by
    rw [embA_apply, mul_assoc, ← hk, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  rw [hg']
  exact mul_mem (Subgroup.mem_sup_left (((flag_jacobi_structure D B.V B.V₀ σ B.d).1 _).2 ⟨u, hu, b, c, rfl⟩))
    (Subgroup.mem_sup_right ⟨h, rfl⟩)

theorem besselGroup_action_fourierBesselBasePoint : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), (∀ g : GA D B.V, g ∈ besGrp B.d B.o ↔ ∃ u ∈ UX D (σ + 1), mt B.V g ⬝ x0 B = x0 B ⬝ u.1) ∧ (∀ a a' : Mx D (σ + 1) (σ + 1), x0 B ⬝ a = x0 B ⬝ a' → a = a') ∧ ∀ g ∈ GQ B.V, ∀ u : UX D (σ + 1), mt B.V g ⬝ x0 B = x0 B ⬝ u.1.1 → u ∈ UXQ D (σ + 1) := by
  intro D σ B
  obtain ⟨⟨P, hP, hPx⟩, hx⟩ := fourierBesselBasePoint_leftInverse_rational D σ B
  refine ⟨fun g => ⟨fun hg => besGrp_le_actUni B hg, fun hg => mem_besGrp_of_actUni B g hg⟩, ?_, ?_⟩
  · intro a a' h
    rw [← Matrix.one_mul a, ← Matrix.one_mul a', ← hPx, Matrix.mul_assoc, Matrix.mul_assoc, h]
  · intro g hg u hgu
    have hinv : mt B.V g⁻¹ ⬝ x0 B = x0 B ⬝ (u.1⁻¹).1 := by
      have h1 : mt B.V g⁻¹ ⬝ (x0 B ⬝ u.1.1) ⬝ (u.1⁻¹).1 = x0 B ⬝ (u.1⁻¹).1 := by
        rw [← hgu, ← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul]
      rw [← h1, Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    refine ⟨?_, ?_⟩
    · have e : u.1.1 = P ⬝ mt B.V g ⬝ x0 B := by
        rw [Matrix.mul_assoc, hgu, ← Matrix.mul_assoc, hPx, Matrix.one_mul]
      rw [e]; exact ratMx_mul (ratMx_mul hP ((mem_GQ_iff _ _).1 hg)) hx
    · have e : (u.1⁻¹).1 = P ⬝ mt B.V g⁻¹ ⬝ x0 B := by
        rw [Matrix.mul_assoc, hinv, ← Matrix.mul_assoc, hPx, Matrix.one_mul]
      rw [e]; exact ratMx_mul (ratMx_mul hP ((mem_GQ_iff _ _).1 (inv_mem hg))) hx

end GlobalTheory.Unf.FB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToFourierJacobiHandedFamilyContinuousAutom
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.HandFam

theorem star_psi_eq {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) :
    star (ψ a) = ψ (-a) := by
  have h1 : ‖ψ a‖ = 1 := hψ.1.2.1 a
  have h2 : ψ a * star (ψ a) = 1 := by
    rw [Complex.star_def, Complex.mul_conj', h1]; simp
  have h3 : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h0 : ψ a ≠ 0 := by intro h; rw [h, zero_mul] at h3; exact zero_ne_one h3
  exact mul_left_cancel₀ h0 (h2.trans h3.symm)

theorem handBF_isQuasiFam : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ)
    (s : StepBF ψ B J) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' → ∀ (l : Link B L' ζ')
    (φ : GA D B.A → ℂ) (Ξ : WO B.V₀ J.W₀ → ℂ), IsContAut B.A φ → IsThetaFunO ψ B.V₀ J.W₀ Ξ →
      IsQuasiFam ψ J.W₀ L' (handBF s l φ Ξ) := by
  intro D ψ ρ B J s L' ζ' hz l φ Ξ hφ hΞ
  obtain ⟨hτ, -⟩ := GlobalTheory.T.besselLineLink_gram_similitude_bijective D ρ B L' ζ' hz l
  obtain ⟨hadd, hcont, hrat, heq, hsym, -⟩ :=
    _root_.GlobalTheory.LinkKappa.kappa_props D B.L L' J.W₀ l.τ 1 hτ (l.κ J.W₀) (fun _ => rfl)
  have hF : ∀ p, IsThetaFunO ψ B.V₀ J.W₀ (s.om₀ p Ξ) := fun p => s.weil₀.om_pres p Ξ hΞ
  have hsub := GlobalTheory.T.weilRepresentation_rational_translate_substitution D ψ B.V₀ J.W₀ s.χV s.χW s.om₀ s.weil₀ Ξ hΞ
  refine ⟨?_, ?_, ?_⟩
  · intro h γ w
    have hr : (B.o.resS J.W₀).symm (0, l.κ J.W₀ (ratW L' J.W₀ γ)) ∈ ratMx D J.W₀.rank B.V₀.rank := by
      rw [B.o.resS_symm_apply, Matrix.zero_mul, zero_add]
      exact ratMx_mul (hrat _ (rat_mem γ)) (rat_mem _)
    obtain ⟨δ, hδ⟩ := hr
    have hs : symplOH B.V₀ J.W₀ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ (ratW L' J.W₀ γ)))
        ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w)) = -(symplOH J.W₀ L' (ratW L' J.W₀ γ) w) := by
      rw [B.o.symplOH_resS]
      simp only [AddEquiv.apply_symm_apply, symplOH_zero_left, zero_add]
      rw [symplOH, symplOH, hsym]
      push_cast
      ring
    have key : ∀ h₀, s.om₀ (B.o.emb (h₀, 1), h) Ξ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ (ratW L' J.W₀ γ + w))) =
        ψ (symplOH J.W₀ L' (ratW L' J.W₀ γ) w) * s.om₀ (B.o.emb (h₀, 1), h) Ξ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w)) := by
      intro h₀
      have e : ((0 : WO B.A J.W₀), l.κ J.W₀ (ratW L' J.W₀ γ + w)) =
          ((0 : WO B.A J.W₀), l.κ J.W₀ (ratW L' J.W₀ γ)) + (0, l.κ J.W₀ w) := by
        rw [hadd, Prod.mk_add_mk, add_zero]
      have hq := (hF (B.o.emb (h₀, 1), h)).quasi δ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w))
      have hδ' : rat δ = (B.o.resS J.W₀).symm (0, l.κ J.W₀ (ratW L' J.W₀ γ)) := hδ
      rw [ratW_eq, hδ', hs, neg_neg] at hq
      rw [e, map_add (f := _), hq]
    simp only [handBF, key]
    simp_rw [mul_left_comm (φ _) (ψ _)]
    rw [integral_const_mul, star_mul', star_psi_eq s.weil₀.std]
  · have jc := _root_.GlobalTheory.Unf.jointCont_all D ψ B.V₀ J.W₀ s.χV s.χW s.om₀ s.weil₀ Ξ hΞ
    have hmap : Continuous fun q : GA D B.A × (GA D J.W₀ × WO J.W₀ L') =>
        ((B.o.emb (q.1, 1), q.2.1), (B.o.resS J.W₀).symm (0, l.κ J.W₀ q.2.2)) :=
      ((B.o.continuous_emb.comp (continuous_fst.prodMk continuous_const)).prodMk
        (continuous_fst.comp continuous_snd)).prodMk
        ((B.o.continuous_resS_symm J.W₀).comp (continuous_const.prodMk (hcont.comp (continuous_snd.comp continuous_snd))))
    have hK := _root_.GlobalTheory.CocompactParam.continuous_integral_param D B.A B.cpt B.vA (GA D J.W₀ × WO J.W₀ L')
      (fun h₀ p => φ h₀ * s.om₀ (B.o.emb (h₀, 1), p.1) Ξ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ p.2)))
      ((hφ.2.comp continuous_fst).mul (jc.comp hmap)) (by
        intro γ hγ h₀ p
        have e : B.o.emb (γ * h₀, 1) = B.o.emb (γ, 1) * B.o.emb (h₀, 1) := by
          rw [← map_mul, Prod.mk_mul_mk, one_mul]
        have hq := hsub (B.o.emb (γ, 1)) (B.o.emb_mem_GQ hγ (one_mem _)) 1 (one_mem _) (B.o.emb (h₀, 1)) p.1
          ((B.o.resS J.W₀).symm (0, l.κ J.W₀ p.2))
        rw [one_mul] at hq
        rw [hφ.1 γ hγ h₀, e, hq, inv_one, mt_one, Matrix.one_mul]
        simp only [B.o.resS_symm_apply, Matrix.zero_mul, zero_add, Matrix.mul_assoc, B.o.pB_emb, mt_one,
          Matrix.one_mul])
    exact continuous_star.comp hK.2.1
  · intro γ hγ h w
    have hκ := heq γ⁻¹ w
    rw [inv_inv] at hκ
    have key : ∀ h₀, s.om₀ (B.o.emb (h₀, 1), γ * h) Ξ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w)) =
        s.om₀ (B.o.emb (h₀, 1), h) Ξ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ (w ⬝ mt J.W₀ γ))) := by
      intro h₀
      have hq := hsub 1 (one_mem _) γ hγ (B.o.emb (h₀, 1)) h ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w))
      rw [one_mul] at hq
      rw [hq, mt_one, Matrix.mul_one, hκ]
      simp only [B.o.resS_symm_apply, Matrix.zero_mul, zero_add, Matrix.mul_assoc]
    simp only [handBF, key]

end GlobalTheory.HandFam

end
end

