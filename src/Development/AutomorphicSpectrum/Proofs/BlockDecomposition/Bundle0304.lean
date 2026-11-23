module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyIsotropicSubspaces
section
open NumberField Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
open GlobalTheory.CuspRep PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.IsotropicDegreeBound

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem conjE_conjE (a : E) : conjE E (conjE E a) = a :=
  IsCMField.complexConj_apply_apply E a

theorem mem_perpD_iff (d : GL (Fin n) E) (W : Submodule E (Fin n → E)) (y : Fin n → E) :
    y ∈ perpD (conjE E) d W ↔ ∀ x ∈ W, (conjE E ∘ x) ⬝ᵥ ((d⁻¹).val *ᵥ y) = 0 := by
  have key : y ∈ perpD (conjE E) d W ↔ (d⁻¹).val *ᵥ y ∈ perp (conjE E) W := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      have : (d⁻¹).val *ᵥ (Matrix.toLin' d.val z) = z := by
        rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec]
      rw [this]
      exact hz
    · intro h
      refine ⟨_, h, ?_⟩
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
  rw [key]
  exact Iff.rfl

theorem gram_nrm (d : GL (Fin n) E) :
    ((nrm d).val.map (conjE E))ᵀ * (d⁻¹).val * (nrm d).val = (d⁻¹).val := by
  set D := d.val with hD
  set Di := (d⁻¹).val with hDi
  have hval : (nrm d).val = D * (Di.map (conjE E))ᵀ := by
    simp only [nrm, Units.val_mul]
    rfl
  have hinv : Di * D = 1 := by
    rw [hDi, hD, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hc : (Di.map (conjE E)) * (D.map (conjE E)) = 1 := by
    rw [← Matrix.map_mul, hinv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hcc : (Di.map (conjE E)).map (conjE E) = Di := by
    ext i j
    simp [conjE_conjE]
  have hm : ((nrm d).val.map (conjE E))ᵀ = Di * (D.map (conjE E))ᵀ := by
    rw [hval, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_map, Matrix.transpose_transpose, hcc]
  rw [hm, hval]
  calc Di * (D.map (conjE E))ᵀ * Di * (D * (Di.map (conjE E))ᵀ)
      = Di * (D.map (conjE E))ᵀ * (Di * D) * (Di.map (conjE E))ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = Di * ((Di.map (conjE E)) * (D.map (conjE E)))ᵀ := by
        rw [hinv, Matrix.transpose_mul, Matrix.mul_one, Matrix.mul_assoc]
    _ = Di := by rw [hc, Matrix.transpose_one, Matrix.mul_one]

theorem pairing_nrm (d : GL (Fin n) E) (u v : Fin n → E) :
    (conjE E ∘ ((nrm d).val *ᵥ u)) ⬝ᵥ ((d⁻¹).val *ᵥ ((nrm d).val *ᵥ v)) =
      (conjE E ∘ u) ⬝ᵥ ((d⁻¹).val *ᵥ v) := by
  have h1 : conjE E ∘ ((nrm d).val *ᵥ u) = ((nrm d).val.map (conjE E)) *ᵥ (conjE E ∘ u) := by
    funext i
    exact RingHom.map_mulVec (conjE E) (nrm d).val u i
  rw [h1, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    gram_nrm]

theorem img_nrm_inf (d : GL (Fin n) E) (W : Submodule E (Fin n → E)) (hW : img (nrm d) W = W) :
    img (nrm d) (W ⊓ perpD (conjE E) d W) = W ⊓ perpD (conjE E) d W := by
  have hinj : Function.Injective (Matrix.toLin' (nrm d).val) := by
    intro a b hab
    have h := congrArg (fun z => ((nrm d)⁻¹).val *ᵥ z) hab
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul] using h
  have hle : img (nrm d) (W ⊓ perpD (conjE E) d W) ≤ W ⊓ perpD (conjE E) d W := by
    rintro _ ⟨y, ⟨hyW, hyP⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · have : Matrix.toLin' (nrm d).val y ∈ img (nrm d) W := ⟨y, hyW, rfl⟩
      rwa [hW] at this
    · rw [SetLike.mem_coe, mem_perpD_iff]
      intro x hx
      rw [← hW] at hx
      obtain ⟨x', hx', rfl⟩ := hx
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, pairing_nrm]
      exact (mem_perpD_iff d W y).1 hyP x' hx'
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm

theorem inf_le_perpD_inf (d : GL (Fin n) E) (W : Submodule E (Fin n → E)) :
    W ⊓ perpD (conjE E) d W ≤ perpD (conjE E) d (W ⊓ perpD (conjE E) d W) := by
  intro y hy
  rw [mem_perpD_iff]
  exact fun x hx => (mem_perpD_iff d W y).1 hy.2 x hx.1

theorem prof_gap {τ : ℝ} (hτ : 0 ≤ τ) {a b m : ℕ} (hab : a < b) (hbm : b ≤ m) :
    prof m τ a + 2 * τ ≤ prof m τ b := by
  have h1 : (a : ℝ) + 1 ≤ b := by exact_mod_cast hab
  have h2 : (b : ℝ) ≤ m := by exact_mod_cast hbm
  have h3 : (2 : ℝ) ≤ ((b : ℝ) - a) * (2 * m + 1 - a - b) := by
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (by linarith : (0 : ℝ) ≤ 2 * m - 1 - a - b)]
  have h4 := mul_nonneg hτ (sub_nonneg.2 h3)
  simp only [prof]
  nlinarith

theorem onlyIsotropic_of : OnlyStable → DegPairing → SizeBasic → OnlyIsotropic := by
  intro h1 h2 h3 E _ _ _ n
  obtain ⟨C₁, hC₁⟩ := h1 E n
  obtain ⟨C₂, hC₂⟩ := h2 E n
  refine ⟨max 0 (max C₁ C₂), fun τ x d hτ => ?_⟩
  have hs0 : 0 ≤ logSize (twConj (thetaA E n) x (ratGL E n d)) := (h3 E n).2.1 _
  have hs1 : 0 ≤ 1 + logSize (twConj (thetaA E n) x (ratGL E n d)) := by linarith
  have l₁ : C₁ ≤ max 0 (max C₁ C₂) := (le_max_left _ _).trans (le_max_right _ _)
  have l₂ : C₂ ≤ max 0 (max C₁ C₂) := (le_max_right _ _).trans (le_max_right _ _)
  have hτ₁ := le_trans (mul_le_mul_of_nonneg_right l₁ hs1) hτ
  have hτ₂ := le_trans (mul_le_mul_of_nonneg_right l₂ hs1) hτ
  have hτ₀ : 0 ≤ τ := le_trans (mul_nonneg (le_max_left _ _) hs1) hτ
  refine ⟨fun hx W _ _ => hx.1 W, fun h => (hC₁ τ x d hτ₁).2 fun W hW => ?_⟩
  have hb := h _ (img_nrm_inf d W hW) (inf_le_perpD_inf d W)
  by_cases heq : W ⊓ perpD (conjE E) d W = W
  · exact h W hW (inf_eq_left.1 heq)
  · have hlt : W ⊓ perpD (conjE E) d W < W := lt_of_le_of_ne inf_le_left heq
    have hr := Submodule.finrank_lt_finrank_of_lt hlt
    have hn : Module.finrank E W ≤ n := by simpa using Submodule.finrank_le W
    have hg := prof_gap hτ₀ hr hn
    have hp := (hC₂ x d).1 W hW
    linarith

end GlobalTheory.CompanionTheory.IsotropicDegreeBound
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyStableSubspaces
section
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.OnlyStab

section Core

variable {K : Type} [Field K] {n : ℕ}

theorem prof_nonneg {τ : ℝ} (hτ : 0 ≤ τ) {k : ℕ} (hk : k ≤ n) : 0 ≤ prof n τ k := by
  have h : (k : ℝ) ≤ n := by exact_mod_cast hk
  have h0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  unfold prof
  exact mul_nonneg (mul_nonneg hτ h0) (by linarith)

theorem finrank_le_n (W : Submodule K (Fin n → K)) : Module.finrank K W ≤ n := by
  simpa using Submodule.finrank_le W

theorem prof_second_diff (τ : ℝ) (a b k : ℕ) (hab : a + b = 2 * k) :
    prof n τ a + prof n τ b = 2 * prof n τ k - 2 * τ * ((k : ℝ) - a) ^ 2 := by
  have h : (b : ℝ) = 2 * k - a := by
    have : ((a + b : ℕ) : ℝ) = ((2 * k : ℕ) : ℝ) := by rw [hab]
    push_cast at this
    linarith
  unfold prof
  rw [h]
  ring

theorem core (deg' : Submodule K (Fin n → K) → ℝ) (g : Submodule K (Fin n → K) → Submodule K (Fin n → K))
    (τ D : ℝ) (hτ : 0 < τ) (hD : D < 2 * τ) (hbdd : BddAbove (Set.range deg'))
    (hsub : ∀ W W', deg' W + deg' W' ≤ deg' (W ⊓ W') + deg' (W ⊔ W'))
    (hmove : ∀ W, deg' W - D ≤ deg' (g W))
    (hrank : ∀ W, Module.finrank K (g W) = Module.finrank K W)
    (hst : ∀ W, g W = W → deg' W ≤ prof n τ (Module.finrank K W)) (W₀ : Submodule K (Fin n → K)) :
    deg' W₀ ≤ prof n τ (Module.finrank K W₀) := by
  by_contra hW₀
  push Not at hW₀
  set ψ : Submodule K (Fin n → K) → ℝ := fun W => deg' W - prof n τ (Module.finrank K W) with hψ
  have hψb : BddAbove (Set.range ψ) := by
    obtain ⟨B, hB⟩ := hbdd
    refine ⟨B, ?_⟩
    rintro _ ⟨W, rfl⟩
    have h1 : deg' W ≤ B := hB ⟨W, rfl⟩
    have h2 := prof_nonneg (n := n) hτ.le (finrank_le_n W)
    simp only [hψ]
    linarith
  set s : ℝ := ⨆ W, ψ W with hs
  have hle : ∀ W, ψ W ≤ s := fun W => le_ciSup hψb W
  have hs0 : 0 < s := lt_of_lt_of_le (by simp only [hψ]; linarith) (hle W₀)
  have hε : 0 < min s (τ - D / 2) := lt_min hs0 (by linarith)
  obtain ⟨W, hW⟩ : ∃ W, s - min s (τ - D / 2) < ψ W :=
    exists_lt_of_lt_ciSup (by rw [hs]; linarith [hε])
  have hε1 : min s (τ - D / 2) ≤ s := min_le_left _ _
  have hε2 : min s (τ - D / 2) ≤ τ - D / 2 := min_le_right _ _
  by_cases hg : g W = W
  · have h := hst W hg
    simp only [hψ] at hW
    linarith
  · have hsum := Submodule.finrank_sup_add_finrank_inf_eq W (g W)
    rw [hrank W] at hsum
    have hne : W ⊓ g W ≠ W := fun h => hg
      (Submodule.eq_of_le_of_finrank_le (inf_eq_left.1 h) (by rw [hrank W])).symm
    have hlt : Module.finrank K (W ⊓ g W : Submodule K (Fin n → K)) < Module.finrank K W :=
      Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left hne)
    have hid := prof_second_diff (n := n) τ (Module.finrank K (W ⊓ g W : Submodule K (Fin n → K)))
      (Module.finrank K (W ⊔ g W : Submodule K (Fin n → K))) (Module.finrank K W) (by omega)
    have hj : (1 : ℝ) ≤ (Module.finrank K W : ℝ) - Module.finrank K (W ⊓ g W : Submodule K (Fin n → K)) := by
      have : ((Module.finrank K (W ⊓ g W : Submodule K (Fin n → K)) + 1 : ℕ) : ℝ) ≤ Module.finrank K W := by
        exact_mod_cast hlt
      push_cast at this
      linarith
    have hj2 : τ * 1 ≤ τ * ((Module.finrank K W : ℝ) - Module.finrank K (W ⊓ g W : Submodule K (Fin n → K))) ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith) hτ.le
    have h1 := hle (W ⊓ g W)
    have h2 := hle (W ⊔ g W)
    have h3 := hsub W (g W)
    have h4 := hmove W
    simp only [hψ] at h1 h2 hW
    linarith

end Core

section Global

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem finrank_img (g : GL (Fin n) E) (W : Submodule E (Fin n → E)) :
    Module.finrank E (img g W) = Module.finrank E W := by
  have hinj : Function.Injective (Matrix.toLin' g.val) := by
    intro a b hab
    have h : (g⁻¹ : GL (Fin n) E).val *ᵥ (g.val *ᵥ a) = (g⁻¹ : GL (Fin n) E).val *ᵥ (g.val *ᵥ b) := by
      simpa [Matrix.toLin'_apply] using congrArg (fun y => (g⁻¹ : GL (Fin n) E).val *ᵥ y) hab
    simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using h
  exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj W).symm

theorem conjSrc_invol (v : HeightOneSpectrum (𝓞 E)) :
    conjSrc (IsCMField.complexConj E).toRingEquiv (conjSrc (IsCMField.complexConj E).toRingEquiv v) = v :=
  (eq_conjSrc fun x => by
    rw [← conjPl_conjSrc (IsCMField.complexConj E).toRingEquiv v ((IsCMField.complexConj E).toRingEquiv x)]
    exact congrArg _ (IsCMField.complexConj_apply_apply E x)).symm

theorem conjFin_invol (x : Af E) :
    conjFin (IsCMField.complexConj E).toRingEquiv (conjFin (IsCMField.complexConj E).toRingEquiv x) = x := by
  have key : ∀ (v w : HeightOneSpectrum (𝓞 E)) (_ : w = v) (f : w.adicCompletion E → v.adicCompletion E),
      Continuous f → (∀ k : E, f (algebraMap E _ k) = algebraMap E _ k) → f (pLoc E w x) = pLoc E v x := by
    rintro _ v rfl f hf h
    exact congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf continuous_id (funext h)) _
  refine FiniteAdeleRing.ext _ fun v => key v _ (conjSrc_invol v) (conjLoc _ v ∘ conjLoc _ _)
    ((conjLoc_spec _ _).1.comp (conjLoc_spec _ _).1) fun k => ?_
  rw [Function.comp_apply, (conjLoc_spec _ _).2.1, (conjLoc_spec _ _).2.1]
  exact congrArg _ (IsCMField.complexConj_apply_apply E k)

theorem pInf_conj (x : Ad E) : pInf E (conjAd E x) = starRingEnd (Cinf E) (pInf E x) :=
  (infEq E).symm_apply_apply _

theorem conjAd_invol (x : Ad E) : conjAd E (conjAd E x) = x :=
  ad_ext (by rw [pInf_conj, pInf_conj, starRingEnd_self_apply]) (conjFin_invol _)

theorem thetaA_invol (x : GA E n) : thetaA E n (thetaA E n x) = x := by
  refine Units.ext ?_
  ext i j
  change conjAd E (conjAd E (x.val i j)) = x.val i j
  exact conjAd_invol _

theorem ratGL_thetaE (d : GL (Fin n) E) : ratGL E n (thetaE E n d) = thetaA E n (ratGL E n d) := by
  refine Units.ext ?_
  ext i j
  have h : ((ratGL E n d)⁻¹ : GA E n) = ratGL E n d⁻¹ := (map_inv _ _).symm
  rw [thetaR_val, h]
  change algebraMap E (Ad E) (conjE E ((d⁻¹ : GL (Fin n) E).val j i)) =
    conjAd E (algebraMap E (Ad E) ((d⁻¹ : GL (Fin n) E).val j i))
  rw [conjAd_algebraMap]
  rfl

theorem conj_nrm (x : GA E n) (d : GL (Fin n) E) :
    x⁻¹ * ratGL E n (nrm d) * x =
      twConj (thetaA E n) x (ratGL E n d) * thetaA E n (twConj (thetaA E n) x (ratGL E n d)) := by
  simp only [twConj, nrm, map_mul, map_inv, thetaA_invol, ratGL_thetaE]
  group

end Global

theorem arith (C₁ C₂ c L l τ : ℝ) (hL0 : 0 ≤ L) (hl0 : 0 ≤ l) (hl : l ≤ 2 * L + |c|)
    (hτ : (1 + |C₁| * (2 + |c|) + |C₂|) * (1 + L) ≤ τ) :
    0 < τ ∧ C₁ * (1 + l) < 2 * τ ∧ C₂ * (1 + L) ≤ τ := by
  have ha : 0 ≤ |C₁| := abs_nonneg _
  have hb : 0 ≤ |C₂| := abs_nonneg _
  have hcc : 0 ≤ |c| := abs_nonneg _
  have hprod : 0 ≤ |C₁| * (2 + |c|) * (1 + L) := by positivity
  have hprod2 : 0 ≤ |C₂| * (1 + L) := by positivity
  have hτ' : 1 + L + |C₁| * (2 + |c|) * (1 + L) + |C₂| * (1 + L) ≤ τ := by
    calc _ = (1 + |C₁| * (2 + |c|) + |C₂|) * (1 + L) := by ring
      _ ≤ τ := hτ
  have hτ0 : 0 < τ := by linarith
  refine ⟨hτ0, ?_, ?_⟩
  · have e1 : C₁ * (1 + l) ≤ |C₁| * (1 + l) := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    have e2 : |C₁| * (1 + l) ≤ |C₁| * (1 + (2 * L + |c|)) := mul_le_mul_of_nonneg_left (by linarith) ha
    have e3 : |C₁| * (1 + (2 * L + |c|)) ≤ |C₁| * (2 + |c|) * (1 + L) := by
      have : 0 ≤ |C₁| * (1 + |c| * L) := by positivity
      nlinarith
    linarith
  · have h3 : C₂ * (1 + L) ≤ |C₂| * (1 + L) := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    linarith

theorem onlyStable_of : DegSubmod → DegMove → DegBdd → DegPairing → SizeBasic → OnlyStable := by
  intro hSub hMove hBdd hPair hSize E _ _ _ n
  obtain ⟨C₁, h₁⟩ := hMove E n
  obtain ⟨C₂, h₂⟩ := hPair E n
  obtain ⟨-, hnn, hθ, c, hc⟩ := hSize E n
  refine ⟨1 + |C₁| * (2 + |c|) + |C₂|, fun τ x d hτ => ?_⟩
  have hls : logSize (x⁻¹ * ratGL E n (nrm d) * x) ≤
      2 * logSize (twConj (thetaA E n) x (ratGL E n d)) + |c| := by
    rw [conj_nrm]
    have h := hc (twConj (thetaA E n) x (ratGL E n d)) (thetaA E n (twConj (thetaA E n) x (ratGL E n d)))
    rw [hθ] at h
    have := le_abs_self c
    linarith
  obtain ⟨hτ0, hD, hC₂⟩ := arith C₁ C₂ c _ _ τ (hnn _) (hnn _) hls hτ
  constructor
  · exact fun h W _ => h.1 W
  · intro hst
    refine ⟨fun W => ?_, ?_⟩
    · exact core (deg x) (img (nrm d)) τ _ hτ0 hD ((hBdd E n).1 x) (hSub E n x) (fun W => h₁ x (nrm d) W)
        (fun W => finrank_img _ W) hst W
    · have h := (h₂ x d).2
      have := neg_abs_le (deg x (⊤ : Submodule E (Fin n → E)))
      linarith

end GlobalTheory.CompanionTheory.OnlyStab
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingIsoOfComponentIsos
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.KunGlue.Transfer

variable {K : Type} [Field K]

theorem exCls (C : Cx.{1} K) {n : ℕ} (c : C.H n) : ∃ (x : C.X n) (hx : C.d n x = 0), C.cls x hx = c := by
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact ⟨x, hx, rfl⟩

theorem sub_mem_of_cls_eq {C : Cx.{1} K} {n : ℕ} {x y : C.X n} {hx : C.d n x = 0} {hy : C.d n y = 0}
    (h : C.cls x hx = C.cls y hy) : x - y ∈ C.B n :=
  (Submodule.Quotient.eq ((C.B n).submoduleOf (C.Z n)) (x := ⟨x, hx⟩) (y := ⟨y, hy⟩)).1 h

theorem cls_eq_of_sub_mem {C : Cx.{1} K} {n : ℕ} {x y : C.X n} {hx : C.d n x = 0} {hy : C.d n y = 0}
    (h : x - y ∈ C.B n) : C.cls x hx = C.cls y hy :=
  (Submodule.Quotient.eq ((C.B n).submoduleOf (C.Z n)) (x := ⟨x, hx⟩) (y := ⟨y, hy⟩)).2 h

theorem d_map_cocycle {C D : Cx.{1} K} (φ : Cx.Hom C D (RingHom.id K)) {n : ℕ} {x : C.X n} (hx : C.d n x = 0) :
    D.d n (φ.f n x) = 0 := by
  rw [φ.comm, hx, map_zero]

theorem d_mu_cocycle {A B M : Cx.{1} K} (pr : CxPairing A B M) {p q n : ℕ} (h : p + q = n) {x : A.X p} {y : B.X q}
    (hx : A.d p x = 0) (hy : B.d q y = 0) : M.d n (pr.μ h x y) = 0 := by
  rw [pr.leib, hx, hy]
  simp

theorem cls_mu_left {A B M : Cx.{1} K} (pr : CxPairing A B M) {p q n : ℕ} (h : p + q = n) {x x' : A.X p} {y : B.X q}
    {hx : A.d p x = 0} {hx' : A.d p x' = 0} (hy : B.d q y = 0) {hz : M.d n (pr.μ h x y) = 0}
    {hz' : M.d n (pr.μ h x' y) = 0} (e : A.cls x hx = A.cls x' hx') :
    M.cls (pr.μ h x y) hz = M.cls (pr.μ h x' y) hz' := by
  apply cls_eq_of_sub_mem
  have hb := sub_mem_of_cls_eq e
  rw [← LinearMap.sub_apply, ← map_sub]
  cases p with
  | zero =>
    have h0 : x - x' = 0 := hb
    rw [h0, map_zero, LinearMap.zero_apply]
    exact zero_mem _
  | succ p =>
    obtain ⟨w, hw⟩ := hb
    obtain rfl : n = (p + q) + 1 := by omega
    change _ ∈ LinearMap.range (M.d (p + q))
    refine ⟨pr.μ rfl w y, ?_⟩
    rw [pr.leib, hw, hy]
    simp

theorem cls_mu_right {A B M : Cx.{1} K} (pr : CxPairing A B M) {p q n : ℕ} (h : p + q = n) {x : A.X p} {y y' : B.X q}
    (hx : A.d p x = 0) {hy : B.d q y = 0} {hy' : B.d q y' = 0} {hz : M.d n (pr.μ h x y) = 0}
    {hz' : M.d n (pr.μ h x y') = 0} (e : B.cls y hy = B.cls y' hy') :
    M.cls (pr.μ h x y) hz = M.cls (pr.μ h x y') hz' := by
  apply cls_eq_of_sub_mem
  have hb := sub_mem_of_cls_eq e
  rw [← map_sub]
  cases q with
  | zero =>
    have h0 : y - y' = 0 := hb
    rw [h0, map_zero]
    exact zero_mem _
  | succ q =>
    obtain ⟨w, hw⟩ := hb
    obtain rfl : n = (p + q) + 1 := by omega
    change _ ∈ LinearMap.range (M.d (p + q))
    refine ⟨(-1 : ℤ) ^ p • pr.μ rfl x w, ?_⟩
    rw [map_zsmul, pr.leib, hw, hx]
    simp [smul_smul, ← mul_pow]

def sumCongr {I : Type} [DecidableEq I] {A B : I → Type 1} [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)]
    [∀ i, Module K (A i)] [∀ i, Module K (B i)] (e : ∀ i, A i ≃ₗ[K] B i) : (⨁ i, A i) ≃ₗ[K] ⨁ i, B i :=
  DFinsupp.mapRange.linearEquiv e

theorem sumCongr_lof {I : Type} [DecidableEq I] {A B : I → Type 1} [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)]
    [∀ i, Module K (A i)] [∀ i, Module K (B i)] (e : ∀ i, A i ≃ₗ[K] B i) (i : I) (x : A i) :
    sumCongr e (DirectSum.lof K I A i x) = DirectSum.lof K I B i (e i x) :=
  DFinsupp.mapRange_single (hf := fun i => map_zero (e i))

theorem kunE_iff : ∀ {K : Type} [Field K] {P P' Q Q' T T' : ℕ → Cx.{1} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)) (pr' : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P' a) (Q' a') (T' c)) (p : ∀ a, Cx.Hom (P a) (P' a) (RingHom.id K)) (f : ∀ a, Cx.Hom (Q a) (Q' a) (RingHom.id K)) (g : ∀ a, Cx.Hom (T a) (T' a) (RingHom.id K)), (∀ a n, Function.Bijective ((p a).mapH n)) → (∀ a n, Function.Bijective ((f a).mapH n)) → (∀ a n, Function.Bijective ((g a).mapH n)) → (∀ {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (h : i + j = n) (x : (P a).X i) (y : (Q a').X j), (g c).f n ((pr ha).μ h x y) = (pr' ha).μ h ((p a).f i x) ((f a').f j y)) → (KunE pr ↔ KunE pr') := by
  intro K _ P P' Q Q' T T' pr pr' p f g hp hf hg hc
  let eP : ∀ a n, (P a).H n ≃ₗ[K] (P' a).H n := fun a n => LinearEquiv.ofBijective ((p a).mapH n) (hp a n)
  let eQ : ∀ a n, (Q a).H n ≃ₗ[K] (Q' a).H n := fun a n => LinearEquiv.ofBijective ((f a).mapH n) (hf a n)
  let eT : ∀ a n, (T a).H n ≃ₗ[K] (T' a).H n := fun a n => LinearEquiv.ofBijective ((g a).mapH n) (hg a n)
  let eS : ∀ c n : ℕ, (⨁ t : Idx c n, (P t.a).H t.i ⊗[K] (Q t.a').H t.j) ≃ₗ[K]
      ⨁ t : Idx c n, (P' t.a).H t.i ⊗[K] (Q' t.a').H t.j :=
    fun c n => sumCongr fun t => TensorProduct.congr (eP t.a t.i) (eQ t.a' t.j)
  have hS : ∀ (c n : ℕ) (t : Idx c n) (x : (P t.a).X t.i) (y : (Q t.a').X t.j) (hx : (P t.a).d t.i x = 0)
      (hy : (Q t.a').d t.j y = 0),
      eS c n (DirectSum.lof K _ (fun t : Idx c n => (P t.a).H t.i ⊗[K] (Q t.a').H t.j) t
        ((P t.a).cls x hx ⊗ₜ (Q t.a').cls y hy)) =
      DirectSum.lof K _ (fun t : Idx c n => (P' t.a).H t.i ⊗[K] (Q' t.a').H t.j) t
        ((P' t.a).cls ((p t.a).f t.i x) (d_map_cocycle _ hx) ⊗ₜ (Q' t.a').cls ((f t.a').f t.j y) (d_map_cocycle _ hy)) := by
    intro c n t x y hx hy
    exact sumCongr_lof _ t _
  have hG : ∀ {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (h : i + j = n) (x : (P a).X i) (y : (Q a').X j)
      (hz : (T c).d n ((pr ha).μ h x y) = 0) (hz' : (T' c).d n ((pr' ha).μ h ((p a).f i x) ((f a').f j y)) = 0),
      eT c n ((T c).cls ((pr ha).μ h x y) hz) = (T' c).cls ((pr' ha).μ h ((p a).f i x) ((f a').f j y)) hz' := by
    intro a a' c ha i j n h x y hz hz'
    have e0 := hc ha h x y
    change (T' c).cls ((g c).f n ((pr ha).μ h x y)) (d_map_cocycle _ hz) = _
    exact cls_eq_of_sub_mem (by rw [e0, sub_self]; exact zero_mem _)
  constructor
  · intro H c n
    obtain ⟨e, he⟩ := H c n
    refine ⟨(eS c n).symm ≪≫ₗ e ≪≫ₗ eT c n, ?_⟩
    intro t x y hx hy hz
    obtain ⟨x0, hx0, e1⟩ := exCls (P t.a) ((eP t.a t.i).symm ((P' t.a).cls x hx))
    obtain ⟨y0, hy0, e2⟩ := exCls (Q t.a') ((eQ t.a' t.j).symm ((Q' t.a').cls y hy))
    have e1' : (P' t.a).cls ((p t.a).f t.i x0) (d_map_cocycle _ hx0) = (P' t.a).cls x hx := by
      have := congrArg (eP t.a t.i) e1
      rwa [LinearEquiv.apply_symm_apply] at this
    have e2' : (Q' t.a').cls ((f t.a').f t.j y0) (d_map_cocycle _ hy0) = (Q' t.a').cls y hy := by
      have := congrArg (eQ t.a' t.j) e2
      rwa [LinearEquiv.apply_symm_apply] at this
    have hS' := hS c n t x0 y0 hx0 hy0
    rw [e1', e2'] at hS'
    have hz0 := d_mu_cocycle (pr t.ha) t.h hx0 hy0
    have hz1 := d_mu_cocycle (pr' t.ha) t.h (d_map_cocycle (p t.a) hx0) (d_map_cocycle (f t.a') hy0)
    have hz2 := d_mu_cocycle (pr' t.ha) t.h hx (d_map_cocycle (f t.a') hy0)
    simp only [LinearEquiv.trans_apply]
    rw [← hS', LinearEquiv.symm_apply_apply, he t x0 y0 hx0 hy0 hz0, hG t.ha t.h x0 y0 hz0 hz1,
      cls_mu_left (pr' t.ha) t.h (d_map_cocycle (f t.a') hy0) (hz' := hz2) e1',
      cls_mu_right (pr' t.ha) t.h hx (hz' := hz) e2']
  · intro H c n
    obtain ⟨e, he⟩ := H c n
    refine ⟨eS c n ≪≫ₗ e ≪≫ₗ (eT c n).symm, ?_⟩
    intro t x y hx hy hz
    have hz1 := d_mu_cocycle (pr' t.ha) t.h (d_map_cocycle (p t.a) hx) (d_map_cocycle (f t.a') hy)
    simp only [LinearEquiv.trans_apply]
    rw [hS c n t x y hx hy, he t _ _ _ _ hz1, ← hG t.ha t.h x y hz hz1, LinearEquiv.symm_apply_apply]

end GlobalTheory.CompanionTheory.KunGlue.Transfer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopGradedQuotientInjectiveMapStatement
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.top_graded_quotient_injective_map : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {d : ℕ} (t : Fin d → Γ(X, W)) (s : ℕ) (E : Frame (sP (KS q s {W})) d)
    (ε : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj E.D), IsLoc q s t E ε → ∀ (σ : ∀ T, E.D ⟶ T) (r : ℤ), r = d → d + 1 ≤ s →
    letI := (strV q W).toAlgebra
    ∃ φ : HQ (KS q s {W}) r (r + 1) d →ₗ[K] Γ(X, W), Function.Injective φ ∧ ∀ (y : Γ(X, W)) (c : HQ (KS q s {W}) r (r + 1) d),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (E.form σ id (ε y)) c → φ c = y := by
  first | exact @GlobalTheory.CompanionTheory.ConeLocal.coef_map | exact GlobalTheory.CompanionTheory.ConeLocal.coef_map | (intros; apply GlobalTheory.CompanionTheory.ConeLocal.coef_map <;> assumption)
end

