module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
public import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1746
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1760
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1749
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetPowerSectionNeZeroDefinite
section
set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
open scoped ComplexConjugate

namespace GlobalTheory.DefConst

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def detPow (Ψ : Finset (E →+* ℂ)) (a : ℤ) (x : Frame Ψ r) : ℂ := ∏ τ, (mat x τ).det ^ a

theorem telescope : ∀ (n : ℕ) (f : Fin (n + 1) → ℝ), (∀ i, f i ≠ 0) →
    ∏ i : Fin n, f i.succ / f i.castSucc = f (Fin.last n) / f 0
  | 0, f, h => by
    rw [Fin.prod_univ_zero]; exact (div_self (h 0)).symm
  | n + 1, f, h => by
    rw [Fin.prod_univ_castSucc]
    have ih : ∏ i : Fin n, f i.succ.castSucc / f i.castSucc.castSucc =
        f (Fin.last n).castSucc / f (0 : Fin (n + 1)).castSucc :=
      telescope n (fun i => f i.castSucc) (fun i => h _)
    simp only [Fin.succ_castSucc]
    rw [ih, Fin.succ_last, Fin.castSucc_zero]
    have h1 := h (Fin.last n).castSucc
    have h2 := h 0
    field_simp

theorem lminor_zero (M : Matrix (Fin r) (Fin r) ℂ) : lminor M 0 = 1 := by
  unfold lminor
  exact Matrix.det_eq_one_of_card_eq_zero (by simp; exact Fintype.card_eq_zero)

theorem lminor_last (M : Matrix (Fin r) (Fin r) ℂ) : lminor M (Fin.last r) = M.det := by
  unfold lminor
  exact Matrix.det_submatrix_equiv_self (finCongr (Fin.val_last r)) M

theorem gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = x.transpose * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  exact Finset.sum_comm

theorem det_gram (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    (gram τ G x).det = x.det * (G.map τ).det * starRingEnd ℂ x.det := by
  rw [gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  congr 1
  exact (RingHom.map_det (starRingEnd ℂ) x).symm

theorem dmin_ne (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm x τ i ≠ 0 := by
  intro h
  have := (hx τ).2 i
  rw [h] at this
  simp at this

theorem pnorm_factor (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (a : ℤ) (τ : X.Ψ) :
    ‖(mat x τ).det ^ a‖ * ∏ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(a : ℝ) / 2) =
      ‖(X.Gm.map τ.1).det‖ ^ (-(a : ℝ) / 2) := by
  have hD : (mat x τ).det ≠ 0 := (hx τ).1
  have hpos : 0 < ‖(mat x τ).det‖ := norm_pos_iff.mpr hD
  have ht := telescope r (fun i => ‖dmin X.Gm x τ i‖) (fun i => norm_ne_zero_iff.mpr (dmin_ne X hx τ i))
  beta_reduce at ht
  have hprod : ∏ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(a : ℝ) / 2) =
      (‖dmin X.Gm x τ (Fin.last r)‖ / ‖dmin X.Gm x τ 0‖) ^ (-(a : ℝ) / 2) := by
    simp_rw [norm_div]
    rw [Real.finsetProd_rpow _ _ (fun i _ => by positivity) _, ht]
  rw [hprod]
  have h0 : dmin X.Gm x τ 0 = 1 := lminor_zero _
  have hl : dmin X.Gm x τ (Fin.last r) = (mat x τ).det * (X.Gm.map τ.1).det * starRingEnd ℂ (mat x τ).det := by
    unfold dmin; rw [lminor_last, det_gram]
  rw [h0, hl, norm_one, div_one, norm_mul, norm_mul, Complex.norm_conj, norm_zpow]
  have hg : 0 ≤ ‖(X.Gm.map τ.1).det‖ := norm_nonneg _
  rw [show ‖(mat x τ).det‖ * ‖(X.Gm.map τ.1).det‖ * ‖(mat x τ).det‖ =
      ‖(mat x τ).det‖ * ‖(mat x τ).det‖ * ‖(X.Gm.map τ.1).det‖ by ring,
    Real.mul_rpow (by positivity) hg, Real.mul_rpow hpos.le hpos.le, ← Real.rpow_intCast,
    ← mul_assoc, ← mul_assoc, ← Real.rpow_add hpos, ← Real.rpow_add hpos]
  have : (a : ℝ) + -(a : ℝ) / 2 + -(a : ℝ) / 2 = 0 := by ring
  rw [this, Real.rpow_zero, one_mul]

theorem pnorm_detPow (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la : Wt X.Ψ r) (a : ℤ)
    (hla : ∀ τ i, la τ i = a) :
    X.pnorm la (detPow X.Ψ a) x = ∏ τ : X.Ψ, ‖(X.Gm.map τ.1).det‖ ^ (-(a : ℝ) / 2) := by
  unfold Data.pnorm detPow
  simp only [hla, norm_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun τ _ => pnorm_factor X hx a τ

theorem det_diff (Ψ : Finset (E →+* ℂ)) (τ : Ψ) : Differentiable ℂ (fun x : Frame Ψ r => (mat x τ).det) := by
  simp only [Matrix.det_apply', mat, Matrix.of_apply]
  fun_prop

theorem detPow_diff (X : Data E r) (a : ℤ) : DifferentiableOn ℂ (detPow X.Ψ a) X.dom := by
  intro x hx
  apply DifferentiableAt.differentiableWithinAt
  unfold detPow
  have h : ∀ τ : X.Ψ, DifferentiableAt ℂ (fun y : Frame X.Ψ r => (mat y τ).det ^ a) x :=
    fun τ => (det_diff X.Ψ τ x).zpow (Or.inl (hx τ).1)
  fun_prop

theorem lact_one {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) : lact 1 x = x := by
  funext τ
  simp [lact, mat, Matrix.map_one]
  rfl

theorem chi_one (X : Data E r) (la : Wt X.Ψ r) : X.χ la 1 = 1 := by
  have h1 : (1 : GL (Fin r) E) ∈ X.Γ := X.Γ.one_mem
  have hm := X.χ_mul la 1 h1 1 h1
  rw [mul_one] at hm
  obtain ⟨n, hn, hf⟩ := X.χ_fin la
  have hne : X.χ la 1 ≠ 0 := fun h0 => by
    have := hf 1 h1
    rw [h0, zero_pow hn.ne'] at this
    exact zero_ne_one this
  exact mul_left_cancel₀ hne (hm.symm.trans (mul_one _).symm)

theorem hermC_mulVec (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (P : Matrix (Fin r) (Fin r) ℂ)
    (v w : Fin r → ℂ) :
    hermC τ G (P.mulVec v) (P.mulVec w) = ∑ k, ∑ l, v k * gram τ G P k l * conj (w l) := by
  have sw : ∀ f : Fin r → Fin r → Fin r → Fin r → ℂ,
      ∑ a, ∑ b, ∑ k, ∑ l, f a b k l = ∑ k, ∑ l, ∑ a, ∑ b, f a b k l := by
    intro f
    calc ∑ a, ∑ b, ∑ k, ∑ l, f a b k l = ∑ a, ∑ k, ∑ b, ∑ l, f a b k l :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ k, ∑ a, ∑ b, ∑ l, f a b k l := Finset.sum_comm
      _ = ∑ k, ∑ a, ∑ l, ∑ b, f a b k l :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ k, ∑ l, ∑ a, ∑ b, f a b k l := Finset.sum_congr rfl fun k _ => Finset.sum_comm
  simp only [hermC, gram, col, Matrix.of_apply, Matrix.mulVec, dotProduct]
  calc _ = ∑ a, ∑ b, ∑ k, ∑ l, P a k * v k * τ (G a b) * conj (P b l * w l) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ a, ∑ b, P a k * v k * τ (G a b) * conj (P b l * w l) := sw _
    _ = _ := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [map_mul]; ring

theorem not_iso (X : Data E r) (hp : X.p0 = 0 ∨ X.p0 = r) (ξ : Fin r → E) : ¬ X.IsIso ξ := by
  rintro ⟨-, h0, hne⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : E →+* ℂ, τ ∈ X.Ψ := by
    let τ0 : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
    by_cases h : τ0 ∈ X.Ψ
    · exact ⟨τ0, h⟩
    · refine ⟨ComplexEmbedding.conjugate τ0, (X.cmType _).2 ?_⟩
      simpa using h
  obtain ⟨P, hP, hg⟩ := X.signature ⟨τ, hτ⟩
  set u : Fin r → ℂ := fun a => τ (ξ a) with hu_def
  have hu : hermC τ X.Gm u u = 0 := by
    have := congrArg τ h0
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [herm, cc, map_sum, map_mul, map_zero, IsCMField.complexEmbedding_complexConj] at this
    simpa [hermC, u] using this
  obtain ⟨e, he, hsg⟩ : ∃ e : ℂ, e ≠ 0 ∧ ∀ a : Fin r, ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) = e := by
    rcases hp with h | h
    · exact ⟨-1, by norm_num, fun a => by simp [sgn, h]⟩
    · exact ⟨1, one_ne_zero, fun a => by simp [sgn, h, a.isLt]⟩
  set v := P⁻¹.mulVec u with hv_def
  have hPv : P.mulVec v = u := by
    rw [hv_def, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hP), Matrix.one_mulVec]
  have hsum : hermC τ X.Gm u u = e * ∑ a, v a * conj (v a) := by
    rw [← hPv, hermC_mulVec, hg]
    simp only [Matrix.diagonal_apply, hsg, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hv : v = 0 := by
    have h1 : ∑ a, (Complex.normSq (v a) : ℂ) = 0 := by
      have := hsum.symm.trans hu
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h he
      · simpa [Complex.mul_conj] using h
    have h2 : ∑ a, Complex.normSq (v a) = 0 := by exact_mod_cast h1
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Complex.normSq_nonneg _)] at h2
    funext a
    simpa using h2 a (Finset.mem_univ _)
  have hu0 : u = 0 := by rw [← hPv, hv, Matrix.mulVec_zero]
  apply hne
  funext a
  have := congrFun hu0 a
  simpa [u] using this

theorem detPow_mem_SS (X : Data E r) (hΓ : ∀ γ ∈ X.Γ, γ = 1) (hdef : ∀ ξ, ¬ X.IsIso ξ) (la : Wt X.Ψ r)
    (a : ℤ) (hla : ∀ τ i, la τ i = a) : detPow X.Ψ a ∈ X.SS la := by
  refine ⟨⟨⟨detPow_diff X a, ?_, ?_⟩, ⟨_, fun x hx => (pnorm_detPow X hx la a hla).le⟩⟩,
    fun ξ hξ => absurd hξ (hdef ξ)⟩
  · intro x _ b hb
    unfold detPow bchar
    have hb' : ∀ τ : X.Ψ, (mat b τ).det = ∏ i, b τ i i := fun τ =>
      Matrix.det_of_upperTriangular (fun i j hij => (hb τ).2 i j hij)
    have e1 : ∀ τ : X.Ψ, (mat (rmul x b) τ).det ^ a = (mat x τ).det ^ a * ∏ i, b τ i i ^ la τ i := by
      intro τ
      rw [show mat (rmul x b) τ = mat x τ * mat b τ from rfl, Matrix.det_mul, mul_zpow, hb' τ]
      simp only [hla]
      rw [Finset.prod_zpow]
    simp only [e1, Finset.prod_mul_distrib]
    ring
  · intro γ hγ x _
    rw [hΓ γ hγ, lact_one, chi_one, one_mul]

theorem exists_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (∀ γ ∈ X.Γ, γ = 1) → (X.p0 = 0 ∨ X.p0 = r) → ∀ s : ℕ, ∀ x ∈ X.dom,
      ∃ P ∈ X.SS (deMul X.Ψ r X.p0 s), P x ≠ 0 := by
  intro E _ _ _ r X hΓ hp s x hx
  refine ⟨detPow X.Ψ (if X.p0 = 0 then ((s / 2 : ℕ) : ℤ) else -((s / 2 : ℕ) : ℤ)),
    detPow_mem_SS X hΓ (not_iso X hp) _ _ ?_, ?_⟩
  · intro τ i
    by_cases h0 : X.p0 = 0
    · simp [deMul, h0]
    · have h : X.p0 = r := hp.resolve_left h0
      have hr : r ≠ 0 := h ▸ h0
      simp [deMul, h0, h, hr, i.isLt]
  · exact Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (hx τ).1

end GlobalTheory.DefConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalUnipotentAdditiveStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny

noncomputable section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_unipotent_additive : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (t : E →ₐ[F] Fv F v),
    ∃ uT uM : Matrix (Fin a') (Fin (a + a')) (Fv F v) →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      (∀ Y, At (evFin F v) (uT Y) ∧ (uT Y).map (piW t) = 0 ∧ GlobalTheory.LinBarAt.coAt G t (uT Y) = Y) ∧
      (∀ z, At (evFin F v) (uM z) ∧ (uM z).map (piW (t.comp σ)) = 0 ∧ (uM z).map (piW t) = -z) ∧
      (∀ u, At (evFin F v) u → ∃ Y z, u = uT Y + uM z) ∧
      (∀ x u, At (evFin F v) x → At (evFin F v) u →
        evFin F v (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) x u) =
          ∑ i, ∑ j, (x.map (piW t)) i j * GlobalTheory.LinBarAt.coAt G t u i j -
            ∑ i, ∑ j, GlobalTheory.LinBarAt.coAt G t x i j * (u.map (piW t)) i j) := by
  first | exact @GlobalTheory.LinBarCoords.exists_split_coords | exact GlobalTheory.LinBarCoords.exists_split_coords | (intros; apply GlobalTheory.LinBarCoords.exists_split_coords <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupsSchroedingerFixContinuousChar
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

noncomputable section

namespace GlobalTheory.SchrFixFin

variable {F : Type} [Field F] [NumberField F]

theorem nonarch_of_inducing {G S : Type} [AddGroup G] [TopologicalSpace G] [NonarchimedeanAddGroup G]
    [AddGroup S] [TopologicalSpace S] [IsTopologicalAddGroup S] (f : S →+ G) (hf : Topology.IsInducing f) :
    NonarchimedeanAddGroup S where
  is_nonarchimedean U hU := by
    rw [hf.nhds_eq_comap, map_zero, Filter.mem_comap] at hU
    obtain ⟨t, ht, hsub⟩ := hU
    obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean t ht
    exact ⟨V.comap f hf.continuous, fun x hx => hsub (hV hx)⟩

theorem nonarch_pi' {ι : Type} {G : ι → Type} [∀ i, AddGroup (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, NonarchimedeanAddGroup (G i)] : NonarchimedeanAddGroup (∀ i, G i) where
  is_nonarchimedean U hU := by
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, hI, t, ht, hs⟩ := hU
    choose K hK using fun i => NonarchimedeanAddGroup.is_nonarchimedean (G := G i) (t i) (ht i)
    exact ⟨⟨AddSubgroup.pi I fun i => (K i : AddSubgroup (G i)), isOpen_set_pi hI fun i _ => (K i).isOpen⟩,
      fun x hx => hs fun i hi => hK i (hx i hi)⟩


variable (F) in
theorem nonarch_finAdeles : NonarchimedeanAddGroup (FiniteAdeleRing (𝓞 F) F) := by
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), NonarchimedeanAddGroup (v.adicCompletionIntegers F) := fun v =>
    nonarch_of_inducing (v.adicCompletionIntegers F).subtype.toAddMonoidHom Topology.IsInducing.subtypeVal
  haveI := nonarch_pi' (G := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F)
  let f : (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) →+ FiniteAdeleRing (𝓞 F) F :=
    { toFun := RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
        (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact NonarchimedeanAddGroup.nonarchimedean_of_emb f
    (RestrictedProduct.isOpenEmbedding_structureMap (fun v => Valued.isOpen_integer _))

def transFix {M : Type} [AddCommGroup M] (Φ : M → ℂ) : AddSubgroup M where
  carrier := {u | ∀ x, Φ (x + u) = Φ x}
  zero_mem' := fun x => by rw [add_zero]
  add_mem' := fun {a b} ha hb x => by rw [← add_assoc, hb, ha]
  neg_mem' := fun {a} ha x => by
    have := ha (x + -a)
    rw [neg_add_cancel_right] at this
    exact this.symm

theorem isOpen_transFix {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] {Φ : M → ℂ}
    (h1 : IsLocallyConstant Φ) (h2 : HasCompactSupport Φ) : IsOpen (transFix Φ : Set M) := by
  have h : ∀ᶠ u in nhds (0 : M), ∀ x ∈ tsupport Φ, Φ (x + u) = Φ x ∧ Φ (x - u) = Φ x := by
    apply h2.isCompact.eventually_forall_of_forall_eventually
    intro x _
    have a1 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 + z.1 by fun_prop)).eventually_eq (0, x)
    have a2 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 - z.1 by fun_prop)).eventually_eq (0, x)
    have a3 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 by fun_prop)).eventually_eq (0, x)
    filter_upwards [a1, a2, a3] with z b1 b2 b3
    simp only [Function.comp, add_zero, sub_zero] at b1 b2 b3
    exact ⟨b1.trans b3.symm, b2.trans b3.symm⟩
  have key : ∀ᶠ u in nhds (0 : M), ∀ x, Φ (x + u) = Φ x := by
    filter_upwards [h] with u hu x
    by_cases hx : x ∈ tsupport Φ
    · exact (hu x hx).1
    · by_cases hx' : x + u ∈ tsupport Φ
      · have := (hu _ hx').2
        rw [add_sub_cancel_right] at this
        exact this.symm
      · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']
  exact AddSubgroup.isOpen_of_mem_nhds _ key

theorem adeleJoin_zero {κ : Type} (y : κ → FiniteAdeleRing (𝓞 F) F) (i : κ) :
    GlobalTheory.WeilCont.adeleJoin F 0 y i = ((0 : InfiniteAdeleRing F), y i) := by
  refine Prod.ext ?_ rfl
  show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm 0 = 0
  exact map_zero _

theorem dot_adeleJoin_zero {κ : Type} [Fintype κ] (v : κ → AdeleRing (𝓞 F) F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    v ⬝ᵥ GlobalTheory.WeilCont.adeleJoin F 0 y = ((0 : InfiniteAdeleRing F), (fun i => (v i).2) ⬝ᵥ y) := by
  let p1 : AdeleRing (𝓞 F) F →+* InfiniteAdeleRing F := RingHom.fst _ _
  let p2 : AdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd _ _
  have e1 : ∀ s : AdeleRing (𝓞 F) F, s.1 = p1 s := fun _ => rfl
  have e2 : ∀ s : AdeleRing (𝓞 F) F, s.2 = p2 s := fun _ => rfl
  refine Prod.ext ?_ ?_
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [e1, dotProduct, map_sum]
      change (∑ i, p1 (v i * GlobalTheory.WeilCont.adeleJoin F 0 y i)) = 0
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_mul, adeleJoin_zero]
      exact mul_zero _
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [e2, dotProduct, map_sum]
      change (∑ i, p2 (v i * GlobalTheory.WeilCont.adeleJoin F 0 y i)) = _
      unfold dotProduct
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, adeleJoin_zero]
      rfl

theorem exists_fix_pure (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : Continuous ψ) (κ : Type) [Fintype κ]
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F),
      IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      ∀ x ∈ L₁, ∀ y ∈ L₂, schr ψ (GlobalTheory.WeilCont.adeleJoin F 0 x, GlobalTheory.WeilCont.adeleJoin F 0 y) (pureA F f g) =
        pureA F f g := by
  haveI := nonarch_finAdeles F
  let χ : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ :=
    ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
  have hχ : Continuous χ := hψ.comp (continuous_const.prodMk continuous_id)
  obtain ⟨H, hH⟩ := _root_.GlobalTheory.CharDotKill.charDot_kill χ hχ κ (tsupport g) hg.2.isCompact
  let c : FiniteAdeleRing (𝓞 F) F := (⅟(2 : AdeleRing (𝓞 F) F)).2
  refine ⟨transFix g ⊓ (H : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)).comap
    (DistribSMul.toAddMonoidHom (κ → FiniteAdeleRing (𝓞 F) F) c), H, ?_, H.isOpen, ?_⟩
  · rw [AddSubgroup.coe_inf]
    exact (isOpen_transFix hg.1 hg.2).inter (H.isOpen.preimage (continuous_const_smul c))
  rintro x ⟨hx1, hx2⟩ y hy
  funext z
  have hf : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((z + GlobalTheory.WeilCont.adeleJoin F 0 x) i).1) =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1 := by
    funext i
    rw [Pi.add_apply, adeleJoin_zero]
    exact congrArg _ (add_zero (z i).1)
  have hgz : (fun i => ((z + GlobalTheory.WeilCont.adeleJoin F 0 x) i).2) = (fun i => (z i).2) + x := by
    funext i
    rw [Pi.add_apply, adeleJoin_zero]
    rfl
  have hz : pureA F f g (z + GlobalTheory.WeilCont.adeleJoin F 0 x) = pureA F f g z := by
    simp only [pureA]
    rw [hf, hgz, hx1]
  simp only [schr]
  rw [hz]
  by_cases hg0 : g (fun i => (z i).2) = 0
  · simp only [pureA, hg0, mul_zero]
  have hzc : (fun i => (z i).2) ∈ tsupport g := subset_tsupport _ hg0
  have harg : z ⬝ᵥ GlobalTheory.WeilCont.adeleJoin F 0 y + ⅟(2 : AdeleRing (𝓞 F) F) *
      (GlobalTheory.WeilCont.adeleJoin F 0 x ⬝ᵥ GlobalTheory.WeilCont.adeleJoin F 0 y) =
      ((0 : InfiniteAdeleRing F), (fun i => (z i).2) ⬝ᵥ y + (c • x) ⬝ᵥ y) := by
    rw [dot_adeleJoin_zero, dot_adeleJoin_zero, smul_dotProduct]
    refine Prod.ext ?_ ?_
    · show (0 : InfiniteAdeleRing F) + (⅟(2 : AdeleRing (𝓞 F) F)).1 * 0 = 0
      rw [mul_zero, add_zero]
    · show (fun i => (z i).2) ⬝ᵥ y + c * ((fun i => (GlobalTheory.WeilCont.adeleJoin F 0 x i).2) ⬝ᵥ y) = _
      rfl
  rw [harg]
  have h1 : ψ ((0 : InfiniteAdeleRing F), (fun i => (z i).2) ⬝ᵥ y + (c • x) ⬝ᵥ y) = 1 :=
    hH _ hzc (c • x) hx2 y hy
  rw [h1, one_mul]

theorem exists_fix : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), Continuous ψ →
    ∀ (κ : Type) [Fintype κ], ∀ Φ ∈ schA F κ,
      ∃ L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F),
        IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
        ∀ x ∈ L₁, ∀ y ∈ L₂, schr ψ (GlobalTheory.WeilCont.adeleJoin F 0 x, GlobalTheory.WeilCont.adeleJoin F 0 y) Φ = Φ := by
  intro F _ _ ψ hψ κ _ Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact exists_fix_pure ψ hψ κ f g hg
  | zero =>
    refine ⟨⊤, ⊤, isOpen_univ, isOpen_univ, fun x _ y _ => ?_⟩
    funext z
    simp [schr]
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨L₁, L₂, o₁, o₂, h⟩ := h1
    obtain ⟨M₁, M₂, p₁, p₂, h'⟩ := h2
    refine ⟨L₁ ⊓ M₁, L₂ ⊓ M₂, by rw [AddSubgroup.coe_inf]; exact o₁.inter p₁,
      by rw [AddSubgroup.coe_inf]; exact o₂.inter p₂, fun x hx y hy => ?_⟩
    have e1 := h x hx.1 y hy.1
    have e2 := h' x hx.2 y hy.2
    funext z
    have a1 := congrFun e1 z
    have a2 := congrFun e2 z
    simp only [schr, Pi.add_apply] at a1 a2 ⊢
    rw [mul_add, a1, a2]
  | smul a Φ _ h =>
    obtain ⟨L₁, L₂, o₁, o₂, h⟩ := h
    refine ⟨L₁, L₂, o₁, o₂, fun x hx y hy => ?_⟩
    funext z
    have a1 := congrFun (h x hx y hy) z
    simp only [schr, Pi.smul_apply, smul_eq_mul] at a1 ⊢
    rw [mul_left_comm, a1]

end GlobalTheory.SchrFixFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweSplittingActsFockActionPlusTraceMultiplesStatement
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howeSplitting_acts_fockAction_plus_traceMultiples : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ)
    (om : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)), IsCMExt F E σ → IsStd ψ →
    FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ → IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om →
    ∃ c, ActsByD τ C om Φ (fun w => fockAct2 (P w) (Q w) (R w) (S w)) c := by
  first | exact @GlobalTheory.HoweD.lieScalarD | exact GlobalTheory.HoweD.lieScalarD | (intros; apply GlobalTheory.HoweD.lieScalarD <;> assumption)
end

