module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OneAddLeLminorSq
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1749
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1643
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1660
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1662
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1745
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1746
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1747

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBalancedFrameCMUnitaryProof
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.BalancedPointPf

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem conj_mem_iff (X : Data E r) (σ : E →+* ℂ) :
    ComplexEmbedding.conjugate σ ∈ X.Ψ ↔ σ ∉ X.Ψ := by
  rw [X.cmType (ComplexEmbedding.conjugate σ)]
  simp [ComplexEmbedding.conjugate, star_star]

theorem sum_eq_two_mul (X : Data E r) (f : (E →+* ℂ) → ℝ)
    (hf : ∀ σ, f (ComplexEmbedding.conjugate σ) = f σ) :
    ∑ σ, f σ = 2 * ∑ τ : X.Ψ, f τ.1 := by
  classical
  rw [← Finset.sum_add_sum_compl X.Ψ, Finset.sum_coe_sort X.Ψ f]
  have h : ∑ σ ∈ X.Ψᶜ, f σ = ∑ σ ∈ X.Ψ, f σ := by
    refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      rw [Finset.mem_compl] at hσ
      exact (conj_mem_iff X σ).2 hσ
    · intro σ hσ
      rw [Finset.mem_compl]
      exact (X.cmType σ).1 hσ
    · intro σ _; simp [ComplexEmbedding.conjugate, star_star]
    · intro σ _; simp [ComplexEmbedding.conjugate, star_star]
    · intro σ _; exact (hf σ).symm
  rw [h]; ring

theorem card_Ψ (X : Data E r) : (Fintype.card X.Ψ : ℝ) = fdeg E := by
  have h := sum_eq_two_mul X (fun _ => (1 : ℝ)) (fun _ => rfl)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  rw [Embeddings.card E ℂ] at h
  have h2 : Module.finrank ℚ E = 2 * Fintype.card X.Ψ := by exact_mod_cast h
  rw [fdeg, h2, Nat.mul_div_cancel_left _ two_pos]

end

end GlobalTheory.BalancedPointPf

namespace GlobalTheory.BalancedPointPf

open Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem embVec_conj (σ : E →+* ℂ) (v : Fin r → E) :
    ReciprocityTheory.MultiplicativeHeights.embVec (ComplexEmbedding.conjugate σ) v = star (ReciprocityTheory.MultiplicativeHeights.embVec σ v) := by
  funext k
  simp [ReciprocityTheory.MultiplicativeHeights.embVec, ComplexEmbedding.conjugate_coe_eq]

theorem maj_eq_hq (X : Data E r) (H : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (x : Frame X.Ψ r)
    (ho : IsOrth X x) (hH : ∀ τ : X.Ψ, (mat x τ)ᴴ * H τ.1 * mat x τ = 1) (τ : X.Ψ) (u : Fin r → ℂ) :
    X.maj x τ u = ReciprocityTheory.MultiplicativeHeights.hq (H τ.1) u := by
  have hmo := GlobalTheory.MajorantOrthFrame.maj_eq_sum_norm_sq_of_isOrth r X x ho
  have hu : IsUnit (mat x τ).det := isUnit_iff_ne_zero.mpr (hmo.1 τ)
  have e : H τ.1 = ((mat x τ)⁻¹)ᴴ * (mat x τ)⁻¹ := by
    calc H τ.1 = (mat x τ * (mat x τ)⁻¹)ᴴ * H τ.1 * (mat x τ * (mat x τ)⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hu]; simp
      _ = ((mat x τ)⁻¹)ᴴ * ((mat x τ)ᴴ * H τ.1 * mat x τ) * (mat x τ)⁻¹ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hH τ, Matrix.mul_one]
  rw [hmo.2 τ u, e, GlobalTheory.Up.BallExPf.hq_ct_mul]
  rfl

theorem balancedPoint :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.BalancedPointStatement E := by
  intro E _ _ _ r X
  obtain ⟨M, hss, hNC⟩ := ReciprocityTheory.MultiplicativeHeights.Closed.semistable E r (MajorantOrthogonality.pform X.toData) X.L'
    (MajorantOrthogonality.isLattice X) (MajorantOrthogonality.selfDual X)
  have hex : ∀ τ : X.Ψ, ∃ x : Matrix (Fin r) (Fin r) ℂ,
      xᴴ * (MajorantOrthogonality.pform X.toData).G.map τ.1 * x = ReciprocityTheory.MultiplicativeHeights.signMat X.p0 r ∧
        xᴴ * M.H τ.1 * x = 1 := fun τ => by
    obtain ⟨P, hP, hPg⟩ := X.signature τ
    exact GlobalTheory.Up.BallExPf.exists_frame (M.posDef τ.1) (M.major τ.1) hP
      ((GlobalTheory.Up.BallExPf.gram_iff X.toData τ.1 P).1 hPg)
  choose y hy1 hy2 using hex
  let x0 : Frame X.Ψ r := fun τ => y τ
  have h0 : IsOrth X.toData x0 := fun τ => (GlobalTheory.Up.BallExPf.gram_iff X.toData τ.1 _).2 (hy1 τ)
  have hmaj : ∀ (τ : X.Ψ) (u : Fin r → ℂ), X.maj x0 τ u = ReciprocityTheory.MultiplicativeHeights.hq (M.H τ.1) u :=
    maj_eq_hq X.toData M.H x0 h0 hy2
  refine ⟨x0, IW.orth_mem_dom X.toData x0 h0, ?_, ?_⟩
  · intro N hN hlt
    have key : ∀ (τ : X.Ψ) (w : Fin r → ℂ), w ≠ 0 →
        ReciprocityTheory.MultiplicativeHeights.hq (M.H τ.1) (N.map τ.1 *ᵥ w) < ReciprocityTheory.MultiplicativeHeights.hq (M.H τ.1) w := by
      intro τ w hw
      obtain ⟨c, hc0, hc1, hc⟩ := hlt τ
      have h1 := hc w
      rw [hmaj, hmaj] at h1
      have hpos : 0 < ReciprocityTheory.MultiplicativeHeights.hq (M.H τ.1) w := (M.posDef τ.1).re_dotProduct_pos hw
      have hc2 : c ^ 2 < 1 := by nlinarith
      nlinarith
    refine hNC N hN fun σ u hu => ?_
    by_cases hσ : σ ∈ X.Ψ
    · exact key ⟨σ, hσ⟩ u hu
    · have hσ' : ComplexEmbedding.conjugate σ ∈ X.Ψ := (conj_mem_iff X.toData σ).2 hσ
      have hsu : star u ≠ 0 := fun h => hu (by simpa using congrArg star h)
      have h := key ⟨_, hσ'⟩ (star u) hsu
      have e1 : M.H (ComplexEmbedding.conjugate σ) = (M.H σ).map (starRingEnd ℂ) := M.conj_compat σ
      have e2 : N.map (ComplexEmbedding.conjugate σ) *ᵥ star u = star (N.map σ *ᵥ u) := by
        funext k
        simp [Matrix.mulVec, dotProduct, ComplexEmbedding.conjugate_coe_eq]
      simp only at h
      rwa [e1, e2, GlobalTheory.Up.BallExPf.hq_conj, GlobalTheory.Up.BallExPf.hq_conj] at h
  · intro v hv hv0
    classical
    set h : (E →+* ℂ) → ℝ := fun σ => ReciprocityTheory.MultiplicativeHeights.hq (M.H σ) (ReciprocityTheory.MultiplicativeHeights.embVec σ v) with hhdef
    have hpos : ∀ σ, 0 < h σ := by
      intro σ
      refine (M.posDef σ).re_dotProduct_pos fun h0 => hv0 ?_
      funext k
      have := congrFun h0 k
      simp only [ReciprocityTheory.MultiplicativeHeights.embVec, Pi.zero_apply, map_eq_zero] at this
      exact this
    have hconj : ∀ σ, h (ComplexEmbedding.conjugate σ) = h σ := by
      intro σ
      simp only [hhdef]
      rw [embVec_conj, show M.H (ComplexEmbedding.conjugate σ) = (M.H σ).map (starRingEnd ℂ) from
        M.conj_compat σ, GlobalTheory.Up.BallExPf.hq_conj]

    set B : Submodule (𝓞 E) (Fin r → E) := Submodule.span (𝓞 E) {v} with hB
    have hrange : Set.range ![v] = {v} := by simp
    have hBL : B ≤ X.L' := by rw [hB, Submodule.span_le]; simpa using hv
    have hbasis : ReciprocityTheory.MultiplicativeHeights.IsKBasisIn B ![v] := by
      refine ⟨fun i => ?_, ?_, fun y hy => ?_⟩
      · rw [Fin.eq_zero i]; exact Submodule.subset_span rfl
      · exact linearIndependent_unique_iff.2 (by simpa using hv0)
      · rw [hB, Submodule.mem_span_singleton] at hy
        obtain ⟨a, rfl⟩ := hy
        rw [hrange]
        have : (algebraMap (𝓞 E) E a) • v ∈ Submodule.span E ({v} : Set (Fin r → E)) :=
          Submodule.smul_mem _ _ (Submodule.subset_span rfl)
        rwa [algebraMap_smul] at this
    have hdeg := hss.2 B hBL 1 ![v] hbasis
    have hidx : (Submodule.span (𝓞 E) (Set.range ![v])).toAddSubgroup.relIndex B.toAddSubgroup = 1 := by
      rw [hrange, ← hB]; exact AddSubgroup.relIndex_self _
    have hdet : ∀ σ, (ReciprocityTheory.MultiplicativeHeights.gramC (M.H σ) σ ![v]).det.re = h σ := by
      intro σ
      rw [Matrix.det_unique]
      rfl
    simp only [ReciprocityTheory.MultiplicativeHeights.latDeg, hidx, Nat.cast_one, Real.log_one, zero_sub, hdet] at hdeg
    have hsum : 0 ≤ ∑ σ, Real.log (h σ) := by linarith
    rw [sum_eq_two_mul X.toData (fun σ => Real.log (h σ)) (fun σ => by simp only [hconj])] at hsum
    have hlog : ∀ τ : X.Ψ, Real.log (h τ.1) ≤ h τ.1 - 1 := fun τ => Real.log_le_sub_one_of_pos (hpos τ.1)
    have hsum2 : 0 ≤ ∑ τ : X.Ψ, (h τ.1 - 1) :=
      (by linarith : 0 ≤ ∑ τ : X.Ψ, Real.log (h τ.1)).trans (Finset.sum_le_sum fun τ _ => hlog τ)
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      card_Ψ X.toData] at hsum2
    have e : ∀ τ : X.Ψ, X.maj x0 τ (Data.emb τ.1 v) = h τ.1 := fun τ => hmaj τ _
    simp only [e]
    linarith

end GlobalTheory.BalancedPointPf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSubgroupUnitaryPointsSupportedAtPla
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix Filter Topology
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SmallAtPlace

open IsDedekindDomain NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


omit [NumberField E] in
theorem smul_tens_single (v : HeightOneSpectrum (𝓞 F)) {u : AF F} (hu : evFin F v u = 0)
    (h1 : ∀ a b : Af F, (LinearMap.inr F (Ainf F) (Af F) (a * b) : AF F) =
      LinearMap.inr F (Ainf F) (Af F) a * LinearMap.inr F (Ainf F) (Af F) b)
    (z : Fv F v ⊗[F] E) :
    u • GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (E := E) (R' := AF F) (LinearMap.inr F (Ainf F) (Af F)) h1
      (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (singleFin v) (singleFin_mul v) z) = 0 := by
  have key : ∀ b : AF F, u * b = 0 → ∀ e : E, u • (b ⊗ₜ[F] e : AF F ⊗[F] E) = 0 := fun b hb e => by
    rw [TensorProduct.smul_tmul', smul_eq_mul, hb, TensorProduct.zero_tmul]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy, add_zero]
  | tmul a e =>
    let b : AF F := LinearMap.inr F (Ainf F) (Af F) (singleFin v a)
    have hb : u * b = 0 := by
      refine Prod.ext (mul_zero _) ?_
      show u.2 * singleFin v a = 0
      refine af_ext fun t => ?_
      rw [map_mul, map_zero]
      by_cases ht : t = v
      · subst ht
        have : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F t u.2 = 0 := hu
        rw [this, zero_mul]
      · rw [evalV_singleFin_ne ht, mul_zero]
    exact key b hb e


omit [NumberField E] in
theorem smul_mat_emb_sub_one (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (x : GLoc σ J v) {u : AF F} (hu : evFin F v u = 0) :
    u • ((HA.mat (AF F) σ J (emb σ J v x)).1 - 1) = 0 := by
  ext r s
  rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply]
  have h1 : ∀ a b : Af F, (LinearMap.inr F (Ainf F) (Af F) (a * b) : AF F) =
      LinearMap.inr F (Ainf F) (Af F) a * LinearMap.inr F (Ainf F) (Af F) b :=
    fun _ _ => Prod.ext (mul_zero _).symm rfl
  have hm := GlobalTheory.AutFunCompare.mat_extH σ J (R' := AF F) (LinearMap.inr F (Ainf F) (Af F)) h1
    (embLocFin σ J v x) r s
  have hm2 := GlobalTheory.AutFunCompare.mat_extH σ J (singleFin v) (singleFin_mul v) x r s
  have e1 : (HA.mat (AF F) σ J (emb σ J v x)).1 r s = _ := hm
  have e2 : (HA.mat (Af F) σ J (embLocFin σ J v x)).1 r s = _ := hm2
  rw [e1, e2]
  set T1 := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (E := E) (R' := AF F) (LinearMap.inr F (Ainf F) (Af F)) h1
  set T2 := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (E := E) (singleFin v) (singleFin_mul v)
  have key : ∀ z, u • T1 (T2 z) = 0 := smul_tens_single v hu h1
  have : (1 - T1 1) * (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) r s +
      T1 ((1 - T2 1) * (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) r s + T2 ((HA.mat _ σ J x).1 r s)) -
      (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) r s =
      T1 (T2 ((HA.mat _ σ J x).1 r s - (1 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) r s)) := by
    by_cases h : r = s
    · subst h
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq, Matrix.one_apply_eq, mul_one, mul_one, map_add (f := _), map_sub, map_sub, map_sub]
      abel
    · simp only [Matrix.one_apply_ne h, mul_zero, zero_add, sub_zero, map_zero]
  rw [this]
  exact key _

omit [NumberField E] in
theorem map_smul_of_eq_one {R : Type} [CommRing R] [Algebra F R] (ψ : AF F →ₐ[F] R) {a : AF F} (ha : ψ a = 1)
    (y : AF F ⊗[F] E) :
    Algebra.TensorProduct.map ψ (AlgHom.id F E) (a • y) = Algebra.TensorProduct.map ψ (AlgHom.id F E) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy]
  | tmul b e =>
    rw [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, smul_eq_mul,
      map_mul, ha, one_mul]

omit [NumberField E] in
theorem mapH_eq_one_of_smul (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {R : Type} [CommRing R]
    [Algebra F R] (ψ : AF F →ₐ[F] R) {a : AF F} (ha : ψ a = 1) {g : GAd σ J}
    (hg : a • ((HA.mat (AF F) σ J g).1 - 1) = 0) : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.mapH σ J ψ g = 1 := by
  refine GlobalTheory.AutFunCompare.HA_ext σ J fun r s => ?_
  rw [GlobalTheory.AutFunCompare.mat_mapH]
  have h := congrArg (Algebra.TensorProduct.map ψ (AlgHom.id F E)) (congrFun (congrFun hg r) s)
  rw [Matrix.smul_apply, Matrix.sub_apply, map_smul_of_eq_one ψ ha, map_sub, Matrix.zero_apply, map_zero, sub_eq_zero] at h
  rw [h]
  show _ = (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) r s
  by_cases e : r = s
  · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, map_zero]


omit [NumberField E] in
theorem eq_emb_proj_of_smul (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    {g : GAd σ J} (hg : ∀ u : AF F, evFin F v u = 0 → u • ((HA.mat (AF F) σ J g).1 - 1) = 0) :
    g = emb σ J v (proj σ J v g) := by
  refine GAd_ext σ J (fun w => ?_) (fun u => ?_)
  · rw [projArch_emb]
    let a : AF F := ((1 : Ainf F), (0 : Af F))
    have h1 : evInf F w a = 1 := by
      show (GlobalTheory.AutFunCompare.evW w) (1 : Ainf F) = 1
      exact map_one _
    have h0 : evFin F v a = 0 := by
      show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (0 : Af F) = 0
      exact map_zero _
    exact mapH_eq_one_of_smul σ J (evInf F w) h1 (hg a h0)
  · by_cases h : u = v
    · subst h; rw [proj_emb_self]
    · rw [proj_emb_ne σ J h]
      let a : AF F := ((0 : Ainf F), singleFin u 1)
      have h1 : evFin F u a = 1 := evalV_singleFin_self u 1
      have h0 : evFin F v a = 0 := evalV_singleFin_ne (Ne.symm h) 1
      exact mapH_eq_one_of_smul σ J (evFin F u) h1 (hg a h0)

theorem exists_compact_subgroup_at_place : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E},
    (∀ x, σ (σ x) = x) → ∀ {n : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (U : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)), U ∈ 𝓝 (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J) →
    ∃ K : Subgroup (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J), (∀ g ∈ K, g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (GlobalTheory.AdelicU.evFin F v)) ∧
      IsCompact (K : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)) ∧
      (∃ O : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J), IsOpen O ∧ (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J) ∈ O ∧
        ∀ g ∈ O, g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (GlobalTheory.AdelicU.evFin F v) → g ∈ K) ∧ (K : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)) ⊆ U := by
  intro F E _ _ _ _ _ σ hσ n X v U hU
  have heq : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) = HR (AF F) σ (X.J.map σ) := by
    have h := GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := X.J) hσ one_ne_zero
    rw [one_smul] at h
    exact h
  let e : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J ≃* GAd σ (X.J.map σ) := MulEquiv.subgroupCongr heq
  have he : Continuous e := continuous_subtype_val.subtype_mk _
  have he' : Continuous e.symm := continuous_subtype_val.subtype_mk _
  let f : GLoc σ (X.J.map σ) v →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J := e.symm.toMonoidHom.comp (emb σ (X.J.map σ) v)
  have hf : Continuous f := he'.comp (continuous_emb σ (X.J.map σ) v)
  have hW : f ⁻¹' U ∈ 𝓝 (1 : GLoc σ (X.J.map σ) v) :=
    hf.continuousAt.preimage_mem_nhds (by rw [map_one]; exact hU)
  haveI := GlobalTheory.Doubling.nonarchimedeanGroup_GLoc σ (X.J.map σ) v
  obtain ⟨V₀, hV₀⟩ := NonarchimedeanGroup.is_nonarchimedean _ hW
  haveI := isLattice_stdLattice (E := E) (n := n)
  let V₁ : Subgroup (GLoc σ (X.J.map σ) v) := (V₀ : Subgroup _) ⊓ stabLoc σ (X.J.map σ) (stdLattice E n) v
  have hV₁o : IsOpen (V₁ : Set (GLoc σ (X.J.map σ) v)) :=
    V₀.isOpen.inter (isOpen_stabLoc σ (X.J.map σ) (stdLattice E n) v)
  have hV₁c : IsCompact (V₁ : Set (GLoc σ (X.J.map σ) v)) :=
    (isCompact_stabLoc σ (X.J.map σ) (stdLattice E n) v).inter_left V₀.isClosed
  have hmat : ∀ g, (HA.mat (AF F) σ (X.J.map σ) (e g)).1 = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g := fun g => rfl
  refine ⟨V₁.map f, ?_, ?_, ⟨(proj σ (X.J.map σ) v ∘ e) ⁻¹' (V₁ : Set _),
    hV₁o.preimage ((continuous_proj σ (X.J.map σ) v).comp he), ?_, ?_⟩, ?_⟩
  · rintro _ ⟨x, -, rfl⟩ u hu
    have h := smul_mat_emb_sub_one σ (X.J.map σ) v x hu
    have h2 : (HA.mat (AF F) σ (X.J.map σ) (e (f x))).1 = (HA.mat (AF F) σ (X.J.map σ) (emb σ (X.J.map σ) v x)).1 := by
      simp [f]
    rw [← hmat, h2]
    exact h
  · rw [Subgroup.coe_map]
    exact hV₁c.image hf
  · show proj σ (X.J.map σ) v (e 1) ∈ V₁
    rw [map_one, map_one]
    exact one_mem _
  · intro g hg hgv
    refine ⟨proj σ (X.J.map σ) v (e g), hg, ?_⟩
    have h : e g = emb σ (X.J.map σ) v (proj σ (X.J.map σ) v (e g)) :=
      eq_emb_proj_of_smul σ (X.J.map σ) v fun u hu => by rw [hmat]; exact hgv u hu
    show e.symm (emb σ (X.J.map σ) v (proj σ (X.J.map σ) v (e g))) = g
    rw [← h, MulEquiv.symm_apply_apply]
  · rintro _ ⟨x, hx, rfl⟩
    exact hV₀ hx.1

end GlobalTheory.SmallAtPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalChartInertPlaceUnitaryPair
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertBridge

open GlobalTheory.InertCoord

theorem exists_chart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∃ (ϖ : w.adicCompletion E) (σL : w.adicCompletion E →+* w.adicCompletion E) (q : ℕ) (δ : w.adicCompletion E)
      (JS : GL (Fin a') (w.adicCompletion E)) (JT : GL (Fin (a + a')) (w.adicCompletion E)) (ψL : AddChar (w.adicCompletion E) ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') (w.adicCompletion E) →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') (w.adicCompletion E)) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) (w.adicCompletion E)) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hw _
  have h : w.under (𝓞 F) = v := (InertChart.under_eq_iff hw w).2 rfl
  obtain ⟨ϖ, σL, q, ψL, hc, hU, hodd, hpi, hpn, hψ⟩ := GlobalTheory.T.exists_inertPlace_localField_data F E σ B hTr.base v w hw h
  obtain ⟨A, hAf, hA⟩ := GlobalTheory.T.exists_inertPlace_orthonormal_selfDual_frame F E σ B a a' G hTr.base hTr.geo v w hw h σL hc
  obtain ⟨δ, Bm, hδ1, hδ2, hBf, hB⟩ := GlobalTheory.T.exists_frame_conjTranspose_mul_eq_smul_one F E σ B a a' G hTr.base hTr.geo v w hw h σL hc
  have hσσ : ∀ x, σL (σL x) = x := hU.1
  have hmapσσ : ∀ {k : ℕ} (M : Matrix (Fin k) (Fin k) (w.adicCompletion E)), (M.map σL).map σL = M := fun M =>
    Matrix.ext fun i j => hσσ _
  have hS : ∀ {k : ℕ} (g : Formalism.UG.UJ σL ((1 : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E))),
      (((g : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E)).map σL)ᵀ *
        ((g : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E)) = 1 := fun {k} g => by
    have := g.2
    change Formalism.UG.cT σL ((g : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E)) *
      (1 : Matrix (Fin k) (Fin k) (w.adicCompletion E)) * ((g : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E)) = 1 at this
    rwa [Matrix.mul_one] at this
  have hS' : ∀ {k : ℕ} (g : Formalism.UG.UJ σL ((1 : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E))),
      ((g : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E))ᵀ *
        ((g : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E)).map σL = 1 := fun g => by
    have h2 := congrArg (fun M => M.map σL) (hS g)
    simp only [Matrix.map_mul (f := σL), Matrix.transpose_map, hmapσσ] at h2
    rw [Matrix.map_one _ (map_zero σL) (map_one σL)] at h2
    exact h2
  let φS : Formalism.UG.UJ σL ((1 : GL (Fin a') (w.adicCompletion E)) : Matrix (Fin a') (Fin a') (w.adicCompletion E)) →*
      GL (Fin a') (w.adicCompletion E) := (Formalism.UG.bc σL).comp (Subgroup.subtype _)
  have hφS : ∀ g, ((φS g : GL (Fin a') (w.adicCompletion E)) : Matrix (Fin a') (Fin a') (w.adicCompletion E)) =
      ((g : GL (Fin a') (w.adicCompletion E)) : Matrix (Fin a') (Fin a') (w.adicCompletion E)).map σL := fun g => rfl
  have hφSu : ∀ g, ((φS g : GL (Fin a') (w.adicCompletion E)) : Matrix (Fin a') (Fin a') (w.adicCompletion E))ᵀ *
      ((φS g : GL (Fin a') (w.adicCompletion E)) : Matrix (Fin a') (Fin a') (w.adicCompletion E)).map σL = 1 := fun g => by
    rw [hφS, hmapσσ]; exact hS g
  obtain ⟨ιS, hSat, hSmat, hSK⟩ := GlobalTheory.T.exists_inertPlace_unitary_adelicHom F E σ v w hw h σL hc G.V' A 1 (by rw [hA, one_smul]) φS hφSu
  obtain ⟨ιT, hTat, hTmat, hTK⟩ := GlobalTheory.T.exists_inertPlace_unitary_adelicHom F E σ v w hw h σL hc G.W Bm δ hB (Subgroup.subtype _) (fun g => hS' g)
  have hgrp : ∀ {k : ℕ} (P M : GL (Fin k) (w.adicCompletion E)),
      ((P⁻¹ : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E)) *
        ((P * M * P⁻¹ : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E)) *
        (P : Matrix (Fin k) (Fin k) (w.adicCompletion E)) = (M : Matrix (Fin k) (Fin k) (w.adicCompletion E)) := fun P M => by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  refine ⟨ϖ, σL, q, δ, 1, 1, ψL, kap hw h (A : Matrix (Fin a') (Fin a') (w.adicCompletion E))
    (Bm : Matrix (Fin (a + a')) (Fin (a + a')) (w.adicCompletion E)), ιS, ιT, hU, hodd, one_mem _, one_mem _, ?_, ?_,
    ⟨hδ1, hδ2⟩, hpi, hpn, (GlobalTheory.T.inertPlacePoint_supported_and_surjective F E v w hw h A Bm).1, (GlobalTheory.T.inertPlacePoint_supported_and_surjective F E v w hw h A Bm).2,
    GlobalTheory.T.inertPoint_mem_tensorLattice_iff_integral_coords F E v w hw h G.V' G.W A Bm hAf hBf, ?_, ?_, fun g => hSat g, fun g => hTat g, ?_, ?_⟩
  · intro i j
    simp only [Units.val_one, Matrix.one_apply, eq_comm (a := i)]
    split_ifs <;> simp
  · intro i j
    simp only [Units.val_one, Matrix.one_apply, eq_comm (a := i)]
    split_ifs <;> simp
  · intro x y
    show _ = B.ψ (⅟(2 : AF F) * Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (-1 * hTens (cA σ) (incM F G.V'.J) (incM F G.W.J) _ _))
    rw [GlobalTheory.T.tensorHermitianForm_inertPoint_eq_localForm F E σ v w hw h σL hc G.V'.J G.W.J _ _ δ hA hB x y]
    exact hψ _
  · intro g k x
    change actAB (cA σ) (ιS g, ιT k) (kap hw h (A : Matrix (Fin a') (Fin a') (w.adicCompletion E)) (Bm : Matrix (Fin (a + a')) (Fin (a + a')) (w.adicCompletion E)) x) = _
    rw [GlobalTheory.T.inertPlace_action_on_tensorCoords F E σ v w hw h G.V' G.W A Bm (ιS g) (ιT k) (hSat g) (hTat k) x, hSmat, hTmat, hgrp, hgrp, hφS]
    congr 1
    have key : ∀ M : GL (Fin a') (w.adicCompletion E),
        ((M : Matrix (Fin a') (Fin a') (w.adicCompletion E)).map σL)ᵀ * (M : Matrix (Fin a') (Fin a') (w.adicCompletion E)) = 1 →
        ((M : Matrix (Fin a') (Fin a') (w.adicCompletion E)).map σL)ᵀ = ((M⁻¹ : GL (Fin a') (w.adicCompletion E)) : Matrix (Fin a') (Fin a') (w.adicCompletion E)) := by
      intro M e
      calc _ = ((M : Matrix (Fin a') (Fin a') (w.adicCompletion E)).map σL)ᵀ *
            ((M : Matrix (Fin a') (Fin a') (w.adicCompletion E)) * ((M⁻¹ : GL (Fin a') (w.adicCompletion E)) : Matrix (Fin a') (Fin a') (w.adicCompletion E))) := by
              rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
        _ = _ := by rw [← Matrix.mul_assoc, e, Matrix.one_mul]
    rw [key _ (hS g)]
    rfl
  · intro g hg
    refine hSK hAf g ?_
    obtain ⟨k, hk⟩ := hg
    let σO : Formalism.UG.intL (w.adicCompletion E) →+* Formalism.UG.intL (w.adicCompletion E) :=
      σL.restrict _ _ fun x hx => by
        change Valued.v (σL x) ≤ 1
        rw [hU.2.1 x]; exact hx
    refine ⟨Formalism.UG.bc σO k, Units.ext (Matrix.ext fun i j => ?_)⟩
    rw [hφS, ← hk]
    rfl
  · intro g hg
    exact hTK hBf g hg

end GlobalTheory.InertBridge

end
end

