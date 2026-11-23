module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
public import ReciprocityTheory.SemistableReduction.Bundle0026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTestVectorExpansion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1746
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1747

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallUnipotentUnitaryElementIsOneProof
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped Matrix

noncomputable section

namespace GlobalTheory.SmallElement

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem span_L' {r : ℕ} (X : DataX E r) :
    Submodule.span E (X.L' : Set (Fin r → E)) = ⊤ := by
  rw [eq_top_iff, ← X.Λ_span, Submodule.span_le]
  intro x hx
  have h1 := X.NA_sub x hx
  have hNA : (X.NA : E) ≠ 0 := by exact_mod_cast X.NA_pos.ne'
  have e : x = (X.NA : E)⁻¹ • ((X.NA : E) • x) := by rw [smul_smul, inv_mul_cancel₀ hNA, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

theorem trace_sub_mem {r : ℕ} (X : DataX E r) (g : ℕ) (hg : IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g)
    (δ : GL (Fin r) E) (hδ : IsUStab X.Gm X.L' δ)
    (hu : IndefiniteRowSideFullHecke.SmallUnipotentElements.IsUnipotentModOver X.L' g δ) :
    ∃ z : 𝓞 E, (δ : Matrix (Fin r) (Fin r) E).trace - r = (g : E) * z := by
  classical
  set N : Matrix (Fin r) (Fin r) E := (δ : Matrix (Fin r) (Fin r) E) - 1 with hNdef
  have htr : N.trace = (δ : Matrix (Fin r) (Fin r) E).trace - r := by
    simp [hNdef, Matrix.trace_sub]
  have hN : ∀ x ∈ X.L', N.mulVec x ∈ X.L' := fun x hx => by
    rw [hNdef, Matrix.sub_mulVec, Matrix.one_mulVec]
    exact X.L'.sub_mem ((hδ.2 x).1 hx) hx
  have hP : ∀ P ∈ (Ideal.span {(g : ℤ)}).primesOver (𝓞 E), ∃ z ∈ P, ((z : 𝓞 E) : E) = N.trace :=
    fun P hP => by
      obtain ⟨k, hk⟩ := hu P hP
      exact GlobalTheory.trace_mem_prime_of_pow_mulVec_mem_smul E r X.L' N P k X.L'_fg (span_L' X) hP.1 hN hk
  have hne : ((Ideal.span {(g : ℤ)}).primesOver (𝓞 E)).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [hg.2]
    exact (Module.finrank_pos (R := ℚ) (M := E)).ne'
  obtain ⟨P0, hP0⟩ := hne
  obtain ⟨t, -, ht⟩ := hP P0 hP0
  have hall : ∀ P ∈ (Ideal.span {(g : ℤ)}).primesOver (𝓞 E), t ∈ P := fun P hP' => by
    obtain ⟨z, hz, hzt⟩ := hP P hP'
    have : z = t := RingOfIntegers.ext (hzt.trans ht.symm)
    exact this ▸ hz
  have hpZ : Prime (g : ℤ) := Nat.prime_iff_prime_int.1 hg.1
  haveI hpr : (Ideal.span {(g : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  have hmax : (Ideal.span {(g : ℤ)}).IsMaximal :=
    hpr.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpZ.ne_zero)
  have hrad := GlobalTheory.SplitRadical.isRadical_span_of_ncard_primesOver E g hg.1 hg.2
  have hmem : t ∈ Ideal.span {(g : 𝓞 E)} := by
    apply hrad
    rw [Ideal.radical_eq_sInf]
    refine Submodule.mem_sInf.2 fun J hJ => ?_
    obtain ⟨hJle, hJp⟩ := hJ
    apply hall J
    refine ⟨hJp, ⟨?_⟩⟩
    have hle : Ideal.span {(g : ℤ)} ≤ Ideal.comap (algebraMap ℤ (𝓞 E)) J := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      show algebraMap ℤ (𝓞 E) (g : ℤ) ∈ J
      rw [map_natCast]
      exact hJle (Ideal.mem_span_singleton_self _)
    exact hmax.eq_of_le (Ideal.IsPrime.ne_top (Ideal.IsPrime.comap _)) hle
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨z, ?_⟩
  rw [← htr, ← ht, ← hz]
  push_cast
  ring

end GlobalTheory.SmallElement

namespace GlobalTheory.SmallElement

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem map_conj_mulVec {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (u : Fin r → ℂ) :
    (M.map (starRingEnd ℂ)) *ᵥ u = star (M *ᵥ star u) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum]

theorem normSq_star {r : ℕ} (u : Fin r → ℂ) : ReciprocityTheory.MultiplicativeHeights.normSq (star u) = ReciprocityTheory.MultiplicativeHeights.normSq u := by
  simp [ReciprocityTheory.MultiplicativeHeights.normSq]

theorem exp_sq (r : ℕ) : Real.exp (1 / (3 * (r : ℝ))) ^ 2 = Real.exp (2 / (3 * (r : ℝ))) := by
  rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

theorem det_ne_of_mul_eq_one {r : ℕ} {A B : Matrix (Fin r) (Fin r) ℂ} (h : A * B = 1) : A.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem map_conj_mul_eq_one {r : ℕ} {A : Matrix (Fin r) (Fin r) ℂ} (hA : IsUnit A.det) :
    (A⁻¹).map (starRingEnd ℂ) * A.map (starRingEnd ℂ) = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hA, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.SmallElement

namespace GlobalTheory.SmallElement

theorem smallElement : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    IndefiniteRowSideFullHecke.SmallUnipotentElements.SmallElementStatement E := by
  intro E _ _ _ r X g hg hgr Γo hstab hunip x hx hNC γ hγ hs
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact Units.ext (Matrix.ext fun i => i.elim0)
  obtain ⟨x1, h1, b, hb, rfl⟩ := ortho_holds r X.toData x hx
  have hx1 := ModeHalfA.dom_of_orth X.toData h1
  have hu : ∀ τ : X.Ψ, IsUnit (mat x1 τ).det :=
    fun τ => isUnit_iff_ne_zero.2 (LUPf.orthogonalFrame_det_ne_zero X.toData x1 h1 τ)
  have hmaj : ∀ (τ : X.Ψ) (v : Fin r → ℂ),
      X.maj (rmul x1 b) τ v = ReciprocityTheory.MultiplicativeHeights.normSq ((mat x1 τ)⁻¹ *ᵥ v) := fun τ v => by
    rw [GlobalTheory.MajInv.maj_rmul X.toData hx1 hb, ModeHalfA.maj_orth X.toData h1]
    rfl
  have hcΨ : ∀ σ : E →+* ℂ, σ ∉ X.Ψ → ComplexEmbedding.conjugate σ ∈ X.Ψ := fun σ hσ =>
    not_not.1 fun h' => hσ ((X.cmType σ).2 h')
  let Q : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ := fun σ =>
    if hσ : σ ∈ X.Ψ then (mat x1 ⟨σ, hσ⟩)⁻¹
    else ((mat x1 ⟨ComplexEmbedding.conjugate σ, hcΨ σ hσ⟩)⁻¹).map (starRingEnd ℂ)
  have hQpos : ∀ σ (hσ : σ ∈ X.Ψ), Q σ = (mat x1 ⟨σ, hσ⟩)⁻¹ := fun σ hσ => dif_pos hσ
  have hQneg : ∀ σ (hσ : σ ∉ X.Ψ),
      Q σ = ((mat x1 ⟨ComplexEmbedding.conjugate σ, hcΨ σ hσ⟩)⁻¹).map (starRingEnd ℂ) :=
    fun σ hσ => dif_neg hσ
  set G : Matrix (Fin r) (Fin r) E := (γ : Matrix (Fin r) (Fin r) E) with hG
  have hposB : ∀ (τ : X.Ψ) (u : Fin r → ℂ),
      ReciprocityTheory.MultiplicativeHeights.normSq (((mat x1 τ)⁻¹ * G.map τ.1 * ((mat x1 τ)⁻¹)⁻¹) *ᵥ u) ≤
        Real.exp (2 / (3 * (r : ℝ))) * ReciprocityTheory.MultiplicativeHeights.normSq u := by
    intro τ u
    have h := hs τ (mat x1 τ *ᵥ u)
    have e : (mat x1 τ)⁻¹ *ᵥ (mat x1 τ *ᵥ u) = u := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hu τ), Matrix.one_mulVec]
    rw [hmaj, hmaj, e, exp_sq] at h
    rw [Matrix.nonsing_inv_nonsing_inv _ (hu τ), ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact h
  have hQdet : ∀ σ, (Q σ).det ≠ 0 := by
    intro σ
    by_cases hσ : σ ∈ X.Ψ
    · rw [hQpos σ hσ]
      exact det_ne_of_mul_eq_one (Matrix.nonsing_inv_mul _ (hu _))
    · rw [hQneg σ hσ]
      exact det_ne_of_mul_eq_one (map_conj_mul_eq_one (hu _))
  have hop : ∀ σ (u : Fin r → ℂ), ReciprocityTheory.MultiplicativeHeights.normSq ((Q σ * G.map σ * (Q σ)⁻¹) *ᵥ u) ≤
      Real.exp (2 / (3 * (r : ℝ))) * ReciprocityTheory.MultiplicativeHeights.normSq u := by
    intro σ u
    by_cases hσ : σ ∈ X.Ψ
    · rw [hQpos σ hσ]
      exact hposB ⟨σ, hσ⟩ u
    · rw [hQneg σ hσ]
      set τ : X.Ψ := ⟨ComplexEmbedding.conjugate σ, hcΨ σ hσ⟩ with hτ
      have hinv : (((mat x1 τ)⁻¹).map (starRingEnd ℂ))⁻¹ = (mat x1 τ).map (starRingEnd ℂ) :=
        Matrix.inv_eq_right_inv (map_conj_mul_eq_one (hu τ))
      have hGm : G.map σ = (G.map τ.1).map (starRingEnd ℂ) := by
        ext i j
        simp [hτ, ComplexEmbedding.conjugate_coe_eq]
      have e : ((mat x1 τ)⁻¹).map (starRingEnd ℂ) * G.map σ *
          (((mat x1 τ)⁻¹).map (starRingEnd ℂ))⁻¹ =
          ((mat x1 τ)⁻¹ * G.map τ.1 * ((mat x1 τ)⁻¹)⁻¹).map (starRingEnd ℂ) := by
        rw [hinv, hGm, Matrix.nonsing_inv_nonsing_inv _ (hu τ), Matrix.map_mul, Matrix.map_mul]
      rw [e, map_conj_mulVec, normSq_star, ← normSq_star u]
      exact hposB τ (star u)
  have htr : ∀ n : ℕ, 1 ≤ n → n ≤ r → ∃ z : 𝓞 E, (G ^ n).trace - r = (g : E) * z := by
    intro n _ _
    have hm := Γo.pow_mem hγ n
    have := trace_sub_mem X g hg (γ ^ n) (hstab _ hm) (hunip _ hm)
    rwa [Units.val_pow_eq_pow_val] at this
  have hg' : (Real.exp (1 / 3) + 1) * r < g := by
    have h3 := ReciprocityTheory.MultiplicativeHeights.sb_exp_third_lt_two
    have hr' : (0 : ℝ) < r := by exact_mod_cast hr
    have hg3 : (3 * r : ℝ) < g := by exact_mod_cast hgr
    nlinarith
  have hU := ReciprocityTheory.MultiplicativeHeights.unipotent_holds E r g G Q htr hg' hQdet hop
  have hN : G - 1 = 0 := by
    refine hNC (G - 1) (fun v hv => ?_) (fun τ => ?_)
    · rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      exact X.L'.sub_mem (((hstab γ hγ).2 v).1 hv) hv
    · set S := ∑ a, ∑ b, ‖(Q τ.1 * (G.map τ.1 - 1) * (Q τ.1)⁻¹) a b‖ ^ 2 with hS
      have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hS1 : S < 1 := hU.2 τ.1
      refine ⟨Real.sqrt S, Real.sqrt_nonneg _, (Real.sqrt_lt' one_pos).2 (by rw [one_pow]; exact hS1),
        fun u => ?_⟩
      rw [Real.sq_sqrt hS0, hmaj, hmaj]
      have hmap : (G - 1).map τ.1 = G.map τ.1 - 1 := by
        rw [← RingHom.mapMatrix_apply, map_sub, map_one, RingHom.mapMatrix_apply]
      have hQτ : Q τ.1 = (mat x1 τ)⁻¹ := hQpos τ.1 τ.2
      have e2 : (mat x1 τ)⁻¹ *ᵥ ((G.map τ.1 - 1) *ᵥ u) =
          ((mat x1 τ)⁻¹ * (G.map τ.1 - 1) * ((mat x1 τ)⁻¹)⁻¹) *ᵥ ((mat x1 τ)⁻¹ *ᵥ u) := by
        rw [Matrix.nonsing_inv_nonsing_inv _ (hu τ)]
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hu τ),
          Matrix.mul_one]
      rw [hmap, e2, hS, hQτ]
      exact ReciprocityTheory.MultiplicativeHeights.sb_normSq_mulVec_le _ _
  exact Units.ext (sub_eq_zero.1 hN)

end GlobalTheory.SmallElement
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCharHalfSymplecticMovedFinitePointTrivia
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.MovedTrChar
open GlobalTheory.BotClassDict (finQ finStd)
open scoped TensorProduct

def secF (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  TensorProduct.map (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)) LinearMap.id

def secI (D : D7) : Ainf D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  TensorProduct.map (LinearMap.inl D.host.F (Ainf D.host.F) (Af D.host.F)) LinearMap.id

theorem decomp {D : D7} (a : AE D) : a = secI D (infPart D a) + secF D (finPart D a) := by
  induction a using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, LinearMap.map_zero, LinearMap.map_zero, add_zero]
  | add a b ha hb =>
    rw [RingHom.map_add (f := _), RingHom.map_add (f := _), LinearMap.map_add (f := _), LinearMap.map_add (f := _)]
    conv_lhs => rw [ha, hb]
    abel
  | tmul c e =>
    have hc : c = LinearMap.inl D.host.F (Ainf D.host.F) (Af D.host.F) (fstA D.host.F c) +
        LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F) (sndA D.host.F c) := by
      refine Prod.ext ?_ ?_
      · exact (add_zero _).symm
      · exact (zero_add _).symm
    conv_lhs => rw [hc]
    erw [TensorProduct.add_tmul]
    rfl

theorem infPart_secF {D : D7} (y : Af D.host.F ⊗[D.host.F] D.host.E) : infPart D (secF D y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => rw [LinearMap.map_zero, RingHom.map_zero]
  | add a b ha hb => rw [LinearMap.map_add (f := _), RingHom.map_add (f := _), ha, hb, add_zero]
  | tmul c e =>
    show fstA D.host.F (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F) c) ⊗ₜ[D.host.F] e = 0
    have : fstA D.host.F (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F) c) = 0 := rfl
    rw [this, TensorProduct.zero_tmul]

theorem finPart_secF {D : D7} (y : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (secF D y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => rw [LinearMap.map_zero, RingHom.map_zero]
  | add a b ha hb => rw [LinearMap.map_add (f := _), RingHom.map_add (f := _), ha, hb]
  | tmul c e =>
    show sndA D.host.F (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F) c) ⊗ₜ[D.host.F] e = c ⊗ₜ[D.host.F] e
    have : sndA D.host.F (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F) c) = c := rfl
    rw [this]

theorem finQ_eq {D : D7} (a : AE D) : finQ D a = (GlobalTheory.BotFormula.toAfE D).symm (finPart D a) := rfl

theorem recon_ex {D : D7} (q : Formalism.MainNotions.StandardLatticesGL3.AE D) : ∃ a : AE D, infPart D a = 0 ∧ finQ D a = q :=
  ⟨secF D (GlobalTheory.BotFormula.toAfE D q), infPart_secF _, by rw [finQ_eq, finPart_secF, RingEquiv.symm_apply_apply]⟩

theorem recon_uniq {D : D7} (a b : AE D) (h1 : infPart D a = infPart D b) (h2 : finQ D a = finQ D b) : a = b := by
  have h3 : finPart D a = finPart D b := by
    rw [finQ_eq, finQ_eq] at h2
    exact (GlobalTheory.BotFormula.toAfE D).symm.injective h2
  rw [decomp a, decomp b, h1, h3]

end GlobalTheory.MovedTrChar

namespace GlobalTheory.MovedTrChar
open GlobalTheory.BotClassDict (finQ finStd)
open scoped TensorProduct

theorem finPt_parts {D : D7} (S T : HSp D) (r : D.host.E) (z : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (i : Fin T.rank) (j : Fin S.rank) :
    infPart D (finPt (S := S) (T := T) rfl rfl r z i j) = 0 ∧
      finQ D (finPt (S := S) (T := T) rfl rfl r z i j) = -(Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹ * Formalism.MainNotions.StandardLatticesGL3.inc D (z i j)) := by
  have e0 : finPt (S := S) (T := T) rfl rfl r z i j = pairA D.host.F 0 1 ⊗ₜ[D.host.F] (-(r⁻¹ * z i j)) := rfl
  rw [e0]
  constructor
  · show fstA D.host.F (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (-(r⁻¹ * z i j)) = 0
    rw [show fstA D.host.F (pairA D.host.F 0 1) = 0 from rfl]
    erw [TensorProduct.zero_tmul]
  · have e1 : finPart D (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (-(r⁻¹ * z i j))) = finPart D (incA D (-(r⁻¹ * z i j))) := rfl
    rw [finQ_eq, e1, ← finQ_eq]
    erw [GlobalTheory.BotClassDict.finQ_inclR]
    rw [RingHom.map_neg, RingHom.map_mul]

theorem uComp {D : D7} (S T : HSp D) (hGS : HSpace.gram S = 1) (hGT : HSpace.gram T = 1)
    (x : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank) (y : Formalism.MainNotions.StandardLatticesGL3.GA D T.rank) (g : GA D S) (h : GA D T)
    (hg : IsFinPt S g x) (hh : IsFinPt T h y) (w : WO S T) (hw : ∀ i j, infPart D (w i j) = 0) (i : Fin T.rank) (j : Fin S.rank) :
    infPart D (actO S T g h w i j) = 0 ∧
      finQ D (actO S T g h w i j) =
        (((y : GL (Fin T.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin T.rank) (Fin T.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * w.map (finQ D) *
          (((x : GL (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin S.rank) (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D))) i j := by
  have hy : finStd T hGT h = y := GlobalTheory.BotClassDict.finStd_of_isFinPt T hGT hh
  have hx : finStd S hGS g⁻¹ = x⁻¹ := by rw [map_inv, GlobalTheory.BotClassDict.finStd_of_isFinPt S hGS hg]
  have eh : (Formalism.L2.Theta.mt T h).map (finQ D) = ((y : GL (Fin T.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin T.rank) (Fin T.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
    ext k l
    rw [Matrix.map_apply, ← hy, GlobalTheory.BotClassDict.finStd_apply]
    rfl
  have eg : (Formalism.L2.Theta.mt S g⁻¹).map (finQ D) =
      (((x : GL (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin S.rank) (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
    ext k l
    rw [Matrix.map_apply]
    have := GlobalTheory.BotClassDict.finStd_apply S hGS g⁻¹ k l
    rw [hx] at this
    exact this.symm
  have key : ∀ {R : Type} [Ring R] (f : AE D →+* R), (actO S T g h w).map f =
      (Formalism.L2.Theta.mt T h).map f * w.map f * (Formalism.L2.Theta.mt S g⁻¹).map f := by
    intro R _ f
    simp only [actO, Matrix.map_mul]
  constructor
  · have hw0 : w.map (infPart D) = 0 := by ext k l; exact hw k l
    have := congrFun (congrFun (key (infPart D)) i) j
    rw [Matrix.map_apply, hw0, Matrix.mul_zero, Matrix.zero_mul] at this
    exact this
  · have := congrFun (congrFun (key (finQ D)) i) j
    rw [Matrix.map_apply, eh, eg] at this
    exact this

end GlobalTheory.MovedTrChar

namespace GlobalTheory.MovedTrChar
open GlobalTheory.BotClassDict (finQ finStd)

theorem symplOH_neg_self {D : D7} (S T : HSp D) (u : WO S T) : symplOH S T (-u) u = 0 := by
  have h0 := Formalism.IndefR.Fin.symplOH_add_left S T u (-u) u
  rw [add_neg_cancel, GlobalTheory.FinTranslate.symplOH_self, zero_add, GlobalTheory.FinTranslate.symplOH_zero_left] at h0
  exact h0.symm

theorem ent_smul {D : D7} {m n : ℕ} (Y : Matrix (Fin m) (Fin m) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (Z : Matrix (Fin m) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D))
    (X : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (c : Formalism.MainNotions.StandardLatticesGL3.AE D) (i : Fin m) (j : Fin n) :
    (Y * (c • Z) * X) i j = c * (Y * Z * X) i j := by
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]


set_option maxHeartbeats 1000000 in
theorem psi_sympl_moved_eq_one : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∀ z : Matrix (Fin d) (Fin a) D.host.E,
  ∃ n : ℕ, 0 < n ∧ ∀ z', Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) z z' →
    ψ (symplOH S T (finPt hS hT r z') (actO S T g h (finPt hS hT r z) - finPt hS hT r z')) = 1 := by
  intro D ψ θ S T a d hS hT cc δ r hset x y g h hg hh z
  subst hS; subst hT
  obtain ⟨A0, hA0⟩ : ∃ A0, A0 = actO S T g h (finPt rfl rfl r z) := ⟨_, rfl⟩
  obtain ⟨N, hN, hC⟩ := _root_.GlobalTheory.FinCharInt.char_sympl_nsmul_int ψ hset.std.1.1 hset.std.1.2.1 S T A0
  obtain ⟨M, hM, hMint⟩ := _root_.GlobalTheory.NormSum.IdealDenom.exists_nat_mul_inv_mul_mem cc r
  refine ⟨N * M, by positivity, fun z' hz' => ?_⟩
  choose t ht hte using hz'
  obtain ⟨u, hu⟩ : ∃ u : WO S T, u = A0 - finPt rfl rfl r z' := ⟨_, rfl⟩
  choose v hv1 hv2 using fun i j => recon_ex (D := D) ((M : Formalism.MainNotions.StandardLatticesGL3.AE D) * (Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹ * t i j))
  have hNv : ∀ i j, (N • Matrix.of v : WO S T) i j = (N : AE D) * v i j := fun i j => by
    rw [Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul]
  have hmap : (finPt (S := S) (T := T) rfl rfl r z).map (finQ D) = (-(Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹)) • z.map (Formalism.MainNotions.StandardLatticesGL3.inc D) := by
    ext i j; rw [Matrix.map_apply, (finPt_parts S T r z i j).2, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, neg_mul]
  have huv : u = N • (Matrix.of v) := by
    ext i j
    have e1 := (uComp S T hset.gS hset.gT x y g h hg hh _ (fun i j => (finPt_parts S T r z i j).1) i j)
    have e2 := finPt_parts S T r z' i j
    apply recon_uniq
    · rw [hNv, map_mul, hv1, mul_zero, hu, Matrix.sub_apply, map_sub, hA0, e1.1, e2.1, sub_zero]
    · rw [hNv, map_mul, hv2]
      rw [hu, Matrix.sub_apply, map_sub]
      rw [hA0, e1.2, e2.2]
      rw [hmap]
      rw [ent_smul]
      rw [map_natCast]
      have h3 := hte i j
      rw [Matrix.sub_apply, Matrix.map_apply] at h3
      push_cast at h3 ⊢
      linear_combination (Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹) * h3
  have hself : symplOH S T (-u) u = 0 := symplOH_neg_self S T u
  have hsum : finPt rfl rfl r z' + u = A0 := by rw [hu]; abel
  have geq : actO S T g h (finPt rfl rfl r z) - finPt rfl rfl r z' = u := by subst hA0; exact hu.symm
  have h1 := Formalism.IndefR.Fin.symplOH_add_left S T (finPt rfl rfl r z') u u
  rw [hsum, GlobalTheory.FinTranslate.symplOH_self, add_zero] at h1
  rw [geq, ← h1, huv]
  exact hC _ (fun i j => hv1 i j) (fun i j => by rw [Matrix.of_apply, hv2]; exact hMint _ (ht i j))

end GlobalTheory.MovedTrChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFiniteOfComponents
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

set_option autoImplicit false

namespace GlobalTheory.CompFin

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}


omit [NumberField E] [IsCMField E] in
theorem castFrame_castFrame {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (x : Frame Ψ' r) :
    castFrame h (castFrame h.symm x) = x := rfl

theorem castFrame_mem_GG (X : Data E r) {Ψ : Finset (E →+* ℂ)} (h : X.Ψ = Ψ) (x : Frame X.Ψ r) :
    castFrame h x ∈ GG Ψ X.Gm X.p0 ↔ x ∈ X.dom := by
  subst h
  rfl

variable {U C : Type} [Group U] [MulAction U C] (M : TwoLevels E r U C)

theorem castFrame_mem_dom (c : C) (x : Frame (M.comp c).Ψ r) :
    castFrame (M.comp_Ψ c) x ∈ M.dom ↔ x ∈ (M.comp c).dom := by
  have := castFrame_mem_GG (M.comp c).toData (M.comp_Ψ c) x
  rw [M.comp_Gm c, M.comp_basePoint c] at this
  exact this

def toComp (c : C) : (C → M.dom → ℂ) →ₗ[ℂ] ((M.comp c).dom → ℂ) where
  toFun v x := v c ⟨castFrame (M.comp_Ψ c) x.1, (castFrame_mem_dom M c x.1).2 x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cusp_le_comap (ka : Wt M.Ψ r) (c : C) :
    M.cusp ka ≤ (Submodule.span ℂ ((fun f : Frame (M.comp c).Ψ r → ℂ => fun x : (M.comp c).dom => f x) ''
      (M.comp c).SS (castWt (M.comp_Ψ c) ka))).comap (toComp M c) := by
  unfold TwoLevels.cusp
  rw [Submodule.span_le]
  rintro _ ⟨F, hF, rfl⟩
  exact Submodule.subset_span ⟨_, hF c, rfl⟩

theorem toComp_inj (v w : C → M.dom → ℂ) (h : ∀ c, toComp M c v = toComp M c w) : v = w := by
  funext c y
  have hy : castFrame (M.comp_Ψ c).symm y.1 ∈ (M.comp c).dom :=
    (castFrame_mem_dom M c _).1 (by rw [castFrame_castFrame]; exact y.2)
  have := congrFun (h c) ⟨_, hy⟩
  exact this

end

end GlobalTheory.CompFin


open GlobalTheory.CompFin in
theorem GlobalTheory.cusp_finite_of_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite C] [MulAction U C] (M : TwoLevels E r U C) (ka : Wt M.Ψ r), (∀ c : C, FiniteDimensional ℂ (Submodule.span ℂ ((fun f : Frame (M.comp c).Ψ r → ℂ => fun x : (M.comp c).dom => f x) '' (M.comp c).SS (castWt (M.comp_Ψ c) ka)))) → Module.Finite ℂ (M.cusp ka) := by
  intro E _ _ _ r U C _ _ _ M ka hfin
  let S : (c : C) → Submodule ℂ ((M.comp c).dom → ℂ) := fun c => Submodule.span ℂ ((fun f : Frame (M.comp c).Ψ r → ℂ =>
    fun x : (M.comp c).dom => f x) '' (M.comp c).SS (castWt (M.comp_Ψ c) ka))
  have : ∀ c, Module.Finite ℂ (S c) := hfin
  let Φ : M.cusp ka →ₗ[ℂ] (∀ c, S c) := LinearMap.pi fun c =>
    ((toComp M c).domRestrict (M.cusp ka)).codRestrict (S c) fun v => cusp_le_comap M ka c v.2
  have hΦ : Function.Injective Φ := by
    intro v w hvw
    apply Subtype.ext
    apply toComp_inj M
    intro c
    have := congrArg Subtype.val (congrFun hvw c)
    exact this
  exact Module.Finite.of_injective Φ hΦ
end

