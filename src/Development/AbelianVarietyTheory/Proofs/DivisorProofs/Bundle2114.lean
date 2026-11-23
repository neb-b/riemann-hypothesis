module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumCMPreservesSchwartzHeisenber
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0258
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0126
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DiagonalLagrangianIntegralSiegelParabolicTransfo
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1452
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1998
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupremumConstantLogBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1691
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishing
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0001
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0002
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsEvalNeZeroOfTotalDegreeLt
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.FiniteDetAddSmulOneEqZero
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1877
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1882
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelWeilSectionLawDiagonalLagrangian
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.SiegelLawDblTargetF

theorem exists_gaf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (p : UG (cA σ) (incM F J)ᵀ) :
    ∃ h : GAF σ J, mtF σ J h = p.1.1 := by
  have hmem : p.1 ∈ HR (AF F) σ J := by
    show Formalism.UG.cT _ _ * _ * _ = _
    have e1 : ((p.1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).map (sigR (AF F) σ)) =
        (p.1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).map (cA σ) := by
      ext i j; exact (GlobalTheory.TransportHeisF.cA_eq_cAF σ _).symm
    have e2 : JR (AF F) J = (incM F Jᵀ)ᵀ := by ext i j; rfl
    have hp' : (p.1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))ᵀ * incM F Jᵀ *
        (p.1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).map (cA σ) = incM F Jᵀ := p.2
    unfold Formalism.UG.cT
    rw [e1, e2]
    have := congrArg Matrix.transpose hp'
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  exact ⟨⟨p.1, hmem⟩, rfl⟩

theorem two_isUnit (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    IsUnit (2 : AF F ⊗[F] E) := by
  have h := (IsUnit.mk0 (2 : F) two_ne_zero).map (algebraMap F (AF F ⊗[F] E))
  rwa [map_ofNat] at h

theorem char_det_one (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (α : GL (Fin n) (AF F ⊗[F] E) →* Circle) (a : GL (Fin n) (AF F ⊗[F] E))
    (ha : Matrix.GeneralLinearGroup.det a = 1) : α a = 1 :=
  MonoidHom.mem_ker.mp (_root_.GlobalTheory.GLGen.mem_of_det_eq_one (AF F ⊗[F] E) (_root_.GlobalTheory.StableRange.adeles_tensor_stableRange_one F E) n α.ker
    (fun i j hij t u hu => MonoidHom.mem_ker.mpr (GlobalTheory.glChar_transvection (two_isUnit F E) α i j hij t u hu)) a ha)

theorem lagr_law : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ (h : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) (t : GL (Fin nT) (AF F ⊗[F] E)),
          mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) = ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * t.1 →
          ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
            GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (ωd (1, h) f) = (χS (Matrix.GeneralLinearGroup.det t) : ℂ) * ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin nS) : ℝ) / 2) : ℝ) : ℂ) * GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd
  obtain ⟨α, hαc, hαr, hlaw⟩ := _root_.PositivityTheory.ThKW.lagrangian_integral_fundamental_domain F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd
  intro h t hht f hf
  by_cases h0 : ∀ g, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ g →
      GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) g = 0
  · rw [h0 _ (hωd.om_pres _ f hf), h0 f hf, mul_zero]
  push_neg at h0
  obtain ⟨f₀, hf₀, hne⟩ := h0
  have hsp := _root_.PositivityTheory.ThKW.lagrangian_integral_parseval F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd α hlaw f₀ hf₀ hne
  have hα : ∀ a : GL (Fin nT) (AF F ⊗[F] E), α a = χS (Matrix.GeneralLinearGroup.det a) := by
    rcases Nat.eq_zero_or_pos nT with hn0 | hpos
    · intro a
      have hd : Matrix.GeneralLinearGroup.det a = 1 := by
        ext; rw [Matrix.GeneralLinearGroup.val_det_apply]; subst hn0; simp
      rw [char_det_one F E nT α a hd, hd, map_one]
    obtain ⟨i0⟩ : Nonempty (Fin nT) := ⟨⟨0, hpos⟩⟩
    have hhec : IsHeckeCharF (α.comp (GlobalTheory.LeviOrigin.dgU nT i0) * χS⁻¹) := by
      refine ⟨?_, ?_⟩
      · exact (hαc.comp (GlobalTheory.LeviOrigin.continuous_dgU nT i0)).mul (hωd.hecS.1.inv)
      · intro x
        rw [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply, hωd.hecS.2 x, inv_one, mul_one,
          GlobalTheory.LeviOrigin.dgU_map (incAF F E) nT i0 x]
        exact hαr _
    have hν1 := _root_.GlobalTheory.HeckeSplitBase.heckeChar_eq_one_of_split F E σ B hB _ hhec (by
      intro e he x hx
      have h2 := hsp e he (GlobalTheory.LeviOrigin.dgU nT i0 x) (by
        intro k l
        rw [GlobalTheory.LeviOrigin.dgU_sub_one]
        split_ifs
        · exact hx
        · exact mul_zero _)
      rw [MonoidHom.mul_apply, MonoidHom.comp_apply, h2, GlobalTheory.LeviOrigin.det_dgU, MonoidHom.inv_apply,
        mul_inv_cancel])
    have hdg : ∀ x, α (GlobalTheory.LeviOrigin.dgU nT i0 x) = χS x := by
      intro x
      have := hν1 x
      rw [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply] at this
      exact mul_inv_eq_one.mp this
    intro a
    have hb : Matrix.GeneralLinearGroup.det (a * (GlobalTheory.LeviOrigin.dgU nT i0 (Matrix.GeneralLinearGroup.det a))⁻¹) = 1 := by
      rw [map_mul, map_inv, GlobalTheory.LeviOrigin.det_dgU, mul_inv_cancel]
    have h3 : α a = α (a * (GlobalTheory.LeviOrigin.dgU nT i0 (Matrix.GeneralLinearGroup.det a))⁻¹) *
        α (GlobalTheory.LeviOrigin.dgU nT i0 (Matrix.GeneralLinearGroup.det a)) := by
      rw [← map_mul, inv_mul_cancel_right]
    rw [h3, char_det_one F E nT α _ hb, one_mul]
    exact hdg _
  rw [hlaw h t hht f hf, hα t]

theorem main_law : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ),
        (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
          co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.ResEtaF χS nS →
      ∀ ωd : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ),
          Formalism.IndefR.DatumF.IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ omp : UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) × UG (cA σ) (incM F JB) →*
            Module.End ℂ ((κ → AF F) → ℂ),
          GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ωd omp →
      ∀ (p : UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ)) (t : GL (Fin nT) (AF F ⊗[F] E)),
        p.1.1 * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) = ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * t.1 →
      ∀ Φ ∈ schA F κ, omp (p, 1) Φ ∈ schA F κ ∧
        GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (omp (p, 1) Φ)) =
          (χS (Matrix.GeneralLinearGroup.det t) : ℂ) *
            ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
              (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin nS) : ℝ) / 2) : ℝ) : ℂ) *
            GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ JB ξ hξ κ _ co hco ν 𝓕 hν h𝓕 χS hχS rχS ωd hωd omp htr p t hpt Φ hΦ
  obtain ⟨h, hh⟩ := exists_gaf σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) p
  have hg : mtF σ JS 1 = ((1 : UG (cA σ) (incM F JB))⁻¹).1.1ᵀ := by
    first
      | (simp only [mtF, map_one, inv_one]; simp; done)
      | (simp [mtF, matHomF]; exact map_one _)
      | (simp [mtF, matHomF]; rfl)
  obtain ⟨hmem, heq⟩ := htr p 1 1 h hh hg Φ hΦ
  refine ⟨hmem, ?_⟩
  have hth := GlobalTheory.TransportHeisF.isThetaFunOF_thetaTr F E σ B hB nS (nT + nT) JS
    (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) hS (GlobalTheory.WeilSchrodinger.DblTargetF.isHermND_dblG hT) ξ₀ hξ₀ hσ hωd.std _ JB ξ
    rfl hξ κ co hco Φ hΦ
  exact (congrArg (GlobalTheory.LagrTheta.lagrInt ν 𝓕
    ((diagCols (Fin nT)).submatrix finSumFinEquiv.symm id)) heq).trans
    (lagr_law F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd h t (by rw [hh]; exact hpt) _ hth)

end GlobalTheory.SiegelLawDblTargetF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianCoordinateDualBasisVector
section
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CovTop.VolUp GlobalTheory.CovTop.VolUp.FrameBox
open Classical

namespace GlobalTheory.CovTop.VolUp.FrameBox

theorem boxCoord_boxVec (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ))
    (d : Ψ → Fin r → ℝ) (z : Fin r) (_hd : ∀ τ a, d τ a = 1 ∨ d τ a = -1) :
    ∀ j k, boxCoord z j (boxVec d z k) = if j = k then 1 else 0 := by
  rintro ⟨τ', ⟨⟨a', b'⟩, hj⟩⟩ ⟨τ, ⟨⟨a, b⟩, hk⟩⟩
  have hjk : ((τ', (⟨(a', b'), hj⟩ : {ab : Fin r × Fin r // ab ≠ (z, z)})) =
      (τ, (⟨(a, b), hk⟩ : {ab : Fin r × Fin r // ab ≠ (z, z)}))) ↔ τ' = τ ∧ a' = a ∧ b' = b := by
    constructor
    · intro h
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      exact ⟨h.1, h.2.1, h.2.2⟩
    · rintro ⟨rfl, rfl, rfl⟩; rfl
  simp only [hjk]
  simp only [boxCoord, boxVec, LinearMap.coe_comp, Function.comp_apply, Complex.reLm_coe, Complex.imLm_coe]
  simp only [entryL, LinearMap.restrictScalars_apply, ContinuousLinearMap.coe_coe, EuclideanSpace.proj, PiLp.toLp_apply]
  by_cases hτ : τ' = τ
  swap
  · split_ifs <;> simp_all
  subst hτ
  simp only [true_and, if_true]
  clear hjk
  split_ifs with h1 h1' h3 h3 h3 h3 h3 h3
  all_goals simp only [LinearMap.coe_comp, Function.comp_apply, Complex.reLm_coe, Complex.imLm_coe, entryL, LinearMap.restrictScalars_apply, ContinuousLinearMap.coe_coe, EuclideanSpace.proj, PiLp.toLp_apply, PiLp.proj_apply, boxEnt, if_true]
  all_goals rcases lt_trichotomy a b with h2 | rfl | h2
  all_goals (try simp only [lt_irrefl, if_false])
  all_goals (try simp only [h2, not_lt_of_gt h2, if_true, if_false])
  all_goals clear _hd
  all_goals (split_ifs with e1 e2 <;> (try obtain ⟨rfl, rfl⟩ := h1') <;> (try obtain ⟨rfl, rfl⟩ := e1) <;> (try obtain ⟨rfl, rfl⟩ := e2) <;> (try simp))
  all_goals (try (simp only [Fin.lt_iff_val_lt_val, Fin.ext_iff, Prod.ext_iff, ne_eq, Prod.mk.injEq] at *; omega))
  all_goals exact absurd ⟨rfl, rfl⟩ h3

end GlobalTheory.CovTop.VolUp.FrameBox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeMaxSquaredBound
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.LamCore

theorem absA_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) {B : ℝ} (hB : 0 ≤ B) (h : ∀ τ k, |(laOf Dw a n τ k : ℝ)| ≤ B) :
    ((GlobalTheory.LevGeo.absA Dw a : ℕ) : ℝ) ≤ (Module.finrank ℚ E : ℝ) * (((Dw.p + Dw.q : ℕ) : ℝ) * B) := by
  have hn : (0 : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have key : ∀ (b : E →+* ℂ) (i : ℕ), i < Dw.mult b → (a (b, i) : ℝ) ≤ B := by
    intro b i hi
    by_cases hb : b (H.rt : E) = H.rt0
    · have hp : i < Dw.p := by simpa [Datum.mult, hb] using hi
      have := h ⟨b, hb⟩ ⟨i, by omega⟩
      simp only [laOf, weightOf, ite_eq_left hp, Int.cast_add, Int.cast_natCast] at this
      linarith [le_abs_self ((a (b, i) : ℝ) + ((n / 2 : ℕ) : ℝ))]
    · have hq : i < Dw.q := by simpa [Datum.mult, hb] using hi
      have := h ⟨conjEmb b, conj_mem hb⟩ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩
      have e1 : ¬ (Dw.p + (Dw.q - 1 - i) < Dw.p) := by omega
      have e2 : Dw.q - 1 - (Dw.p + (Dw.q - 1 - i) - Dw.p) = i := by omega
      simp only [laOf, weightOf, ite_eq_right e1, e2, conjEmb_conjEmb, Int.cast_sub, Int.cast_neg, Int.cast_natCast] at this
      linarith [neg_abs_le (-(a (b, i) : ℝ) - ((n / 2 : ℕ) : ℝ))]
  unfold GlobalTheory.LevGeo.absA
  rw [Nat.cast_sum, ← NumberField.Embeddings.card E ℂ, ← nsmul_eq_mul, ← Finset.card_univ]
  refine Finset.sum_le_card_nsmul _ _ _ fun b _ => ?_
  rw [Nat.cast_sum]
  refine (Finset.sum_le_card_nsmul _ _ B fun (i : Fin (Dw.mult b)) _ => key b (i : Fin (Dw.mult b)) i.2).trans ?_
  rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ hB
  have : Dw.mult b ≤ Dw.p + Dw.q := by unfold Datum.mult; split_ifs <;> omega
  exact_mod_cast this

theorem collect {f r q L b X x Om w lam sc rd : ℝ} (hf : 8 ≤ f) (hr : 1 ≤ r) (_hq0 : 0 ≤ q) (hq : q ≤ r) (hL : 10 ≤ L)
    (hLx : L ≤ x) (hb : 1 ≤ b) (hZ : f * r * L ≤ X) (hOm : |Om| ≤ 3 * L) (hw0 : 0 ≤ w) (hw : w ≤ 10 * (f * r) * b)
    (h1 : lam ≤ ((1 + |Om|) / 2 + 2 * L + (2 * q + 1) * (6 * f + 48) * (2 * L)) * w)
    (h2 : sc ≤ 250 * f ^ 2 * r ^ 2 * (2 * L)) (h3 : rd ≤ 217 * (f * r * L) ^ 2) :
    2 * lam + 2 * sc + rd ≤ x ^ 4 * X ^ 2 * b := by
  have hfr : 1 ≤ f * r := by nlinarith
  have hZ0 : L ≤ f * r * L := by nlinarith
  have hfrX : f * r ≤ X := by nlinarith
  have hX : 1 ≤ X := hfr.trans hfrX
  have a1 : (2 * q + 1) * (6 * f + 48) ≤ (3 * r) * (12 * f) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have a2 : (2 * q + 1) * (6 * f + 48) * (2 * L) ≤ 72 * (f * r * L) := by nlinarith
  have a3 : (1 + |Om|) / 2 + 2 * L + (2 * q + 1) * (6 * f + 48) * (2 * L) ≤ 76 * X := by linarith
  have a4 : w ≤ 10 * X * b := hw.trans (by gcongr)
  have a5 : lam ≤ 76 * X * (10 * X * b) := h1.trans (mul_le_mul a3 a4 hw0 (by positivity))
  have a6 : (f * r * L) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (by linarith) hZ 2
  have a7 : (f * r) * (f * r * L) ≤ X * X := mul_le_mul hfrX hZ (by linarith) (by linarith)
  have a8 : X ^ 2 ≤ X ^ 2 * b := le_mul_of_one_le_right (by positivity) hb
  have a9 : (10 : ℝ) ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) (hL.trans hLx) 4
  have a10 : 10 ^ 4 * (X ^ 2 * b) ≤ x ^ 4 * (X ^ 2 * b) := mul_le_mul_of_nonneg_right a9 (by positivity)
  have a11 : 0 ≤ X ^ 2 * b := by positivity
  nlinarith

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem ne_bot_of_form {K K' R W : Type} [Field K] [NumberField K] [Field K'] [AddCommGroup R] [Module K R] [AddCommGroup W]
    [Module K W] [Module K' W] {C C' : Submodule K R} (hC : C' = C) [Module (𝓞 K) C'] {M : Submodule (𝓞 K) C'}
    (hs : Submodule.span K (M : Set C') = ⊤) {WK : Submodule K W} (e : C ≃ₗ[K] WK) {n : ℕ} {b : Fin n → W} (hb : ∀ k, b k ∈ WK)
    (hsp : Submodule.span K' (Set.range b) = ⊤) {y : W} (hy : y ≠ 0) : M ≠ ⊥ := by
  subst hC
  rintro rfl
  rw [Submodule.bot_coe, Submodule.span_zero_singleton] at hs
  have h3 : ∀ k, b k = 0 := fun k => by
    have h1 : e.symm ⟨b k, hb k⟩ ∈ (⊥ : Submodule K C') := by rw [hs]; exact Submodule.mem_top
    rw [Submodule.mem_bot, LinearEquiv.map_eq_zero_iff] at h1
    exact congrArg Subtype.val h1
  have h4 : Submodule.span K' (Set.range b) ≤ ⊥ := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact h3 k)
  exact hy (h4 (by rw [hsp]; exact Submodule.mem_top))


set_option maxHeartbeats 1000000 in
theorem latW_ne_bot (h : GramAt p i) : latW (p.T.U ((i : ℕ) + 1)) (Gk p i) ≠ ⊥ := by
  obtain ⟨-, -, hg, -, -, hs⟩ := h
  obtain ⟨y, -, hy⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hg
  obtain ⟨n, b, hb, -, -, -, hsp⟩ := p.fw.ks i
  exact ne_bot_of_form (cuspW_wtZ _ _) hs (p.fw.e i) hb hsp hy


set_option maxHeartbeats 1000000 in
theorem slopeMax_le (h6 : GlobalTheory.Published.TamagawaSpecialUnitary) {PP A : ℝ} (hR : RecTied D L) (hG : GramAt p i)
    (hN : HostNum D L PP A 1) (hW : WtNum p i PP) :
    slopeMax_sq (nrmK p.fw i) (latW (p.T.U ((i : ℕ) + 1)) (Gk p i)) ≤ L.sc.x ^ (2 * A + 4) * L.sc.b := by
  have hj : Formalism.L2.Pj.InR D ((i : ℕ) + 1) := ⟨by omega, i.2⟩
  obtain ⟨hLaws, hnorm⟩ := GlobalTheory.LevGeo.laws_of_coreJ D p.T _ p.fw.laws hj
  have hn : normW (p.T.U ((i : ℕ) + 1)) (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) (GlobalTheory.LevGeo.coreDict p.T.toCore ((i : ℕ) + 1))
      (Gk p i) = nrmK p.fw i := by
    funext σ f; exact hnorm _ σ f
  obtain ⟨_, χ, hχ, hOm, -, -⟩ := _root_.GlobalTheory.CovTop.Period.period_eq_kronecker D L p.T.Q p.fw.laws.pins.1 p.Del p.h0
  have hgood : GoodW (p.T.U ((i : ℕ) + 1)) (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1))
      (GlobalTheory.LevGeo.coreDict p.T.toCore ((i : ℕ) + 1)) (Gk p i) := ⟨by rw [hn]; exact hG.2.2.2.1, hG.2.2.2.2⟩
  have main := _root_.GlobalTheory.mumaxTop h6 D _ _ _ _ _ _ _ _ hLaws χ hχ (wtA (p.κ i)) (p.κ i).n hW.dom hgood (latW_ne_bot p i hG)
  rw [hn] at main
  refine main.trans ?_
  rw [hOm, p.fw.laws.pins.2.1.1, hW.cols]
  obtain ⟨-, hL, hLx, -⟩ := hN.big
  have hfd : fdeg D.host.E = D.R.f := by unfold fdeg; rw [hN.deg]; omega
  have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hN.f8
  have hr2 : 2 ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : 1 ≤ D.R.r)
  have hnV : (1 : ℝ) ≤ D.R.nV := by exact_mod_cast (by unfold Ranks.nV; omega : 1 ≤ D.R.nV)
  have hbL : L.sc.b = Real.exp L.sc.L := rfl
  have hb : 1 ≤ L.sc.b := by rw [hbL]; exact Real.one_le_exp (by linarith)
  have hx0 : 0 < L.sc.x := by linarith
  have hXb : L.sc.x ^ A ≤ L.sc.b := by simpa using hN.room
  have hP := hN.poly.2.2
  have hfr : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
  have hZ : (D.R.f : ℝ) * D.R.r * L.sc.L ≤ L.sc.x ^ A :=
    le_trans (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) hnV) (by linarith)) hP
  have ht : ((fdeg D.host.E * D.R.r * D.R.nV : ℕ) : ℝ) ≤ L.sc.b := by
    rw [hfd]; push_cast
    exact (le_mul_of_one_le_right (by positivity) (by linarith)).trans (hP.trans hXb)
  have hs : ((GlobalTheory.LevGeo.absA (dat p i) (wtA (p.κ i)) : ℕ) : ℝ) ≤ 8 * ((D.R.f : ℝ) * D.R.r) * L.sc.b := by
    have := absA_le (dat p i) (wtA (p.κ i)) (p.κ i).n (by positivity) hW.up
    rw [hW.sig.2.2, hN.deg] at this
    push_cast at this
    linarith
  have hs0 : (0 : ℝ) ≤ ((GlobalTheory.LevGeo.absA (dat p i) (wtA (p.κ i)) : ℕ) : ℝ) := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ ((fdeg D.host.E * D.R.r * D.R.nV : ℕ) : ℝ) := Nat.cast_nonneg _
  generalize ((GlobalTheory.LevGeo.absA (dat p i) (wtA (p.κ i)) : ℕ) : ℝ) = s at *
  generalize ((fdeg D.host.E * D.R.r * D.R.nV : ℕ) : ℝ) = t at *
  have hbb : L.sc.b ≤ (D.R.f : ℝ) * D.R.r * L.sc.b := le_mul_of_one_le_left (by linarith) hfr
  have hw : s + t + 1 ≤ 10 * ((D.R.f : ℝ) * D.R.r) * L.sc.b := by linarith
  have hlw : Real.log (s + t + 1) ≤ 2 * (2 * L.sc.L) := by
    refine (Real.log_le_log (by linarith) hw).trans ?_
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity), hbL, Real.log_exp]
    linarith [hN.logfr.1, Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)]
  have hg : ∀ k, 0 < D.host.g k := fun k => (D.host.g_prime k).pos
  have hM : 1 ≤ D.host.g 0 * D.host.g 1 := Nat.mul_pos (hg 0) (hg 1)
  have hlM : Real.log ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) ≤ 30 * (2 * L.sc.L) := by
    push_cast
    rw [Real.log_mul (by exact_mod_cast (hg 0).ne') (by exact_mod_cast (hg 1).ne')]
    linarith [hN.logg 0, hN.logg 1]
  have hd : 1 ≤ D.host.d := by rw [← p.fw.laws.pins.1.1]; exact p.T.Q.H.d_prime.pos
  have hl1 : Real.log ((fdeg D.host.E : ℝ) * D.R.r) ≤ 2 * L.sc.L := by rw [hfd]; linarith [hN.logfr.1]
  have hl2 : Real.log (dE D.host.E) ≤ 4 * (fdeg D.host.E : ℝ) * (2 * L.sc.L) := by
    rw [hfd]; unfold dE
    have : 0 ≤ (D.R.f : ℝ) * L.sc.L := by positivity
    linarith [hN.disc]
  have hl3 : Real.log (D.host.d : ℝ) ≤ 4 * (2 * L.sc.L) := by linarith [hN.logd]
  have n1 := (_root_.GlobalTheory.SupConstSize.supConst_size D.host.E D.R.r D.host.d _ (s + t + 1) (2 * L.sc.L) hr2 hd hM (by linarith) (by linarith)
    hl1 hlM hl2 hl3 hlw).2
  have n2 := _root_.GlobalTheory.LamSize.lamSup_le D.host.E D.R.r (dat p i).q D.host.d _ (ofRecord D L p.Del p.h0).logOm s t (2 * L.sc.L) (by omega) hd hM
    (by linarith) hs0 ht0 hl1 hlM hl2 hl3 hlw
  have n3 := (log_rd_le_fieldSz _).trans (hR.core_size_le p (by linarith))
  rw [hfd] at n1 n2
  have hq : ((dat p i).q : ℝ) ≤ D.R.r := by exact_mod_cast (by have := hW.sig.2.2; omega : (dat p i).q ≤ D.R.r)
  have e : L.sc.x ^ (2 * A + 4) = L.sc.x ^ 4 * (L.sc.x ^ A) ^ 2 := by
    rw [Real.rpow_add hx0, mul_comm 2 A, Real.rpow_mul hx0.le, mul_comm]
    norm_cast
  rw [e]
  exact collect hf hr (Nat.cast_nonneg _) hq hL hLx hb hZ hW.om (add_nonneg hs0 ht0) (by linarith) n2 n1 n3

theorem lamCore : GlobalTheory.CovTop.Hypotheses2 → Gram → Lifts fun Fm x _ ι p i _ A =>
    slopeMax_sq (nrmK p.fw i) (latW (p.T.U ((i : ℕ) + 1)) (Gk p i)) ≤ (Fm.L x ι).sc.x ^ A * (Fm.L x ι).sc.b := by
  intro hP hG
  refine Closed.imp (Closed.and hG (Closed.and (GlobalTheory.CovTop.Sizes.hostN 1) _root_.GlobalTheory.CovTop.WtShape.wtN)) ?_
  rintro eps Fm CH - ⟨⟨_, -, h1⟩, ⟨A, hA, h2⟩, ⟨_, -, h3⟩⟩
  obtain ⟨x0, h⟩ := h1.and (h2.and h3)
  refine ⟨2 * A + 4, by linarith, x0, fun x hx hle ι p hp i => ?_⟩
  obtain ⟨a, b, c⟩ := h x hx hle ι p hp
  exact slopeMax_le p i hP.p6 hp.2 (a i) (b i) (c i)

end GlobalTheory.CovTop.LamCore

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionsPairSumRatFnFamilyTensor
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem smallFam_pair_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (J : Type) (f : J → X.functionField) (w : J → ℝ), (∀ j, f j ∈ P.Bl 1 1 (Real.exp (-w j))) → SmallFam (P.L.tens P.A) f w := by
  intro k _ X _ p P J f w hf
  have e (c : (P.L.tens P.A).B.ι) (j : J) :
      f j * (((P.r c.1 * P.r' c.2 : X.functionFieldˣ)) : X.functionField) = P.loc 1 1 (f j) c.1 c.2 := by
    simp only [Pair.loc, Units.val_mul, zpow_one]; ring
  refine ⟨fun c => P.r c.1 * P.r' c.2, GlobalTheory.PtHtComb.isRatSec_tens P.hr P.hr', ?_, ?_⟩
  · intro x c hc j
    rw [e]
    exact (hf j).1 x c.1 c.2 hc.1 hc.2
  · intro σ y c hc j
    obtain ⟨hc₁, hc₂⟩ := mem_ptsIn_inf.1 hc
    have h := nu_eq k X p P 1 1 (f j) (hf j).1 σ y c.1 c.2 hc₁ hc₂
    have hb := (hf j).2 σ y
    rw [h] at hb
    rw [e]
    change _ * Real.exp (-((P.L.φ σ).φ c.1 y + (P.A.φ σ).φ c.2 y) / 2) ≤ _
    simpa using hb

end GlobalTheory.HSNef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineOpenFinitePresentationStalkKaehlerFrStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_affineOpen_finitePresentation_stalkKaehler_free_rank : ∀ (k : Type) [Field k] (X : Scheme.{0}) (p : X ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n p] (U : X.affineOpens) (x : X) (hx : x ∈ U.1), letI := (algX p U.1).toAlgebra; letI := ((X.presheaf.germ U.1 x hx).hom.comp (algX p U.1)).toAlgebra; Algebra.FinitePresentation k Γ(X, U.1) ∧ Module.Free (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] ∧ Module.Finite (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] ∧ Module.finrank (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] = n := by
  first | exact @GlobalTheory.SmoothStalk.smooth_stalk | exact GlobalTheory.SmoothStalk.smooth_stalk | (intros; apply GlobalTheory.SmoothStalk.smooth_stalk <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothExistsPointLiftSquareZeroLocalRingStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_exists_point_lift_squareZero_localRing : ∀ (U S : Scheme.{0}) (p : U ⟶ S) [Smooth p] (C : Type) [CommRing C] [IsLocalRing C] (I : Ideal C), I ^ 2 = ⊥ → ∀ (s : Sp C ⟶ S) (u₀ : Sp (C ⧸ I) ⟶ U), u₀ ≫ p = spMap (Ideal.Quotient.mk I) ≫ s → ∃ u : Sp C ⟶ U, spMap (Ideal.Quotient.mk I) ≫ u = u₀ ∧ u ≫ p = s := by
  first | exact @GlobalTheory.SmoothPtLift.exists_lift | exact GlobalTheory.SmoothPtLift.exists_lift | (intros; apply GlobalTheory.SmoothPtLift.exists_lift <;> assumption)
end

