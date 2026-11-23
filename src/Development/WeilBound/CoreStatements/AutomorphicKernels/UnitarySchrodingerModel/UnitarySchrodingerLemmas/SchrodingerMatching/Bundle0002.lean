module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.PsiPlaces
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerAdditivity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1659
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1861
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0072

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.MonoSch
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwMatch

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.SiegelND

theorem monoFock (D : D7) (n : ℕ) (V : HSp D) (θ : InfFam D) (l : D.what₂.Tau → ℝ)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : Mx D V.rank n → ℂ) (h : IsMonoFock θ V l s φ) :
    φ ∈ fockA θ V n l s := by
  obtain ⟨e, c, g, d, bs, gv, hp, rfl⟩ := h
  exact Submodule.subset_span ⟨_, g, GlobalTheory.CompanionTheory.WhitAdd.sb_of_pure hp, rfl⟩

def MonoSchPos : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D) (θ : InfFam D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ),
    (∀ τ, l τ ≠ 0) → (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) →
    ∀ φ : Mx D V.rank n → ℂ, IsMonoFock θ V l s φ → φ ∈ schwartzA θ V.rank n ∧ φ ∈ fockA θ V n l s

theorem monoSchPos : MonoSchPos := by
  intro D n V θ l s hl hs φ h
  refine ⟨?_, monoFock D n V θ l s φ h⟩
  obtain ⟨e, c, g, d, bs, gv, hp, rfl⟩ := h
  obtain ⟨f, hf⟩ := GlobalTheory.CompanionTheory.WhitAdd.exists_schwartz_polyGauss V l hl s hs (MvPolynomial.monomial e c)
  refine Submodule.subset_span ⟨f, g, GlobalTheory.CompanionTheory.WhitAdd.sb_of_pure hp, ?_⟩
  funext x
  rw [hf]
  rfl

def MonoSchStd : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ →
    ∀ φ : Mx D V.rank n → ℂ, IsMonoFock θ V l s φ → φ ∈ schwartzA θ V.rank n ∧ φ ∈ fockA θ V n l s

theorem monoSchStd : MonoSchStd := fun D n V _ _ θ _ _ _ l s _ _ hS φ h =>
  monoSchPos D n V θ l s (GlobalTheory.CompanionTheory.WhitAdd.par_ne_zero hS) hS.hs φ h

end PositivityTheory.PfSWUS.SwMatch

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.PsiVal
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwMatch

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.SiegelND

theorem exists_ext_infFam (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) :
    ∃ θ' : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ),
      (∀ φ, Formalism.MainNotions.StandardLattice.IsInfEmb φ (θ' φ)) ∧ ∀ τ, θ' (tauE D τ) = θ τ := by
  classical
  obtain ⟨θ₀, h₀⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  refine ⟨Function.extend (tauE D) θ θ₀, fun φ => ?_, fun τ => (GlobalTheory.MassLink.tauE_injective' D).extend_apply θ θ₀ τ⟩
  by_cases h : ∃ τ, tauE D τ = φ
  · obtain ⟨τ, rfl⟩ := h
    rw [(GlobalTheory.MassLink.tauE_injective' D).extend_apply θ θ₀ τ]
    exact hθ τ
  · rw [Function.extend_apply' θ θ₀ φ h]
    exact h₀ φ

theorem infFam_spec (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) :
    (∀ τ, Continuous (θ τ)) ∧
      (∀ τ z, θ τ (sigR (Ainf D.host.F) D.sp.cm.sig z) = starRingEnd ℂ (θ τ z)) ∧
      Function.Bijective fun (z : Ainf D.host.F ⊗[D.host.F] D.host.E) τ => θ τ z := by
  obtain ⟨θ', h', e⟩ := exists_ext_infFam D θ hθ
  obtain ⟨h1, h2, h3⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).2 θ' h'
  refine ⟨fun τ => e τ ▸ h1 _, fun τ z => e τ ▸ h2 _ z, ?_⟩
  have h0 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  let ι : D.what₂.Tau → {φ : D.host.E →+* ℂ // φ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD} :=
    fun τ => ⟨tauE D τ, (Formalism.L2.Theta.tauE_sqrtMinusD D τ).trans h0.symm⟩
  have hι : Function.Bijective ι :=
    ⟨fun a b h => GlobalTheory.MassLink.tauE_injective' D (congrArg Subtype.val h), fun φ => by
      obtain ⟨τ, hτ⟩ := GlobalTheory.MassLink.tauE_surj' D φ.1 (φ.2.trans h0)
      exact ⟨τ, Subtype.ext hτ⟩⟩
  have h4 := (hι.comp_right (γ := ℂ)).comp h3
  convert h4 using 2 with z
  funext τ
  exact (congrArg (fun t => t z) (e τ)).symm

theorem psiPlaces : PsiPlaces := by
  intro D n V ψ χ θ μ ω H l s ν Φ h
  obtain ⟨h1, h2, h3⟩ := infFam_spec D θ h.hθ
  exact ⟨h.hψ, h1, h3, h2, GlobalTheory.ResAniso.VacSchwartz.realPar_ne_zero D θ h.hθ ψ h.hψ l h.hl, h.hl⟩


open GlobalTheory.CompanionTheory.SiegelND.ThetaGlue in
theorem valueSide : ValueSide := by
  intro D r V ν hν φ β hβ μH 𝓕 hμ h𝓕
  have hrank : ∀ (δ : GL (Fin V.rank) D.host.E) (ξ : Matrix (Fin V.rank) (Fin r) D.host.E),
      (δ.1 * ξ).rank = ξ.rank := fun δ ξ =>
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 δ.isUnit)
  have hL := GlobalTheory.CompanionTheory.SplitGram.leftInv_subtypeSum V φ
    (fun x : Matrix (Fin V.rank) (Fin r) D.host.E => x.rank = r ∧ gramQ V x = β.1)
    (fun δ hδ ξ h => ⟨(hrank δ ξ).trans h.1, (GlobalTheory.CompanionTheory.SplitGram.gramQ_mul V hδ ξ).trans h.2⟩)
  have hI := average_eq_meanC V ν μH hν hμ 𝓕 h𝓕 _ hL
  have hS : HeckeCharacterZeroLocus.SiegelWeilU.thetaS D.host.F D.host.E D.sp.cm.sig V.rank V.gram (fun X => φ (tupOf X))
      {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE D.sp.cm.sig V.gram X = β.1} =
      fun h => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1},
        φ (GlobalTheory.SiegelFormula.invPt V h x.1) := by
    funext h
    refine (tsum_congr fun X => ?_).trans ((fibEquiv V β hβ).tsum_eq
      fun x => φ (GlobalTheory.SiegelFormula.invPt V h x.1))
    exact congrArg φ (tupOf_actW V h X.1)
  exact hI.trans (congrArg (HeckeCharacterZeroLocus.SiegelWeilU.meanC μH 𝓕) hS.symm)

end PositivityTheory.PfSWUS.SwMatch

end
end

