module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0174
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0322
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0357
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransfer
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0026
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0251
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0319
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.LeOfFiniteSplitNotSplitBauer

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComapRealSubfieldEqIffEqOrIsConjPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
noncomputable section

namespace GlobalTheory.PlacePair

theorem hostConj_eq (D : D7) (x : D.host.E) : D.host.conj x = IsCMField.complexConj D.host.E x :=
  D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])

theorem cO_cO (D : D7) (x : 𝓞 D.host.E) :
    IsCMField.ringOfIntegersComplexConj D.host.E (IsCMField.ringOfIntegersComplexConj D.host.E x) = x := by
  apply RingOfIntegers.ext
  rw [IsCMField.coe_ringOfIntegersComplexConj, IsCMField.coe_ringOfIntegersComplexConj]
  exact IsCMField.complexConj_apply_apply D.host.E (x : D.host.E)

theorem cO_algebraMap (D : D7) (a : 𝓞 (maximalRealSubfield D.host.E)) :
    IsCMField.ringOfIntegersComplexConj D.host.E
        (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) a) =
      algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) a :=
  (IsCMField.ringOfIntegersComplexConj_eq_self_iff D.host.E _).2 ⟨a, rfl⟩

theorem isConjPl_iff (D : D7) (P P' : PlE D.host) :
    IsConjPl D.host P P' ↔
      ∀ x : 𝓞 D.host.E, x ∈ P.asIdeal ↔ IsCMField.ringOfIntegersComplexConj D.host.E x ∈ P'.asIdeal := by
  constructor
  · intro h x
    exact h x _ (by rw [IsCMField.coe_ringOfIntegersComplexConj, hostConj_eq])
  · intro h x y hxy
    have : y = IsCMField.ringOfIntegersComplexConj D.host.E x := by
      apply RingOfIntegers.ext
      rw [hxy, hostConj_eq, IsCMField.coe_ringOfIntegersComplexConj]
    rw [this]; exact h x

theorem eq_or_eq_conj (D : D7) (P w : PlE D.host)
    (hw : w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) =
      P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E))) :
    w.asIdeal = P.asIdeal ∨
      w.asIdeal = P.asIdeal.comap (IsCMField.ringOfIntegersComplexConj D.host.E : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
  set Q : Ideal (𝓞 D.host.E) :=
    P.asIdeal.comap (IsCMField.ringOfIntegersComplexConj D.host.E : 𝓞 D.host.E →+* 𝓞 D.host.E) with hQ
  have hQp : Q.IsPrime := Ideal.comap_isPrime _ _
  by_contra hne
  push_neg at hne
  obtain ⟨h1, h2⟩ := hne
  have nle : ∀ I : Ideal (𝓞 D.host.E), I.IsPrime → w.asIdeal ≠ I → ¬ w.asIdeal ≤ I := fun I hI h hle =>
    h (w.isMaximal.eq_of_le hI.ne_top hle)
  obtain ⟨a, ha, haP⟩ := Set.not_subset.mp (nle P.asIdeal P.isPrime h1)
  obtain ⟨b, hb, hbQ⟩ := Set.not_subset.mp (nle Q hQp h2)
  have key : ∃ x ∈ w.asIdeal, x ∉ P.asIdeal ∧ x ∉ Q := by
    by_cases haQ : a ∈ Q
    · by_cases hbP : b ∈ P.asIdeal
      · refine ⟨a + b, w.asIdeal.add_mem ha hb, fun h => haP ?_, fun h => hbQ ?_⟩
        · simpa using P.asIdeal.sub_mem h hbP
        · simpa using Q.sub_mem h haQ
      · exact ⟨b, hb, hbP, hbQ⟩
    · exact ⟨a, ha, haP, haQ⟩
  obtain ⟨x, hx, hxP, hxQ⟩ := key
  have hxQ' : IsCMField.ringOfIntegersComplexConj D.host.E x ∉ P.asIdeal := hxQ
  have hfix : IsCMField.ringOfIntegersComplexConj D.host.E (x * IsCMField.ringOfIntegersComplexConj D.host.E x) =
      x * IsCMField.ringOfIntegersComplexConj D.host.E x := by
    rw [map_mul, cO_cO, mul_comm]
  obtain ⟨y, hy⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff D.host.E _).1 hfix
  have hyw : y ∈ w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := by
    rw [Ideal.mem_comap, hy]; exact w.asIdeal.mul_mem_right _ hx
  rw [hw, Ideal.mem_comap, hy] at hyw
  rcases P.isPrime.mem_or_mem hyw with h | h
  · exact hxP h
  · exact hxQ' h

theorem comap_eq_iff : ∀ (D : D7) (P P' : PlE D.host),
    P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) =
      P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) ↔
        (P = P' ∨ IsConjPl D.host P P') := by
  intro D P P'
  constructor
  · intro h
    rcases eq_or_eq_conj D P P' h.symm with e | e
    · exact Or.inl (HeightOneSpectrum.ext e.symm)
    · refine Or.inr ((isConjPl_iff D P P').2 fun x => ?_)
      rw [e, Ideal.mem_comap, RingHom.coe_coe, cO_cO]
  · rintro (rfl | h)
    · rfl
    · rw [isConjPl_iff] at h
      ext a
      rw [Ideal.mem_comap, Ideal.mem_comap, h, cO_algebraMap]

end GlobalTheory.PlacePair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjSplit
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeckeFrob

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

def conjSplit (s : SplitPlace L) : SplitPlace L := ⟨s.v, s.i.comp (IsCMField.complexConj L).toAlgHom⟩

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def IsLocMap {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (s : SplitPlace L)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L)
    (T : σ.V →ₗ[ℂ] (GAf L n → W)) : Prop :=
  ∀ x : GAf L n, TrivOutside {s.v} x → ∀ a,
    T (σ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) a) = NG.rt L n x (T a)

end

def twEig (w : HeightOneSpectrum (𝓞 L)) {n : ℕ} (α : Fin n → ℂˣ) : Multiset ℂ :=
  (Finset.univ.val.map fun i => ((α i : ℂ))⁻¹).map (· * ((normV w : ℕ) : ℂ) ^ (((1 - (n : ℝ)) / 2 : ℝ) : ℂ))

end GlobalTheory.HeckeFrob

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEvaluationIntertwinerCuspidalValues
section
open Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.ConjRowCuspGap

theorem gap_of_sign {D : D7} (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (τ : D.what₂.Tau) (a b : Fin D.R.r)
    (hab : a < b) (hne : epsS D.R a ≠ epsS D.R b) :
    100 * (D.R.r : ℝ) ^ 4 ≤ lamS D.R (D.hc τ) a - lamS D.R (D.hc τ) b := by
  obtain ⟨hr, hgp⟩ := hG
  have hkb := GlobalTheory.Core.Rk.HdNc.node_of_sign D.R a b hab hne
  have hbr : b.1 < D.R.r := b.2
  have hm2 := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  have hr' : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hstep : ∀ (i : Fin D.R.r) (hi : i.1 + 1 < D.R.r),
      lamS D.R (D.hc τ) ⟨i.1 + 1, hi⟩ < lamS D.R (D.hc τ) i := fun i hi =>
    (Formalism.MainNotions.S.Inh.aut_isHCParam_lamS D.R (D.hc τ)).1 (show i < ⟨i.1 + 1, hi⟩ by rw [Fin.lt_def]; simp)
  set j := b.1 - D.R.k with hj
  have hj1 : j + 1 < D.R.m := by omega
  have e1 : b = ⟨D.R.k - 1 + (j + 1), by omega⟩ := by ext; simp only []; omega
  have hac : a ≤ (⟨D.R.k - 1 + j, by omega⟩ : Fin D.R.r) := by
    rw [Fin.le_def]; simp only []; have : a.1 < b.1 := hab; omega
  have h1 := GlobalTheory.Core.Rk.HdNc.anti_of_step _ hstep _ _ hac
  have hg := hgp τ ⟨j, by omega⟩ hj1
  have hgR : (16 : ℝ) * (D.R.r : ℝ) ^ 19 ≤
      (((D.hc τ).b ⟨j + 1, hj1⟩ : ℚ) : ℝ) - (((D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ) := by
    exact_mod_cast hg
  rw [GlobalTheory.Core.Rk.HdNc.lamS_node D.R (D.hc τ) j (by omega) (by omega)] at h1
  rw [e1, GlobalTheory.Core.Rk.HdNc.lamS_node D.R (D.hc τ) (j + 1) hj1 (by omega)]
  have hr7 : (7 : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : 7 ≤ D.R.r)
  have h5 : (D.R.r : ℝ) ^ 5 ≤ (D.R.r : ℝ) ^ 19 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h4 : (0 : ℝ) ≤ (D.R.r : ℝ) ^ 4 := by positivity
  have h6 : 7 * (D.R.r : ℝ) ^ 4 ≤ (D.R.r : ℝ) ^ 5 := by
    rw [pow_succ]; nlinarith
  linarith

theorem gapGe_of_gapHyp {D : D7} (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (X : HidaSetting D) :
    GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) := by
  have key : ∀ (τ : D.what₂.Tau) (a b : Fin D.R.r), epsS D.R a ≠ epsS D.R b →
      100 * (D.R.r : ℝ) ^ 4 ≤ |lamS D.R (D.hc τ) a - lamS D.R (D.hc τ) b| := by
    intro τ a b hne
    have hp : (0 : ℝ) ≤ 100 * (D.R.r : ℝ) ^ 4 := by positivity
    rcases lt_trichotomy a b with h | h | h
    · have := gap_of_sign hG τ a b h hne
      rw [abs_of_nonneg (by linarith)]
      linarith
    · exact absurd (by rw [h]) hne
    · have := gap_of_sign hG τ b a h (Ne.symm hne)
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
  intro v a b hab
  rw [X.eps_eq, X.eps_eq] at hab
  rw [X.lam_eq, X.lam_eq]
  exact key _ _ _ hab

theorem conjMap_isCuspFun : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ u : (MP R).Vec, IsCuspFun (D.sp.Y 0) (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u) := by
  intro _ _ _ _ D G' _ _ Pl0 T A Ks _ _ _ R F X h t _ hG _ _ _ _ c _ Φ hΦ hcont u
  obtain ⟨ψ, hψ⟩ := hcont u
  have hgap := gapGe_of_gapHyp hG X
  obtain ⟨hd, hl, hH, hb, -⟩ := GlobalTheory.Core.Mi.seeData_of_gap D X hgap
  have hK : ∀ v, Formalism.MainNotions.S.IsKTypeOf (X.B.I.ε v) (X.B.σ v) (Formalism.QuantumDeterminants.lowK (X.B.I.ε v) (X.B.lam v))
      (Formalism.MainNotions.S.lowKSub (X.B.I.ε v) (X.B.lam v) (X.B.σ v)) := fun v =>
    GlobalTheory.Jet.MultGap.isKTypeOf_lowKSub _ _ _ _ _ (hd v).1 (hd v).2.1 fun a b hab =>
      (GlobalTheory.Dec.ProjCuspGap.two_mul_lt _ _ (hb v) (GlobalTheory.Dec.ProjCuspGap.rank_pos_of_ne _ hab)).trans_le (hgap v a b hab)
  have hL2 := ((GlobalTheory.Dec.CuspAllKType.cusp_all X.B X.dv _ hd hK (GlobalTheory.PinScale.one_le_g X) hb hl hH Φ hΦ).2
    (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))).1
  have hψc := GlobalTheory.ConjRowMultCusp.isCuspFn_of_contRep X hψ hL2
  have hY := GlobalTheory.ConjRowMultCusp.isCuspFun_of_isCuspFn_iota D X.B.I h X.B.μf ψ hψ.1 hψ.2.1 hψc
  have e : GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u = fun y => star (ψ (iotaX X h (y * t⁻¹))) := by
    funext y
    rw [GlobalTheory.ConjRowMult.conjMap_apply, GlobalTheory.ConjRowMult.contRepL_spec X hψ]
  rw [e]
  intro r C hC μ 𝓕 hμ h𝓕 g
  have hz : ∫ n in 𝓕, ψ (iotaX X h ((n : GA D (D.sp.Y 0)) * (g * t⁻¹))) ∂μ = 0 := hY r C hC μ 𝓕 hμ h𝓕 (g * t⁻¹)
  show ∫ n in 𝓕, star (ψ (iotaX X h ((n : GA D (D.sp.Y 0)) * g * t⁻¹))) ∂μ = 0
  simp only [mul_assoc]
  have := congrArg (starRingEnd ℂ) hz
  rw [← integral_conj, map_zero] at this
  exact this

end GlobalTheory.ConjRowCuspGap

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugatedIntertwinerEquivariantRealPlaceStatement
section
public section

alias GlobalTheory.T.conjugated_intertwiner_equivariant_real_place :=
  GlobalTheory.ConjEquivRealSee.conjMap_update_real_see
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousMapRep
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.HeightCounting.PhtExt

variable {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut}

theorem continuous_mapRep {Γ : Type} [Group Γ] [TopologicalSpace Γ] {A B : Type} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] {a : ℕ} (f : A →+* B) (hf : Continuous f) (ρ : Γ →* GL (Fin a) A)
    (hρ : Continuous fun g => ((ρ g : GL (Fin a) A) : Matrix (Fin a) (Fin a) A)) :
    Continuous fun g => ((mapRep f ρ g : GL (Fin a) B) : Matrix (Fin a) (Fin a) B) := by
  have : (fun g => ((mapRep f ρ g : GL (Fin a) B) : Matrix (Fin a) (Fin a) B)) =
      fun g => ((ρ g : GL (Fin a) A) : Matrix (Fin a) (Fin a) A).map f := by
    funext g; rfl
  rw [this]
  exact hρ.matrix_map hf

end GlobalTheory.HeightCounting.PhtExt

namespace GlobalTheory.HeightCounting.PhtExt

variable {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut}

noncomputable def ext (Wd₀ : WDSide D T) : WDSide D T :=
  { Wd₀ with
    IsdRW := fun l _ ι a r w =>
      (Continuous fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) ∧ Wd₀.IsdRW l ι r w
    wdOf_unrL := fun l _ ι _ r w hw hc hd => Wd₀.wdOf_unrL l ι r w hw hc hd.2
    wdOf_mono0L := fun l _ ι _ r w hw hc hd => Wd₀.wdOf_mono0L l ι r w hw hc hd.2
    loc := by
      intro l _ ι w hw O _ _ _ Bw hB φ hφ
      obtain ⟨h1, h2⟩ := Wd₀.loc l ι w hw O Bw hB φ hφ
      have hφc : Continuous φ := by
        have e : (φ : O → Qbar l) = fun x => ((Bw.toLL x : ↥Bw.LL.1) : Loc.Om l) := funext hφ
        rw [e]
        unfold LocBridge.toLL
        exact continuous_subtype_val.comp (continuous_subtype_val.comp Bw.eO_cont)
      refine ⟨fun m ρ hρ => ?_, fun LL' hLL' m ρ hρ => ?_⟩
      · obtain ⟨c1, c2, c3, c4⟩ := h1 m ρ hρ
        exact ⟨c1, (and_iff_right (continuous_mapRep φ hφc ρ hρ)).trans c2, c3, c4⟩
      · have hf : Continuous (algebraMap ↥LL'.1 (Qbar l)) := continuous_subtype_val
        obtain ⟨c1, c2, c3, c4⟩ := h2 LL' hLL' m ρ hρ
        exact ⟨c1, (and_iff_right (continuous_mapRep _ hf ρ hρ)).trans c2, c3, c4⟩ }

theorem exists_phtOn_all : PhtCmp → ∀ (D : D7) (fr : OmFrame D) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), WDSide D T →
    ∃ Wd : WDSide D T, PhtOn Wd fr fun _ _ _ _ => True := by
  intro hP D fr T Wd₀
  exact ⟨ext Wd₀, ⟨fun l _ ι a r τ w _ hw hd => (hP D fr T Wd₀).card l ι a r τ w hd.1 hw hd.2⟩⟩

end GlobalTheory.HeightCounting.PhtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualModClassLatticeEquivQuotientStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_mod_class_lattice_equiv_quotient : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u, DiscCl (D := I.rec7 l Z) (u := u) := by
  first | exact @GlobalTheory.Mem.Col2.TC.disc_cl | exact GlobalTheory.Mem.Col2.TC.disc_cl | (intros; apply GlobalTheory.Mem.Col2.TC.disc_cl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvRoots
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

section CapelliMinorMembership

variable (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw)

def piCoef (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (u : Formalism.IndefR.NX.U D.nd) : ↥D.LL0 :=
  (Nat.card (Formalism.IndefR.NX.U D.nd) : ↥D.LL0)⁻¹ * (((psiUOf D.nd (NX.xiRed D) θ u)⁻¹ : (↥D.LL0)ˣ) : ↥D.LL0)

def eLop (j : ℕ) : Module.End D.what₂.LL (S.WL j) :=
  ∑ᶠ g : G0g D.nd, ((D.nexp.eLL0 g : ↥D.LL0) : D.what₂.LL) • actL D S j g

def piLop (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (j : ℕ) : Module.End D.what₂.LL (S.WL j) :=
  ∑ᶠ u : Formalism.IndefR.NX.U D.nd, ((piCoef D θ u : ↥D.LL0) : D.what₂.LL) • actL D S j (u : G0g D.nd)


open Classical in
def evRoots (In : RatIn D S) (j k : ℕ) (P : PlE D.host) : Finset ↥D.LL0 :=
  (Finset.univ.filter fun σ : D.what₂.FT => D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ).image fun σ => In.eig j σ k P

def evPol (In : RatIn D S) (j k : ℕ) (P : PlE D.host) : Polynomial ↥D.LL0 :=
  ∏ r ∈ evRoots D S In j k P, (X - C r)

def phiLop (In : RatIn D S) (j k : ℕ) (P : PlE D.host) : Module.End D.what₂.LL (S.WL j) :=
  aeval (In.hL j k P) ((evPol D S In j k P).map (algebraMap ↥D.LL0 D.what₂.LL))

def hLT (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host) :
    Module.End (FractionRing (T.O i)) (FmT D T S i j b) :=
  (Module.End.baseChangeHom S.Ks (KT D T i b) ↥(WKr D S j) (hLr D S In j k P) :
    Module.End (KT D T i b) (KT D T i b ⊗[S.Ks] ↥(WKr D S j)))

def piKop (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) : Module.End (FractionRing (T.O i)) (FmT D T S i j b) :=
  ∑ᶠ u : Formalism.IndefR.NX.U D.nd, readT D T i b (piCoef D In.θ u) • (actGT D T S In.rho In.chi i j b (u : G0g D.nd)).toLinearMap

def phiKop (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host) :
    Module.End (FractionRing (T.O i)) (FmT D T S i j b) :=
  aeval (hLT D T S In i j b k P) ((evPol D S In j k P).map (readT D T i b))

theorem hkT_eq (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host) :
    hkT D T S In i j b k P = (algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i)) ^ k • hLT D T S In i j b k P :=
  rfl

end CapelliMinorMembership

end GlobalTheory.HeightCounting.FormsStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateSplitPlaceAndUniformizer
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.SplitExConj

theorem exists_splitPlace_conj_unif : ∀ (D : D7), (∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) :=
  fun D => GlobalTheory.SplitConjPlace.splitEx_all D

end GlobalTheory.SplitExConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordinateModelOfAlgWeight
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutQuot.Model

theorem isIrreducible_of_linearEquiv {F G V W : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] {ρ : Representation F G V} {σ : Representation F G W} (κ : V ≃ₗ[F] W)
    (h : ∀ g v, κ (ρ g v) = σ g (κ v)) (hρ : ρ.IsIrreducible) : σ.IsIrreducible := by
  let E : Subrepresentation ρ ≃o Subrepresentation σ :=
    { toFun := fun S => ⟨S.toSubmodule.comap κ.symm.toLinearMap, fun g w hw => by
        obtain ⟨v, rfl⟩ := κ.surjective w
        have hv : v ∈ S.toSubmodule := κ.symm_apply_apply v ▸ hw
        simpa [← h] using S.apply_mem_toSubmodule g hv⟩
      invFun := fun T => ⟨T.toSubmodule.comap κ.toLinearMap, fun g v hv => by
        show κ (ρ g v) ∈ T.toSubmodule
        rw [h]
        exact T.apply_mem_toSubmodule _ hv⟩
      left_inv := fun S => Subrepresentation.toSubmodule_injective (by ext v; simp)
      right_inv := fun T => Subrepresentation.toSubmodule_injective (by ext v; simp)
      map_rel_iff' := fun {S T} => ⟨fun hh v hv => by
        have : κ.symm (κ v) ∈ S.toSubmodule := (κ.symm_apply_apply v).symm ▸ hv
        have h2 : κ.symm (κ v) ∈ T.toSubmodule := hh this
        exact κ.symm_apply_apply v ▸ h2, fun hh v hv => hh hv⟩ }
  exact E.isSimpleOrder_iff.1 hρ

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def conjRep {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (e : W ≃ₗ[ℂ] W')
    (ρ : Representation ℂ (GQ L n) W) : Representation ℂ (GQ L n) W' where
  toFun γ := e.toLinearMap ∘ₗ ρ γ ∘ₗ e.symm.toLinearMap
  map_one' := by ext x; simp
  map_mul' γ δ := by ext x; simp

theorem conjRep_apply {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (e : W ≃ₗ[ℂ] W')
    (ρ : Representation ℂ (GQ L n) W) (γ : GQ L n) (x : W') : conjRep e ρ γ x = e (ρ γ (e.symm x)) := rfl

theorem isAlgWeight_conjRep {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (e : W ≃ₗ[ℂ] W')
    (ρ : Representation ℂ (GQ L n) W) (h : IsAlgWeight L n ρ) : IsAlgWeight L n (conjRep e ρ) := by
  obtain ⟨hfd, ι, i1, i2, b, P, hP⟩ := h
  refine ⟨LinearEquiv.finiteDimensional e, ι, i1, i2, b.map e, P, fun γ γ₀ hγ => ?_⟩
  rw [← hP γ γ₀ hγ]
  ext i j
  simp [LinearMap.toMatrix_apply, conjRep_apply]

theorem exists_model : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n),
    ∃ m : GlobalTheory.AutQuot.AlgWtM L n, a.Iso m.toAlgWt := by
  intro L _ _ _ n a
  haveI : FiniteDimensional ℂ a.W := a.alg.1
  let e : a.W ≃ₗ[ℂ] (Fin (Module.finrank ℂ a.W) → ℂ) := (Module.finBasis ℂ a.W).equivFun
  refine ⟨⟨Module.finrank ℂ a.W, conjRep e a.ρ, isAlgWeight_conjRep e a.ρ a.alg,
    isIrreducible_of_linearEquiv e (fun γ x => by simp [conjRep_apply]) a.irr⟩, e, fun γ x => ?_⟩
  show e (a.ρ γ x) = conjRep e a.ρ γ (e x)
  simp [conjRep_apply]

end GlobalTheory.AutQuot.Model

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpanEqOneModOfSplitsInRayClassFieldStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_span_eq_one_mod_of_splits_in_rayClassField : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (𝔮 : Ideal (𝓞 K)),
    GlobalTheory.Mem.Fld.IsRayField K L 𝔮 → ∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔮 →
      (𝔭.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L →
        ∃ π : 𝓞 K, 𝔭.asIdeal = Ideal.span {π} ∧ π - 1 ∈ 𝔮 := by
  first | exact @GlobalTheory.Mem.RaySplit.exists_span_eq_of_splits | exact GlobalTheory.Mem.RaySplit.exists_span_eq_of_splits | (intros; apply GlobalTheory.Mem.RaySplit.exists_span_eq_of_splits <;> assumption)
end

