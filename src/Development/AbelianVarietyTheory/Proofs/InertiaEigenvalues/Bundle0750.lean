module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0640
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0636
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1417
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0382
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0367
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0616
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0220
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameReductionEqOneOfFrameMatrixCongruentOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

namespace GlobalTheory.RedAt

theorem redFn_finE_eq_one : ∀ (D : D7) (W : HSp D) (β : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (k : GA D W) (PP : Pl D.host.E), finE W k ∈ St β → (∀ a b, Valued.v (GlobalTheory.StdFrames.cpt PP (((HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) - 1) a b)) < 1) → redFn β PP (finE W k) = 1 := by
  intro D W β k PP hk hv
  obtain ⟨y, hy⟩ := hk
  have hyv : (Formalism.L2.DIV.intGL _ _ _ y).val
      = (HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val :
          Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) := by
    have h2 : Formalism.L2.DIV.intGL _ _ _ y = β⁻¹ * finE W k * β := by
      rw [← hy]; simp [Formalism.L2.DIV.frGL, MulAut.conj_apply, mul_assoc]
    rw [h2]; rfl
  rw [← hy, GlobalTheory.LiftLevel.redFn_eq_one_iff]
  intro i j
  rw [GlobalTheory.AdIsom.resS_eq_zero_iff_cpt]
  have := hv i j
  rw [← hyv] at this
  convert this using 3
  simp [Matrix.sub_apply, Matrix.one_apply, Formalism.L2.DIV.intGL, Formalism.UG.bc]
  split_ifs <;> simp

end GlobalTheory.RedAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodToralOfIsSubquotientProdIrr
section
open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT

namespace GlobalTheory.RecT

theorem geometricLemma_holds : GlobalTheory.Published.GeometricLemma :=
  GlobalTheory.geometricLemma_of_filtration GlobalTheory.bernsteinZelevinskyFiniteness_holds GlobalTheory.geometricLemmaFiltration_holds

theorem good_toral_of_isSubquotient_prodIrr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (t : ℕ) (y : Fin t → IrrGL (k := k)) (x : IrrGL (k := k)) (hd : ∑ i, (y i).1 = x.1),
    IsSubquotient x.rep (prodIrr y hd) → (Good x → ∀ i, Good (y i)) ∧ (Toral x → ∀ i, Toral (y i)) ∧
      ((∀ i, Good (y i)) → Good x) ∧ ((∀ i, Toral (y i)) → Toral x) := by
  intro k _ _ _ _ t y x hd hsq
  have hG := geometricLemma_holds
  have hBZ := GlobalTheory.bernsteinZelevinskyFiniteness_holds
  choose s hs using fun i => GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport hBZ hG (y i)
  have hx : HasSupport x.rep (∑ i, s i) :=
    GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr hs x.2.rep.irr hsq

  have down : ∀ P : IrrGL (k := k) → Prop, (∃ u, HasSupport x.rep u ∧ ∀ z ∈ u, P z) →
      ∀ i, ∃ u, HasSupport (y i).rep u ∧ ∀ z ∈ u, P z := by
    rintro P ⟨u, hu, hP⟩ i
    have := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG hBZ hu hx
    exact ⟨s i, hs i, fun z hz => hP z (this ▸ Multiset.mem_sum.2 ⟨i, Finset.mem_univ _, hz⟩)⟩

  have up : ∀ P : IrrGL (k := k) → Prop, (∀ i, ∃ u, HasSupport (y i).rep u ∧ ∀ z ∈ u, P z) →
      ∃ u, HasSupport x.rep u ∧ ∀ z ∈ u, P z := by
    intro P h
    choose u hu hP using h
    refine ⟨∑ i, u i, GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr hu x.2.rep.irr hsq, fun z hz => ?_⟩
    obtain ⟨i, -, hz⟩ := Multiset.mem_sum.1 hz
    exact hP i z hz
  exact ⟨down _, down _, up _, up _⟩

end GlobalTheory.RecT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralGLPullbackContinuousRingEquiv
section
open IsDedekindDomain NumberField
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IntegralPullback

open Filter Topology ValuativeRel

theorem valued_le_one_of_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (c : v.adicCompletion F ≃+* w.adicCompletion E) (hc : Continuous c) (z : v.adicCompletion F)
    (hz : Valued.v (c z) ≤ 1) : Valued.v z ≤ 1 := by
  by_contra h
  rw [not_le] at h
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at h
  have hcz : c z ≠ 0 := (map_ne_zero c).mpr hz0

  have hinv : Valued.v z⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ h
  have ht : Tendsto (fun n : ℕ => (c z⁻¹) ^ n) atTop (𝓝 0) := by
    have := (hc.tendsto 0).comp (Valued.tendsto_zero_pow_of_v_lt_one hinv)
    simpa [Function.comp_def, map_pow] using this

  have h1 : 1 ≤ Valued.v (c z⁻¹) := by
    rw [map_inv₀]
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (c z)⁻¹ * Valued.v (c z) := by
          rw [← map_mul, inv_mul_cancel₀ hcz, map_one]
      _ ≤ Valued.v (c z)⁻¹ * 1 := by gcongr
      _ = Valued.v (c z)⁻¹ := mul_one _
  have hU : {y : w.adicCompletion E | Valued.v y < 1} ∈ 𝓝 (0 : w.adicCompletion E) :=
    Valued.mem_nhds_zero.mpr ⟨1, fun y hy => by simpa using hy⟩
  obtain ⟨n, hn⟩ := (ht.eventually_mem hU).exists
  have hn' : Valued.v ((c z⁻¹) ^ n) < 1 := hn
  rw [map_pow] at hn'
  exact absurd hn' (not_lt.mpr (one_le_pow₀ h1))

theorem mem_integer_iff {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)}
    (z : w.adicCompletion E) :
    z ∈ (valuation (w.adicCompletion E)).integer ↔ Valued.v z ≤ 1 := by
  rw [Valuation.mem_integer_iff, ← Valuation.vle_one_iff (valuation (w.adicCompletion E))]
  show Valued.v z ≤ Valued.v 1 ↔ _
  rw [map_one]

private theorem mem_KO_of_integral_entries' {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} {n : ℕ} (A : GL (Fin n) (v.adicCompletion F))
    (h1 : ∀ i j, (A : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈
      (valuation (v.adicCompletion F)).integer)
    (h2 : ∀ i j, ((A⁻¹ : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ (valuation (v.adicCompletion F)).integer) :
    A ∈ GlobalTheory.SplitWeil.KO (v.adicCompletion F) (Fin n) := by

  let P : Matrix (Fin n) (Fin n) (valuation (v.adicCompletion F)).integer :=
    Matrix.of fun i j => ⟨_, h1 i j⟩
  let Q : Matrix (Fin n) (Fin n) (valuation (v.adicCompletion F)).integer :=
    Matrix.of fun i j => ⟨_, h2 i j⟩
  let f := algebraMap (valuation (v.adicCompletion F)).integer (v.adicCompletion F)
  have hP : P.map f = (A : Matrix (Fin n) (Fin n) _) := by
    ext i j
    simp only [P, f, Matrix.map_apply, Matrix.of_apply, Algebra.algebraMap_ofSubsemiring_apply]
  have hQ : Q.map f = ((A⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) := by
    ext i j
    simp only [Q, f, Matrix.map_apply, Matrix.of_apply, Algebra.algebraMap_ofSubsemiring_apply]
  have inj : ∀ X Y : Matrix (Fin n) (Fin n) (valuation (v.adicCompletion F)).integer,
      X.map f = Y.map f → X = Y := by
    intro X Y h
    exact Matrix.ext fun i j => Subtype.ext (congrFun (congrFun h i) j)
  have hPQ : P * Q = 1 := inj _ _ (by
    rw [Matrix.map_mul, Matrix.map_one f (map_zero f) (map_one f), hP, hQ]
    exact A.mul_inv)
  have hQP : Q * P = 1 := inj _ _ (by
    rw [Matrix.map_mul, Matrix.map_one f (map_zero f) (map_one f), hP, hQ]
    exact A.inv_mul)
  unfold GlobalTheory.SplitWeil.KO
  refine MonoidHom.mem_range.mpr ⟨⟨P, Q, hPQ, hQP⟩, ?_⟩
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.map_apply]
  exact congrFun (congrFun hP i) j

private theorem entry_mem_integer_of_map_mem_KO {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (c : v.adicCompletion F ≃+* w.adicCompletion E) (hc : Continuous c) {n : ℕ}
    (M : GL (Fin n) (v.adicCompletion F))
    (hM : Matrix.GeneralLinearGroup.map c.toRingHom M ∈ GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n))
    (i j : Fin n) :
    (M : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈
      (valuation (v.adicCompletion F)).integer := by
  unfold GlobalTheory.SplitWeil.KO at hM
  obtain ⟨C, hC⟩ := MonoidHom.mem_range.mp hM
  rw [GlobalTheory.IntegralPullback.mem_integer_iff]
  apply valued_le_one_of_map c hc
  rw [← GlobalTheory.IntegralPullback.mem_integer_iff]
  have hij := congrArg (fun g : GL (Fin n) (w.adicCompletion E) =>
    (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) hC
  simp only [Matrix.GeneralLinearGroup.map_apply] at hij
  have : c ((M : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) =
      ((C : Matrix (Fin n) (Fin n) (valuation (w.adicCompletion E)).integer) i j :
        w.adicCompletion E) := hij.symm
  rw [this]
  exact ((C : Matrix (Fin n) (Fin n) (valuation (w.adicCompletion E)).integer) i j).2

theorem mem_KO_of_map : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (c : v.adicCompletion F ≃+* w.adicCompletion E), Continuous c → ∀ {n : ℕ} (A : GL (Fin n) (v.adicCompletion F)), Matrix.GeneralLinearGroup.map c.toRingHom A ∈ GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) → A ∈ GlobalTheory.SplitWeil.KO (v.adicCompletion F) (Fin n) := by
  intro F E _ _ _ _ v w c hc n A hA
  have hAinv : Matrix.GeneralLinearGroup.map c.toRingHom A⁻¹ ∈
      GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) := by
    rw [map_inv]
    exact inv_mem hA
  exact mem_KO_of_integral_entries' A (entry_mem_integer_of_map_mem_KO c hc A hA) (entry_mem_integer_of_map_mem_KO c hc A⁻¹ hAinv)

end GlobalTheory.IntegralPullback
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocMemKOneOfSame
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain
open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT GlobalTheory.HeightCounting
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.UniDepthZero

theorem algHom_eq_or_conj {L K : Type} [Field L] [NumberField L] [IsCMField L] [Field K] [Algebra (maximalRealSubfield L) K]
    (φ ψ : L →ₐ[(maximalRealSubfield L)] K) : φ = ψ ∨ φ = ψ.comp (IsCMField.complexConj L).toAlgHom := by
  let e : L ≃ₐ[(maximalRealSubfield L)] ψ.fieldRange := AlgEquiv.ofInjectiveField ψ
  haveI : Normal (maximalRealSubfield L) ψ.fieldRange := Normal.of_algEquiv e
  have hR : φ.fieldRange = ψ.fieldRange := by
    have h := AlgHom.fieldRange_of_normal (E := ψ.fieldRange) (φ.comp e.symm.toAlgHom)
    rw [← h]
    ext x
    simp only [AlgHom.mem_fieldRange, AlgHom.comp_apply]
    constructor
    · rintro ⟨y, rfl⟩; exact ⟨e y, by simp⟩
    · rintro ⟨y, rfl⟩; exact ⟨_, rfl⟩
  have hmem : ∀ z, φ z ∈ ψ.fieldRange := fun z => hR ▸ ⟨z, rfl⟩
  let g₀ : L →ₐ[(maximalRealSubfield L)] L := e.symm.toAlgHom.comp (φ.codRestrict ψ.fieldRange.toSubalgebra hmem)
  have hg₀ : ∀ z, ψ (g₀ z) = φ z := fun z => by
    have := congrArg Subtype.val (e.apply_symm_apply ⟨φ z, hmem z⟩)
    exact this
  let σ : L ≃ₐ[(maximalRealSubfield L)] L := AlgEquiv.ofBijective g₀ (Algebra.IsAlgebraic.algHom_bijective g₀)
  have hσ : ∀ z, ψ (σ z) = φ z := hg₀
  have htop := IsCMField.zpowers_complexConj_eq_top L
  have hmemσ : σ ∈ Subgroup.zpowers (IsCMField.complexConj L) := by rw [htop]; trivial
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmemσ
  have hk2 : IsCMField.complexConj L ^ (k % 2) = σ := by
    have h := zpow_mod_orderOf (IsCMField.complexConj L) k
    rw [IsCMField.orderOf_complexConj L] at h
    rw [← hk]
    exact_mod_cast h
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [h0, zpow_zero] at hk2
    ext z
    rw [← hσ, ← hk2]
    rfl
  · right
    rw [h1, zpow_one] at hk2
    ext z
    rw [← hσ, ← hk2]
    rfl

end GlobalTheory.UniDepthZero

namespace GlobalTheory.UniDepthZero

theorem proj_conj {L : Type} [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (i i₀ : L →ₐ[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L))
    (hi : i = i₀.comp (IsCMField.complexConj L).toAlgHom) (x : AL L) :
    (SplitPlace.proj (⟨v, i⟩ : SplitPlace L)) x = (SplitPlace.proj (⟨v, i₀⟩ : SplitPlace L)) (conjAL L x) := by
  subst hi
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [SplitPlace.proj, conjAL, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]

theorem loc_conj_apply {L : Type} [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (i i₀ : L →ₐ[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L))
    (hi : i = i₀.comp (IsCMField.complexConj L).toAlgHom) {n : ℕ} (κ : GA L n) (a b : Fin n) :
    (SplitPlace.loc (⟨v, i⟩ : SplitPlace L) n κ).val a b =
      (SplitPlace.loc (⟨v, i₀⟩ : SplitPlace L) n κ⁻¹).val b a := by
  have hm := κ.2
  simp only [GA, UGroup, Subgroup.mem_mk] at hm
  have h1 : ((κ.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = conjT (conjAL L) κ.1 :=
    Units.inv_eq_of_mul_eq_one_right hm
  have h2 : (((κ⁻¹ : GA L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) b a = conjAL L ((κ.1 : Matrix (Fin n) (Fin n) (AL L)) a b) := by
    rw [InvMemClass.coe_inv, h1]; rfl
  simp only [SplitPlace.loc, MonoidHom.comp_apply, Subgroup.coe_subtype, GeneralLinearGroup.map_apply]
  rw [h2, proj_conj v i i₀ hi]

theorem loc_mem_KOne_of_same {L : Type} [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (i i₀ : L →ₐ[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) {n : ℕ} (κ : GA L n)
    (h : SplitPlace.loc (⟨v, i⟩ : SplitPlace L) n κ ∈ KOne (v.adicCompletion (maximalRealSubfield L)) (Fin n)) :
    SplitPlace.loc (⟨v, i₀⟩ : SplitPlace L) n κ ∈ KOne (v.adicCompletion (maximalRealSubfield L)) (Fin n) := by
  rcases algHom_eq_or_conj i i₀ with rfl | hi
  · exact h
  · have h' : SplitPlace.loc (⟨v, i₀⟩ : SplitPlace L) n κ⁻¹ ∈ KOne (v.adicCompletion (maximalRealSubfield L)) (Fin n) := by
      refine (GlobalTheory.FixedAtSplit.mem_KOne_iff' _).2 fun a b => ?_
      have := (GlobalTheory.FixedAtSplit.mem_KOne_iff' _).1 h b a
      simp only [Matrix.sub_apply, Matrix.one_apply] at this ⊢
      rw [← loc_conj_apply v i i₀ hi]
      by_cases hab : a = b
      · subst hab; simpa using this
      · simpa [hab, Ne.symm hab] using this
    have := inv_mem h'
    rwa [map_inv, inv_inv] at this

end GlobalTheory.UniDepthZero

namespace GlobalTheory.UniDepthZero

theorem level_trivial {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (s₀ : SplitPlace L) (r : ℕ)
    (ψ₀ : AddChar (s₀.v.adicCompletion (maximalRealSubfield L)) ℂ)
    (ξ : (s₀.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ)
    (hJ : NG.LevelUni J χ s₀ r ψ₀ ξ) (hψ : NG.IsPsi0 s₀ ψ₀)
    (hξ : ∀ u : (s₀.v.adicCompletion (maximalRealSubfield L))ˣ,
      Valued.v ((u : s₀.v.adicCompletion (maximalRealSubfield L)) - 1) < 1 → ξ u = 1)
    (κ : GAf L n) (hκ : TrivOutside {s₀.v} κ)
    (hK : s₀.loc n κ ∈ KOne (s₀.v.adicCompletion (maximalRealSubfield L)) (Fin n)) :
    ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1 := by
  set g := s₀.loc n κ with hg
  have hv := (GlobalTheory.FixedAtSplit.mem_KOne_iff' g).1 hK
  have hoff : ∀ a b : Fin n, a ≠ b → Valued.v (g.val a b) < 1 := fun a b hab => by
    simpa [Matrix.sub_apply, Matrix.one_apply_ne hab] using hv a b
  have hdiag : ∀ a : Fin n, Valued.v (g.val a a - 1) < 1 := fun a => by
    simpa [Matrix.sub_apply] using hv a a
  have hint : g ∈ Formalism.UG.GLint (Fin n) (s₀.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := by
    rw [(GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne s₀.v n).1]
    exact GlobalTheory.StepData.KOne_le_KO hK
  have huni : NG.UniRT s₀ r g := by
    refine ⟨⟨hint, fun a b ha hb => hoff a b ?_⟩, fun a b ha hb => ⟨fun hba => hoff a b ?_, fun hab => ?_⟩⟩
    · rintro rfl; omega
    · rintro rfl; omega
    · subst hab; exact hdiag a
  have hmem : κ ∈ J := (hJ.mem κ hκ).2 huni
  let D : Matrix {x : Fin n // r ≤ x.val} {x : Fin n // r ≤ x.val} (s₀.v.adicCompletion (maximalRealSubfield L)) :=
    Matrix.of fun a b => g.val a.1 b.1
  have hD : GlobalTheory.StepData.MaxM (D - 1) := by
    have hm := GlobalTheory.StepData.mem_KOne.1 hK
    intro a b
    have h3 := hm a.1 b.1
    by_cases hab : a = b
    · subst hab
      simpa [D, Matrix.sub_apply] using h3
    · have h4 : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
      simpa [D, Matrix.sub_apply, Matrix.one_apply_ne hab, Matrix.one_apply_ne h4] using h3
  obtain ⟨u', hu', hu'v⟩ := GlobalTheory.StepData.exists_mem_KOne hD
  have hdet := GlobalTheory.StepData.det_of_mem_KOne hu'
  have : (Valued.v : Valuation (s₀.v.adicCompletion (maximalRealSubfield L)) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (s₀.v.adicCompletion (maximalRealSubfield L)))
    (Valued.v : Valuation (s₀.v.adicCompletion (maximalRealSubfield L)) (WithZero (Multiplicative ℤ)))
  have hdetv : Valued.v (NG.detDD s₀ r g - 1) < 1 := by
    rw [← he.lt_one_iff_lt_one]
    convert hdet using 3
    rw [Matrix.GeneralLinearGroup.val_det_apply, hu'v]
    rfl
  have hne : NG.detDD s₀ r g ≠ 0 := fun h0 => by
    rw [h0, zero_sub, Valuation.map_neg, Valuation.map_one] at hdetv
    exact lt_irrefl _ hdetv
  have hχ := hJ.chr κ hmem hκ (Units.mk0 _ hne) rfl
  have h1 : ψ₀ (NG.supDiag s₀ r g) = 1 := by
    refine hψ.1 _ ?_
    refine Valuation.map_sum_lt _ one_ne_zero fun a _ => Valuation.map_sum_lt _ one_ne_zero fun b _ => ?_
    split_ifs with h
    · exact hoff a b (fun e => by subst e; omega)
    · simp
  have h2 : ξ (Units.mk0 _ hne) = 1 := hξ _ (by simpa using hdetv)
  refine ⟨hmem, Units.ext ?_⟩
  rw [hχ, h1, h2]
  simp

end GlobalTheory.UniDepthZero

namespace GlobalTheory.UniDepthZero

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (J : Subgroup (GAf L n)) (χ : J →* ℂˣ), (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → ∀ (s₀ : SplitPlace L) (r : ℕ) (ψ₀ : AddChar (s₀.v.adicCompletion (maximalRealSubfield L)) ℂ) (ξ : (s₀.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), NG.LevelUni J χ s₀ r ψ₀ ξ → NG.IsPsi0 s₀ ψ₀ → (∀ u : (s₀.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v ((u : s₀.v.adicCompletion (maximalRealSubfield L)) - 1) < 1 → ξ u = 1) → ∀ f ∈ NG.isoTyp a.ρ S, f ∈ NG.TypeSp a.ρ J χ → f ≠ 0 → ∀ (s : SplitPlace L), s.v = s₀.v → ∀ (σ : IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → fixed (GlobalTheory.LocLanglands.cls σ).rep (KOne (s.w.adicCompletion L) (Fin n)) ≠ ⊥ := by
  intro L _ _ _ n a S hS J χ _ s₀ r ψ₀ ξ hJ hψ hξ f hf hfJ hf0 s hs σ hσ
  obtain ⟨c, T, hc, hci, -⟩ := id hσ
  have hfix : ∀ κ : GAf L n, TrivOutside {s.v} κ →
      s.loc n κ ∈ KOne (s.v.adicCompletion (maximalRealSubfield L)) (Fin n) → NG.rt L n κ f = f := by
    intro κ hκ hK
    obtain ⟨v, i⟩ := s
    obtain ⟨v₀, i₀⟩ := s₀
    obtain rfl : v = v₀ := hs
    have hK₀ := loc_mem_KOne_of_same _ i i₀ κ hK
    obtain ⟨hm, h1⟩ := level_trivial J χ _ r ψ₀ ξ hJ hψ hξ κ hκ hK₀
    have h2 := hfJ.2 ⟨κ, hm⟩
    rw [h1] at h2
    simpa using h2
  obtain ⟨u, hu0, hu⟩ := GlobalTheory.LocVec.main L n a S hS s σ hσ c hc hci
    (KOne (s.v.adicCompletion (maximalRealSubfield L)) (Fin n)) 1
    (fun g hg => by
      rw [(GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne s.v n).1]
      exact GlobalTheory.StepData.KOne_le_KO hg)
    (by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ)
    f hf hf0 (fun κ hκ h => by rw [hfix κ hκ h]; simp)
  refine GlobalTheory.LocLanglands.fixed_ne_bot_of_equiv (IrrRep.nonempty_equiv_rep σ).some.symm ?_
  rw [Submodule.ne_bot_iff]
  refine ⟨u, GlobalTheory.Parabolic.mem_fixed.2 fun h hh => ?_, hu0⟩
  have e : Matrix.GeneralLinearGroup.map c.toRingHom (Matrix.GeneralLinearGroup.map c.symm.toRingHom h) = h := by
    ext i j
    simp
  have hg := GlobalTheory.FixedAtSplit.mem_KOne_of_map c hc _ (e.symm ▸ hh)
  have h3 := hu _ hg
  rw [e] at h3
  simpa using h3

end GlobalTheory.UniDepthZero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimeIdempotentOfIdempotentSumPlaceSplit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

namespace GlobalTheory.IdemSumBranch

open GlobalTheory.StdFrames GlobalTheory.IdemSupport

variable {D : D7}

theorem cpt_idemSum {ea : AE D} {S : Finset (Pl D.host.E)} (h : IsIdemSum ea S) {Q : Pl D.host.E} (hQ : Q ∈ S) :
    cpt Q (toEAf D ea) = 1 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  have hs := map_sum ((cpt Q).comp (toEAf D)).toAddMonoidHom es S
  refine hs.trans ?_
  rw [Finset.sum_eq_single_of_mem Q hQ]
  · exact (cpt_of_isIdemAt (hes Q hQ)).1
  · intro R hR hne
    exact (cpt_of_isIdemAt (hes R hR)).2 Q hne.symm

theorem conjPrime_ne {ea : AE D} {S : Finset (Pl D.host.E)} (h : IsIdemSum ea S) {P Q : Pl D.host.E} (hP : P ∈ S)
    (hQ : Q ∈ S) : cP Q ≠ P := by
  intro hc
  have h1 := congrArg (fun t => cpt P (toEAf D t)) h.2
  simp only [RingHom.map_mul, RingHom.map_zero, cpt_idemSum h hP, one_mul] at h1
  rw [toEAf_cA, ← hc] at h1
  have h2 := cpt_sg_eq_zero h1
  rw [sg_sg, cpt_idemSum h hQ] at h2
  exact one_ne_zero h2

theorem branch : ∀ (D : D7) (P : Pl D.host.E) (e f ea : AE D) (S : Finset (Pl D.host.E)),
    IsPrimeIdem P e f → IsIdemSum ea S → P ∈ S → Formalism.L2.NTheta.IsIdemAt e P ∧ f = e + cA D e ∧ cA D f = f ∧
      infPart D f = 0 ∧ ∀ PP ∈ S, GlobalTheory.IdemSupport.cP PP ≠ P := by
  intro D P e f ea S h1 hS hP
  obtain ⟨hd, ε, hε, hf⟩ := of_isPrimeIdem (comp_toAd D) h1
  have hinf : infPart D f = 0 := hf ▸ (place_comp (comp_toAd D) hε).1
  rcases h1 with ⟨h1, h2⟩ | ⟨rfl, -⟩
  · refine ⟨h1, h2, ?_, hinf, fun Q hQ => conjPrime_ne hS hP hQ⟩
    rw [h2, RingHom.map_add (f := _), Formalism.L2.Theta.cA_cA, add_comm]
  · exfalso
    have h2 := (place_comp (comp_toAd D) hε).2.1 (cP P) (under_cP P)
    rw [← hf, hd.2.2 _ (conjPrime_ne hS hP hP)] at h2
    exact zero_ne_one h2

end GlobalTheory.IdemSumBranch
end

