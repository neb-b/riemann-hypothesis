module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishing
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
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
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1494
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmObjHomOfTypeLinearIndependent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.CM.IntCoord
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCM.HomIndep

theorem phiP_independent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q) (x : Fin p → 𝓞 E),
    ∏ a, ((X.A true).t.act.act (x a) ≫ GlobalTheory.FlatCM.phiP X a) = 1 → x = 0 := by
  intro E _ _ _ H K _ _ ρ σ₁ p q X x hx
  classical
  have hU := GlobalTheory.thetaUnifAV_all
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  obtain ⟨τ, hτ⟩ := GlobalTheory.CM.NumInh.exists_char X.split X.ρ_sq
  have FA : ∀ b, GenFib (X.A b).pol := fun b =>
    (GenFib.nonempty_of_baseChange hL.polBaseChange K (X.A b).pol).some
  have FB : GenFib X.B.pol := (GenFib.nonempty_of_baseChange hL.polBaseChange K X.B.pol).some
  have hMex : ∀ j : Fin p ⊕ Fin q, ∃ M, (FA j.isLeft).IsDiffOf FB (X.φ j) M := fun j =>
    ((GlobalTheory.CM.DiffCoord.existsUnique_isDiffOf K _ (FA j.isLeft) _ FB (X.φ j) (X.lin j).isMonHom).1).exists
  choose M hM using hMex
  obtain ⟨-, hrank, hinj, hind, -⟩ := GlobalTheory.CM.Indep.letters_independent hU hL E H K ρ σ₁ p q X FA FB M hM
  funext a
  show x a = 0
  have hcA := integral_tangent_coordinates K _ (FA true)
  have hcB := integral_tangent_coordinates K _ FB

  have hne : (FA true).eigLat (X.A true).t.act τ ≠ ⊥ := by
    intro h0
    have h1 := hrank (Sum.inl a, τ)
    rw [if_pos (by simpa using hτ)] at h1
    change latRank K (((FA true).eigLat (X.A true).t.act τ).map ((M (Sum.inl a)).restrictScalars (𝓞 K))) = 1 at h1
    rw [h0] at h1
    have hb : Submodule.span K (((⊥ : Submodule (𝓞 K) (Fin (FA true).P₀.g → K)).map
        ((M (Sum.inl a)).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (Fin FB.P₀.g → K)) : Set (Fin FB.P₀.g → K)) = ⊥ :=
      Submodule.span_eq_bot.2 fun z hz => by
        obtain ⟨y, hy, rfl⟩ := hz
        obtain rfl : y = 0 := (Submodule.mem_bot (𝓞 K)).1 hy
        exact map_zero _
    rw [latRank, hb, finrank_bot] at h1
    exact zero_ne_one h1
  obtain ⟨e, he, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨u, hu, heig⟩ := (hcA.2.2.2.2.2 _ _ τ e).1 he
  have hs : ∀ b, FB.IsCoord (u ≫ ((X.A true).t.act.act (x b) ≫ phiP X b)) (M (Sum.inl b) (τ (x b) • e)) := by
    intro b
    rw [← Category.assoc]
    exact hM (Sum.inl b) _ _ (isCoord_smul (FA true) hu (heig (x b)))
  have hprod : ∀ s : Finset (Fin p), FB.IsCoord (u ≫ ∏ b ∈ s, ((X.A true).t.act.act (x b) ≫ phiP X b))
      (∑ b ∈ s, M (Sum.inl b) (τ (x b) • e)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.sum_empty, comp_one]
      exact isCoord_one FB
    | insert b s hb ih =>
      rw [Finset.prod_insert hb, Finset.sum_insert hb, comp_mul]
      exact isCoord_mul FB (hs b) ih
  have hsum : ∑ b, M (Sum.inl b) (τ (x b) • e) = 0 := by
    have h1 := hprod Finset.univ
    rw [hx, comp_one] at h1
    exact (hcB.1 _ h1.1).unique h1 (isCoord_one FB)
  have hind' := hind.comp (f := fun b : Fin p => ((Sum.inl b, τ) : (Fin p ⊕ Fin q) × (𝓞 E →+* 𝓞 K)))
    (fun b b' h => Sum.inl_injective (Prod.ext_iff.1 h).1)
  have hva := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).1 hind' Finset.univ
    (fun b => M (Sum.inl b) (τ (x b) • e))
    (fun b _ => Submodule.subset_span (Submodule.mem_map_of_mem
      (f := (M (Sum.inl b)).restrictScalars (𝓞 K)) (Submodule.smul_mem _ (τ (x b)) he))) hsum a (Finset.mem_univ a)
  have h0 : τ (x a) • e = 0 := hinj (Sum.inl a) (by rw [hva]; exact (map_zero _).symm)
  rw [← algebraMap_smul K (τ (x a)) e, smul_eq_zero] at h0
  have hτa : τ (x a) = 0 :=
    (map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).1 (h0.resolve_right he0)
  exact ringOfIntegers_hom_injective τ (by rw [hτa, map_zero])

end GlobalTheory.FlatCM.HomIndep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentRepresentativesInjectiveDoubleCoset
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.RepsInj
open Matrix GlobalTheory.AdLat GlobalTheory.UCls

theorem cc_eq (D : D7) : IsCMField.complexConj D.host.E = GlobalTheory.Member.cF D :=
  AlgEquiv.ext fun x => ((GlobalTheory.Member.latHat_eq_hat_and_gram D D.sp.X').2.2.2.2.2.1 x).symm

section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem hermA_single (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    hermA c G (Pi.single i 1) (Pi.single j 1) = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ G i j := by
  simp [hermA, Pi.single_apply]

theorem hermA_mulVec_single (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) (RA F E)) (i j : Fin n) :
    hermA c G (g *ᵥ Pi.single i 1) (g *ᵥ Pi.single j 1) =
      (gᵀ * G.map (fun x => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) * g.map (sg (FiniteAdeleRing (𝓞 F) F) c)) i j := by
  simp only [hermA, Matrix.mul_apply, Finset.sum_mul, Matrix.mulVec_single_one, Matrix.transpose_apply, Matrix.map_apply]
  rw [Finset.sum_comm]
  rfl

theorem transpose_form' {A : Type} [CommRing A] {m : ℕ} (s : A →+* A) (J g : Matrix (Fin m) (Fin m) A) :
    gᵀ * Jᵀ * g.map s = Jᵀ ↔ Formalism.UG.cT s g * J * g = J := by
  rw [← Matrix.transpose_inj, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_transpose, ← Matrix.mul_assoc, Formalism.UG.cT]

theorem unitary_of_isUA (c : E ≃ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) (RA F E))
    (h : IsUA c (-Jᵀ) g) :
    Formalism.UG.cT (sigR (FiniteAdeleRing (𝓞 F) F) (c : E →ₐ[F] E)) g * JR (FiniteAdeleRing (𝓞 F) F) J * g =
      JR (FiniteAdeleRing (𝓞 F) F) J := by
  rw [← transpose_form']
  have key : gᵀ * (-Jᵀ).map (fun x => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) * g.map (sg (FiniteAdeleRing (𝓞 F) F) c) =
      (-Jᵀ).map (fun x => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) := by
    ext i j
    rw [← hermA_mulVec_single, h.2, hermA_single, Matrix.map_apply]
  have e : (-Jᵀ).map (fun x => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) = -(JR (FiniteAdeleRing (𝓞 F) F) J)ᵀ := by
    ext i j; simp [JR, inclR, TensorProduct.tmul_neg]
  rw [e, Matrix.mul_neg, Matrix.neg_mul, neg_inj] at key
  exact key

theorem af_nontrivial : Nontrivial (FiniteAdeleRing (𝓞 F) F) := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
  let v : HeightOneSpectrum (𝓞 F) :=
    ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩
  refine ⟨0, 1, fun h => ?_⟩
  have h2 : (0 : v.adicCompletion F) = 1 := congrArg (fun x : FiniteAdeleRing (𝓞 F) F => x v) h
  exact zero_ne_one h2

theorem incl_inj : Function.Injective (inclR (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)) :=
  haveI := af_nontrivial (F := F)
  Algebra.TensorProduct.includeRight_injective (algebraMap F (FiniteAdeleRing (𝓞 F) F)).injective

theorem cT_map_inclR (R : Type) [CommRing R] [Algebra F R] (c : E →ₐ[F] E) (γ : Matrix (Fin n) (Fin n) E) :
    (Formalism.UG.cT (c : E →+* E) γ).map (inclR R) = Formalism.UG.cT (sigR R c) (γ.map (inclR R)) := by
  ext i j
  simp [Formalism.UG.cT, sigR, inclR]

theorem rat_unitary (c : E ≃ₐ[F] E) (J γ : Matrix (Fin n) (Fin n) E) (h : IsUA c (-Jᵀ) (ratM F γ)) :
    γ.det ≠ 0 ∧ Formalism.UG.cT ((c : E →ₐ[F] E) : E →+* E) γ * J * γ = J := by
  have hr : ratM F γ = γ.map (inclR (FiniteAdeleRing (𝓞 F) F)) := rfl
  constructor
  · intro h0
    have hu := h.1
    rw [hr, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero] at hu
    haveI := af_nontrivial (F := F)
    haveI : Nontrivial (RA F E) := (incl_inj (F := F) (E := E)).nontrivial
    exact not_isUnit_zero hu
  · have hu := unitary_of_isUA c J _ h
    apply Matrix.map_injective (incl_inj (F := F) (E := E))
    dsimp only
    rw [Matrix.map_mul, Matrix.map_mul, cT_map_inclR]
    exact hu

end Gen

theorem gq_of_isUA (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E)
    (h : IsUA (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (ratM (maximalRealSubfield D.host.E) γ)) :
    ∃ γ₀ ∈ GQ V, ((finHom V γ₀).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) =
      ratM (maximalRealSubfield D.host.E) γ := by
  rw [cc_eq] at h
  obtain ⟨hd, hu⟩ := rat_unitary _ _ _ h
  let γu : GL (Fin V.rank) D.host.E := ((Matrix.isUnit_iff_isUnit_det γ).2 (Ne.isUnit hd)).unit
  have hU : γu ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := hu
  have hm : Formalism.UG.bc (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) γu ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    show Formalism.UG.cT _ (γ.map (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F))) * JR (AF D.host.F) V.gram * γ.map (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) =
      JR (AF D.host.F) V.gram
    rw [← cT_map_inclR, JR, ← Matrix.map_mul, ← Matrix.map_mul]
    exact congrArg (fun M => M.map (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F))) hU
  refine ⟨⟨_, hm⟩, ⟨γu, hU, rfl⟩, ?_⟩
  ext i j
  rfl

theorem kf_of_isKM (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (M : ℕ) (Kf : Subgroup (GA D V)) (hK : IsLevelK V M Kf)
    (κ : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E))
    (h : IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) M κ) :
    ∃ κA ∈ Kf, ((finHom V κA).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) = κ := by
  rw [cc_eq] at h
  have hu := unitary_of_isUA _ _ _ h.1
  let κu : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E) := ((Matrix.isUnit_iff_isUnit_det κ).2 h.1.1).unit
  have hmem : κu ∈ HR (Af D.host.F) D.sp.cm.sig V.gram := hu
  obtain ⟨κA, hG, hf⟩ := (_root_.GlobalTheory.UnitaryGlue.adelic_glue D V).1 κu hmem
  refine ⟨κA, (hK κA).2 ⟨hG, ?_⟩, by rw [hf]; rfl⟩
  intro z hz
  rw [(GlobalTheory.Member.latHat_eq_hat_and_gram D V).1] at hz ⊢
  rw [hf]
  exact h.2.1 z hz

theorem reps_inj : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (Comp : Type) (X : Comp → Data D.host.E V.rank)
    (dict : GA D V → Σ k, Frame (X k).Ψ V.rank) (Kf : Subgroup (GA D V))
    (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : ℕ) (gA : Comp → GA D V),
    IsLevelK V M Kf → (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) → DictIsUnif V dict Kf th rfl →
    (∀ k, (dict (gA k)).1 = k) → ∀ k k',
      GlobalTheory.UCls.UEquiv (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) M
        ((finHom V (gA k)).1 : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E))
        ((finHom V (gA k')).1 : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) → k = k' := by
  intro D V Comp X dict Kf th M gA hK _ hD hgA k k' hE
  obtain ⟨γ, hγ, κ, hκ, he⟩ := hE
  obtain ⟨γ₀, hγ₀, hγf⟩ := gq_of_isUA D V γ hγ
  obtain ⟨κA, hκA, hκf⟩ := kf_of_isKM D V M Kf hK κ hκ
  have hfin : finHom V (gA k') = finHom V (γ₀ * gA k * κA) := by
    rw [map_mul, map_mul]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact he.trans (by rw [← hγf, ← hκf])
  have hx : (γ₀ * gA k * κA)⁻¹ * gA k' ∈ GinfC V := by
    show finHom V _ = 1
    rw [map_mul, map_inv, hfin, inv_mul_cancel]
  have hk' : gA k' = γ₀ * gA k * κA * ((γ₀ * gA k * κA)⁻¹ * gA k') := by group
  obtain ⟨h1, h2, ⟨x0, -, h3⟩, -⟩ := hD
  have s3 : (dict (gA k')).1 = (dict (γ₀ * gA k * κA)).1 := by
    obtain ⟨γ', -, e⟩ := h3 (γ₀ * gA k * κA) _ hx
    rw [hk', e]
  have s2 : (dict (γ₀ * gA k * κA)).1 = (dict (γ₀ * gA k)).1 := by
    obtain ⟨γ', -, e⟩ := h2 κA hκA (γ₀ * gA k)
    rw [e]
  have s1 : (dict (γ₀ * gA k)).1 = (dict (gA k)).1 := by
    obtain ⟨γ', -, e⟩ := h1 γ₀ hγ₀ (gA k)
    rw [e]
  rw [← hgA k, ← hgA k', s3, s2, s1]

end GlobalTheory.RepsInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongOneInvMulIff
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.CongReps

variable (D : D7) (𝔪 : Ideal (𝓞 D.host.E))


variable {D 𝔪} in
theorem mul_mem_hatId {t x : AE D} (ht : t ∈ OhE D) (hx : x ∈ hatId D 𝔪) : t * x ∈ hatId D 𝔪 := by
  unfold hatId at hx ⊢
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨b, hb, t * s, mul_mem ht hs, by ring⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
  | neg y _ hy => rw [mul_neg]; exact neg_mem hy


variable {D 𝔪} in
theorem inc_sub_mem {r r' : 𝓞 D.host.E} (h : r - r' ∈ 𝔪) :
    inc D (r : D.host.E) - inc D (r' : D.host.E) ∈ hatId D 𝔪 :=
  AddSubgroup.subset_closure ⟨r - r', h, 1, one_mem _, by push_cast; rw [map_sub, mul_one]⟩


variable {D 𝔪} in
theorem exists_rep (h𝔪 : 𝔪 ≠ ⊥) {s : AE D} (hs : s ∈ OhE D) :
    ∃ r : 𝓞 D.host.E, s - inc D (r : D.host.E) ∈ hatId D 𝔪 := by
  have hn : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 h𝔪)
  obtain ⟨r, hr, w, hw, e⟩ := GlobalTheory.HeckeVal.exists_approx D _ hn s hs
  refine ⟨⟨r, hr⟩, AddSubgroup.subset_closure ⟨(Ideal.absNorm 𝔪 : 𝓞 D.host.E), Ideal.absNorm_mem 𝔪, w, hw, ?_⟩⟩
  rw [e]
  change inc D r + (Ideal.absNorm 𝔪 : AE D) * w - inc D r = inc D (((Ideal.absNorm 𝔪 : ℕ) : 𝓞 D.host.E) : D.host.E) * w
  simp

def congRel (N : ℕ) : Setoid {k : GA D N // k ∈ intG D N} where
  r k k' := ∀ i j, ((k.1 : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j -
    ((k'.1 : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ hatId D 𝔪
  iseqv := by
    refine ⟨fun k i j => by rw [sub_self]; exact zero_mem _, fun h i j => by rw [← neg_sub]; exact neg_mem (h i j),
      fun h h' i j => ?_⟩
    have := add_mem (h i j) (h' i j)
    rwa [sub_add_sub_cancel] at this


variable {D 𝔪} in
theorem congOne_inv_mul_iff {N : ℕ} {r : GA D N} (hr : r ∈ intG D N) (k : GA D N) :
    CongOne D 𝔪 (r⁻¹ * k) ↔ ∀ i j, ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j -
      ((r : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ hatId D 𝔪 := by
  have hI := (mem_intG r).1 hr
  set Rm : Matrix (Fin N) (Fin N) (AE D) := ((r : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))
  set Ri : Matrix (Fin N) (Fin N) (AE D) := (((r : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))
  set K : Matrix (Fin N) (Fin N) (AE D) := ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))
  have e0 : (((r⁻¹ * k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) = Ri * K := by
    simp [Rm, Ri, K]
  have e1 : Ri * K - 1 = Ri * (K - Rm) := by
    rw [Matrix.mul_sub]
    congr 1
    exact (Units.inv_mul (r : GL (Fin N) (AE D))).symm
  have e2 : K - Rm = Rm * (Ri * K - 1) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, Matrix.mul_one]
    congr 1
    rw [show Rm * Ri = 1 from Units.mul_inv (r : GL (Fin N) (AE D)), Matrix.one_mul]
  unfold CongOne
  rw [e0]
  constructor
  · intro h i j
    rw [← Matrix.sub_apply, e2, Matrix.mul_apply]
    exact sum_mem fun l _ => mul_mem_hatId (hI i l).1 (h l j)
  · intro h i j
    rw [e1, Matrix.mul_apply]
    exact sum_mem fun l _ => mul_mem_hatId (hI i l).2 (by rw [Matrix.sub_apply]; exact h l j)


open Classical in
def red (x : AE D) : 𝓞 D.host.E ⧸ 𝔪 :=
  if h : ∃ r : 𝓞 D.host.E, x - inc D (r : D.host.E) ∈ hatId D 𝔪 then Ideal.Quotient.mk 𝔪 h.choose else 0


variable {D 𝔪} in
theorem sub_mem_of_red_eq (h𝔪 : 𝔪 ≠ ⊥) {x y : AE D} (hx : x ∈ OhE D) (hy : y ∈ OhE D) (h : red D 𝔪 x = red D 𝔪 y) :
    x - y ∈ hatId D 𝔪 := by
  have ex := exists_rep h𝔪 hx
  have ey := exists_rep h𝔪 hy
  unfold red at h
  rw [dite_eq_left ex, dite_eq_left ey, Ideal.Quotient.eq] at h
  have := add_mem (sub_mem ex.choose_spec ey.choose_spec) (inc_sub_mem h)
  convert this using 1
  ring

theorem finite_congRel (h𝔪 : 𝔪 ≠ ⊥) (N : ℕ) : Finite (Quotient (congRel D 𝔪 N)) := by
  haveI : Finite (𝓞 D.host.E ⧸ 𝔪) := Ideal.finiteQuotientOfFreeOfNeBot 𝔪 h𝔪
  let φ : {k : GA D N // k ∈ intG D N} → Fin N → Fin N → 𝓞 D.host.E ⧸ 𝔪 := fun k i j =>
    red D 𝔪 (((k.1 : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j)
  let g : {q // ∃ k, φ k = q} → Quotient (congRel D 𝔪 N) := fun q => Quotient.mk _ q.2.choose
  refine Finite.of_surjective g fun c => ?_
  induction c using Quotient.inductionOn with
  | h k =>
    refine ⟨⟨φ k, k, rfl⟩, Quotient.sound fun i j => ?_⟩
    have hq : φ (⟨φ k, k, rfl⟩ : {q // ∃ k, φ k = q}).2.choose = φ k := (⟨φ k, k, rfl⟩ : {q // ∃ k, φ k = q}).2.choose_spec
    set k' := (⟨φ k, k, rfl⟩ : {q // ∃ k, φ k = q}).2.choose
    exact sub_mem_of_red_eq h𝔪 (((mem_intG k'.1).1 k'.2) i j).1 (((mem_intG k.1).1 k.2) i j).1
      (congrFun (congrFun hq i) j)

theorem exists_reps : ∀ (D : D7) (N : ℕ) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∃ R : Finset (GA D N),
    (∀ r ∈ R, r ∈ intG D N) ∧ ∀ k ∈ intG D N, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k) := by
  intro D N 𝔪 h𝔪
  haveI := finite_congRel D 𝔪 h𝔪 N
  haveI : Fintype (Quotient (congRel D 𝔪 N)) := Fintype.ofFinite _
  classical
  refine ⟨Finset.univ.image fun c : Quotient (congRel D 𝔪 N) => c.out.1, ?_, ?_⟩
  · intro r hr
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hr
    exact c.out.2
  · intro k hk
    let c := Quotient.mk (congRel D 𝔪 N) ⟨k, hk⟩
    refine ⟨c.out.1, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ c), ?_⟩, ?_⟩
    · rw [congOne_inv_mul_iff c.out.2]
      have := Quotient.exact (Quotient.out_eq c)
      intro i j
      have h := (congRel D 𝔪 N).iseqv.symm this i j
      exact h
    · rintro r ⟨hr, hc⟩
      obtain ⟨c', -, rfl⟩ := Finset.mem_image.1 hr
      rw [congOne_inv_mul_iff c'.out.2] at hc
      have h1 : (congRel D 𝔪 N) c'.out ⟨k, hk⟩ := (congRel D 𝔪 N).iseqv.symm hc
      have h3 : c' = c := by
        rw [← Quotient.out_eq c']
        exact Quotient.sound h1
      rw [h3]

end GlobalTheory.CongReps

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryAdelicOfFrameColumns
section
noncomputable section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem continuous_of_frameCols : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (X : Type) [TopologicalSpace X] (f : X → GAd σ J), Continuous (fun x => (matHom _ σ J (f x)).1 * adMat F C) → Continuous (fun x => (matHom _ σ J (f x)).1 * adMat F Z) → Continuous (fun x => (matHom _ σ J (f x)).1 * adMat F D) → Continuous f := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF X _ f hC hZ hD
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hs : adMat F C * adMat F (cT (σ : E →+* E) D * J) + adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J))
      + adMat F D * adMat F (cT (σ : E →+* E) C * J) = 1 := by
    simp only [adMat, ← Matrix.map_mul]
    rw [← Matrix.map_add _ (map_add _), ← Matrix.map_add _ (map_add _), hF.sum]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hval : Continuous fun x => (matHom _ σ J (f x)).1 := by
    have e : ∀ x, (matHom _ σ J (f x)).1 = (matHom _ σ J (f x)).1 * adMat F C * adMat F (cT (σ : E →+* E) D * J)
        + (matHom _ σ J (f x)).1 * adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J))
        + (matHom _ σ J (f x)).1 * adMat F D * adMat F (cT (σ : E →+* E) C * J) := by
      intro x
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add, ← Matrix.mul_add, hs, Matrix.mul_one]
    refine Continuous.congr ?_ fun x => (e x).symm
    exact ((hC.matrix_mul continuous_const).add (hZ.matrix_mul continuous_const)).add (hD.matrix_mul continuous_const)
  have hcont : Continuous (adjA σ J) := (continuous_const.matrix_mul (continuous_id.matrix_map
      (GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ)).matrix_transpose).matrix_mul continuous_const
  have hinv : Continuous fun x => ((matHom _ σ J (f x))⁻¹).1 := by
    have e : ∀ x, ((matHom _ σ J (f x))⁻¹).1 = adjA σ J (matHom _ σ J (f x)).1 := fun x => by
      rw [adjA_mat hF.herm, map_inv]
    exact (hcont.comp hval).congr fun x => (e x).symm
  exact (isEmbedding_matHom (AF F) σ J).continuous_iff.2 (Units.continuous_iff.2 ⟨hval, hinv⟩)

end GlobalTheory.SphEis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleSchemeRepresentingEtaleLevelsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteEtaleScheme_representing_etaleLevels : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), N.Coprime p → IsEtPlace b w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s), ∃ (Y : Scheme.{0}) (π : Y ⟶ S) (lu : D.La → (Over.mk π ⟶ o.A)), IsFinite π ∧ Etale π ∧ IsEtLevOver o w0 r lu ∧ ∀ (T : Over S) (l : D.La → (T ⟶ o.A)), IsEtLevOver o w0 r l → ∃! f : T ⟶ Over.mk π, ∀ y, f ≫ lu y = l y := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.exists_etLevScheme) | (exact GlobalTheory.UPel.HT.EtLev.exists_etLevScheme) | (intros; apply GlobalTheory.UPel.HT.EtLev.exists_etLevScheme <;> assumption)
end

