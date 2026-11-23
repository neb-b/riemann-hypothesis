module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
public import Formalism.LocalToGlobal.GroupLattices.LevelCharts.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0695
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0387
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0116
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVeryAmpleBySectionsOfInvertibleLinearChange
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1486
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1485
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Formalism.PairingDivisors.StatementH

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDefiniteUnitaryQuotientEqClassSum
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormDictClassSum

section Compact

open Formalism.MainNotions.StandardLattice Matrix
open scoped TensorProduct ComplexOrder MatrixOrder

theorem negDef_of_signature {n q : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature G 0 q) : (-G).PosDef := by
  obtain ⟨e, P, hP⟩ := h
  have h1 : Formalism.UG.Jpq 0 q = -1 := by
    ext (i | i) (j | j)
    · exact i.elim0
    · exact i.elim0
    · exact j.elim0
    · simp [Formalism.UG.Jpq, Matrix.one_apply]
  have h2 : (star P.1 * (-G).reindex e e * P.1).PosDef := by
    have e1 : (-G).reindex e e = -(G.reindex e e) := by ext i j; simp
    have : star P.1 * (-G).reindex e e * P.1 = 1 := by
      have hP' : star P.1 * G.reindex e e * P.1 = Formalism.UG.Jpq 0 q := hP
      rw [e1, Matrix.mul_neg, Matrix.neg_mul, hP', h1, neg_neg]
    rw [this]; exact Matrix.PosDef.one
  have h3 := ((Matrix.IsUnit.posDef_star_left_conjugate_iff P.isUnit).1 h2).submatrix e.injective
  simpa using h3

theorem exists_bound_definite {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef ∨ (-G).PosDef) :
    ∃ R : ℝ, ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * G * g = G → ∀ i j, ‖g i j‖ ≤ R := by
  rcases hG with hG | hG
  · exact GlobalTheory.DefiniteQuotient.exists_bound_unitary hG
  · obtain ⟨R, hR⟩ := GlobalTheory.DefiniteQuotient.exists_bound_unitary hG
    refine ⟨R, fun g hg => hR g ?_⟩
    rw [Matrix.mul_neg, Matrix.neg_mul, hg]

variable {D : D7}

theorem definite_gramAt (V : HSp D) (hs : V.SigOK) (hd : V.IsDefinite) (τ : D.what₂.Tau) :
    (gramAt D V τ).PosDef ∨ (-gramAt D V τ).PosDef := by
  have h1 := hs (tauE D τ)
  rcases hd (tauE D τ) with h | h
  · left; rw [h] at h1; exact GlobalTheory.DefiniteQuotient.posDef_of_signature h1
  · right; rw [h] at h1; exact negDef_of_signature h1

theorem exists_compact_def (V : HSp D) (hs : V.SigOK) (hd : V.IsDefinite) :
    ∃ C : Set (GA D V), IsCompact C ∧ ∀ h : GA D V, ∃ γ ∈ GQ V, ∃ c ∈ C, h = γ * c := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
  have hf : GlobalTheory.Mass.FiniteClasses (GQ V) ((GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram).comap π) := by
    refine (GlobalTheory.Mass.finiteClasses_comap π (GlobalTheory.Mass.ratIn _ _ _) _ hπ.surjective hπ.injOn).2 ?_
    rw [hπ.map_ratIn]
    exact GlobalTheory.Mass.finiteClasses_unitary (GlobalTheory.DefiniteQuotient.cmExt D) (GlobalTheory.DefiniteQuotient.gram_hermND V)
      (Formalism.L2.G.gram_totDef D.sp.cm V hs hd)
      (GlobalTheory.Mass.isCompact_stdLevel _ _ (GlobalTheory.DefiniteQuotient.gram_hermND V).2) (GlobalTheory.Mass.isOpen_stdLevel _ _)
  choose R hR using fun τ => exists_bound_definite (definite_gramAt V hs hd τ)
  obtain ⟨C, hC, hCe⟩ := (GlobalTheory.Mass.intTens_open_compact D.host.F D.host.E).2
  obtain ⟨C', hC', hCe'⟩ := GlobalTheory.StabCompact.exists_compact_adele D θ hθ (∑ τ, |R τ|) C hC
  obtain ⟨K, hK, hKe⟩ := GlobalTheory.StabCompact.exists_compact_of_entries (AF D.host.F) D.sp.cm.sig V.gram
    (GlobalTheory.DefiniteQuotient.gram_hermND V).2 C' hC'
  have hsub : ∀ k : GA D V, π k ∈ GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram → k ∈ K := by
    intro k hk
    refine hKe k fun i j => hCe' _ (hCe _ ?_) fun τ => ?_
    · have := ((GlobalTheory.Mass.mem_stdLevel _ _ _).1 hk i j).1
      rwa [hπ k] at this
    · have hJ : (V.gram.map (incA D)).map ((θ τ).comp (infPart D)) = gramAt D V τ := by
        ext i j; exact GlobalTheory.FockCompare.comp_incA hθ τ _
      have hu : Formalism.UG.cT (cA D) (mt V k) * V.gram.map (incA D) * mt V k = V.gram.map (incA D) := k.2
      have e : (Formalism.UG.cT (cA D) (mt V k)).map ((θ τ).comp (infPart D)) =
          ((mt V k).map ((θ τ).comp (infPart D)))ᴴ := by
        ext i j; exact GlobalTheory.FockCompare.comp_cA hθ τ _
      have := congrArg (fun M => M.map ((θ τ).comp (infPart D))) hu
      simp only [Matrix.map_mul, e, hJ] at this
      exact ((hR τ _ this i j).trans (le_abs_self _)).trans
        (Finset.single_le_sum (f := fun τ => |R τ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ τ))
  haveI := hf.1
  refine ⟨⋃ c : Formalism.UG.ClassSet (GQ V) ((GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram).comap π),
    (fun k => c.out * k) '' K, isCompact_iUnion fun c => hK.image (continuous_const_mul _), fun h => ?_⟩
  obtain ⟨γ, hγ, k, hk, e⟩ := DoubleCoset.mk_out_eq_mul (GQ V) ((GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram).comap π) h
  refine ⟨γ⁻¹, inv_mem hγ, _, Set.mem_iUnion.2 ⟨DoubleCoset.mk _ _ h, k⁻¹, hsub _ (inv_mem hk), rfl⟩, ?_⟩
  simp only [e]
  group

end Compact


set_option maxHeartbeats 4000000 in
theorem integral_eq_classSum : ∀ {D : D7} (V : HSp D) (n : ℕ) (ι : Formalism.MainNotions.StandardLatticesGL3.GA D n →* GA D V) (J : Subgroup (Formalism.MainNotions.StandardLatticesGL3.GA D n))
  (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)),
  GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace V → Function.Injective ι → ι.range = GfC V →
  (∀ x, (∃ γ ∈ GQ V, finHom V γ = finHom V (ι x)) ↔ x ∈ ratG D n) →
  GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel V K → (∀ x, Lev.finE V (ι x) ∈ K ↔ x ∈ J) → Links.IsMeasDef V K μ 𝓕 →
  ∀ Φ : GA D V → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsClassFun V K Φ →
    Finite (Cls D n J) ∧ Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ V) Φ) (GlobalTheory.AutomorphicL2Unitary.autMeasure V μ) ∧
    ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) Φ q ∂GlobalTheory.AutomorphicL2Unitary.autMeasure V μ =
      ∑ᶠ x : Cls D n J, ((gam D J x.out : ℂ))⁻¹ * Φ (ι x.out) := by
  intro D V n ι J K μ 𝓕 hV hinj hran hrat hK hJ hμ Φ hΦ
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.2.2.2.2.1
  haveI : μ.IsHaarMeasure := hμ.1.1
  have hF : IsFundamentalDomain (GQ V) 𝓕 μ := hμ.2
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) Φ := hΦ.left
  let Ψ : Formalism.MainNotions.StandardLatticesGL3.GA D n →* Bridge.Gf V := (finHom V).rangeRestrict.comp ι
  have hΨi : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : ι x ∈ GinfC V := congrArg Subtype.val hx
    have h2 : ι x ∈ GfC V := by rw [← hran]; exact ⟨x, rfl⟩
    exact hinj ((GlobalTheory.AutFunCounterexample.GfC_inf_GinfC V h2 h1).trans (map_one ι).symm)
  have hΨs : Function.Surjective Ψ := by
    intro g
    obtain ⟨α, hα, e⟩ := GlobalTheory.Mem.FinPartLift.exists_gfC_finHom_eq V g
    rw [← hran] at hα
    obtain ⟨x, rfl⟩ := hα
    exact ⟨x, Subtype.ext e⟩
  have hratΨ : ∀ x, x ∈ ratG D n ↔ ∃ γ : GQ V, Bridge.ratF V γ = Ψ x := by
    intro x
    rw [← hrat x]
    constructor
    · rintro ⟨γ, hγ, h⟩; exact ⟨⟨γ, hγ⟩, Subtype.ext h⟩
    · rintro ⟨γ, h⟩; exact ⟨γ, γ.2, congrArg Subtype.val h⟩
  have hJΨ : ∀ x, x ∈ J ↔ Ψ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin V K := fun x =>
    (hJ x).symm.trans (GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.mem_levelFin (ι x)).symm
  have hΨdef : ∀ x, Ψ x = (finHom V).rangeRestrict (ι x) := fun _ => rfl
  clear_value Ψ
  obtain ⟨e, he⟩ : ∃ e : Formalism.MainNotions.StandardLatticesGL3.GA D n ≃* Bridge.Gf V, ∀ x, e x = Ψ x :=
    ⟨MulEquiv.ofBijective Ψ ⟨hΨi, hΨs⟩, fun _ => rfl⟩
  have hre : ∀ y, Ψ (e.symm y) = y := fun y => (he _).symm.trans (e.apply_symm_apply y)

  obtain ⟨C, hC, hCe⟩ := exists_compact_def V hV.1 hV.2
  obtain ⟨m, c, hc⟩ := GlobalTheory.RepsObj.exists_cover_of_compact (GQ V) (finHom V).rangeRestrict
    (finHom V).rangeRestrict_surjective (GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin V K) hK.1 hC hCe
  have hsurj : Function.Surjective fun a : Fin m => (DoubleCoset.mk (ratG D n) J (e.symm (c a)) : Cls D n J) := by
    intro q
    obtain ⟨a, γ, k, hk⟩ := hc (Ψ q.out)
    refine ⟨a, ?_⟩
    show DoubleCoset.mk (ratG D n) J (e.symm (c a)) = q
    conv_rhs => rw [← DoubleCoset.out_eq' q]
    rw [DoubleCoset.eq]
    refine ⟨e.symm (Bridge.ratF V γ), (hratΨ _).2 ⟨γ, (hre _).symm⟩, e.symm k,
      (hJΨ _).2 (by rw [hre]; exact k.2), ?_⟩
    apply hΨi
    simp only [map_mul, hre]
    exact hk
  haveI hfin : Finite (Cls D n J) := Finite.of_surjective _ hsurj
  haveI : Fintype (Cls D n J) := Fintype.ofFinite _

  have hreps : Bridge.IsReps (Bridge.ratF V) (GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin V K) (fun q : Cls D n J => Ψ q.out) := by
    intro g
    refine (hΨs g).elim fun x hx => ?_
    rw [← hx]
    refine ⟨DoubleCoset.mk (ratG D n) J x, ?_, ?_⟩
    · obtain ⟨h, hh, k, hk, hout⟩ := DoubleCoset.mk_out_eq_mul (ratG D n) J x
      obtain ⟨γ, hγ⟩ := (hratΨ h⁻¹).1 (inv_mem hh)
      refine ⟨γ, ⟨Ψ k⁻¹, (hJΨ _).1 (inv_mem hk)⟩, ?_⟩
      show Ψ x = Bridge.ratF V γ * Ψ (DoubleCoset.mk (ratG D n) J x).out * Ψ k⁻¹
      rw [hγ, hout, ← map_mul Ψ, ← map_mul Ψ]
      congr 1
      group
    · rintro q ⟨γ, k, hq⟩
      rw [← DoubleCoset.out_eq' q, DoubleCoset.eq]
      refine ⟨e.symm (Bridge.ratF V γ), (hratΨ _).2 ⟨γ, (hre _).symm⟩, e.symm k,
        (hJΨ _).2 (by rw [hre]; exact k.2), ?_⟩
      apply hΨi
      simp only [map_mul, hre]
      exact hq
  obtain ⟨-, hIO, hsum⟩ := GlobalTheory.DefiniteClassSum.classSumIntegral D V hV K hK μ 𝓕 hμ (Cls D n J)
    (fun q => Ψ q.out) hreps (fun q => ι q.out) (fun q => (hΨdef _).symm) Φ hΦ

  have hcard : ∀ x, Nat.card (GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.classGroupAt V K (Ψ x)) = gam D J x := by
    intro x
    unfold gam
    refine Nat.card_eq_of_bijective (fun γ => ⟨e.symm (Bridge.ratF V γ.1), (hratΨ _).2 ⟨γ.1, (hre _).symm⟩,
      (hJΨ _).2 ?_⟩) ⟨?_, ?_⟩
    · simp only [map_mul, map_inv, hre]
      exact (Bridge.mem_stab _).1 γ.2
    · intro a b hab
      have h1 := congrArg (fun s : {γ : Formalism.MainNotions.StandardLatticesGL3.GA D n // γ ∈ ratG D n ∧ x⁻¹ * γ * x ∈ J} => Ψ s.1) hab
      simp only [hre] at h1
      exact Subtype.ext (GlobalTheory.FormInner.ratF_injective V h1)
    · rintro ⟨y, hy1, hy2⟩
      refine ((hratΨ y).1 hy1).elim fun γ hγ => ?_
      refine ⟨⟨γ, (Bridge.mem_stab _).2 ?_⟩, ?_⟩
      · rw [hγ, ← map_inv Ψ, ← map_mul Ψ, ← map_mul Ψ]
        exact (hJΨ _).1 hy2
      · apply Subtype.ext
        apply hΨi
        exact (hre _).trans hγ
  refine ⟨hfin, ?_, ?_⟩
  · have h1 : MemLp (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) (GlobalTheory.AutomorphicL2Unitary.descend (GQ V) Φ)) 1 (μ.restrict 𝓕) := by
      rw [hL.lift_descend]; exact memLp_one_iff_integrable.2 hIO
    exact memLp_one_iff_integrable.1 ((GlobalTheory.AutomorphicL2Unitary.memLp_quotMeasure_iff hF).2 h1)
  · show ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) Φ q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) μ = _
    rw [GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure hF]
    simp only [hL.descend_mk]
    rw [hsum, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hcard]

end GlobalTheory.NormDictClassSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenComapProdLev
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.FunObj.ProdOpen

open Filter Topology

variable {D : D7}

theorem mem_GLint_of_entries {L : Type} [Field L] {n : ℕ} (O : Subring L) (g : GL (Fin n) L)
    (h1 : ∀ i j, g.1 i j ∈ O) (h2 : ∀ i j, g⁻¹.1 i j ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem inBasis_apply {n n' : ℕ} (h : n' = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) (i j : Fin n') :
    (inBasis h β w x).1 i j = cpt w ((β⁻¹ * x * β).1 (finCongr h i) (finCongr h j)) := rfl

theorem inBasis_mem_KO {n : ℕ} (β x : GL (Fin n) (Lev.EAf D)) (hx : x ∈ St β) (w : Pl D.host.E) :
    inBasis rfl β w x ∈ KO (Kw w) (Fin n) := by
  obtain ⟨y, rfl⟩ := hx
  rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
  have hm : ∀ z : GL (Fin n) (Lev.EAf D), z ∈ ({Formalism.L2.DIV.intGL _ _ n y, (Formalism.L2.DIV.intGL _ _ n y)⁻¹} : Set _) →
      ∀ a b, cpt w (z.1 a b) ∈ Formalism.UG.Ov D.host.E w := by
    intro z hz a b
    refine (mem_OA_iff _).1 ?_ w
    rcases hz with rfl | rfl
    · exact (y.1 a b).2
    · rw [← map_inv]; exact ((y⁻¹).1 a b).2
  have e1 : β⁻¹ * Formalism.L2.DIV.frGL β y * β = Formalism.L2.DIV.intGL _ _ n y := by
    simp only [Formalism.L2.DIV.frGL, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply]
    group
  have e2 : β⁻¹ * (Formalism.L2.DIV.frGL β y)⁻¹ * β = (Formalism.L2.DIV.intGL _ _ n y)⁻¹ := by
    rw [← e1]; group
  refine mem_GLint_of_entries _ _ (fun i j => ?_) (fun i j => ?_)
  · rw [inBasis_apply, e1]; exact hm _ (Or.inl rfl) _ _
  · rw [← map_inv, inBasis_apply, e2]; exact hm _ (Or.inr rfl) _ _

theorem tendsto_inBasis_val (V : HSp D) {n' : ℕ} (h : n' = V.rank) (β : GL (Fin V.rank) (Lev.EAf D)) (w : Pl D.host.E) :
    Tendsto (fun κ : GA D V => ((inBasis h β w (Lev.finE V κ)).1 : Matrix (Fin n') (Fin n') (Kw w))) (𝓝 1) (𝓝 1) := by
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
  have hf : Continuous (finHom V) := (continuous_subtype_val.comp hπ.continuous).congr fun κ => hπ κ
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (GlobalTheory.LocalData.norm_resChar_lt_one w)
  have hN : Formalism.MainNotions.S.Loc.resChar w ^ k ≠ 0 := pow_ne_zero _ (GlobalTheory.LocalData.resChar_prime w).ne_zero
  filter_upwards [eventually_cong_mat β hN hf (map_one _)] with κ ⟨z, hz, e⟩
  change (β⁻¹ * Lev.finE V κ * β).1 - 1 = _ at e
  have e2 := congr_fun (congr_fun e (finCongr h i)) (finCongr h j)
  rw [Matrix.sub_apply, Matrix.smul_apply, sub_eq_iff_eq_add] at e2
  have e3 : cpt w ((1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) (finCongr h i) (finCongr h j)) =
      (1 : Matrix (Fin n') (Fin n') (Kw w)) i j := by
    simp only [Matrix.one_apply, (finCongr h).injective.eq_iff]
    split_ifs <;> simp
  have hz1 : ‖cpt w (z (finCongr h i) (finCongr h j))‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.2 ((mem_OA_iff _).1 (hz _ _) w)
  rw [dist_eq_norm, inBasis_apply, e2, map_add (f := _), e3, add_sub_cancel_right, map_nsmul, nsmul_eq_mul, norm_mul,
    Nat.cast_pow, norm_pow]
  calc ‖((Formalism.MainNotions.S.Loc.resChar w : ℕ) : Kw w)‖ ^ k * ‖cpt w (z (finCongr h i) (finCongr h j))‖
      ≤ ‖((Formalism.MainNotions.S.Loc.resChar w : ℕ) : Kw w)‖ ^ k * 1 := by gcongr
    _ < ε := by rwa [mul_one]

theorem tendsto_inBasis (V : HSp D) {n' : ℕ} (h : n' = V.rank) (β : GL (Fin V.rank) (Lev.EAf D)) (w : Pl D.host.E) :
    Tendsto (fun κ : GA D V => inBasis h β w (Lev.finE V κ)) (𝓝 1) (𝓝 1) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  rw [Units.isInducing_embedProduct.tendsto_nhds_iff]
  have hinv : Tendsto (fun κ : GA D V => κ⁻¹) (𝓝 1) (𝓝 1) := by
    simpa using (continuous_inv.tendsto (1 : GA D V))
  have h2 : Tendsto (fun κ : GA D V => ((inBasis h β w (Lev.finE V κ))⁻¹).1) (𝓝 1) (𝓝 1) := by
    have := (tendsto_inBasis_val V h β w).comp hinv
    refine this.congr fun κ => ?_
    simp only [Function.comp_apply, map_inv]
  have h3 := (tendsto_inBasis_val V h β w).prodMk_nhds (MulOpposite.continuous_op.tendsto _ |>.comp h2)
  convert h3 using 2
  · ext <;> simp [Units.embedProduct]
  · rw [map_one]; rfl

theorem isOpen_comap_prodLev : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (P : Finset (Pl D.host.E)) {n' : P → ℕ}
    (h : ∀ w, n' w = V.rank) (K : ∀ w : P, Subgroup (GL (Fin (n' w)) (Kw w.1))),
    (∀ w, IsOpen (K w : Set (GL (Fin (n' w)) (Kw w.1)))) →
      IsOpen (((prodLev β P h K).comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) := by
  intro D V β P n' h K hK
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have hP : ∀ w : P, ∀ᶠ κ in 𝓝 (1 : GA D V), inBasis (h w) β w (Lev.finE V κ) ∈ K w := fun w =>
    tendsto_inBasis V (h w) β w.1 ((hK w).mem_nhds (one_mem _))
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ V β ∅, Filter.eventually_all.2 hP] with κ hh h3
  exact Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 h3,
    Subgroup.mem_iInf.2 fun w' => Subgroup.mem_iInf.2 fun _ => inBasis_mem_KO β _ hh.2.1 w'⟩

end GlobalTheory.FunObj.ProdOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVeryAmpleBySectionsOfLinearSpanCombination
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

noncomputable section

namespace GlobalTheory.SpanVA

open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp PSpace resG)
open GlobalTheory.ProjSpace (toProj O1 coord)

theorem iSup_nonzeroLocus_of_span {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) {H : LB X} {m N : ℕ}
    {s : Fin (m + 1) → H.Sec} {t : Fin (N + 1) → H.Sec} {a : Matrix (Fin (m + 1)) (Fin (N + 1)) R}
    (hs : ⨆ i, nonzeroLocus (s i) = ⊤) (hst : ∀ i, s i = ∑ j, GlobalTheory.AbLaw.cst f ⊤ (a i j) • t j) :
    ⨆ j, nonzeroLocus (t j) = ⊤ := by
  refine top_unique fun y _ => ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hs.ge (Set.mem_univ y))
  obtain ⟨k, hk⟩ := GlobalTheory.exists_chart_of_mem_nonzeroLocus hi
  by_contra hne
  have hnu : ∀ j, ¬ IsUnit (X.presheaf.germ (H.U k) y hk ((t j).f k)) := fun j hu =>
    hne (Opens.mem_iSup.2 ⟨j, (GlobalTheory.mem_nonzeroLocus_iff_basicOpen _ hk).2 ((X.mem_basicOpen _ y hk).2 hu)⟩)
  have hu := (X.mem_basicOpen _ y hk).1 ((GlobalTheory.mem_nonzeroLocus_iff_basicOpen _ hk).1 hi)
  have e : (s i).f k = ∑ j, GlobalTheory.AbLaw.cst f (H.U k) (a i j) * (t j).f k := by
    rw [hst i, GlobalTheory.LinChange.sum_f]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [GlobalTheory.LB.smul_f, GlobalTheory.LinChange.resG_cst]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum] at hu
  refine (IsLocalRing.mem_maximalIdeal _).1 (Ideal.sum_mem _ fun j _ => ?_) hu
  rw [map_mul]
  exact Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hnu j))

theorem isClosedImmersion_of_comp_open {X P Q S : Scheme.{0}} (U : P.Opens) (φ : X ⟶ U.toScheme)
    (ψ : U.toScheme ⟶ Q) (p : P ⟶ S) (q : Q ⟶ S) (hc : IsClosedImmersion (φ ≫ ψ)) (hp : IsSeparated p)
    (hq : ψ ≫ q = U.ι ≫ p) (hpr : IsProper (φ ≫ U.ι ≫ p)) : IsClosedImmersion (φ ≫ U.ι) := by
  have : IsSeparated (ψ ≫ q) := by rw [hq]; infer_instance
  have : IsSeparated ψ := IsSeparated.of_comp ψ q
  have : IsClosedImmersion φ := IsClosedImmersion.of_comp φ ψ
  have : IsProper ((φ ≫ U.ι) ≫ p) := by rw [Category.assoc]; exact hpr
  have : IsProper (φ ≫ U.ι) := IsProper.of_comp _ p
  exact IsClosedImmersion.of_isPreimmersion _ (φ ≫ U.ι).isClosedMap.isClosed_range

end GlobalTheory.SpanVA


open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus) in
theorem GlobalTheory.veryAmpleBy_of_span : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (m N : ℕ) (s : Fin (m + 1) → LB.Sec H) (t : Fin (N + 1) → LB.Sec H) (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R), H.IsLB → GlobalTheory.AbLaw.VeryAmpleBy f H s → (∀ i, s i = ∑ j, GlobalTheory.AbLaw.cst f ⊤ (a i j) • t j) → GlobalTheory.AbLaw.VeryAmpleBy f H t := by
  intro R _ X f H m N s t a hH hv hst
  obtain ⟨hs, hci⟩ := (GlobalTheory.ProjSpace.veryAmpleBy_iff f s).1 hv
  have ht := GlobalTheory.SpanVA.iSup_nonzeroLocus_of_span f hs hst
  refine (GlobalTheory.ProjSpace.veryAmpleBy_iff f t).2 ⟨ht, ?_⟩
  have hpre : GlobalTheory.ProjSpace.toProj f t ht ⁻¹ᵁ GlobalTheory.SpanVA.dom a = ⊤ := by
    rw [GlobalTheory.SpanVA.dom, Scheme.Hom.preimage_iSup]
    simp only [_root_.GlobalTheory.SpanVA.toProj_preimage_nonzeroLocus_lin R X f H m N s t a hH ht hst]
    exact hs
  have e := _root_.GlobalTheory.SpanVA.toProj_eq_liftDom_proj R X f H m N s t a hH hs ht hst hpre
  rw [← GlobalTheory.SpanVA.liftDom_fac a _ hpre]
  have hp : IsSeparated (PSpace.str R N) := by unfold PSpace.str; infer_instance
  refine GlobalTheory.SpanVA.isClosedImmersion_of_comp_open _ _ (GlobalTheory.SpanVA.proj a) (PSpace.str R N) (PSpace.str R m)
    (e ▸ hci) hp (GlobalTheory.ProjSpace.toProj_str _ _ _) ?_
  rw [← Category.assoc, GlobalTheory.SpanVA.liftDom_fac, GlobalTheory.ProjSpace.toProj_str]
  exact GlobalTheory.isProper_of_veryAmpleBy hv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.SmallRoute

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def outer (W : G.Weil) (M : Vol G) {t : T} {i j : ℕ} (d : PureT G (routeSmall t i j)) (F : Fn G (.grid i (j + 1)))
    (g₁ : GA D (G.V (.grid (i + 1) j))) : Fn G (.grid i j) := fun u =>
  W.kerA (.right i j) d.2 u g₁ * ∫ g in M.fd (.grid i (j + 1)), W.kerA (.down t i j) d.1.2 g u * F g ∂M.ν (.grid i (j + 1))

theorem liftT_routeSmall (W : G.Weil) (M : Vol G) {t : T} {i j : ℕ} (τ : TotT G (routeSmall t i j))
    (F : Fn G (.grid i (j + 1))) (g₁ : GA D (G.V (.grid (i + 1) j))) :
    liftT W M (routeSmall t i j) τ F g₁ = τ.sum fun d c => c * ∫ u in M.fd (.grid i j), outer W M d F g₁ u ∂M.ν (.grid i j) := by
  simp only [liftT, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rfl

end GlobalTheory.SmallRoute
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanInfLogNormEmbeddingEqLogNormDiv
section
open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)

namespace GlobalTheory

theorem meanInf_log_norm_embedding (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (a : K) (ha : a ≠ 0) :
    Formalism.PairingDivisionLocalBalance.meanInf K (fun v => Real.log ‖v.embedding a‖) = Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| / Module.finrank ℚ K := by
  unfold Formalism.PairingDivisionLocalBalance.meanInf
  have hprod := InfinitePlace.prod_eq_abs_norm (K := K) a
  have hmult : ∀ v : InfinitePlace K, v.mult = 2 := fun v => by
    rw [InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex v))]
  have hpos : ∀ v : InfinitePlace K, 0 < v a := fun v => by
    rw [InfinitePlace.pos_iff]; exact ha
  have hsum : Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| = ∑ v : InfinitePlace K, 2 * Real.log (v a) := by
    rw [show |((Algebra.norm ℚ a : ℚ) : ℝ)| = ((|Algebra.norm ℚ a| : ℚ) : ℝ) by push_cast; rfl, ← hprod, Real.log_prod]
    · refine Finset.sum_congr rfl fun v _ => ?_
      rw [hmult, Real.log_pow]; push_cast; ring
    · intro v _; exact pow_ne_zero _ (hpos v).ne'
  have he : ∀ v : InfinitePlace K, ‖v.embedding a‖ = v a := fun v => InfinitePlace.norm_embedding_eq v a
  simp only [he]
  rw [hsum, ← Finset.mul_sum]
  ring

end GlobalTheory
end

