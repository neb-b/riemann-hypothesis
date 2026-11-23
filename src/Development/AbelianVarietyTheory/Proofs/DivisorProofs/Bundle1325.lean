module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0630
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1256
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1050
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1260
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1316
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1289
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalOfIsSupercuspidal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0624
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrrParIffCuspidalProduct
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1303

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContraMapInjective
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

noncomputable section

namespace GlobalTheory.CosocleOfContra

open ProjLine

section General

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ G V}

theorem isIrreducible_quot {S : Subrepresentation π} (hS : IsCoatom S) : (quot S).IsIrreducible := by
  have h1 : S.toSubmodule ≠ ⊤ := fun e => hS.1 (Subrepresentation.toSubmodule_injective e)
  have := Submodule.Quotient.nontrivial_iff.2 h1
  have : Nontrivial (Subrepresentation (quot S)) := ⟨⊥, ⊤, fun e =>
    bot_ne_top (α := Submodule ℂ (V ⧸ S.toSubmodule)) (congrArg Subrepresentation.toSubmodule e)⟩
  refine ⟨fun T => ?_⟩
  let T' : Subrepresentation π := ⟨T.toSubmodule.comap S.toSubmodule.mkQ, fun g v hv => T.apply_mem_toSubmodule g hv⟩
  have hle : S ≤ T' := fun v hv => by
    show S.toSubmodule.mkQ v ∈ T.toSubmodule
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 hv]
    exact T.toSubmodule.zero_mem
  rcases hS.le_iff.1 hle with e | e
  · right
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨v, rfl⟩ := S.toSubmodule.mkQ_surjective y
    have : v ∈ T' := e ▸ trivial
    exact this
  · left
    refine eq_bot_iff.2 fun y hy => ?_
    obtain ⟨v, rfl⟩ := S.toSubmodule.mkQ_surjective y
    have : v ∈ T' := hy
    rw [e] at this
    exact (Submodule.Quotient.mk_eq_zero _).2 this

end General

section GeneralLinearIntegers

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V}

theorem isSmooth_quot (hπ : IsSmooth π) (S : Subrepresentation π) : IsSmooth (quot S) :=
  (IsSubquotient.of_surjective (quotMk S) S.toSubmodule.mkQ_surjective).isSmooth hπ

end GeneralLinearIntegers

end GlobalTheory.CosocleOfContra
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineBlockLatticesOverPowerSeriesRing
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

namespace GlobalTheory.WachBlock

theorem wach_inputs : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (σ : Equiv.Perm (E →+* PadicAlgCl l)), IsFrobPerm σ → ∀ (n t h : ℕ) (J : (E →+* PadicAlgCl l) → Fin n → ℤ) (bot : (E →+* PadicAlgCl l) → ℤ), (∀ i a, 0 ≤ J i a ∧ J i a ≤ h) → (∀ i (s : Fin t), 0 ≤ bot i + ((s : ℕ) : ℤ) ∧ bot i + ((s : ℕ) : ℤ) ≤ h) → BlockPair E Ω l n t J bot → ∃ (O' F L' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : Algebra ℤ_[l] O') (_ : Field F) (_ : CharP F l) (_ : Field L') (I : Ideal O') (_ : IsAdicComplete I O') (Wl : Formalism.CohomologicalDescent.FrobeniusPeriodChange.WLat (E →+* PadicAlgCl l) t n O' F) (u : ℤ_[l]ˣ) (c : ℤ_[l]) (kap : (E →+* PadicAlgCl l) → Fin t → ℤ) (ζ : O') (em : O' →+* L') (jj : ℕ → PowerSeries O' →+* PowerSeries L'), Formalism.CohomologicalDescent.FrobeniusPeriodChange.NInputs Wl σ l h u c J (fun i s => bot i + ((s : ℕ) : ℤ)) kap I ζ em jj := by
  intro hBS E Ω _ _ _ _ _ _ l _ hl2 hdisc σ hσ n t h J bot hJ hbot hBP
  obtain ⟨O', F, L', i1, i2, i3, i4, i5, i6, I, i7, red, un, N, Npsi, u, c, ζ, em, jj, hU, hR, hN, hψ, hF⟩ :=
    _root_.GlobalTheory.WachPlace.wach_lattices hBS E Ω l hl2 hdisc σ hσ n t h J bot hJ hbot (_root_.GlobalTheory.WachBlock.integralBlock_of_blockPair E Ω l n t J bot hBP)
  obtain ⟨g, b, pos, w, kap, hpos, hP, hG, hPd, hGd⟩ :=
    _root_.GlobalTheory.WachBlock.adapted_bases_of_redFilt _ σ l n t F _ _ _ _ _ (Fact.out : l.Prime).pos inferInstance hF
  exact ⟨O', F, L', i1, i2, i3, i4, i5, i6, I, i7, ⟨red, un, N, Npsi, g, b, pos, w⟩, u, c, kap, ζ, em, jj,
    ⟨hU, hJ, hbot, hpos, hP, hG, hPd, hGd⟩, hR, hN, hψ⟩

end GlobalTheory.WachBlock

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveDegreeNonnegZmodFibreOfNefOnFiniteFieldFibr
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

namespace GlobalTheory.NefFibPrime

theorem isClosedImmersion_spMap_zmod (p : ℕ) : IsClosedImmersion (spMap (Int.castRingHom (ZMod p))) :=
  IsClosedImmersion.spec_of_surjective _ (ZMod.ringHom_surjective (Int.castRingHom (ZMod p)))

theorem topSelf_nonneg_of_nefFib (k : Type) [CommRing k] (W : Scheme.{0}) (q : W ⟶ Sp k) (L : HermLB q) (p : ℕ)
    [Fact p.Prime] (h : ArInt.NefFib L) (Z : Scheme.{0})
    (i : Z ⟶ pullback (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))))
    [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod p) Γ(Z, ⊤)] (hd : topologicalKrullDim Z = 1) :
    0 ≤ topSelfIntersection (ZMod p) ((L.B.pull (pullback.fst (q ≫ spMap (Int.castRingHom k))
      (spMap (Int.castRingHom (ZMod p))))).pull i) 1 := by
  have := isClosedImmersion_spMap_zmod p
  have : IsClosedImmersion (pullback.fst (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))) :=
    IsClosedImmersion.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip this
  set f := pullback.fst (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))) with hf
  have h1 := h Z (i ≫ f) (ZMod p) hd
  have e : topSelfIntersection (ZMod p) ((L.B.pull f).pull i) 1 = topSelfIntersection (ZMod p) (L.B.pull (i ≫ f)) 1 := by
    rw [topSelf_def, topSelf_def]
    refine interNum_congr_cls (ZMod p) _ (fun _ => LB.isLB_pull (LB.isLB_pull L.isLB f) i)
      (fun _ => LB.isLB_pull L.isLB (i ≫ f)) fun _ => ?_
    show pull i (pull f (cls L.B L.isLB)) = pull (i ≫ f) (cls L.B L.isLB)
    rw [← pull_comp]
  rw [e]
  exact h1

end GlobalTheory.NefFibPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormGLSiegelConeDecayOneStep
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

theorem cuspForm_decay_step : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ψ : Sm E a), IsCuspForm ψ → ∀ t : ℝ, 0 < t → ∀ i j : Fin a, (j : ℕ) = i + 1 → ∀ (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω → ∃ (Ω' : Set (GL (Fin a) (Cinf E))) (B : Finset (Lie E a)) (C : ℝ), IsCompact Ω' ∧ 0 ≤ C ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∀ M : ℝ, 0 ≤ M → (∀ Y ∈ B, ∀ c' ∈ Ω', ‖lieD Y ψ.1 (infGL E a (d * c'))‖ ≤ M) → ∀ c ∈ Ω, ‖ψ.1 (infGL E a (d * c))‖ ≤ C * (r j / r i) * M := by
  intro E _ _ _ a ψ hψ t ht i j hij Ω hΩ
  have hL : {k | finRep E a k ψ = ψ} ∈ nhds (1 : GL (Fin a) (Af E)) :=
    hψ.1.level.mem_nhds (by simp)
  obtain ⟨R, hR0, hcov⟩ := _root_.GlobalTheory.RapCover.unip_eq_rat_mul_inf_mul_fin E a (j : ℕ) _ hL
  obtain ⟨Ω', B, C, hΩ', hC, hvar⟩ := _root_.GlobalTheory.rap_vari E a t ht i j hij Ω hΩ R hR0
  refine ⟨Ω', B, C, hΩ', hC, fun r d hr hrt hd M hM hY c hc => ?_⟩
  refine _root_.GlobalTheory.CuspRep.norm_le_of_unip_variation E a ψ hψ (j : ℕ) (by omega) j.2 (infGL E a (d * c)) (C * (r j / r i) * M) fun x => ?_
  obtain ⟨ξ, z, k, hk, hz, hx⟩ := hcov x
  have hk' : finRep E a k ψ = ψ := hk
  have e : ψ.1 (unip x * infGL E a (d * c)) = ψ.1 (infGL E a (unip z * (d * c))) := by
    rw [hx, mul_assoc, mul_assoc, ← infGL_comm, ← mul_assoc (infGL E a (unip z)), ← map_mul, hψ.1.left]
    have := congrArg (fun φ : Sm E a => φ.1 (infGL E a (unip z * (d * c)))) hk'
    exact this
  rw [e]
  exact hvar ψ r d hr hrt hd M hM hY c hc z hz

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspRepPairedWithItselfStatement
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_rep_paired_with_itself : GlobalTheory.Published.JacquetShalikaRigidity → GlobalTheory.Published.CuspFormsBoundedGL → GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a, GlobalTheory.DiscSpec.IsNormalised π → Paired π π invTOp := by
  first | exact @GlobalTheory.GKPair.paired_invTOp | exact GlobalTheory.GKPair.paired_invTOp | (intros; apply GlobalTheory.GKPair.paired_invTOp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalInvTranspose
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

namespace GlobalTheory.InvTransposeCusp

theorem invTranspose_invol {R : Type} [CommRing R] (n : ℕ) (g : GL (Fin n) R) :
    GlobalTheory.TypeTame.invTranspose n (GlobalTheory.TypeTame.invTranspose n g) = g := by
  apply Units.ext
  exact Matrix.transpose_transpose (g : Matrix (Fin n) (Fin n) R)

theorem isSupercuspidal_comp_invTranspose (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (hs : IsSupercuspidal π) :
    IsSupercuspidal (π.comp (GlobalTheory.TypeTame.invTranspose n)) := by
  have hcont := GlobalTheory.TypeTame.continuous_invTranspose (R := k) n
  obtain ⟨hsm, hc⟩ := hs
  refine ⟨fun v => (hsm v).preimage hcont, ?_⟩
  intro v l hl
  have hl' : l ∈ smoothPart π.dual := by
    show IsOpen {g | π.dual g l = l}
    have : {g | π.dual g l = l} = (GlobalTheory.TypeTame.invTranspose n) ⁻¹'
        {g | Representation.dual (π.comp (GlobalTheory.TypeTame.invTranspose n)) g l = l} := by
      ext g
      simp [Representation.dual, map_inv, invTranspose_invol]
    rw [this]
    exact hl.preimage hcont
  obtain ⟨C, hC, hCl⟩ := hc v l hl'
  refine ⟨(GlobalTheory.TypeTame.invTranspose n) '' C, hC.image hcont, fun g hg => ?_⟩
  obtain ⟨z, hz, c, hcC, hgc⟩ := hCl (GlobalTheory.TypeTame.invTranspose n g) hg
  refine ⟨GlobalTheory.TypeTame.invTranspose n z, ?_, GlobalTheory.TypeTame.invTranspose n c, ⟨c, hcC, rfl⟩, ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro h
    have := Subgroup.mem_center_iff.1 hz (GlobalTheory.TypeTame.invTranspose n h)
    have h2 := congrArg (GlobalTheory.TypeTame.invTranspose n) this
    simpa [map_mul, invTranspose_invol] using h2
  · rw [← map_mul, ← hgc, invTranspose_invol]

theorem isCuspidal_comp_invTranspose : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsCuspidal π → IsCuspidal (π.comp (GlobalTheory.TypeTame.invTranspose n)) := by
  intro k _ _ _ _ n V _ _ π h
  exact GlobalTheory.SuperCusp.isCuspidal_of_isSupercuspidal k n V _
    (isSupercuspidal_comp_invTranspose k n V π
      (GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal k n V π h))

end GlobalTheory.InvTransposeCusp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalSpectrumFinitenessOfDecayHarishChandra
section
noncomputable section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SpecFinite

open GlobalTheory.CuspMult GlobalTheory.PRep

section Abstract

variable {H X : Type} [Group H] [TopologicalSpace H] [AddCommGroup X] [Module ℂ X]

theorem simple_asSubmodule {ρ : Representation ℂ H X} (U : Subrepresentation ρ) (hU : U.toRepresentation.IsIrreducible) :
    IsSimpleModule (MonoidAlgebra ℂ H) U.asSubmodule := by
  haveI : IsSimpleModule (MonoidAlgebra ℂ H) U.toRepresentation.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).1 hU
  exact IsSimpleModule.congr (GlobalTheory.RepCount.subEquiv U).symm

theorem exists_sub_equiv {W : Type} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ H W} {ρ : Representation ℂ H X}
    (h1 : σ.IsIrreducible) {f : W →ₗ[ℂ] X} (hf : ∀ g s, f (σ g s) = ρ g (f s)) (h0 : f ≠ 0) :
    ∃ U : Subrepresentation ρ, U.toSubmodule = LinearMap.range f ∧ Function.Injective f ∧
      ∃ e : W ≃ₗ[ℂ] U.toSubmodule, (∀ s, (e s : X) = f s) ∧ ∀ g s, e (σ g s) = U.toRepresentation g (e s) := by
  let F := f.intertwiningMap_of_isIntertwiningMap σ ρ hf
  have hi : Function.Injective f := by
    rcases Representation.IsIrreducible.injective_or_eq_zero F with hi | hz
    · exact hi
    · exact absurd (LinearMap.ext fun s => DFunLike.congr_fun hz s) h0
  exact ⟨F.range, rfl, hi, LinearEquiv.ofInjective f hi, fun s => rfl, fun g s => Subtype.ext (hf g s)⟩

theorem rank_homInto_lt {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ H W) (ρ : Representation ℂ H X)
    (C : Submodule ℂ X) (K : Subgroup H) (hA : FiniteDimensional ℂ ↥(C ⊓ fixed ρ K)) (h1 : σ.IsIrreducible)
    {x : W} (hx0 : x ≠ 0) (hx : ∀ k ∈ K, σ k x = x) : Module.rank ℂ (homInto σ ρ C) < Cardinal.aleph0 := by
  let ev : homInto σ ρ C →ₗ[ℂ] ↥(C ⊓ fixed ρ K) :=
    { toFun := fun f => ⟨(f : W →ₗ[ℂ] X) x, f.2.1 x, GlobalTheory.CuspDec.mem_fixed.2 fun k hk => by rw [← f.2.2, hx k hk]⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective ev := by
    refine (injective_iff_map_eq_zero ev).2 fun f hf => ?_
    by_contra hne
    obtain ⟨U, -, hi, -⟩ := exists_sub_equiv h1 f.2.2 (fun h => hne (Subtype.ext h))
    have h0 : (f : W →ₗ[ℂ] X) x = (f : W →ₗ[ℂ] X) 0 := by
      rw [map_zero]
      exact congrArg Subtype.val hf
    exact hx0 (hi h0)
  haveI := FiniteDimensional.of_injective ev hinj
  exact Module.rank_lt_aleph0 ℂ _

theorem finite_classes (ρ : Representation ℂ H X) (C : Submodule ℂ X) (K : Subgroup H)
    (hA : FiniteDimensional ℂ ↥(C ⊓ fixed ρ K)) :
    ∃ (n : ℕ) (Ws : Fin n → Type) (_ : ∀ i, AddCommGroup (Ws i)) (_ : ∀ i, Module ℂ (Ws i))
      (σs : ∀ i, Representation ℂ H (Ws i)),
      ((∀ i, (σs i).IsIrreducible) ∧ (∀ i, IsAdmissible (σs i)) ∧ ∀ i j, i ≠ j → IsEmpty ((σs i).Equiv (σs j))) ∧
      ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ H W), σ.IsIrreducible → IsAdmissible σ →
        homInto σ ρ C ≠ ⊥ → (∃ x : W, x ≠ 0 ∧ ∀ k ∈ K, σ k x = x) → ∃ i, Nonempty (σ.Equiv (σs i)) := by
  classical
  let S : Set (Subrepresentation ρ) := {U | U.toSubmodule ≤ C ∧ U.toRepresentation.IsIrreducible ∧
    IsAdmissible U.toRepresentation ∧ U.toSubmodule ⊓ fixed ρ K ≠ ⊥}
  let comp : Subrepresentation ρ → Submodule (MonoidAlgebra ℂ H) ρ.asModule :=
    fun U => isotypicComponent (MonoidAlgebra ℂ H) ρ.asModule U.asSubmodule
  let T : Set (Submodule (MonoidAlgebra ℂ H) ρ.asModule) := comp '' S
  have hT : sSupIndep T := (sSupIndep_isotypicComponents (MonoidAlgebra ℂ H) ρ.asModule).mono (by
    rintro _ ⟨U, hU, rfl⟩
    exact ⟨U.asSubmodule, simple_asSubmodule U hU.2.1, rfl⟩)
  have hy : ∀ c : T, ∃ y : ↥(C ⊓ fixed ρ K), y ≠ 0 ∧
      ρ.asModuleEquiv.symm (y : X) ∈ (c : Submodule (MonoidAlgebra ℂ H) ρ.asModule) := by
    rintro ⟨_, U, hU, rfl⟩
    obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hU.2.2.2
    exact ⟨⟨y, hU.1 hy.1, hy.2⟩, fun h => hy0 (congrArg Subtype.val h), U.asSubmodule.le_isotypicComponent hy.1⟩
  choose y hy0 hyc using hy
  have hsm : ∀ (c : T) (a : ℂ), ρ.asModuleEquiv.symm ((a • y c : ↥(C ⊓ fixed ρ K)) : X) ∈
      (c : Submodule (MonoidAlgebra ℂ H) ρ.asModule) := fun c a => by
    rw [Submodule.coe_smul, map_smul]
    exact Submodule.smul_of_tower_mem _ a (hyc c)
  have hli : LinearIndependent ℂ y := by
    rw [linearIndependent_iff']
    intro s g hs i hi
    have hx : ρ.asModuleEquiv.symm ((g i • y i : ↥(C ⊓ fixed ρ K)) : X) ∈
        (i : Submodule (MonoidAlgebra ℂ H) ρ.asModule) ⊓ sSup (T \ {(i : Submodule (MonoidAlgebra ℂ H) ρ.asModule)}) := by
      refine ⟨hsm i (g i), ?_⟩
      have he : (g i • y i : ↥(C ⊓ fixed ρ K)) = - ∑ j ∈ s.erase i, g j • y j := by
        rw [eq_neg_iff_add_eq_zero, Finset.add_sum_erase s (fun j => g j • y j) hi, hs]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [he, Submodule.coe_neg, Submodule.coe_sum, map_neg, map_sum]
      refine Submodule.neg_mem _ (Submodule.sum_mem _ fun j hj => ?_)
      refine (le_sSup (show (j : Submodule (MonoidAlgebra ℂ H) ρ.asModule) ∈ T \ {(i : Submodule (MonoidAlgebra ℂ H) ρ.asModule)} from
          ⟨j.2, fun h => Finset.ne_of_mem_erase hj (Subtype.ext h)⟩) :
        (j : Submodule (MonoidAlgebra ℂ H) ρ.asModule) ≤ _) (hsm j (g j))
    rw [(hT i.2).eq_bot, Submodule.mem_bot, LinearEquiv.map_eq_zero_iff, Submodule.coe_eq_zero, smul_eq_zero] at hx
    exact hx.resolve_right (hy0 i)
  haveI : Finite T := hli.finite
  haveI := Fintype.ofFinite T
  let e := Fintype.equivFin T
  have hrep : ∀ c : T, ∃ U ∈ S, comp U = c := fun c => c.2
  choose U hUS hUc using hrep
  refine ⟨Fintype.card T, fun i => ↥(U (e.symm i)).toSubmodule, fun i => inferInstance, fun i => inferInstance,
    fun i => (U (e.symm i)).toRepresentation, ⟨fun i => (hUS _).2.1, fun i => (hUS _).2.2.1, fun i j hij => ⟨fun φ => hij ?_⟩⟩, ?_⟩
  · obtain ⟨ψ⟩ := (GlobalTheory.CuspFactor.nonempty_equiv_iff _ _).1 ⟨φ⟩
    have h3 := ((GlobalTheory.RepCount.subEquiv _).symm.trans (ψ.trans (GlobalTheory.RepCount.subEquiv _))).isotypicComponent_eq
      (M := ρ.asModule)
    exact e.symm.injective (Subtype.ext ((hUc _).symm.trans (h3.trans (hUc _))))
  · rintro W _ _ σ h1 h2 hne ⟨x, hx0, hx⟩
    obtain ⟨f, hf, hf0⟩ := (Submodule.ne_bot_iff _).1 hne
    obtain ⟨V, hV, hi, ev, hev, heq⟩ := exists_sub_equiv h1 hf.2 hf0
    haveI : IsSimpleModule (MonoidAlgebra ℂ H) σ.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule _).1 h1
    let ψ : σ.asModule ≃ₗ[MonoidAlgebra ℂ H] V.toRepresentation.asModule :=
      LinearEquiv.ofBijective (GlobalTheory.RepCount.modMap ev.toLinearMap heq) ev.bijective
    have hVirr : V.toRepresentation.IsIrreducible :=
      (Representation.irreducible_iff_isSimpleModule_asModule _).2 (IsSimpleModule.congr ψ.symm)
    have hVS : V ∈ S := by
      refine ⟨?_, hVirr, GlobalTheory.RepCount.isAdmissible_of_injective ev.symm.toLinearMap (fun g s => ?_) ev.symm.injective h2, ?_⟩
      · rw [hV]
        rintro _ ⟨s, rfl⟩
        exact hf.1 s
      · rw [LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_eq, heq, LinearEquiv.apply_symm_apply]
      · rw [Submodule.ne_bot_iff]
        refine ⟨f x, ⟨hV ▸ ⟨x, rfl⟩, GlobalTheory.CuspDec.mem_fixed.2 fun k hk => by rw [← hf.2, hx k hk]⟩, fun h => hx0 (hi ?_)⟩
        rw [h, map_zero]
    refine ⟨e ⟨comp V, V, hVS, rfl⟩, ?_⟩
    show Nonempty (σ.Equiv (U (e.symm (e ⟨comp V, V, hVS, rfl⟩))).toRepresentation)
    generalize hc : e.symm (e ⟨comp V, V, hVS, rfl⟩) = c
    rw [Equiv.symm_apply_apply] at hc
    haveI := simple_asSubmodule V hVirr
    haveI := simple_asSubmodule (U c) (hUS c).2.1
    have hle : (U c).asSubmodule ≤ comp V :=
      ((U c).asSubmodule.le_isotypicComponent).trans_eq ((hUc c).trans (congrArg Subtype.val hc).symm)
    obtain ⟨χ⟩ := isIsotypicOfType_submodule_iff.mp
      (IsIsotypicOfType.isotypicComponent (MonoidAlgebra ℂ H) ρ.asModule V.asSubmodule) _ hle
    exact (GlobalTheory.CuspFactor.nonempty_equiv_iff _ _).2
      ⟨(ψ.trans (GlobalTheory.RepCount.subEquiv V)).trans (χ.symm.trans (GlobalTheory.RepCount.subEquiv _).symm)⟩

end Abstract

theorem specFin : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.DixmierMalliavinFactorisation →
    SpecFin := by
  intro hQ hP hDM D V S M μ _ _
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  have hm : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), IsAdmissible σ →
      mCuspDS μ σ M = Module.rank ℂ (homInto σ (finRep M) (allMaps θ M)) := fun W _ _ σ h =>
    (_root_.GlobalTheory.AutMult.cuspMult_eq_mCuspDS hQ hP hDM D θ hθ V S M μ W σ h.1).symm
  refine ⟨fun W _ _ σ h1 h2 => ?_, fun K hK => ?_⟩
  · haveI := GlobalTheory.CuspFactor.nontrivial_of_irr σ h1
    obtain ⟨x, hx0⟩ := exists_ne (0 : W)
    let St : Subgroup (GfC V) :=
      { carrier := {g | σ g x = x}
        mul_mem' := fun {a b} ha hb => by
          show σ (a * b) x = x
          rw [map_mul, Module.End.mul_apply, hb, ha]
        one_mem' := by simp
        inv_mem' := fun {a} ha => by
          show σ a⁻¹ x = x
          conv_lhs => rw [← ha]
          simp }
    rw [hm W σ h2]
    exact rank_homInto_lt σ (finRep M) (allMaps θ M) St (GlobalTheory.CuspDec.finiteDimensional_fixed hP hθ St (h2.1 x)) h1 hx0
      (fun k hk => hk)
  · obtain ⟨n, Ws, i1, i2, σs, hs, hcov⟩ :=
      finite_classes (finRep M) (allMaps θ M) K (GlobalTheory.CuspDec.finiteDimensional_fixed hP hθ K hK)
    refine ⟨n, Ws, i1, i2, σs, hs, fun W _ _ σ h1 h2 hm0 hx => hcov W σ h1 h2 (fun h => hm0 ?_) hx⟩
    rw [hm W σ h2, h, rank_bot]

end GlobalTheory.SpecFinite

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetColumnsNeZeroOfPointValuesIndependent
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShort.DetNe

theorem det_ne_zero_of_indep : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → E) (δ : ℕ) (Φ : S.Flat E A' s δ) (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∀ (col : Fin d → S.Col) (u : Fin (S.D + 1) × Fin S.N → E), LinearIndependent E (fun k => word Φ.mul (fun q j => u ((col k).β q, j)) (Φ.ι (col k).x)) → S.det c col ≠ 0 := by
  intro F A _ _ _ _ _ _ S hS E A' _ _ _ _ s δ Φ d b c hc col u hind hdet
  obtain ⟨c', hspan, hval⟩ := _root_.GlobalTheory.HSShort.ColEval.columns_eval F A S hS E A' s δ Φ d b c hc
  set v : Fin d → A' := fun k => word Φ.mul (fun q j => u ((col k).β q, j)) (Φ.ι (col k).x) with hv
  set M : Matrix (Fin d) (Fin d) E := Matrix.of fun i k => c' i (v k) with hM
  have hMdet : M.det = 0 := by
    have h1 : aeval u (S.det c col) = 0 := by rw [hdet, map_zero]
    rw [Sys.det, AlgHom.map_det] at h1
    convert h1 using 2
    ext i k
    simp only [hM, Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply]
    exact ((hval (col k) u).2 i).symm
  obtain ⟨a, ha, hMa⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hMdet
  have hmem : ∀ k, v k ∈ Submodule.span E (Φ.ι '' S.V S.T) := fun k => (hval (col k) u).1
  set x : A' := ∑ k, a k • v k with hx
  have hxmem : x ∈ Submodule.span E (Φ.ι '' S.V S.T) :=
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hmem k)
  have hcx : ∀ i, c' i x = 0 := by
    intro i
    have := congrFun hMa i
    simp only [Matrix.mulVec, dotProduct, hM, Matrix.of_apply, Pi.zero_apply] at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx, map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hx0 : x = 0 := by
    rw [← hspan x hxmem]
    simp [hcx]
  have ha0 := (Fintype.linearIndependent_iff.mp hind) a hx0
  exact ha (funext ha0)

end GlobalTheory.HSShort.DetNe
end

