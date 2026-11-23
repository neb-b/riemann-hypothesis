module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0231
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatchOfMatchOffTEmpty
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0178
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0755
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0355
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0701
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0234
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0233
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraicModularFormsStrongMultiplicityOneStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_modular_forms_strong_multiplicity_one : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S₁ S₂ : Submodule ℂ (GAf L n → a.W)) (h₁ : NG.IsIrrRep a.ρ S₁) (h₂ : NG.IsIrrRep a.ρ S₂), (∀ s : SplitPlace L, ∃ σ₁ σ₂ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)), IsLocS S₁ s σ₁ ∧ IsLocS S₂ s σ₂ ∧ Nonempty (σ₁.ρ.Equiv σ₂.ρ)) → (∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)), (∀ s : SplitPlace L, s.v ≠ v) → ∃ (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.OverPl w v ∧ NG.SatAt { a with S := S₁, irrS := h₁ } Dv α ∧ NG.SatAt { a with S := S₂, irrS := h₂ } Dv α) → NG.IsoRep S₁ S₂ := by
  first | exact @GlobalTheory.GlobDet.main | exact GlobalTheory.GlobDet.main | (intros; apply GlobalTheory.GlobDet.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutFormFixedByIntegralPointsAlmostAllPlaces
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
open GlobalTheory.Cong.AdaptLev

noncomputable section

namespace GlobalTheory.Cong.AutFormFix

open Matrix GlobalTheory.BCT.GlobLev GroundTheory.Automorphic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem eq_one_of_forall_cLoc {x : UA E a} (hx : x ∈ finU (E := E) (n := a)) (h : ∀ u, cLoc u x = 1) : x = 1 := by
  refine Subtype.ext (ga_ext ?_ ?_)
  · exact (MonoidHom.mem_ker.1 hx).trans (map_one _).symm
  · rw [Subgroup.coe_one, map_one]
    refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun u => ?_)
    have := congrArg (fun g : GL (Fin a) (u.adicCompletion E) => g.val i j) (h u)
    simp only [Units.val_one, Matrix.one_apply] at this
    refine this.trans ?_
    split_ifs with hij <;> simp [hij] <;> rfl

theorem mem_integral_iff (k : finU (E := E) (n := a)) :
    k ∈ (AdelicGLn.integralFiniteGL E a).comap (finPart E a) ↔ ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u (n := a) := by
  rw [Subgroup.mem_comap, AdelicGLn.mem_integralFiniteGL_iff, ← map_inv]
  simp only [mem_KGL_iff_val, ← map_inv, GroundTheory.Global.mem_integralFiniteAdeles]
  exact ⟨fun h u => ⟨fun i j => h.1 i j u, fun i j => h.2 i j u⟩,
    fun h => ⟨fun i j u => (h u).1 i j, fun i j u => (h u).2 i j⟩⟩

theorem isCompact_integral :
    IsCompact (((AdelicGLn.integralFiniteGL E a).comap (finPart E a) : Subgroup (finU (E := E) (n := a))) : Set (finU (E := E) (n := a))) := by
  have hO : IsOpen (((AdelicGLn.integralFiniteGL E a).comap (finPart E a) : Subgroup (finU (E := E) (n := a))) : Set (finU (E := E) (n := a))) :=
    (AdelicGLn.isOpen_integralFiniteGL E a).preimage continuous_finPart
  refine IsCompact.of_isClosed_subset (isClosedEmbedding_finU.isCompact_preimage
    ((AdelicGLn.isCompact_integralFiniteGL E a).image continuous_finGL_ad))
    (Subgroup.isClosed_of_isOpen _ hO) fun x hx => ⟨finPart E a x, hx, ?_⟩
  have h1 : GeneralLinearGroup.map (pInf E) ((x : UA E a) : GA E a) = 1 := x.2
  exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)

end GlobalTheory.Cong.AutFormFix

namespace GlobalTheory.Cong.AutFormFix

open Matrix GlobalTheory.BCT.GlobLev GroundTheory.Automorphic

theorem fixed_intU_eventually : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (φ : UA E a → ℂ),
    IsAutFormU φ → ∀ᶠ w in Filter.cofinite, ∀ x ∈ GlobalTheory.Cong.AdaptLev.intU a w, RU E a x φ = φ := by
  intro E _ _ _ a φ hφ
  classical
  set St : Set (finU (E := E) (n := a)) := {k : finU (E := E) (n := a) | RU E a k φ = φ} with hSt
  set K₀ : Set (finU (E := E) (n := a)) := (((AdelicGLn.integralFiniteGL E a).comap (finPart E a) : Subgroup (finU (E := E) (n := a))) : Set (finU (E := E) (n := a)))
  let t : Finset (HeightOneSpectrum (𝓞 E)) → Set (finU (E := E) (n := a)) := fun S =>
    {k : finU (E := E) (n := a) | ∀ u ∈ S, cLoc u k.1 = 1} ∩ Stᶜ
  have htc : ∀ S, IsClosed (t S) := by
    intro S
    refine IsClosed.inter ?_ hφ.level.isClosed_compl
    have : {k : finU (E := E) (n := a) | ∀ u ∈ S, cLoc u k.1 = 1} = ⋂ u ∈ S, {k : finU (E := E) (n := a) | cLoc u k.1 = 1} := by
      ext k; simp
    rw [this]
    refine isClosed_biInter fun u _ => ?_
    haveI : T2Space (GL (Fin a) (u.adicCompletion E)) := Units.isEmbedding_embedProduct.t2Space
    exact isClosed_eq ((continuous_cLoc u).comp continuous_subtype_val) continuous_const
  have hst : K₀ ∩ ⋂ S, t S = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun k hk => ?_
    have hall : ∀ u, cLoc u k.1 = 1 := fun u =>
      (Set.mem_iInter.1 hk.2 {u}).1 u (Finset.mem_singleton_self u)
    have h1 : k = 1 := Subtype.ext (eq_one_of_forall_cLoc k.2 hall)
    have hnot := (Set.mem_iInter.1 hk.2 ∅).2
    apply hnot
    rw [h1]
    show RU E a ((1 : finU (E := E) (n := a)) : UA E a) φ = φ
    rw [Subgroup.coe_one, map_one]; rfl
  have hdt : Directed (· ⊇ ·) t := by
    intro S₁ S₂
    refine ⟨S₁ ∪ S₂, ?_, ?_⟩ <;> rintro k ⟨hk, hk'⟩ <;> refine ⟨fun u hu => hk u ?_, hk'⟩ <;> simp [hu]
  obtain ⟨S, hS⟩ := isCompact_integral.elim_directed_family_closed t htc (Set.disjoint_iff_inter_eq_empty.mpr hst) hdt
  have hfin : {w : HeightOneSpectrum (𝓞 E) | ¬ ∀ u ∈ S, Apart u w}.Finite := by
    refine ((S.finite_toSet.biUnion fun u _ => (Set.toFinite ({u, conjSrc (GlobalTheory.SplitPts.conjE E) u} : Set _)))).subset ?_
    intro w hw
    simp only [Set.mem_setOf_eq, not_forall, Apart, not_not] at hw
    obtain ⟨u, hu, he⟩ := hw
    refine Set.mem_biUnion hu ?_
    rcases eq_or_eq_conjSrc he.symm with rfl | rfl
    · simp
    · simp
  refine Filter.eventually_cofinite.2 (hfin.subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq] at hw ⊢
  intro hS'
  apply hw
  intro x hx
  obtain ⟨hxl, hxi⟩ := GlobalTheory.Cong.AdaptLev.mem_intU.1 hx
  have hxf : x ∈ finU (E := E) (n := a) := (Subgroup.mem_inf.1 hxl).1
  have hcomp : ∀ u, Apart u w → cLoc u x = 1 := fun u hu =>
    MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hxl).2 u) hu)
  have hK : (⟨x, hxf⟩ : finU (E := E) (n := a)) ∈ K₀ := by
    refine (mem_integral_iff _).2 fun u => ?_
    by_cases hu : Apart u w
    · show cLoc u x ∈ _
      rw [hcomp u hu]; exact one_mem _
    · exact hxi u hu
  by_contra hne
  have : (⟨x, hxf⟩ : finU (E := E) (n := a)) ∈ K₀ ∩ t S := ⟨hK, fun u hu => hcomp u (hS' u hu), hne⟩
  exact (Set.disjoint_left.mp hS) this.1 this.2

end GlobalTheory.Cong.AutFormFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClauseAtOfRepIso
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published GlobalTheory.ContraPair

namespace GlobalTheory.GalCut

theorem clauseAt_of_repIso : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : CuspSub E a) (r r' : G E Ω →* GL (Fin a) (Qbar l)), Continuous r → UpperTheory.V.Af.RepIso r r' → ∀ c w, ClauseAt c π ι r w → ClauseAt c π ι r' w := by
  intro E Ω _ _ _ _ _ _ l _ ι a π r r' _ hiso c w hc
  obtain ⟨p, hp⟩ := hiso
  have hcw : ∀ {A : ValuationSubring Ω} (h : IsPlaceOver A w) (g : Weil h), p * r g = r' g * p :=
    fun h g => by rw [hp]; group
  have hcd : ∀ (A : ValuationSubring Ω) (g : ↥(Dec (F := E) A)), r'.comp (Dec (F := E) A).subtype g =
      p * r.comp (Dec (F := E) A).subtype g * p⁻¹ := fun A g => hp g
  cases c with
  | ss =>
    intro hl A h rc hrc σ hσ g
    rw [← wdOf_eq_of_conj hl p (hcw h)]
    exact hc hl A h rc hrc σ hσ g
  | pure =>
    intro hl A h wt hwt
    rw [← wdOf_eq_of_conj hl p (hcw h)]
    exact hc hl A h wt hwt
  | dR =>
    intro P AI hT A hA O _ _ _ Bw hj
    obtain ⟨h1, h2⟩ := hc P AI hT A hA O Bw hj
    obtain ⟨k1, -, -, k4⟩ := GlobalTheory.ConjLocal.local_conj l P E Ω O _ Bw a _ _ p (hcd A)
    exact ⟨k1 h1, fun τ LL' τ' hτ J hJ => k4 τ J (h2 τ LL' τ' hτ J hJ)⟩
  | crys =>
    intro P AI hT A hA O _ _ _ Bw hj σ hσ hS
    obtain ⟨-, k2, -, -⟩ := GlobalTheory.ConjLocal.local_conj l P E Ω O _ Bw a _ _ p (hcd A)
    exact k2 (hc P AI hT A hA O Bw hj σ hσ hS)
  | iwa =>
    intro P AI hT A h O _ _ _ Bw hj σ hσ hI
    obtain ⟨h3, h4⟩ := hc P AI hT A h O Bw hj σ hσ hI
    exact ⟨GlobalTheory.AboveL.RepConj.isSstAt_conj P Bw p (hcd A) h3, fun rc hrc =>
      (GlobalTheory.AboveL.RepConj.wdAt_conj P ι Bw h hj p (hcd A)).trans (h4 rc hrc)⟩

end GlobalTheory.GalCut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeIffLocalComponentSatakeStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspRep_satake_iff_localComponent_satake : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), π.IsLocComp w σ → (∀ B, (CG.mk π).HasSat w B ↔ GlobalTheory.LFun.HasSatGL w σ.ρ B) ∧ (GlobalTheory.SmGL.IsSpherical σ.ρ ↔ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.LFun.KGL w (n := a)) ≠ ⊥) := by
  first | (exact @GlobalTheory.Cong.satake_locComp) | (exact GlobalTheory.Cong.satake_locComp) | (intros; apply GlobalTheory.Cong.satake_locComp  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DefiniteUnitaryIntegralBelowPlaceCompactOpen
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
open GlobalTheory.Cong.AdaptLev

noncomputable section

namespace GlobalTheory.Cong.AdaptLev

open GlobalTheory.BCT.GlobLev GroundTheory.Automorphic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem finPart_mem_integral_iff (k : finU (E := E) (n := a)) :
    finPart E a k ∈ AdelicGLn.integralFiniteGL E a ↔ ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u (n := a) := by
  rw [AdelicGLn.mem_integralFiniteGL_iff, ← map_inv]
  simp only [mem_KGL_iff_val, ← map_inv, GroundTheory.Global.mem_integralFiniteAdeles]
  exact ⟨fun h u => ⟨fun i j => h.1 i j u, fun i j => h.2 i j u⟩,
    fun h => ⟨fun i j u => (h u).1 i j, fun i j u => (h u).2 i j⟩⟩

theorem isOpen_KGL (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) :
    IsOpen (GlobalTheory.LFun.KGL w (n := a) : Set (GL (Fin a) (w.adicCompletion E))) := by
  have hK := GlobalTheory.SmGL.SphCompletion.KO_completion (F := E) w a
  have h : IsOpen (GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin a) : Set (GL (Fin a) (w.adicCompletion E))) :=
    GlobalTheory.SplitFlip.isOpen_KO
  rwa [hK] at h

theorem isClosed_KGL (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) :
    IsClosed (GlobalTheory.LFun.KGL w (n := a) : Set (GL (Fin a) (w.adicCompletion E))) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_KGL w a)

theorem mem_intU_iff_of_mem_locU {w : HeightOneSpectrum (𝓞 E)} {x : UA E a} (hx : x ∈ locU a w) :
    x ∈ intU a w ↔ cLoc w x ∈ GlobalTheory.LFun.KGL w (n := a) :=
  ⟨fun h => (mem_intU.1 h).2 w (fun h' => h' rfl), mem_intU_of hx⟩

theorem isOpen_intU (w : HeightOneSpectrum (𝓞 E)) :
    IsOpen (((intU a w).subgroupOf (locU a w)) : Set (locU a w)) := by
  have e : (((intU a w).subgroupOf (locU a w)) : Set (locU a w)) =
      (fun x : locU a w => cLoc w x.1) ⁻¹' (GlobalTheory.LFun.KGL w (n := a) : Set _) := by
    ext x
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_preimage]
    exact mem_intU_iff_of_mem_locU x.2
  rw [e]
  exact (isOpen_KGL w a).preimage ((continuous_cLoc w).comp continuous_subtype_val)

theorem isCompact_intU (w : HeightOneSpectrum (𝓞 E)) :
    IsCompact (intU a w : Set (UA E a)) := by
  haveI : ∀ u : HeightOneSpectrum (𝓞 E), T2Space (GL (Fin a) (u.adicCompletion E)) :=
    fun _ => Units.isEmbedding_embedProduct.t2Space
  let T : Set (finU (E := E) (n := a)) := {x | x.1 ∈ intU a w}
  have hK0 : IsCompact {x : finU (E := E) (n := a) | ((x : UA E a) : GA E a) ∈
      finGL E a '' (AdelicGLn.integralFiniteGL E a : Set _)} :=
    isClosedEmbedding_finU.isCompact_preimage
      ((AdelicGLn.isCompact_integralFiniteGL E a).image continuous_finGL_ad)
  have hTsub : T ⊆ {x : finU (E := E) (n := a) | ((x : UA E a) : GA E a) ∈
      finGL E a '' (AdelicGLn.integralFiniteGL E a : Set _)} := by
    intro x hx
    have hx' := mem_intU.1 hx
    have hall : ∀ u, cLoc u x.1 ∈ GlobalTheory.LFun.KGL u (n := a) := by
      intro u
      by_cases hu : Apart u w
      · rw [((GlobalTheory.Cong.LevelExt.mem_locU_iff x.1).1 hx'.1).2 u hu]
        exact one_mem _
      · exact hx'.2 u hu
    refine ⟨finPart E a x, (finPart_mem_integral_iff x).2 hall, ?_⟩
    have h1 : Matrix.GeneralLinearGroup.map (pInf E) ((x : UA E a) : GA E a) = 1 := x.2
    exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)
  have hTe : T = (⋂ u, ⋂ (_ : Apart u w), {x : finU (E := E) (n := a) | cLoc u x.1 = 1}) ∩
      ⋂ u, ⋂ (_ : ¬ Apart u w), {x : finU (E := E) (n := a) | cLoc u x.1 ∈ GlobalTheory.LFun.KGL u (n := a)} := by
    ext x
    simp only [T, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, mem_intU,
      GlobalTheory.Cong.LevelExt.mem_locU_iff]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨x.2, h.1⟩, h.2⟩⟩
  have hTc : IsClosed T := by
    rw [hTe]
    refine (isClosed_iInter fun u => isClosed_iInter fun _ => ?_).inter
      (isClosed_iInter fun u => isClosed_iInter fun _ => ?_)
    · exact isClosed_eq ((continuous_cLoc u).comp continuous_subtype_val) continuous_const
    · exact (isClosed_KGL u a).preimage ((continuous_cLoc u).comp continuous_subtype_val)
  have hT := (hK0.of_isClosed_subset hTc hTsub).image continuous_subtype_val
  have e : Subtype.val '' T = (intU a w : Set (UA E a)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro hy
      exact ⟨⟨y, ((GlobalTheory.Cong.LevelExt.mem_locU_iff y).1 (intU_le_locU w hy)).1⟩, hy, rfl⟩
  rwa [e] at hT

theorem intU_isCompact_isOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)), IsCompact (GlobalTheory.Cong.AdaptLev.intU a w : Set (UA E a)) ∧ IsOpen (((GlobalTheory.Cong.AdaptLev.intU a w).subgroupOf (locU a w)) : Set (locU a w)) :=
  fun _ _ _ _ _ w => ⟨isCompact_intU w, isOpen_intU w⟩

end GlobalTheory.Cong.AdaptLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DefiniteUnitaryLocalComponentSplitPlaceHomeomorpStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitaryLocalComponent_splitPlace_homeomorph : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → Function.Bijective ((cLoc w).comp (locU a w).subtype) ∧ IsOpenMap ((cLoc w).comp (locU a w).subtype) ∧ Continuous ((cLoc w).comp (locU a w).subtype) := by
  first | (exact @GlobalTheory.Cong.cLoc_locU_bijective_open_continuous) | (exact GlobalTheory.Cong.cLoc_locU_bijective_open_continuous) | (intros; apply GlobalTheory.Cong.cLoc_locU_bijective_open_continuous  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeterminantIdealNormOneAndCharUnitarySmulStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinantIdeal_normOne_char_unitary_smul : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ (N : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Even N → IsSDLat D.host.E N L → TaylorLogMetric.N1 D (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) ∧ ∀ e : Matrix (Fin N) (Fin N) D.host.E, e * star e = 1 → χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) (SDLat.smulLat e L)) = (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ e.det)⁻¹ * χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) := by
  first | exact @GlobalTheory.DetIdealUnitary.determinantIdeal_normOne_and_char_unitary_smul | exact GlobalTheory.DetIdealUnitary.determinantIdeal_normOne_and_char_unitary_smul | (intros; apply GlobalTheory.DetIdealUnitary.determinantIdeal_normOne_and_char_unitary_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAbelianTotallyRealExtPrescribedCompletionStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelian_totallyReal_ext_prescribedCompletion : ∀ (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω] [IsTotallyReal F] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (h : IsPlaceOver A v) (V : Subgroup (Dec (F := F) A)), IsOpen (V : Set (Dec (F := F) A)) → commutator (Dec (F := F) A) ≤ V → ∀ T : Finset (HeightOneSpectrum (𝓞 F)), v ∉ T → ∃ F₁ : IntermediateField F Ω, FiniteDimensional F F₁ ∧ IsAbelianGalois F F₁ ∧ (∀ φ : F₁ →+* ℂ, ComplexEmbedding.IsReal φ) ∧ (∀ g : Dec (F := F) A, (g : G F Ω) ∈ F₁.fixingSubgroup ↔ g ∈ V) ∧ ∀ u ∈ T, ∀ A' : ValuationSubring Ω, IsPlaceOver A' u → Dec (F := F) A' ≤ F₁.fixingSubgroup := by
  first | exact @GlobalTheory.AbStep.exists_abelian_real_field | exact GlobalTheory.AbStep.exists_abelian_real_field | (intros; apply GlobalTheory.AbStep.exists_abelian_real_field <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenGaloisSubgroupTraceNeZeroStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_galoisSubgroup_trace_ne_zero : ∀ (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (a : ℕ), 1 ≤ a → ∀ r : G K Ω →* GL (Fin a) (Qbar l), Continuous r → ∃ N : Subgroup (G K Ω), IsOpen (N : Set (G K Ω)) ∧ ∀ n ∈ N, (r n).val.trace ≠ 0 := by
  first | exact @GlobalTheory.AboveL.exists_open_trace_ne_zero | exact GlobalTheory.AboveL.exists_open_trace_ne_zero | (intros; apply GlobalTheory.AboveL.exists_open_trace_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueSplitPlaceComponentDefiniteUnitaryStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_splitPlaceComponent_definiteUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → (∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ) ∧ ∀ σ σ' : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ → IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ'.ρ → Nonempty (σ.ρ.Equiv σ'.ρ) := by
  first | (exact @GlobalTheory.SplitComp.exists_comp_and_unique) | (exact GlobalTheory.SplitComp.exists_comp_and_unique) | (intros; apply GlobalTheory.SplitComp.exists_comp_and_unique  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsVectorFixedByProductLocalLevelsStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_vector_fixed_by_product_localLevels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∀ (w₀ : HeightOneSpectrum (𝓞 E)) (K : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)), (∀ w, K w ≤ locU a w) → (∀ w u, ¬ Apart w u → K w = K u) → (∀ w, IsCompact (K w : Set (UA E a))) → (∀ᶠ w in Filter.cofinite, ∀ x ∈ K w, cLoc w x ∈ GlobalTheory.LFun.KGL w (n := a)) → (∀ w, IsOpen ((K w).subgroupOf (locU a w) : Set (locU a w))) → (∀ w, Apart w w₀ → ∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ K w, RU E a x φ = φ) → ∃ φ ∈ U, φ ≠ 0 ∧ ∀ w, Apart w w₀ → ∀ x ∈ K w, RU E a x φ = φ := by
  first | (exact @GlobalTheory.Cong.FixProd.fix_prod) | (exact GlobalTheory.Cong.FixProd.fix_prod) | (intros; apply GlobalTheory.Cong.FixProd.fix_prod  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDecompositionGroupsCoverOpenQuotientStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_decompositionGroups_cover_openQuotient : ∀ (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω] (v : HeightOneSpectrum (𝓞 F)) (N : Subgroup (G F Ω)), IsOpen (N : Set (G F Ω)) → ∃ T : Finset (HeightOneSpectrum (𝓞 F)), v ∉ T ∧ ∀ g : G F Ω, ∃ u ∈ T, ∃ A' : ValuationSubring Ω, IsPlaceOver A' u ∧ ∃ x ∈ Dec (F := F) A', ∃ n ∈ N, g = x * n := by
  first | exact @GlobalTheory.DecCover.main | exact GlobalTheory.DecCover.main | (intros; apply GlobalTheory.DecCover.main <;> assumption)
end

