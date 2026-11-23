module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RationalRootsDef
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0421
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CongruenceLevelEqDepthSucc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricFlagBasisVectorEqSingleOfNoExtra
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0175
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0389
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
public import Formalism.UnipotentAdelicQuotients.Bundle0002
public import Formalism.LocalRingCardinality.FactDelDualNabla
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0425
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolynomialModelValueRationalStep
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0427
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0402
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiAtCongInvariant

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrePin
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.NT GlobalTheory.Mem.Fld

namespace GlobalTheory.Mem.Top.Bl.KPxCond

theorem exists_prePin (K : Ctx) : ∃ P : Pre, K.Over P ∧ PrePin P :=
  ⟨GlobalTheory.StdFrameObj.coordPre K.P K.Lv, ⟨_, _, _, _, _, _, rfl, GlobalTheory.StdFrameObj.diagSpaces_coordPre K.P K.Lv⟩,
    fun a b h => PinsCoord.extTo_basis _ _ a b h⟩

theorem baseCond_KPx : RayField → PrincipalIdealSt → CMCurveGoodOutsidePrimeSt → StandardLattice.SiegelMassRatioCM → BaseCond KPx := by
  intro hR hP hA h2b
  exact baseCond_of (PP := fun P _ => PrePin P) (GlobalTheory.Mem.KsExactCond.ksCond_exact hR hP hA)
    (EvG.imp (evG_of_ev (ev_preX_frame h2b)) fun K _ _ _ _ hfr => by
      obtain ⟨P, hO, hp⟩ := exists_prePin K
      obtain ⟨f⟩ := (hfr P hO).2
      exact ⟨P, f, hO, hp⟩)

end GlobalTheory.Mem.Top.Bl.KPxCond
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarNe
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.AdT.PlaceUnder

theorem exists_star_ne {X : Fields} (hX : X.Ok) : ∃ x : X.E, star x ≠ x := by
  by_contra H
  push Not at H
  have := hX.cplxE
  obtain ⟨φ⟩ : Nonempty (X.E →+* ℂ) := inferInstance
  refine IsTotallyComplex.complexEmbedding_not_isReal φ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq, ← hX.conjE, H]

theorem main : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (P : SBof I a), P.1 ∈ I.Q a → ∃ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) ∧ ∀ P' : SBof I a, P' ≠ P → ¬ Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P'.1) := by
  classical
  intro B X I hI _ l Z a P _
  have hseam : ∀ Q : HeightOneSpectrum (𝓞 B.fields.E), GlobalTheory.TwU.seamP (sm I l Z) Q = Q := by
    intro Q
    ext x
    exact GlobalTheory.TwU.mem_seamP (sm I l Z) Q x
  obtain ⟨hX, -, -⟩ := base_fields_primes_ok B X
  have hc := (GlobalTheory.TopStepPrimes.primes_top_ok hI B.u₀ a).2.1
  refine ⟨HeightOneSpectrum.under (𝓞 (I.rec7 l Z).host.F) (GlobalTheory.TwU.seamP (sm I l Z) P.1), rfl, fun P' hne hov => ?_⟩
  rw [hseam, hseam] at hov
  have hu : P'.1.under (𝓞 B.fields.F) = P.1.under (𝓞 B.fields.F) := HeightOneSpectrum.ext (Eq.symm hov)
  rcases (GlobalTheory.NormOneUnit.under_eq_iff hX.star_F hX.rankE (exists_star_ne hX) P.1 P'.1).1 hu with h | h
  · exact hne (Subtype.ext h)
  · exact hc P.1 (Finset.mem_union_right _ P.2) (h ▸ Finset.mem_union_right _ P'.2)

end GlobalTheory.Mem.Col2.AdT.PlaceUnder
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaChrTied
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Links (ChrEq)
open Formalism.L2.Host (HChar)
open scoped TensorProduct

namespace GlobalTheory.TowerCharRead

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem chrEq_mul {c c' : (AE D)ˣ →* Circle} {χ χ' : HChar D.host.E} (h : ChrEq c χ) (h' : ChrEq c' χ') :
    ChrEq (c * c') (χ * χ') := by
  refine ⟨⟨h.1.1.mul h'.1.1, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · rw [MonoidHom.mul_apply, h.1.2, h'.1.2, one_mul]
  · rw [MonoidHom.mul_apply, Circle.coe_mul, h.2 P e he k x hx, h'.2 P e he k x hx, ← Units.val_mul]
    rfl

theorem exists_thetaChrTied (D : D7) (C : Formalism.L2.Host.CharFrame D) (nch : NChoice D) (Tp : Formalism.L2.Host.TupTied D C nch)
    (X : ThetaX D) (T : ThetaTied D X) (hR : ChrRead T C Tp.xi) :
    ∃ H : Formalism.L2.Host.ThetaChrTied D C nch Tp X, ∀ c, ChrEq (T.eChr c) (H.eChr c) := by
  obtain ⟨u1, u2, u3⟩ := GlobalTheory.ChrEqUnique.chrEq_unique D
  have hc : ∀ c, IsHeckeChar D (T.eChr c) ∧ ∀ τ, ∃ a, HasInfExp D (T.eChr c) τ a := fun c => by
    have : T.eChr c ∈ Set.range T.eChr := ⟨c, rfl⟩
    rwa [T.eChr_range] at this
  choose e he using fun c => GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D (T.eChr c) (hc c).1
  have hmul : ∀ a b, e (a * b) = e a * e b := fun a b =>
    u1 _ _ _ (he (a * b)) (by rw [map_mul]; exact chrEq_mul (he a) (he b))
  have hinf : ∀ c, (e c).HasInfQ (Formalism.L2.Host.embTau D) (X.infTy c) := fun c =>
    (GlobalTheory.HeckeInfExp.hasInfExp_iff_hasInfQ D _ _ _ (he c)).1 (T.infTy c)
  refine ⟨⟨MonoidHom.mk' e hmul, fun a b hab => T.eChr_inj (u2 _ _ _ (he a) ?_), fun χ => ⟨?_, ?_⟩, hinf,
    fun μ j => u1 _ _ _ (he _) (hR.chr μ j), u1 _ _ _ (he _) hR.eta⟩, he⟩
  · have hab' : e a = e b := hab
    rw [hab']
    exact he b
  · rintro ⟨c, rfl⟩
    exact ⟨u3 _ _ (he c), _, hinf c⟩
  · rintro ⟨hu, a, ha⟩
    obtain ⟨c, hcχ⟩ := GlobalTheory.CharTransport.exists_chrEq D χ hu
    have hm : c ∈ Set.range T.eChr := by
      rw [T.eChr_range]
      exact ⟨hcχ.1, fun τ => ⟨a τ, (GlobalTheory.HeckeInfExp.hasInfExp_iff_hasInfQ D _ _ _ hcχ).2 ha τ⟩⟩
    obtain ⟨x, rfl⟩ := hm
    exact ⟨x, u1 _ _ _ (he x) hcχ⟩

end GlobalTheory.TowerCharRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTopStepLevelCongruentBlockSumOne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT

open GlobalTheory.TopStep

section Local

variable {E : Type} [Field E] {N : ℕ}

theorem prXpG_sumE (hN : N = (N - 1) + 1) (g : Sp E (N - 1) ≃ₗ[E] Sp E (N - 1)) :
    prXpG E N ∘ₗ (sumE hN g 1).toLinearMap = (g.toLinearMap : Sp E ((N - 1) + 0) →ₗ[E] Sp E ((N - 1) + 0)) ∘ₗ prXpG E N := by
  refine LinearMap.ext fun x => funext fun i => ?_

  exact congrFun (prH_sumE hN g 1 x) i

theorem atNL_sumE (hN : N = (N - 1) + 1) (g : Sp E (N - 1) ≃ₗ[E] Sp E (N - 1)) :
    atNL E N (N - 1) ∘ₗ (sumE hN g 1).toLinearMap = atNL E N (N - 1) := by
  refine LinearMap.ext fun x => ?_
  have hlt : N - 1 < N := by omega

  have h := sumE_last hN g 1 x
  rw [Units.val_one, one_mul] at h
  simp only [LinearMap.comp_apply, atNL, dif_pos hlt, LinearMap.proj_apply]
  exact h

end Local

end GlobalTheory.Mem.Col2.AdT

namespace GlobalTheory.Mem.Col2.AdT

open GlobalTheory.TopStep

theorem exists_topLev_liftsInv : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i = B.R.m →
    ∀ (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (P : SBof I a), ∃ g g' z,
      GlobalTheory.TwU.TopLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i P g z ∧ LiftsInv I κ P g' ∧
        CongE P.1 (GlobalTheory.TwU.topDep I.sel (I.tup a) (I.cst a) P) g g' := by
  intro B X I hI u a i hi b κ P
  subst hi

  rcases b with ⟨_ | b₀, hb⟩
  swap
  · exact absurd (hb.mp rfl) (lt_irrefl _)
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1

  have hq : ((qOf P.1 : ℕ) : 𝓞 B.fields.E) ∉ P.1.asIdeal ^ 2 :=
    Formalism.L2.Ker.mq_rowSG_unif (I.tup a) (GlobalTheory.Mem.FieldsLaws.fields_ok (B := B)) hPr hI.sel_ok P
  have hN := N_m_succ B.R
  by_cases hP : P.1 ∈ (B.primes X).vGs
  ·
    have hQn : P.1 ∉ I.Q a := QE_disj (I.tup a) hPr hI.sel_ok hI.g_mem P.1 hP
    have hmem : κ.2.1.1 ⟨P.1, hP⟩ ∈ (levGTop I.Ch I.Ps ⟨P.1, hP⟩).H := by
      have h := κ.2.1.2
      simp only [LevFam.grp, Subgroup.mem_pi] at h
      rw [← topLev_levG_m I.Ch I.sel (I.tup a) (I.cst a) I.Ps]
      exact h ⟨P.1, hP⟩ (Set.mem_univ _)
    obtain ⟨h₀, hh₀, hdiag⟩ := (mem_levDiag _ _ _).mp hmem
    rw [rowTyG_PsymF_H] at hh₀
    have hr : B.R.r = B.R.k + 2 * B.R.rS + 1 := by
      simp only [Formalism.BasicNotions.Ranks.rS, Formalism.BasicNotions.Ranks.r]
      obtain ⟨s, hs⟩ := B.R.m_even
      have := B.R.two_le_m
      omega
    have hsym : rSym B.R.k B.R.rS = B.R.r := by rw [hr]; rfl

    have hJ := (mem_HJsym_iff_JSymG (𝓞 B.fields.E ⧸ P.1.asIdeal) (B.R.N B.R.m - 1) B.R.k B.R.r B.R.t B.R.m B.R.rS
      (r_le_X' B.R) hr B.R.t_odd.pos (rank_X'_eq B.R) h₀⁻¹).mp (Subgroup.inv_mem _ hh₀)

    obtain ⟨j, hj⟩ := redGL_surjective (E := B.fields.E) (n := B.R.N B.R.m - 1) P.1 h₀⁻¹
    have hjinv : redGL _ P.1 j⁻¹ = h₀ := by rw [map_inv, hj, inv_inv]
    have hlev : j.1 ∈ GlobalTheory.TwU.rowLevTop (B.primes X) B.R (I.cst a).sharp (B.R.N B.R.m) P.1 := by
      have h := GlobalTheory.Mem.LastGrp.mem_JGsym0 (fun x hx h0 => intAt_div_of_redP hq hx h0)
        (hsym.symm ▸ r_le_X' B.R) j
        (fun x y hxy => by rw [← redGL_val, hj]; exact hJ.1.1 x y hxy)
        (fun x y hxy => by rw [← redGL_val, hjinv]; simpa using hJ.2.1 x y hxy)
        (fun x hx => by rw [← redGL_val, hj]; exact hJ.1.2.1 x hx)
        (fun x y hx hy => by rw [← redGL_val, hj]; exact hJ.1.2.2.1 x y hx hy)
      have e : GlobalTheory.CongLevel.extE 0 j.1 = j.1 := LinearEquiv.ext (GlobalTheory.Mem.LastGrp.extE_zero j.1)
      rw [e, hsym] at h
      simp only [GlobalTheory.TwU.rowLevTop, if_pos hP, hI.sharp a, if_true]
      exact h
    refine ⟨sumE hN j.1 1, sumE hN j.1 1, _, ⟨j.1, hlev, prXpG_sumE hN j.1, atNL_sumE hN j.1, rfl⟩, ⟨?_, ?_, ?_⟩, congE_refl _ _ _⟩
    · rw [← extI_val hN j]
      exact (extI hN P.1 j).2
    · intro h x hx
      rw [← extI_val hN j, redV_redGL _ hx, redGL_extI, hj, ← hdiag, ← map_inv]
    · exact fun h => absurd h hQn
  ·
    have hQ : P.1 ∈ I.Q a := by
      classical
      have h := P.2
      simp only [SBof, rowSG, uSG, Finset.mem_union] at h
      exact h.resolve_left hP
    have hmem : κ.2.2.1 ⟨P.1, hQ⟩ ∈ (levQTop B.R I.sel (I.tup a) (topDep B.R (I.cst a).M) ⟨P.1, hQ⟩).H := by
      have h := κ.2.2.2
      simp only [LevQFam.grp, Subgroup.mem_pi] at h
      rw [← topLev_levQ_m I.Ch I.sel (I.tup a) (I.cst a) I.Ps]
      exact h ⟨P.1, hQ⟩ (Set.mem_univ _)
    simp only [levQTop] at hmem
    obtain ⟨j, hj, hjc⟩ := (mem_levCong _ _ _ _).mp (Subgroup.inv_mem _ hmem)
    have hlev : j.1 ∈ GlobalTheory.TwU.rowLevTop (B.primes X) B.R (I.cst a).sharp (B.R.N B.R.m) P.1 := by
      simp only [GlobalTheory.TwU.rowLevTop, if_neg hP]
      exact GlobalTheory.TopLaw.mem_JQ_of_red hq j ((mem_levRed _ _).mp hj)
    refine ⟨sumE hN j.1 1, ((κ.2.2.1 ⟨P.1, hQ⟩)⁻¹).1, _, ⟨j.1, hlev, prXpG_sumE hN j.1, atNL_sumE hN j.1, rfl⟩,
      ⟨((κ.2.2.1 ⟨P.1, hQ⟩)⁻¹).2, fun h => absurd h hP, fun h => rfl⟩, ?_⟩

    have h2 : (extI hN P.1 j)⁻¹ * (κ.2.2.1 ⟨P.1, hQ⟩)⁻¹ ∈ prinCong _ P.1 (2 * (I.cst a).M) :=
      prinCong_anti (by have := two_mul_le_topDep B.R (I.cst a).M; omega) hjc
    have h3 : ((κ.2.2.1 ⟨P.1, hQ⟩)⁻¹)⁻¹ * extI hN P.1 j ∈ prinCong _ P.1 (2 * (I.cst a).M) := by
      have := Subgroup.inv_mem _ h2
      rwa [_root_.mul_inv_rev, inv_inv] at this
    have h4 := (inv_mul_mem_prinCong _ _ _).mp h3
    intro x hx
    simp only [GlobalTheory.TwU.topDep, if_neg hP]
    have := h4 x hx
    rwa [extI_val] at this

end GlobalTheory.Mem.Col2.AdT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteAdeleFieldIdentificationEqBaseChangeRingEq
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem isAdIso_eq_afIso (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ι : AfE F E ≃+* FiniteAdeleRing (𝓞 E) E) (hι : GlobalTheory.TwU.IsAdIso ι) (x : AfE F E) : ι x = afIso F E x := by
  have key : ∀ P : HeightOneSpectrum (𝓞 E), ι x P = afIso F E x P := by
    intro P
    have ev : ∀ a b : FiniteAdeleRing (𝓞 E) E, (a + b) P = a P + b P := fun _ _ => rfl
    have evm : ∀ a b : FiniteAdeleRing (𝓞 E) E, (a * b) P = a P * b P := fun _ _ => rfl
    have evn : ∀ n : ℕ, ((n : FiniteAdeleRing (𝓞 E) E)) P = (n : P.adicCompletion E) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [Nat.cast_succ, ev, ih, Nat.cast_succ]; rfl
    rw [← sub_eq_zero]
    by_contra hne
    set d := ι x P - afIso F E x P with hd
    have hv : Valued.v d ≠ 0 := (Valuation.ne_zero_iff _).2 hne
    obtain ⟨y, N, r, hr, hN, e⟩ := exists_approx_small (F := F) (E := E) x {P} hv
    have hNP := hN P (Finset.mem_singleton_self P)
    have h1 : ι (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) y) = afIso F E (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) y) := by
      show ι (y ⊗ₜ[F] 1) = afIso F E (y ⊗ₜ[F] 1)
      rw [hι.1, afIso_tmul_one]
    have hd2 : d = (N : P.adicCompletion E) * (ι r P - afIso F E r P) := by
      rw [hd, e, map_add (f := _), map_add (f := _), h1, map_mul, map_mul, map_natCast, map_natCast]
      rw [ev, ev, evm, evm, evn]
      ring
    have hr1 : Valued.v (ι r P) ≤ 1 := (hι.2 r).1 hr P
    have hr2 : Valued.v (afIso F E r P) ≤ 1 := (mem_rInt_iff F E r).1 hr P
    have hsub : Valued.v (ι r P - afIso F E r P) ≤ 1 :=
      (Valuation.map_sub _ _ _).trans (max_le hr1 hr2)
    have hle : Valued.v d ≤ Valued.v (N : P.adicCompletion E) := by
      rw [hd2, map_mul]
      exact mul_le_of_le_one_right' hsub
    exact lt_irrefl _ (hle.trans_lt hNP)
  exact Subtype.ext (funext key)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsLatticeAtClassIffTwistedPolynomial
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatSCore

theorem prSC_int_iff (hW : WeylLatticeDuality.Stmt) {D : D7} (Pl : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (Bs : PlaceMatrixFamily D)
    (hC : CanOnto Pl) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ) (hi : i < D.R.m) (c : (D.chTw u μ).cls i)
    (v : ValQ O u μ i) :
    (∀ J : KM.ColChoice (D.R.N i) (nuD D u i),
        ‖prSC Pl O Bs u μ w i c v (MvPolynomial.map (Int.castRingHom _) (KM.nablaX (D.R.N i) (nuD D u i) J))‖ ≤ 1) ↔
      srcFun Pl Bs u μ w i c (secC O u μ i v) ∈
        WeylLatticeDuality.DelW (D.what₂.places.resChar w) D.what₂.Tau (D.R.N i) (nuT D u i) := by
  have hS := canS_of Pl Bs hC u μ w i hi c (secC O u μ i v)
  have hcan : canM D w (D.R.N i) (nuD D u i) (prSC Pl O Bs u μ w i c v) = srcFun Pl Bs u μ w i c (secC O u μ i v) :=
    canInv_spec D w (D.R.N i) (nuD D u i) _ hS
  rw [← hcan]
  exact hW (D.what₂.places.resChar w) _ D.what₂.Tau (tauPl D) (tauPl_bij D) (D.R.N i) (nuD D u i) (nuT D u i)
    (diagram_fits_source_rank D u i hi).1 (diagram_fits_source_rank D u i hi).2 (prSC Pl O Bs u μ w i c v)

theorem latS_at_class : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → ∀ (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ (i : ℕ) (hi : i < B.R.m) (eY : (I.chain l u μ).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi.le), I.IdY l Z u μ i hi.le eY → ∀ (c : (I.stp u μ i).Cl) (f : (I.chain l u μ).Y i → ℂ), (∃ P ∈ Formalism.L2.Forms.RatSpan (I.rec7 l Z) ((I.fm l u μ).lam i), ∀ z, f z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) 1 P (eY z)) → ∀ Bm : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E, Formalism.L2.Forms.IsLocBasis ((I.rec7 l Z).what₂.places.resChar w) (((I.stp u μ i).rep c).1.1.deco.1.N : Set (Sp B.fields.E (B.R.N i))) Bm → ((∃ P ∈ Formalism.L2.Forms.IntSpan (I.rec7 l Z) w ((I.fm l u μ).lam i), ∀ z, f z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) (atInf (embT (I.rec7 l Z)) ((Bm⁻¹ : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E)) P (eY z)) ↔ ∃ v : ValQ O u μ i, evC O u μ i v = f ∧ ∀ J : KM.ColChoice ((I.rec7 l Z).R.N i) (nuD (I.rec7 l Z) u i), ‖prSC Pl O Bs u μ w i c v (MvPolynomial.map (Int.castRingHom _) (KM.nablaX ((I.rec7 l Z).R.N i) (nuD (I.rec7 l Z) u i) J))‖ ≤ 1) := by
  intro B X I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hw i hi eY hId c f hrat Bm hBm
  have hi' : i < (I.rec7 l Z).R.m := hi
  have key := prSC_int_iff _root_.GlobalTheory.WeylLatDualProof.mainProof Pl O Bs (_root_.GlobalTheory.Mem.CanonicalSurjection.canOnto_all _ Pl) u μ w i hi' c
  constructor
  · intro hL
    obtain ⟨v, hv⟩ := _root_.GlobalTheory.CmpEx.exists_valQ I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hw i hi eY hId c f hrat
    refine ⟨v, hv, ?_⟩
    rw [key v]
    exact (_root_.GlobalTheory.IntegralityCompare.lattice_iff_weyl I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hw i hi eY hId c f hrat Bm hBm v hv).1 hL
  · rintro ⟨v, hv, hJ⟩
    rw [key v] at hJ
    exact (_root_.GlobalTheory.IntegralityCompare.lattice_iff_weyl I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hw i hi eY hId c f hrat Bm hBm v hv).2 hJ

end GlobalTheory.LatSCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMemPlaceIdealSpanOfNeOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar.EwZero

variable {D : D7}


open Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.RowDictPf in
theorem Wq_le_wInt (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    Wq X.B.I (wB X w) ≤ GlobalTheory.Mem.SymChar.wInt X w := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, ha, rfl⟩
  refine Submodule.subset_span ⟨a, ⟨RingOfIntegers.mapRingEquiv X.ιE a, ha, by simp⟩, rfl⟩


open Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.RowDictPf in
theorem Lq_le_wLf (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    Lq X.B.I (wB X w) ≤ wLf X w := by
  show Formalism.MainNotions.S.lamAf (F := X.B.I.F) (wLat0 X.B.I (wB X w)) ≤ Formalism.MainNotions.S.lamAf (F := X.B.I.F) (wLat X w)
  rw [wLat_eq]

theorem ew_mem_wInt (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k)
    (hw : ¬ GlobalTheory.Mem.SymFrame.EwAt X (D.naut.plGw kv.1 kv.2)) :
    X.ew ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  obtain ⟨ob, h1, -⟩ := Formalism.L2.SG.Pf.KppFwdPf.ew_res X kv
  cases ob with
  | false =>
    simp only [Bool.false_eq_true, if_false, sub_zero] at h1
    exact Wq_le_wInt X _ h1
  | true =>
    simp only [if_true] at h1
    exfalso
    apply hw
    intro y hy
    have h2 : 1 - X.ew ∈ Formalism.L2.SG.Pf.KppRedW.Wq X.B.I (Formalism.L2.SG.Pf.RowDictPf.wB X (D.naut.plGw kv.1 kv.2)) := by
      have := neg_mem h1
      rwa [neg_sub] at this
    exact Lq_le_wLf X _ (Formalism.L2.SG.Pf.KppRedW.Wq_smul h2 hy)

end GlobalTheory.Mem.SymChar.EwZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevQOfCongE
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT

theorem levQ_of_congE {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
    {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}
    (hL : L.Ok Ch sel mu cst G m2) (j : ℕ) (hj : j < R.m) (b : L.β j) (P : rowSG Pr sel mu)
    (hP : P.1 ∈ QE sel (mu : Chr X.F X.E X.K)) (g : Formalism.L2.Col.GLint X.E (R.N j) P.1)
    (h1 : ∀ x ∈ stdAt X.E (R.N j) P.1, ((qOf P.1 ^ cst.D P : ℕ) : X.E)⁻¹ • (g.1 x - x) ∈ stdAt X.E (R.N j) P.1) :
    ∃ h : g ∈ (L.levQ j b ⟨P.1, hP⟩).H, (L.levQ j b ⟨P.1, hP⟩).lam ⟨g, h⟩ = 1 := by
  have m := GlobalTheory.TwU.MidIndep.extE_cong_mem hL j hj b P g.1 h1
    (GlobalTheory.TwU.MidIndep.cong_inv P.1 _ _ (hL.cst_ok.D_pos P) g.1 h1)
  have hx := GlobalTheory.CongLevel.extE_inX (cOf R j) g.1
  have hmem : g ∈ (L.levQ j b ⟨P.1, hP⟩).H := by
    rw [hL.grpQ j b ⟨P.1, hP⟩, Subgroup.mem_subgroupOf]
    exact ⟨_, m.1, hx⟩
  refine ⟨hmem, Units.ext ?_⟩
  rw [hL.chrQ j b ⟨P.1, hP⟩ ⟨g, hmem⟩ _ m.1 hx]
  exact m.2

theorem levQ_deep : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (a : I.ι) (j : ℕ), j < B.R.m → ∀ (b : (I.idx a).β j) (P : SBof I a) (hP : P.1 ∈ I.Q a) (g : Formalism.L2.Col.GLint B.fields.E (B.R.N j) P.1), CongE P.1 ((I.cst a).D P) g.1 1 → ∃ h : g ∈ ((I.idx a).levQ j b ⟨P.1, hP⟩).H, ((I.idx a).levQ j b ⟨P.1, hP⟩).lam ⟨g, h⟩ = 1 := by
  intro B X I hOk a j hj b P hP g hg
  refine levQ_of_congE (hOk.idx_ok a) j hj b P hP g fun x hx => ?_
  rw [Nat.cast_pow]
  exact hg x hx

end GlobalTheory.Mem.Col2.AdT

end
end

