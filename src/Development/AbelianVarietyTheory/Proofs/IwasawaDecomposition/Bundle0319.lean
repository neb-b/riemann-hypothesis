module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
public import Formalism.LocalToGlobal.PlaceMapInjectivity.MapPlInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.LeOfFiniteSplitNotSplitBauer
public import Formalism.LocalToGlobal.Divisibility.ConjugationAtDistinguishedPlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0315
public import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
public import Lean
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Formalism.LocalToGlobal.NumberFieldFamilies.NPartCNd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemIsot
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowFix

open Formalism.L2.NG Formalism.IndefR.principalLevelFrame

theorem exists_fixed_of_mem_isot {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {A : Type} [AddCommGroup A] [Module ℂ A] (ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A)
    (π : FinTyp L n) (Q : (π.S →ₗ[ℂ] A) → Prop) (Kp : Formalism.AUTREP.GAf L n → Prop) {y : A}
    (hy : y ∈ ⨆ (Φ : π.S →ₗ[ℂ] A) (_ : IsEqvA ρ π Φ ∧ Q Φ), LinearMap.range Φ) (hy0 : y ≠ 0)
    (hfix : ∀ κ, Kp κ → ρ κ y = y) :
    ∃ f ∈ π.S, f ≠ 0 ∧ ∀ κ, Kp κ → rt L n κ f = f := by
  classical
  let ι := {Φ : π.S →ₗ[ℂ] A // IsEqvA ρ π Φ ∧ Q Φ}
  have hy' : y ∈ ⨆ j : ι, LinearMap.range j.1 := by
    rwa [iSup_subtype'] at hy
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hy'
  let Y : Finset ι → Submodule ℂ A := fun t => ⨆ j ∈ t, LinearMap.range j.1
  have hYst : ∀ (t : Finset ι) (g : Formalism.AUTREP.GAf L n) (x : A), x ∈ Y t → ρ g x ∈ Y t := by
    intro t g x hx
    have hle : Y t ≤ (Y t).comap (ρ g) := by
      refine iSup₂_le fun j hj => ?_
      rintro _ ⟨v, rfl⟩
      rw [Submodule.mem_comap, ← j.2.1 g v]
      exact (le_iSup₂ (f := fun j (_ : j ∈ t) => LinearMap.range j.1) j hj) (LinearMap.mem_range_self _ _)
    exact hle hx
  have key : ∀ (t : Finset ι) (x : A), x ∈ Y t → x ≠ 0 → (∀ κ, Kp κ → ρ κ x = x) →
      ∃ f ∈ π.S, f ≠ 0 ∧ ∀ κ, Kp κ → rt L n κ f = f := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro x hx hx0 _
      exact absurd (by simpa [Y] using hx) hx0
    | insert j t hjt ih =>
      intro x hx hx0 hxfix
      have hx' : x ∈ LinearMap.range j.1 ⊔ Y t := by
        simpa [Y, Finset.iSup_insert] using hx
      obtain ⟨_, ⟨v, rfl⟩, z, hz, rfl⟩ := Submodule.mem_sup.1 hx'
      let U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ) := ((Y t).comap j.1).map π.S.subtype
      have hUst : ∀ h, ∀ f ∈ U, rt L n h f ∈ U := by
        rintro h _ ⟨a, ha, rfl⟩
        refine ⟨⟨rt L n h a, π.stable h a a.2⟩, ?_, rfl⟩
        have ha' : j.1 a ∈ Y t := ha
        show j.1 _ ∈ Y t
        rw [j.2.1 h a]
        exact hYst t h _ ha'
      rcases π.irr U (Submodule.map_subtype_le _ _) hUst with hU | hU
      ·
        have hvfix : ∀ κ, Kp κ → rt L n κ (v : Formalism.AUTREP.GAf L n → ℂ) = v := by
          intro κ hκ
          let v' : π.S := ⟨rt L n κ v, π.stable κ v v.2⟩
          have hmem : v' - v ∈ (Y t).comap j.1 := by
            rw [Submodule.mem_comap, map_sub, j.2.1 κ v]
            have h1 := hxfix κ hκ
            rw [map_add (f := _)] at h1
            have h3 : ρ κ (j.1 v) - j.1 v = z - ρ κ z := by
              rw [sub_eq_sub_iff_add_eq_add, h1, add_comm]
            rw [h3]
            exact sub_mem hz (hYst t κ z hz)
          have hU' : ((v' - v : π.S) : Formalism.AUTREP.GAf L n → ℂ) ∈ U := ⟨_, hmem, rfl⟩
          rw [hU, Submodule.mem_bot] at hU'
          exact sub_eq_zero.1 hU'
        by_cases hv : (v : Formalism.AUTREP.GAf L n → ℂ) = 0
        · have hv' : v = 0 := Subtype.ext hv
          subst hv'
          simp only [map_zero, zero_add] at hx0 hxfix
          exact ih z hz hx0 hxfix
        · exact ⟨v, v.2, hv, hvfix⟩
      · have hvU : (v : Formalism.AUTREP.GAf L n → ℂ) ∈ U := by rw [hU]; exact v.2
        obtain ⟨a, ha, hav⟩ := hvU
        have : a = v := Subtype.ext hav
        subst this
        exact ih _ (add_mem ha hz) hx0 hxfix
  exact key s y (by simpa [Y] using hs) hy0 hfix

theorem exists_fixed_rowRep : ∀ (D : D7) (V : HSp D) (n : ℕ) (Sp : D.what₂.Tau → SPar) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (P : principalLevelFrame.RowPsi V n) (M : Mult.DSModel V Sp) (J : Bool → Set (GA D V)) (χ : Bool → GA D V → ℂ) (e : Bool → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (σ : principalLevelFrame.FTR θ P M J χ e) (Kp : Formalism.AUTREP.GAf D.host.E n → Prop), (∀ b κ, Kp κ → P.ψ κ ∈ J b ∧ χ b (P.ψ κ) = 1) → ∃ f ∈ (principalLevelFrame.rowRepR θ σ).S, f ≠ 0 ∧ ∀ κ, Kp κ → NG.rt D.host.E n κ f = f := by
  intro D V n Sp θ P M J χ e σ Kp hK
  obtain ⟨b, hb⟩ := rowRepR_occ θ σ
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  have hy' : y ∈ Formalism.IndefR.Mult.goodPart θ M (J b) (χ b) (e b) ⊓
      isotIn (actM P M) (Minf θ P M) (FinTyp.conjT (rowRepR θ σ)) := hy
  rw [Submodule.mem_inf] at hy'
  have hM : y ∈ Formalism.IndefR.Mult.Mult θ M (J b) (χ b) := (Submodule.mem_inf.1 hy'.1).1
  have hfixY : ∀ κ, Kp κ → actM P M κ y = y := by
    intro κ hκ
    have hle : Formalism.IndefR.Mult.Mult θ M (J b) (χ b) ≤ LinearMap.ker (actM P M κ - LinearMap.id) := by
      refine Submodule.span_le.2 ?_
      intro T hT
      have hT' : Formalism.IndefR.Mult.IsMultMap θ M (J b) (χ b) T := hT
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      apply MultilinearMap.ext
      intro v
      funext g
      rw [actM_apply, hT'.lev v _ (hK b κ hκ).1 g, (hK b κ hκ).2, one_mul]
    have h := hle hM
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h
    exact h
  obtain ⟨f, hf, hf0, hffix⟩ := exists_fixed_of_mem_isot (actM P M) (FinTyp.conjT (rowRepR θ σ))
    (fun Φ => LinearMap.range Φ ≤ Minf θ P M) Kp hy'.2 hy0 hfixY
  refine ⟨fun g => star (f g), (mem_conjSub).1 hf, ?_, fun κ hκ => ?_⟩
  · intro h0
    apply hf0
    funext g
    have := congrFun h0 g
    simpa using this
  · rw [← conj_rt, hffix κ hκ]

end GlobalTheory.RowFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasSatGLLocRep
section
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.CuspRep.UnrSat

open GlobalTheory.CuspRep GlobalTheory.LFun GlobalTheory.PRep

theorem exists_hasSatGL_locRep : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E]
    [NumberField.IsTotallyComplex E] (a : ℕ) (π : GlobalTheory.CuspRep.CuspSub E a) (v : HeightOneSpectrum (𝓞 E)),
    GlobalTheory.LGrp.IsSpherical (π.locRep v) (GlobalTheory.LFun.KGL v (n := a)) → ∃ B : Multiset ℂˣ, GlobalTheory.LFun.HasSatGL v (π.locRep v) B := by
  intro hF E _ _ _ a π v hs
  obtain ⟨σ, hσ, hadm⟩ := LocEx.exists_isLocComp hF E a π v
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hs
  obtain ⟨y, hy0, hy⟩ := LocSph.exists_fixed_of_mem_iSup ((finRep E a).comp (locGL E a v)) σ.ρ σ.irred
    (fun f : LocSph.Maps π v σ => f.1) (fun f => f.2.2) (KGL v (n := a) : Set _) x.1 (fun e => hx0 (Subtype.ext e))
    (fun k hk => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hx k hk))
    (by rw [LocSph.iSup_range_eq π v σ hσ]; exact x.2)
  have hsph : GlobalTheory.LGrp.IsSpherical σ.ρ (KGL v (n := a)) :=
    (Submodule.ne_bot_iff _).2 ⟨y, GlobalTheory.LGrp.mem_fixed.2 hy, hy0⟩
  have hfin : FiniteDimensional ℂ (fixed σ.ρ (KGL v (n := a))) :=
    hadm.2 _ (SatCompare.isOpen_isCompact_KGL v a).1 (SatCompare.isOpen_isCompact_KGL v a).2
  obtain ⟨B, hB⟩ := SatCompare.exists_hasSatGL ⟨σ.smooth, σ.irred⟩ hfin hsph
  exact ⟨B, HeightCounting.Blocks.hasSatGL_locRep hσ hB⟩

end GlobalTheory.CuspRep.UnrSat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMulGaloisConjEqPrimeImagQuadratic
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.RayFieldNorm

theorem normSq_eq_absNorm {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
    (hK : Module.finrank ℚ K = 2) (φ : K →+* ℂ) (π : 𝓞 K) :
    ‖φ π‖ ^ 2 = (Ideal.absNorm (Ideal.span {π}) : ℝ) := by
  have h1 : Fintype.card (InfinitePlace K) = 1 := by
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
    have h3 := InfinitePlace.card_add_two_mul_card_eq_rank K
    have h4 := IsTotallyComplex.nrRealPlaces_eq_zero K
    omega
  have : Subsingleton (InfinitePlace K) := Fintype.card_le_one_iff_subsingleton.mp h1.le
  have h5 := InfinitePlace.prod_eq_abs_norm (π : K)
  rw [Fintype.prod_subsingleton _ (InfinitePlace.mk φ), IsTotallyComplex.mult_eq,
    InfinitePlace.apply] at h5
  rw [h5, Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int]
  simp

theorem isTotallyComplex_of_isEmpty {K : Type} [Field K] [NumberField K]
    (h : IsEmpty (K →+* ℝ)) : IsTotallyComplex K := by
  rw [isTotallyComplex_iff]
  intro w
  rw [← InfinitePlace.not_isReal_iff_isComplex]
  intro hw
  obtain ⟨φ, hφ, -⟩ := hw
  exact h.elim (NumberField.ComplexEmbedding.IsReal.embedding hφ)

theorem exists_mul_conj_eq_norm : ∀ (K : Type) [Field K] [NumberField K], IsEmpty (K →+* ℝ) → Module.finrank ℚ K = 2 →
    ∀ (j : K →+* Qb) (π : 𝓞 K) (p : ℕ), Ideal.absNorm (Ideal.span {π}) = p →
      ∃ σ : Qb →ₐ[ℚ] Qb, j (π : K) * σ (j (π : K)) = (p : Qb) := by
  intro K _ _ hE hK j π p hp
  haveI := isTotallyComplex_of_isEmpty hE
  haveI : Algebra.IsAlgebraic ℚ Qb := AlgebraicClosure.isAlgebraic ℚ
  let ι : Qb →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := Qb)).toRingHom
  refine ⟨(Formalism.L2.DIV.conjQb ι).toAlgHom, ?_⟩
  apply ι.injective
  have hn := normSq_eq_absNorm hK (ι.comp j) π
  rw [hp] at hn
  have hc : ι (j (π : K)) * starRingEnd ℂ (ι (j (π : K))) = ((‖ι (j (π : K))‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hs := Formalism.L2.DIV.conjQb_spec ι (j (π : K))
  change ι (j (π : K) * (Formalism.L2.DIV.conjQb ι) (j (π : K))) = ι (p : Qb)
  rw [map_mul, hs, hc, map_natCast]
  simp only [RingHom.comp_apply] at hn
  rw [hn]
  simp

end GlobalTheory.RayFieldNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReOfDiv
section
noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000

section Trans

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

def LocIso.trans {A B C : Formalism.MainNotions.S.Loc.LocAt F E sig p} (a : Formalism.L2.S.LocIso A B) (b : Formalism.L2.S.LocIso B C) :
    Formalism.L2.S.LocIso A C where
  eF := a.eF.trans b.eF
  eF_ι x := (congrArg b.eF (a.eF_ι x)).trans (b.eF_ι x)
  eF_val x y := (a.eF_val x y).trans (b.eF_val _ _)
  eF_cont := b.eF_cont.comp a.eF_cont
  eF_symm_cont := a.eF_symm_cont.comp b.eF_symm_cont
  eF_ql x := (congrArg b.eF (a.eF_ql x)).trans (b.eF_ql x)
  eE := a.eE.trans b.eE
  eE_alg x := (congrArg b.eE (a.eE_alg x)).trans (b.eE_alg _)
  eE_ι x := (congrArg b.eE (a.eE_ι x)).trans (b.eE_ι x)
  eE_cont := b.eE_cont.comp a.eE_cont
  eE_symm_cont := a.eE_symm_cont.comp b.eE_symm_cont
  eE_cj y := (congrArg b.eE (a.eE_cj y)).trans (b.eE_cj _)
  eE_O y := (a.eE_O y).trans (b.eE_O _)
  eE_psi y := (a.eE_psi y).trans (b.eE_psi _)

variable {R : Ranks} {Word Tau : Type} {hc : Word → Tau → HCParam R}

def SIso.trans {s s' s'' : Formalism.MainNotions.S.Draft.SData R F E sig Word Tau hc} (a : SIso s s') (b : SIso s' s'') : SIso s s'' where
  cd := a.cd.trans b.cd
  del := a.del.trans b.del
  letter := a.letter.trans b.letter
  eHH := a.eHH.trans b.eHH
  eCu u := (a.eCu u).trans (b.eCu u)
  Pu_eq u x := (congrArg b.eHH (a.Pu_eq u x)).trans (b.Pu_eq u _)
  volN := a.volN.trans b.volN
  volH := a.volH.trans b.volH
  eT u u' := (a.eT u u').trans (b.eT u u')
  aTerm_eq u u' t x := (congrArg (b.eCu u) (a.aTerm_eq u u' t x)).trans (b.aTerm_eq u u' _ _)
  isId t := (a.isId t).trans (b.isId _)
  inS t := (a.inS t).trans (b.inS _)
  relevant t := (a.relevant t).trans (b.relevant _)
  FeqF t := (a.FeqF t).trans (b.FeqF _)
  Gterm t := (a.Gterm t).trans (b.Gterm _)
  atP p := LocIso.trans (a.atP p) (b.atP p)
  ePl := a.ePl.trans b.ePl
  BBne t q := (a.BBne t q).trans (b.BBne _ _)
  generic t := (a.generic t).trans (b.generic _)
  eP u u' := (a.eP u u').trans (b.eP u u')
  pfst p := (congrArg (b.eT _ _) (a.pfst p)).trans (b.pfst _)
  psnd p := (congrArg (b.eT _ _) (a.psnd p)).trans (b.psnd _)
  s0 p := (a.s0 p).trans (b.s0 _)
  scalarPair p := (a.scalarPair p).trans (b.scalarPair _)
  pval p := (a.pval p).trans (b.pval _)
  ptOf t := (a.ptOf t).trans (b.ptOf _)
  cTerm t := (a.cTerm t).trans (b.cTerm _)
  massPair p := (a.massPair p).trans (b.massPair _)
  meanCount := a.meanCount.trans b.meanCount

end Trans

section Move

variable {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (hh : D.what₂.Word → ℝ)

theorem SRest.exists_re_ofDiv {F : ∀ u, Forms0 D u} {P : SPack D F} (S : SRest P)
    {F' : ∀ u, Forms0 (reD D (New.ofDiv D N hh)) u} (h : SameForms0LevelsAndValues (New.ofDiv D N hh) F F')
    (hF : FinX (reY (New.ofDiv D N hh) P.Y)) :
    ∃ S' : SRest (P.re (New.ofDiv D N hh) h hF), HEq S'.j S.j := by
  obtain ⟨e, heH, heC⟩ := sIso_reD D (New.ofDiv D N hh) P.X P.Y P.fin hF
  let hI' : SIso (reD D (New.ofDiv D N hh)).s (sOf (P.re (New.ofDiv D N hh) h hF).fin) := (by with_unfolding_all exact (SIso.trans S.hI e :))
  let aT : Formalism.MainNotions.S.AutTie (reD D (New.ofDiv D N hh)) (P.re (New.ofDiv D N hh) h hF).X.B
      (P.re (New.ofDiv D N hh) h hF).X.pl :=
    ⟨(by with_unfolding_all exact (S.autTie.n_eq :)), (by with_unfolding_all exact (S.autTie.f_eq :)), (by with_unfolding_all exact (S.autTie.rd_eq :)), (by with_unfolding_all exact (S.autTie.eps_eq :)),
      (by with_unfolding_all exact (S.autTie.lam_eq :)), (by with_unfolding_all exact (S.autTie.ds :)), (by with_unfolding_all exact (S.autTie.low :)), (by with_unfolding_all exact (S.autTie.g_eq :)),
      (by with_unfolding_all exact (S.autTie.g0_eq :)), (by with_unfolding_all exact (S.autTie.D_eq :)), (by with_unfolding_all exact (S.autTie.Dstar_eq :))⟩
  let jj : (reD D (New.ofDiv D N hh)).what₂.EE ≃ₗᵢ[ℂ] EEC (P.re (New.ofDiv D N hh) h hF).X
      (P.re (New.ofDiv D N hh) h hF).G := (by with_unfolding_all exact (S.j :))
  have lT : Formalism.L2.SG.Pf.LocCP.LocTied (reD D (New.ofDiv D N hh)) := (by with_unfolding_all exact (S.locTied :))
  have cP : ∀ (u : (reD D (New.ofDiv D N hh)).what₂.Word) (x : (reD D (New.ofDiv D N hh)).s.Cu u),
      colDict (P.re (New.ofDiv D N hh) h hF).X ((P.re (New.ofDiv D N hh) h hF).tr u)
        (P.re (New.ofDiv D N hh) h hF).Y.hK ((P.re (New.ofDiv D N hh) h hF).into u)
        ((P.re (New.ofDiv D N hh) h hF).bij u) (hI'.eCu u x) = (reD D (New.ofDiv D N hh)).s_Cu u x := by
    intro u x
    have hx : hI'.eCu u x = ((by with_unfolding_all exact (S.hI.eCu u x :))) := (by with_unfolding_all exact (congrArg (fun f => f (S.hI.eCu u x)) (eq_of_heq (heC u)) :))
    rw [hx]
    apply Subtype.ext
    exact (by with_unfolding_all exact ((colDictL_reTr (New.ofDiv D N hh) (P.tr u) (h u).2.1 (h u).2.2 P.Y.hK
      (toCu (cs := P.Y.cs u) (hinj := P.fin.shInj u) P.X P.Y.hK (S.hI.eCu u x))).trans (congrArg Subtype.val (S.colPin u x)) :))
  have rP : ∀ x : (reD D (New.ofDiv D N hh)).what₂.EE,
      hI'.eHH ((reD D (New.ofDiv D N hh)).sEE x) =
        conjHH (P.re (New.ofDiv D N hh) h hF).X (P.re (New.ofDiv D N hh) h hF).G (jj x) := by
    intro x
    exact (by with_unfolding_all exact ((congrArg (fun f => f (S.hI.eHH (D.sEE x))) (eq_of_heq heH)).trans (S.rowPin x) :))
  exact ⟨⟨hI', aT, cP, jj, rP, lT⟩, (by with_unfolding_all exact (HEq.refl S.j :))⟩

end Move

end GlobalTheory.Mem.SRe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingEquivFinExtIntegersPadicIntOf
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.IntOfFinExt

theorem mem_integer_iff_norm_le_one (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) :
    x ∈ (PadicAlgCl.valued l).v.integer ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_integer_iff]
  show ‖x‖₊ ≤ 1 ↔ ‖x‖ ≤ 1
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]

theorem mem_intOf_iff (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
    (x : PadicAlgCl l) : x ∈ intOf l K ↔ x ∈ K ∧ ‖x‖ ≤ 1 := by
  unfold intOf
  rw [Subring.mem_inf, mem_integer_iff_norm_le_one]
  rfl

def toIntOf (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l) : ↥(Loc.OL K) →+* ↥(intOf l K.1) :=
  RingHom.codRestrict ((K.1.val.toRingHom).comp (Loc.OL K).val.toRingHom) (intOf l K.1)
    (fun y => (mem_intOf_iff l K.1 _).2
      ⟨((y : ↥K.1)).2, (GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one l K (y : ↥K.1)).1 y.2⟩)

theorem toIntOf_bijective (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l) :
    Function.Bijective (toIntOf l K) := by
  constructor
  · intro a b h
    have h' : (((a : ↥K.1) : PadicAlgCl l)) = ((b : ↥K.1) : PadicAlgCl l) :=
      congrArg (fun w : ↥(intOf l K.1) => (w : PadicAlgCl l)) h
    exact Subtype.ext (Subtype.ext h')
  · intro z
    obtain ⟨hK, hn⟩ := (mem_intOf_iff l K.1 z).1 z.2
    refine ⟨⟨⟨(z : PadicAlgCl l), hK⟩,
      (GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one l K ⟨(z : PadicAlgCl l), hK⟩).2 hn⟩, ?_⟩
    exact Subtype.ext rfl

theorem exists_ringEquiv_intOf : ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l),
    ∃ e : ↥(Loc.OL K) ≃+* ↥(intOf l K.1), ∀ y, (e y : PadicAlgCl l) = ((y : ↥K.1) : PadicAlgCl l) :=
  fun l _ K => ⟨RingEquiv.ofBijective (toIntOf l K) (toIntOf_bijective l K), fun _ => rfl⟩

end GlobalTheory.IntOfFinExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpanEqOneModOfSplitsInRayClassField
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.Mem.RaySplit

open GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem.Fld

theorem exists_span_eq_of_splits (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (𝔮 : Ideal (𝓞 K)) (hR : GlobalTheory.Mem.Fld.IsRayField K L 𝔮) (𝔭 : HeightOneSpectrum (𝓞 K)) (hnd : ¬ 𝔭.asIdeal ∣ 𝔮)
    (hs : (𝔭.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L) :
    ∃ π : 𝓞 K, 𝔭.asIdeal = Ideal.span {π} ∧ π - 1 ∈ 𝔮 := by
  have := hR.1
  have := 𝔭.isPrime
  have := 𝔭.isMaximal
  have hcop : IsCoprime 𝔭.asIdeal 𝔮 := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    exact hnd (Ideal.dvd_iff_le.2 (le_sup_right.trans (𝔭.isMaximal.eq_of_le h le_sup_left).symm.le))
  obtain ⟨σ, P, hP, hPo, hσ⟩ := exists_isFrob L 𝔭
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
  have hPm : P.IsMaximal := hP.isMaximal hne
  have hef := (GlobalTheory.Bauer.ncard_eq_finrank_iff K L 𝔭).1 hs P ⟨hP, hPo⟩
  have hf : 𝔭.asIdeal.inertiaDeg' P = 1 := by
    rw [Ideal.inertiaDeg'_eq_inertiaDeg]
    exact Nat.eq_one_of_mul_eq_one_left hef
  have hN : Ideal.absNorm P = Ideal.absNorm 𝔭.asIdeal := by
    rw [Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P 𝔭.asIdeal 𝔭.isPrime 𝔭.ne_bot, hf, pow_one]
  have : Finite (𝓞 L ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  letI := Ideal.Quotient.field P
  letI := Fintype.ofFinite (𝓞 L ⧸ P)
  have hpow : ∀ x : 𝓞 L, x ^ Ideal.absNorm 𝔭.asIdeal - x ∈ P := fun x => by
    rw [← Ideal.Quotient.eq, map_pow, ← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card _
  have hin : InInertia L 𝔭 σ := ⟨P, hP, hPo, fun x => by
    have := add_mem (hσ x) (hpow x)
    rwa [sub_add_sub_cancel] at this⟩
  have hσ1 : σ = 1 := hR.2.1 𝔭 hnd σ hin
  have hχ : ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ 𝔭.asIdeal = 1 := fun χ => by
    rw [heckeIdeal_asIdeal, heckeVal_of_unramIn L χ (hR.2.1 𝔭 hnd) ⟨P, hP, hPo, hσ⟩, hσ1, map_one, Units.val_one]
  obtain ⟨α, β, hab, he⟩ := (hR.2.2.2 𝔭.asIdeal 𝔭.ne_bot hcop).1 hχ
  have hα : α ∈ 𝔭.asIdeal * Ideal.span {β} := he ▸ Ideal.mem_span_singleton_self α
  obtain ⟨π, hπ, rfl⟩ := Ideal.mem_mul_span_singleton.1 hα
  have hβ0 : Ideal.span {β} ≠ (0 : Ideal (𝓞 K)) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hab.2.1
  have hsp : 𝔭.asIdeal = Ideal.span {π} := by
    refine mul_right_cancel₀ hβ0 ?_
    rw [he, Ideal.span_singleton_mul_span_singleton]
  refine ⟨π, hsp, ?_⟩
  obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.1 hab.2.2.2.1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hi
  have h1 : (π - 1) * β ∈ 𝔮 := by
    have := hab.2.2.2.2.1
    rwa [show π * β - β = (π - 1) * β by ring] at this
  have h2 : π - 1 = c * ((π - 1) * β) + (π - 1) * j := by
    linear_combination (π - 1) * hij.symm
  rw [h2]
  exact add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ hj)

end GlobalTheory.Mem.RaySplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteExceptionalPlacesOverPrime
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.PlacesExc

theorem finite_exceptional : ∀ (D : D7) (l : ℕ), l.Prime → ∃ F : Finset (PlE D.host), ∀ v, v ∉ F → v ∉ placesOver D.host.E l ∧ v ∉ placesS D l := by
  intro D l hl
  have h1 : (placesOver D.host.E l).Finite := Formalism.L2.Fam.NPC.placesOver_fin D.host l hl
  have h2 : (placesS D l).Finite := Formalism.L2.Fam.NPC.exceptional_places_finite D.host l
  refine ⟨(h1.union h2).toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset] at hv
  exact ⟨fun h => hv (Or.inl h), fun h => hv (Or.inr h)⟩

end GlobalTheory.PlacesExc
end

