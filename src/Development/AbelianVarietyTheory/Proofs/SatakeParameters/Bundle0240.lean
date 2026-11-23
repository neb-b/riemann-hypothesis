module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0239
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.XiAtPenultimateEqXiCpl1
public import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
public import Formalism.LocalToGlobal.Columns.Bundle0047
public import Formalism.LocalToGlobal.Columns.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0175
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsBridge
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0720
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCmFieldLiftDisjointOfRealSolvable
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0660
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0116
public import GroundTheory.GlobalFields.TateThesis.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1455
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1121
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0012
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0004
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0007
public import Formalism.LocalToGlobal.InertKernelTheory.KernelsIntegralInert

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutRepDefiniteUnitarySpannedBySplitComponentStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.autRepDefiniteUnitary_spanned_by_split_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ → ∀ φ ∈ U, φ ∈ ⨆ (f : {f : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, f v ∈ U) ∧ ∀ (x : locU a w) v, f (σ.ρ (cLoc w x) v) = RU E a x (f v)}), LinearMap.range f.1 := by
  first | (exact @GlobalTheory.Cong.span_comp_of_split) | (exact GlobalTheory.Cong.span_comp_of_split) | (intros; apply GlobalTheory.Cong.span_comp_of_split  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockExtMemTwistedK1
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep

namespace GlobalTheory.TopStep

theorem ext_mem_twisted_k1_level : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)),
    ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → ∀ {N n : ℕ} (hN : N = n + 1) (r b c : ℕ), n = r + b →
    ∀ j : GLint E n P, redGL n P j ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b → extI hN P j ∈ twK1H P N r c := by
  intro E _ _ _ P hq N n hN r b c hn j h
  subst hN
  have hent : ∀ k : GLint E n P, redGL n P k ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b →
      ∀ a l : Fin n, a.1 < r → r ≤ l.1 → IntAt P (k.1 (Pi.single a 1) l / (qOf P : E)) := by
    intro k hk a l ha hl
    have h0 : redP P (k.1 (Pi.single a 1) l) = 0 := by
      have := twTQ_HQ_entry hk ha hl
      rwa [redGL_val] at this
    exact intAt_div_of_redP hq (glint_entry k l a) h0
  refine mem_kOne_of_block P (n := n + 1) (r := r) (c := c) (by omega) (extI rfl P j) (j.1 : Sp E n ≃ₗ[E] Sp E n) ?_ ?_ ?_
  · intro x l
    rw [extI_val]
    by_cases hl : l.1 < n
    · rw [dite_eq_left (show l.1 < n + 1 - 1 by omega)]
      have := congrFun (prH_sumE rfl j.1 1 x) ⟨l.1, hl⟩
      exact this
    · rw [dite_eq_right (show ¬ l.1 < n + 1 - 1 by omega)]
      have e : l = Br.iL (rfl : n + 1 = n + 1) := Fin.ext (by have := l.2; show l.1 = n; omega)
      subst e
      rw [sumE_last, Units.val_one, one_mul]
  · exact fun a l ha hl => hent j h a l ha hl
  · intro a l ha hl
    have := hent j⁻¹ (by rw [map_inv]; exact inv_mem h) a l ha hl
    exact this

end GlobalTheory.TopStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamDescends
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DRDescent

theorem deRham_descends : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (l : ℕ) [Fact l.Prime], ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (a : ℕ) (r : G K Ω →* GL (Fin a) (Qbar l)), Continuous r → ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l K Ω (Dec (F := K) A) O), GlobalTheory.Pst.Induces Bw → ∃ (O' : Type) (_ : CommRing O') (_ : Algebra ℤ_[l] O') (_ : TopologicalSpace O') (Bw' : LocBridge l L Ω (Dec (F := L) A) O'), GlobalTheory.Pst.Induces Bw' ∧ Bw'.j = Bw.j ∧ (IsdRAt P Bw' ((resTo L r).comp (Dec (F := L) A).subtype) → IsdRAt P Bw (r.comp (Dec (F := K) A).subtype)) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' l _ P AI hT a r hr O _ _ _ Bw hj
  obtain ⟨T⟩ := hT
  obtain ⟨LL₀, Bw', hjj, hS, hKle⟩ := GlobalTheory.AboveLRes.exists_bridge (L := L) Bw hj Bw.LL
  have hj' : GlobalTheory.Pst.Induces Bw' := fun x => by rw [hjj]; exact hj x
  refine ⟨_, _, _, _, Bw', hj', hjj, fun hc => ?_⟩
  have hcont : Continuous (fun g => (r g : Matrix (Fin a) (Fin a) (Om l))) := Units.continuous_val.comp hr
  obtain ⟨M, hM, hmem⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (G K Ω) a r hcont Bw'.LL
  obtain ⟨r₁, -, hr₁⟩ := GlobalTheory.DeRhamRead.exists_model_of_mem r hcont M hmem
  set rE : ↥(Dec (F := K) A) →* GL (Fin a) ↥M.1 := r₁.comp (Dec (F := K) A).subtype with hrE
  have hmodE : IsModel Bw (r.comp (Dec (F := K) A).subtype) M rE := by
    refine ⟨hS.trans hM, ?_⟩
    ext g i k
    exact congrArg (fun f : G K Ω →* GL (Fin a) (Om l) =>
      ((f (g : G K Ω) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hr₁
  have hmodL : IsModel Bw' ((resTo L r).comp (Dec (F := L) A).subtype) M (rE.comp (GlobalTheory.AboveLRes.decRes A)) := by
    refine ⟨hM, ?_⟩
    ext g i k
    exact congrArg (fun f : G K Ω →* GL (Fin a) (Om l) =>
      ((f ((GlobalTheory.AboveLRes.decRes (K := K) A g : ↥(Dec (F := K) A)) : G K Ω) : GL (Fin a) (Om l)) :
        Matrix (Fin a) (Fin a) (Om l)) i k) hr₁
  have hrep := GlobalTheory.AboveLRes.repE_decRes Bw Bw' hjj hKle M rE
  have hdL : Bw'.IsdRE P M (rE.comp (GlobalTheory.AboveLRes.decRes A)) := (hmodL.isdRAt_iff P).1 hc
  have hdR' : IsDR (P.PD Bw'.Kw) (GlobalTheory.Pst.resTo (Bw.repE M rE) hKle) := by
    unfold IsDR
    rw [← hrep, Module.finrank_fin_fun]
    exact hdL
  have hdR : IsDR (P.PD Bw.Kw) (Bw.repE M rE) :=
    (GlobalTheory.Per.TiedRestrict.isDR_restrict_iff hKle (Bw.repE M rE) T).2 hdR'
  have hdK : Bw.IsdRE P M rE := by
    have := hdR
    unfold IsDR at this
    rw [Module.finrank_fin_fun] at this
    exact this
  exact ⟨M, rE, hmodE, hdK⟩

end GlobalTheory.DRDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCharacterSupportBaseChangeLiftDegreeOne
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix GlobalTheory.IsoPull

namespace GlobalTheory.DegOneChar

section Char

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem detChar_map (i : k ≃+* k') (χ : kˣ →* ℂˣ) (g : GL (Fin 1) k') :
    detChar (Fin 1) χ (GeneralLinearGroup.map (n := Fin 1) i.symm.toRingHom g) =
      detChar (Fin 1) (χ.comp (Units.map i.symm.toRingHom.toMonoidHom)) g := by
  simp only [detChar_apply, MonoidHom.comp_apply]
  congr 1
  ext
  simp [RingHom.map_det]

theorem trGL_ofChar (i : k ≃+* k') (hi' : Continuous i.symm) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ)
    (h' : IsSmoothChar (χ.comp (Units.map i.symm.toRingHom.toMonoidHom))) :
    GlobalTheory.SuppIne.trGL i hi' (IrrGL.ofChar χ hχ) = IrrGL.ofChar (χ.comp (Units.map i.symm.toRingHom.toMonoidHom)) h' := by
  unfold GlobalTheory.SuppIne.trGL
  change _ = IrrGL.of (IrrRep.det (Fin 1) _ h').ρ (IrrRep.det (Fin 1) _ h').smooth (IrrRep.det (Fin 1) _ h').irr
  refine IrrGL.of_eq_of.2 ⟨?_⟩
  let E := (equivRep (IrrRep.det (Fin 1) χ hχ)).symm
  refine GlobalTheory.LocGL.equivOfBijective ⟨E.toLinearEquiv.toLinearMap, fun g => LinearMap.ext fun x => ?_⟩ E.toLinearEquiv.bijective
  have h1 := LinearMap.congr_fun (E.isIntertwining' (GeneralLinearGroup.map (n := Fin 1) i.symm.toRingHom g)) x
  change E.toLinearEquiv ((IrrRep.det (Fin 1) χ hχ).cl.rep.ρ _ x) = _
  refine h1.trans ?_
  change ((detChar (Fin 1) χ (GeneralLinearGroup.map (n := Fin 1) i.symm.toRingHom g) : ℂˣ) : ℂ) • E.toLinearEquiv x =
    ((detChar (Fin 1) (χ.comp (Units.map i.symm.toRingHom.toMonoidHom)) (g : GL (Fin 1) k') : ℂˣ) : ℂ) • E.toLinearEquiv x
  exact congrArg (fun z : ℂˣ => (z : ℂ) • E.toLinearEquiv x) (detChar_map i χ g)

end Char

section Norm

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

theorem adicCompletionMap_eq (e : K ≃+* M) (he : ∀ x, e x = algebraMap K M x) {v : HeightOneSpectrum (𝓞 K)}
    {u : HeightOneSpectrum (𝓞 M)} [u.asIdeal.LiesOver v.asIdeal] (hO : Over e v u) (z : v.adicCompletion K) :
    GroundTheory.Global.adicCompletionMap v u z = cLoc hO z :=
  congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := K) v).equalizer
    (GroundTheory.Global.continuous_adicCompletionMap v u) (continuous_cLoc hO)
    (funext fun x => (GroundTheory.Global.adicCompletionMap_algebraMap v u x).trans
      (by rw [Function.comp_apply, cLoc_algebraMap hO x, he]))) z

theorem normU_apply (e : K ≃+* M) (he : ∀ x, e x = algebraMap K M x) {v : HeightOneSpectrum (𝓞 K)}
    {u : HeightOneSpectrum (𝓞 M)} [u.asIdeal.LiesOver v.asIdeal] (hO : Over e v u) (y : (u.adicCompletion M)ˣ) :
    ((GlobalTheory.BCChar.normU v u y : (v.adicCompletion K)ˣ) : v.adicCompletion K) = (locEquiv hO).symm y := by
  letI : Algebra (v.adicCompletion K) (u.adicCompletion M) := (GroundTheory.Global.adicCompletionMap v u).toAlgebra
  have hf : ∀ z, algebraMap (v.adicCompletion K) (u.adicCompletion M) z = locEquiv hO z :=
    adicCompletionMap_eq e he hO
  have hb : Function.Bijective (algebraMap (v.adicCompletion K) (u.adicCompletion M)) := by
    have : ⇑(algebraMap (v.adicCompletion K) (u.adicCompletion M)) = locEquiv hO := funext hf
    rw [this]
    exact (locEquiv hO).bijective
  have h1 : Module.finrank (v.adicCompletion K) (u.adicCompletion M) = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.2 hb
  obtain ⟨z, hz⟩ := hb.2 (y : u.adicCompletion M)
  change Algebra.norm (v.adicCompletion K) (y : u.adicCompletion M) = _
  rw [← hz, Algebra.norm_algebraMap, h1, pow_one, hf, RingEquiv.symm_apply_apply]

theorem normU_eq (e : K ≃+* M) (he : ∀ x, e x = algebraMap K M x) {v : HeightOneSpectrum (𝓞 K)}
    {u : HeightOneSpectrum (𝓞 M)} [u.asIdeal.LiesOver v.asIdeal] (hO : Over e v u) :
    GlobalTheory.BCChar.normU v u = Units.map (locEquiv hO).symm.toRingHom.toMonoidHom :=
  MonoidHom.ext fun y => Units.ext (normU_apply e he hO y)

theorem over_of_liesOver (e : K ≃+* M) (he : ∀ x, e x = algebraMap K M x) (v : HeightOneSpectrum (𝓞 K))
    (u : HeightOneSpectrum (𝓞 M)) [h : u.asIdeal.LiesOver v.asIdeal] : Over e v u := fun x => by
  have hx : RingOfIntegers.mapRingEquiv e x = algebraMap (𝓞 K) (𝓞 M) x := RingOfIntegers.ext (he x)
  rw [hx, h.over, Ideal.under_def, Ideal.mem_comap]

end Norm

section Lift

theorem ofChar_congr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {χ ψ : kˣ →* ℂˣ} (h : χ = ψ) (hχ : IsSmoothChar χ) (hψ : IsSmoothChar ψ) : IrrGL.ofChar χ hχ = IrrGL.ofChar ψ hψ := by
  subst h
  rfl

variable {K M : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M]
  [Algebra K M]

theorem charLift_of_isLift (h1 : Module.finrank K M = 1) {a : ℕ} {π : CuspSub K a} {P : CuspSub M a}
    (hP : IsLift π P) : CharLift π P := by
  refine ⟨hP, fun v u _ τ T hτ hT ξ hξ hs => ?_⟩
  let e : K ≃+* M := RingEquiv.ofBijective (algebraMap K M) (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h1)
  have he : ∀ x, e x = algebraMap K M x := fun _ => rfl
  have hO : Over e v u := over_of_liesOver e he v u
  let i := locEquiv hO
  have hi : Continuous i := continuous_cLoc hO
  have hi' : Continuous i.symm := continuous_cLoc hO.symm
  obtain ⟨E, hE⟩ := hP.loc v u i hi (fun x => cLoc_algebraMap hO x) τ T hτ hT
  have hg : ∀ g : GL (Fin a) (u.adicCompletion M),
      GeneralLinearGroup.map i.toRingHom (GeneralLinearGroup.map i.symm.toRingHom g) = g := fun g =>
    Units.ext (Matrix.ext fun _ _ => i.apply_symm_apply _)
  let φ : Representation.Equiv (τ.ρ.comp (GeneralLinearGroup.map (n := Fin a) i.symm.toRingHom)) T.ρ :=
    GlobalTheory.LocGL.equivOfBijective ⟨E.toLinearMap, fun g => LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      change E (τ.ρ (GeneralLinearGroup.map i.symm.toRingHom g) x) = T.ρ g (E x)
      rw [hE, hg]⟩ E.bijective
  have hs2 := (GlobalTheory.SuppIne.hasSupport_comp i hi hi' hs).of_equiv φ
  have hN := normU_eq e he hO
  have hc : (chars ξ hξ).map (GlobalTheory.SuppIne.trGL i hi') =
      chars (fun j => (ξ j).comp (GlobalTheory.BCChar.normU v u)) fun j => GlobalTheory.BCChar.isSmoothChar_comp_normU v u (hξ j) := by
    unfold chars
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun j _ => ?_
    have hj : IsSmoothChar ((ξ j).comp (Units.map i.symm.toRingHom.toMonoidHom)) := by
      have := GlobalTheory.BCChar.isSmoothChar_comp_normU v u (hξ j)
      rwa [hN] at this
    rw [Function.comp_apply, trGL_ofChar i hi' (ξ j) (hξ j) hj]
    exact ofChar_congr (by rw [hN]) _ _
  rw [← hc]
  exact hs2

end Lift

theorem exists_charLift : ∀ (K M : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Algebra K M], Module.finrank K M = 1 → ∀ (a : ℕ), 1 ≤ a → ∀ π : CuspSub K a, ∃ P : CuspSub M a, CharLift π P := by
  intro K M _ _ _ _ _ _ _ h1 a _ π
  obtain ⟨P, hP⟩ := GlobalTheory.DegOneLift.isLift K M h1 a π
  exact ⟨P, charLift_of_isLift h1 hP⟩

end GlobalTheory.DegOneChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCmFieldLiftDisjointOfRealSolvableStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmField_lift_disjoint_of_real_solvable : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))), ∀ N : Subgroup (G E Ω), IsOpen (N : Set (G E Ω)) → ∃ T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield E))), v ∉ T ∧ ∀ F₁ : IntermediateField (maximalRealSubfield E) Ω, FiniteDimensional (maximalRealSubfield E) F₁ → IsGalois (maximalRealSubfield E) F₁ → IsSolvable (F₁ ≃ₐ[maximalRealSubfield E] F₁) → (∀ φ : F₁ →+* ℂ, ComplexEmbedding.IsReal φ) → (∀ u ∈ T, ∀ A' : ValuationSubring Ω, IsPlaceOver A' u → Dec (F := maximalRealSubfield E) A' ≤ F₁.fixingSubgroup) → ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra M Ω) (_ : IsAlgClosure M Ω) (_ : Algebra E M) (_ : IsScalarTower E M Ω), SolvDisj M N ∧ (∀ g : G E Ω, (∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) ↔ ∀ z ∈ F₁, g z = z) ∧ ∀ z ∈ F₁, ∃ x ∈ maximalRealSubfield M, algebraMap M Ω x = z := by
  first | exact @GlobalTheory.KLift.exists_cm_lift | exact GlobalTheory.KLift.exists_cm_lift | (intros; apply GlobalTheory.KLift.exists_cm_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenSubgroupWeilElementCharacterKernel
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU

theorem exists_open_sub_charKer : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w), ∀ (n : ℕ), ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a → ∀ g : Weil h, deg g ≠ 0 → ∃ V : Subgroup (Dec (F := E) A), IsOpen (V : Set (Dec (F := E) A)) ∧ commutator (Dec (F := E) A) ≤ V ∧ (⟨(g : G E Ω), Weil_le_Dec h g.2⟩ : Dec (F := E) A) ∈ V ∧ ∀ t : Ine (F := E) A, ∀ x ∈ V, (x : G E Ω) = t → ∀ j, ξ j (a (ineIncl h t)) = 1 := by
  intro Ω _ E _ _ _ _ w A h n ξ hξ a ha g hg
  let χ : Fin n → Weil h →* ℂˣ := fun j => (ξ j).comp a
  have hχ : ∀ j, IsSmooth (χ j) := fun j => ha.smooth (hξ j)
  let b := WDRep.ofChars h χ hχ
  have hy : AbW (WD.mk b) := by
    intro g₁ g₂
    rw [WD.charPol_mk, WD.lpDim_mk]
    have hc : ∀ i, χ i (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) = 1 := fun i => by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_right_comm (χ i g₁ * χ i g₂),
        mul_inv_cancel_right, mul_inv_cancel]
    have e : b.ρ (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) = 1 := by
      rw [WDRep.ofChars_ρ]
      refine LinearMap.ext fun v => funext fun i => ?_
      rw [diagEnd_apply, hc i, Units.val_one, one_mul, Module.End.one_apply]
    rw [e, LinearMap.charpoly_one]
  obtain ⟨V, hV1, hV2, hV3, hV4⟩ := GlobalTheory.AboveL.AbSub.exists_open_sub E Ω A w h (WD.mk b) hy g hg
  refine ⟨V, hV1, hV2, hV3, ?_⟩
  intro t x hx hxt j
  have hc := hV4 t x hx hxt
  rw [WD.charPol_mk, WD.lpDim_mk] at hc
  have h1 := GlobalTheory.AboveL.AbSub.eq_one_of_charpoly _ (b.semisimple _) hc
  have h2 := congrArg (fun f : Module.End ℂ (Fin n → ℂ) => f (Pi.single j 1) j) h1
  simp only [b, WDRep.ofChars_ρ, diagEnd_apply, Module.End.one_apply, Pi.single_eq_same, mul_one, χ,
    MonoidHom.comp_apply] at h2
  exact Units.ext h2

end GlobalTheory.RoadU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FieldPointLiftsGenericFibre
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.SatSupp.hasSupport_of_hasSatGL : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ), 1 ≤ n → ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B → ∃ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) (ϖ : (w.adicCompletion E)ˣ), HasSupport (IrrGL.of σ.ρ σ.smooth σ.irred).rep (chars ξ hξ) ∧ (∀ j (x : (w.adicCompletion E)ˣ), Valued.v (x : w.adicCompletion E) = 1 → ξ j x = 1) ∧ Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1 : ℤ) ∧ B = Finset.univ.val.map fun j => ξ j ϖ := by
  intro E _ _ n _ w σ B hB
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_ringHom (algebraMap E (w.adicCompletion E)).injective
  obtain ⟨α, hαB, hα⟩ := (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ σ.ρ B).1
    (GlobalTheory.LFun.SatCompare.hasSatakeGL_iff.2 ⟨⟨σ.smooth, σ.irred⟩, hB⟩)
  have hϖ : Valued.v ((GroundTheory.Global.uniformizerUnit w : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
      WithZero.exp (-1 : ℤ) := by
    simpa using GroundTheory.Global.valued_uniformizerUnit_zpow w 1
  refine ⟨fun j => GlobalTheory.SmGL.unrChar _ (α j),
    fun j => GlobalTheory.SmGL.isSmoothChar_of_isUnram (GlobalTheory.SmGL.isUnram_unrChar _ (α j)),
    GroundTheory.Global.uniformizerUnit w, ?_, ?_, hϖ, ?_⟩
  · let π : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E)) := ⟨σ.V, σ.ρ, σ.smooth, σ.irred⟩
    exact (GlobalTheory.LocLanglands.hasSupport_of_isSubquotient_prinSeries _ n _ _ π hα.2.2).of_equiv
      (IrrGL.equivOf σ.ρ σ.smooth σ.irred)
  · intro j x hx
    rw [GlobalTheory.SmGL.unrChar_apply, GlobalTheory.SmGL.SphCompletion.ord_completion, hx]
    simp
  · rw [← hαB]
    congr 1
    funext j
    rw [GlobalTheory.SmGL.unrChar_apply, GlobalTheory.SmGL.SphCompletion.ord_completion, hϖ]
    simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodGenericCharacterOfSeriesTypesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodGenericCharacter_of_weakCharacterisation : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → ∀ s, A3.fam3.Ok3 s → (∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; ∃ (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod (D.host.g k))) (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k)) C), ∀ f, D.ntypes.eSer k f = Formalism.L2.NT.eSerO O D.R.r f) → GoodGeneric A3.A.X F.P0 F.ψ0 ∧ GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ := by
  first | exact @GlobalTheory.GoodGenericSer.goodGenericCharacter_of_seriesTypes | exact GlobalTheory.GoodGenericSer.goodGenericCharacter_of_seriesTypes | (intros; apply GlobalTheory.GoodGenericSer.goodGenericCharacter_of_seriesTypes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeClose
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3.HeckeClose

theorem heckeClose : HoweUnram → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), ∀ s, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → InertJunk A3 → (∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; ∃ (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod (D.host.g k))) (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k)) C), ∀ f, D.ntypes.eSer k f = Formalism.L2.NT.eSerO O D.R.r f) → ((∃ tr, R.TrISem F tr ∧ TrISepWith A3 tr) → R.TrISem F A3.trI ∧ A3.fam3.TrISep) → R.toRealDat.LUnif → R.PGUnit F → R.PGEquiv F → R.PLevW F → R.PThmA → R.PThmB → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → (R.toCx3 F).PartsW false → ((∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) ∧ (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint)) ∧ R.PHecke F ∧ A3.fam3.TypesSep3 ∧ ∃ tr, R.TrISem F tr ∧ TrISepWith A3 tr := by
  intro hH hHC hCD D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hEx hJ hSer hPass hU hGU hGE hLW hA hB hPos hParts
  have hLI : GlobalTheory.Chain.LiftInteg D := GlobalTheory.Chain.LiftConv.liftInteg_of_cuspRapidDecay hCD D
  have hS : SchurAll R.toRealDat := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCD R.toRealDat
  have hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  obtain ⟨tr, htr⟩ := _root_.GlobalTheory.TrPass.exists_inert_passage hH R F hLI hC hEx hS hJ hX hB hPos
  have hTS : A3.fam3.TypesSep3 :=
    _root_.GlobalTheory.Hk3.typesSep3_of_pin hCD hH R F hLI hOk hC hEx ⟨fun t k => hJ.R t k.1 k.2, fun j t k => hJ.L j t k.1 k.2⟩ hPass hPos hB
  have hG : GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ := (GlobalTheory.GoodGenericSer.goodGenericCharacter_of_seriesTypes R F hC s hOk hSer).2
  have hR := _root_.GlobalTheory.Hk3.HeckeRowsClose.exists_heckeIntertwiningDefinite_of_liftInteg hH hHC hCD R F hLI hC hEx hJ hB hPos
  have hL := _root_.GlobalTheory.Hk3.heckeTheta_level3_exists_alt hH hHC hCD R F hLI hC hEx hJ s hOk hG hU hGU hGE hLW hA hPos hB hParts hTS hPass
  exact ⟨_root_.GlobalTheory.InertOkH.heckeOperators_rows_lifts_rational_adjointClosed R F hC hJ, ⟨hR, hL⟩, hTS, tr, htr⟩

end GlobalTheory.Hk3.HeckeClose

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InePolLpTwOfMemIne
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.DepthZeroRec

theorem inePol_lpTw_of_mem_Ine {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    (y : WD h) (s : ℝ) {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) :
    (y.lpTw s).inePol σ = y.inePol σ := by
  rw [WD.inePol_of_mem_Ine _ hσ, WD.inePol_of_mem_Ine _ hσ]
  obtain ⟨m, b, rfl⟩ := y.exists_rep
  rw [WD.lpTw, WD.lpTwist_mk, WD.charPol_mk, WD.charPol_mk]
  congr 1
  show ((unrChar h (qPow w s) (ineIncl h ⟨σ, hσ⟩) : ℂˣ) : ℂ) • b.ρ (ineIncl h ⟨σ, hσ⟩) = _
  rw [WeilDeligne.unrChar_apply, deg_ineIncl, zpow_zero, Units.val_one, one_smul]

end GlobalTheory.RoadU.DepthZeroRec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntInertOfComplexMultiplicationCondition
section
namespace GlobalTheory

theorem intInert_of_complexMultiplication_condition : Formalism.L2.Th1.CM.CM2 → Formalism.L2.KerInert.IntInert :=
  fun h => by
    haveI : Fact Formalism.L2.Th1.CM.CM2 := ⟨h⟩
    exact Formalism.L2.KerInert.kernels_integral_inert

end GlobalTheory
end

