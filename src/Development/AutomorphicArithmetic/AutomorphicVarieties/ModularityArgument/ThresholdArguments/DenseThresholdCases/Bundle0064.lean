module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.AuTeichEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0044
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0063
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0048
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0062
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0055
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.DownCsdK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0029
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAUpDownOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0042
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0036
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0033
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0038
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.GaloisRepExistsTotallyRealGL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0026
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.OpOfProj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PaLevel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0047
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0059
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroFinal

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AuTeichEx
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
private theorem au_teich_ex (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] :
    ∃ τ : ResidueField O →* O, ∀ x, residue O (τ x) = x := by
  haveI : CharP (O ⧸ maximalIdeal O) l := inferInstanceAs (CharP (ResidueField O) l)
  haveI : PerfectRing (ResidueField O) l := inferInstance
  let j : ResidueField O →+* Perfection (O ⧸ maximalIdeal O) l :=
    Perfection.lift l (ResidueField O) (O ⧸ maximalIdeal O) (RingHom.id (ResidueField O))
  have hj : ∀ x, Perfection.coeff (O ⧸ maximalIdeal O) l 0 (j x) = x := fun x => by
    have := (Perfection.lift l (ResidueField O) (O ⧸ maximalIdeal O)).symm_apply_apply (RingHom.id (ResidueField O))
    exact RingHom.congr_fun this x
  refine ⟨(Perfection.teichmuller l (maximalIdeal O)).comp j, fun x => ?_⟩
  exact (Perfection.mk_teichmuller (j x)).trans (hj x)
private theorem au_isTeich {l : ℕ} [hl : Fact l.Prime] {F : W.GFrame l} (c : Coef l) {n : ℕ} (r : Resid F c.O n) :
    ∃ t, r.IsTeich t := by
  obtain ⟨hc, hfin, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  haveI : Finite (ResidueField c.O) := hfin
  haveI : CharP (ResidueField c.O) l := by
    refine (CharP.charP_iff_prime_eq_zero hl.out).2 ?_
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]
    exact hlm
  obtain ⟨τ, hτ⟩ := au_teich_ex l c.O
  refine ⟨fun i => (Units.map τ).comp (r.chib i), fun i g => ⟨hτ _, ?_⟩⟩
  rw [MonoidHom.comp_apply, ← map_pow, ← Nat.card_units, pow_card_eq_one', map_one]
private theorem au_open {G O : Type} [Group G] [TopologicalSpace G] [CommRing O] {m : ℕ} (f : O →+* ℂ) (hf : Function.Injective f)
    (τ : G →* GL (Fin m) O) (h : IsOpen (((Matrix.GeneralLinearGroup.map f).comp τ).ker : Set G)) : IsOpen (τ.ker : Set G) := by
  have : ((Matrix.GeneralLinearGroup.map f).comp τ).ker = τ.ker := by
    refine MonoidHom.ker_comp_of_injective _ _ fun a b hab => ?_
    ext i j
    exact hf (congrArg (fun x : GL (Fin m) ℂ => (x : Matrix (Fin m) (Fin m) ℂ) i j) hab)
  rwa [this] at h
theorem UpperTheory.V.Hi.automorphicHeckeSet_unitaryPointProperties_of_typeFor :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀ →
    (hset Q τ₀).AutomorphicHeckeSet ι (_root_.UpperTheory.V.Hi.CaseU.UnitaryPointProperties r ι) := by
  intro hP l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι m τ₀ hτ lam _ d ξ hξ F hF hK hI
  obtain ⟨e, he⟩ := hξ
  obtain ⟨t, ht⟩ := au_isTeich c r
  have hop : IsOpen (τ₀.ker : Set (KT n (wt s))) :=
    au_open _ (ι.injective.comp Subtype.val_injective) τ₀ (hτ t ht).1
  have h1 := decompU l L Ω s n hn V Q c m τ₀ ι hop lam d e ξ he F hF hK hI
  refine SetLike.le_def.1 (iSup_le fun σ => ?_) h1
  by_cases h0 : YOf Q ι τ₀ e ξ σ.1 = ⊥
  · rw [h0]; exact bot_le
  · obtain ⟨Y, hY, hPU, -⟩ := _root_.UpperTheory.V.Z.Desc.P.partU_alt hP l L Ω s n hn V Q c r ι m τ₀ hτ lam d e ξ he σ.1 σ.2 h0
    rw [← hY]
    exact le_iSup (fun Y : {Y : (hset Q τ₀).PartAltAlt ι lam ξ // _root_.UpperTheory.V.Hi.CaseU.UnitaryPointProperties r ι lam Y.r} => Y.1.Y) ⟨Y, hPU⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutUOT
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.V.Z UpperTheory.V.Z.Ord UpperTheory.Gal.projectedFormsSystemPart UpperTheory.GalN.V
namespace UpperTheory.Gal.projectedFormsSystemPart
section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)} {w : Plc F} {τ : SmIrr (GLw n w)} {B : Multiset ℂˣ}
end
private theorem part2 (H : _root_.UpperTheory.V.Af.HypothesesH') {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) {n : ℕ} (hn : 1 ≤ n) {V : s.Lev} {ι : Qbar l ≃+* ℂ}
    {ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)} (hρ : Continuous ρ) {σ : Submodule ℂ (UA L n → ℂ)} (hσ : IsAutRepU σ)
    (hLG : ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ →
      _root_.UpperTheory.V.Z.Win.LocGlobT ι (ρ.comp V.pr) w τ) (hi : Af.IsIrr (ρ.comp V.pr)) :
    ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ Af.AttC ι (ρ.comp V.pr) π ∧
      (∀ w, IsUnramU σ w → ∃ B, (CG.mk π).HasSat w B) ∧ ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w),
        π.IsLocComp w τ ↔ IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ := by
  have hc : Continuous (ρ.comp V.pr) := hρ.comp (V.pr_cont W.continuous_resP)
  have hoff : ∀ᶠ w : Plc L in Filter.cofinite, ((l : ℕ) : 𝓞 L) ∉ w.asIdeal := by
    have h0 : Ideal.span {((l : ℕ) : 𝓞 L)} ≠ 0 := by
      simp [(Fact.out : l.Prime).ne_zero]
    exact (Ideal.finite_factors h0).subset fun w hw => Ideal.dvd_span_singleton.mpr (not_not.mp hw)
  exact _root_.UpperTheory.Gal.projectedFormsSystemPart.link2_alt H L Ω (UpperTheory.isUnramifiedAt_totallyReal_of_inertia_le_restriction_range L Ω s.unr) l s.odd ι n hn σ hσ _ hc hi
    (hoff.mono fun w hw hsp τ hτ B hB => _root_.UpperTheory.Gal.projectedFormsSystemPart.frobLG'_alt H.toClassicalTheorems hc hw hB (hLG w hsp τ hτ))
theorem autUO_of_printsH : _root_.UpperTheory.V.Af.HypothesesH' → _root_.UpperTheory.V.Z.Ord.AutUOAlt := by
  intro H l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι m τ₀ hτ lam _ d ξ hξ F hF hK hI
  obtain ⟨e, he⟩ := hξ
  have hTeich : ∃ t, r.IsTeich t := by
    obtain ⟨hc, hfin, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
    have : CharP (ResidueField c.O) l := by
      refine (CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).2 ?_
      rw [← map_natCast (residue c.O), residue_eq_zero_iff]
      exact hlm
    have : CharP (c.O ⧸ maximalIdeal c.O) l := inferInstanceAs (CharP (ResidueField c.O) l)
    have : PerfectRing (ResidueField c.O) l := inferInstance
    let lift := Perfection.lift l (ResidueField c.O) (c.O ⧸ maximalIdeal c.O)
    let j := lift (RingHom.id (ResidueField c.O))
    let τ := (Perfection.teichmuller l (maximalIdeal c.O)).comp j.toMonoidHom
    have hres (x : ResidueField c.O) : residue c.O (τ x) = x :=
      (Perfection.mk_teichmuller (j x)).trans
        (RingHom.congr_fun (lift.symm_apply_apply (RingHom.id (ResidueField c.O))) x)
    refine ⟨fun i => (Units.map τ).comp (r.chib i), fun i g => ⟨hres _, ?_⟩⟩
    rw [MonoidHom.comp_apply, ← map_pow, ← Nat.card_units, pow_card_eq_one', map_one]
  obtain ⟨t, ht⟩ := hTeich
  have hop : IsOpen (τ₀.ker : Set (KT n (wt s))) := by
    let f := ι.toRingHom.comp (algebraMap c.O (Qbar l))
    have hf : Function.Injective f := ι.injective.comp Subtype.val_injective
    have hmap : Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin m) f) := by
      intro A B hAB
      apply Units.ext
      apply Matrix.ext
      intro i j
      exact hf (congrArg (fun M : GL (Fin m) ℂ => (M : Matrix (Fin m) (Fin m) ℂ) i j) hAB)
    rw [← MonoidHom.ker_comp_of_injective τ₀ _ hmap]
    exact (hτ t ht).1
  have h1 := decompU l L Ω s n hn V Q c m τ₀ ι hop lam d e ξ he F hF hK hI
  refine IsConcreteLE.le_iff.1 (iSup_le fun σ => ?_) h1
  by_cases h0 : YOf Q ι τ₀ e ξ σ.1 = ⊥
  · rw [h0]; exact bot_le
  obtain ⟨Y, hY, -, hcomp, hLG⟩ := _root_.UpperTheory.V.Z.Desc.P.partU_alt H l L Ω s n hn V Q c r ι m τ₀ hτ lam d e ξ he σ.1 σ.2 h0
  rw [← hY]
  refine le_iSup (fun Y : {Y : (hset Q τ₀).PartAltAlt ι lam ξ // Af.IsIrr (Y.r.comp V.pr) → ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧
    GlobalTheory.ContraPair.DualIsConj π ∧ Af.AttC ι (Y.r.comp V.pr) π ∧ ∀ v, π.IsLocComp ((hset Q τ₀).Sl v) (Y.σl v)} => Y.1.Y) ⟨Y, fun hi => ?_⟩
  obtain ⟨π, p1, p2, p3, -, p5⟩ := part2 H s hn Y.cont σ.2 hLG hi
  refine ⟨π, p1, p2, p3, fun v => ?_⟩
  have hsplit : IsSplitAt (s.w v.1) :=
    UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA v.1) (s.split _ (Or.inl v.2)) _
      (HeightOneSpectrum.ext (Ideal.ext fun x =>
        (show _ ↔ _ from (s.hw v.1) (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v.1 x)))
  exact (p5 _ hsplit _).2 (hcomp v)
end UpperTheory.Gal.projectedFormsSystemPart
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EndsRankThreeOfLocal
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.GalN.V UpperTheory.V.Z.Win
set_option linter.unusedVariables false
namespace UpperTheory.V.Z.Win.Dn
theorem isoTw_alt : _root_.UpperTheory.V.Z.Win.AIsoTwAlt := _root_.UpperTheory.V.Z.Win.aIsoTwOf_alt flagLaws ImaginaryQuadraticEtaCharacter.winTw
theorem aUpDown_alt (H : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Z.Win.AUpDownAlt :=
  _root_.UpperTheory.V.Z.Win.aUpDownOf_alt weakOfAtt flagLaws (thruAway plainRec) (_root_.UpperTheory.V.Z.Ord.thruL_alt H.toClassicalTheorems plainRec) ImaginaryQuadraticEtaCharacter.winUpDown ImaginaryQuadraticEtaCharacter.winOf
theorem aAcross_alt (H : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Z.Win.AAcrossAlt := _root_.UpperTheory.V.Z.Win.a_across_of_statement flagLaws (_root_.UpperTheory.V.Z.Win.Dn.aUpDown_alt H) _root_.UpperTheory.V.Z.Win.Dn.isoTw_alt
theorem ends_rank_three_of_local (H : _root_.UpperTheory.V.Af.HypothesesH') : RowT := _root_.UpperTheory.Gal.SV.rowOf' H.litN.aut.gal
local instance  (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω] : Module.IsTorsionFree L Ω := DivisionSemiring.to_moduleIsTorsionFree
section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)}
  (K : Type) [Field K] [NumberField K] [IsCMField F] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsGalois F K]
theorem automorphy_up_base_change (H : _root_.UpperTheory.V.Af.HypothesesH') (hs : Group.IsSolvable (K ≃ₐ[F] K)) (hn : 1 ≤ n) (hc : Continuous r)
    (hi : IsIrr (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω))) (hp : Sol.Pol ι r) (ha : IsRegAlgAutomorphicAttached ι r) (hF : Flagged r)
    (h : WitA ι r) : WitA ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) :=
  (_root_.UpperTheory.V.Z.Win.Dn.aUpDown_alt H H (_root_.UpperTheory.V.Z.Win.Dn.ends_rank_three_of_local H) F K Ω hs l ι n hn r hc hi hp ha hF).1 h
theorem down'_alt (H : _root_.UpperTheory.V.Af.HypothesesH') (hs : Group.IsSolvable (K ≃ₐ[F] K)) (hn : 1 ≤ n) (hc : Continuous r)
    (hi : IsIrr (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω))) (hp : Sol.Pol ι r) (ha : IsRegAlgAutomorphicAttached ι r) (hF : Flagged r)
    (hI : IneAb r) (hK : Keeps r K) (h : WitA ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω))) : WitA ι r :=
  (_root_.UpperTheory.V.Z.Win.Dn.aUpDown_alt H H (_root_.UpperTheory.V.Z.Win.Dn.ends_rank_three_of_local H) F K Ω hs l ι n hn r hc hi hp ha hF).2 hI hK h
end
theorem across'_alt (H : _root_.UpperTheory.V.Af.HypothesesH') (K Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω]
    (hK : Module.finrank ℚ K = 2) {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} (hn : 1 ≤ n)
    (hs : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ g ∈ Dec (F := ℚ) A, ∀ x : K, g (algebraMap K Ω x) = algebraMap K Ω x)
    {r : G ℚ Ω →* GL (Fin n) (Qbar l)} (hc : Continuous r) (ha : IsAutomorphicOverImagQuad ι r) (hd : ∃ θ, IsAlgChar ι θ ∧ DualTw r θ) (hI : IneAb r)
    (hF : Flagged r) (hi : IsIrr (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)))
    (h : WitA ι (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω))) : WitAQ ι r :=
  _root_.UpperTheory.V.Z.Win.Dn.aAcross_alt H H (_root_.UpperTheory.V.Z.Win.Dn.ends_rank_three_of_local H) K Ω hK l ι n hn hs r hc ha hd hI hF hi h
theorem twist'_alt (P : _root_.UpperTheory.V.Af.Hypotheses') {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {r : G F Ω →* GL (Fin n) (Qbar l)} {μ : G F Ω →* (Qbar l)ˣ} (hμ : IsAlgChar ι μ)
    (hc : Continuous μ) (h : WitA ι r) : WitA ι (tw r μ) :=
  (_root_.UpperTheory.V.Z.Win.Dn.isoTw_alt P F Ω l ι n r h).2 μ hμ
def DownCsdKAlt : Prop :=
  ∀ (K L Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field L] [NumberField L] [IsCMField L] [Field Ω] [CharZero Ω]
    [IsAlgClosure ℚ Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K L]
    [Group.IsSolvable (L ≃ₐ[K] L)] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n →
    ∀ (r : G K Ω →* GL (Fin n) (Qbar l)) (σ : G ℚ Ω), Sd.IsCC σ → Continuous r →
    (∃ P, Sd.IsPair σ r (cycBar K Ω l ^ (1 - (n : ℤ))) P) → IsIrr (r.comp (galEmb K L Ω)) →
    IneAb r → Flagged r → Keeps r L → _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (r.comp (galEmb K L Ω)) → _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r
end UpperTheory.V.Z.Win.Dn
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GalRepDescentAlongQuadraticExtension
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
theorem UpperTheory.V.Af.rankTwoAutomorphyDescends_of_printsH :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Pr.RankTwoAutomorphyDescendsFromAbelianCMToRat := fun P =>
  Or.elim P.cyc2 (fun h => _root_.UpperTheory.V.Z.Bc.isAutR_of_isAutC_comp_galEmb_of_odd_quadratic_char P P.cyc h (_root_.UpperTheory.V.Z.Bc.gapTwo_alt P))
    fun h L Ω _ _ _ _ _ _ _ _ l _ ι W h1 h2 h3 h4 h5 => h L Ω l ι W h1 h2 h3 h4 h5
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevOpOf
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem opOf_proj {Λ Γ Q M : Type} [CommRing Λ] [Group Γ] [Group Q] [AddCommGroup M] [Module Λ M]
    (ρ : Representation Λ Q M) (e : Γ ≃* Q) (hP : Module.Projective (MonoidAlgebra Λ Q) ρ.asModule) :
    Module.Projective (MonoidAlgebra Λ Γ) (Representation.asModule (ρ.comp e.toMonoidHom : Representation Λ Γ M)) := by
  let σ : MonoidAlgebra Λ Q ≃+* MonoidAlgebra Λ Γ := (MonoidAlgebra.domCongr Λ Λ e.symm).toRingEquiv
  let ρ' : Representation Λ Γ M := ρ.comp e.toMonoidHom
  have key : ∀ a : MonoidAlgebra Λ Q, ρ'.asAlgebraHom (σ a) = ρ.asAlgebraHom a := fun a => by
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
    | single g c => simp [σ, ρ']
  haveI := RingHomInvPair.of_ringEquiv σ
  haveI := RingHomInvPair.of_ringEquiv_symm σ
  let f : ρ.asModule ≃ₛₗ[(σ : MonoidAlgebra Λ Q →+* MonoidAlgebra Λ Γ)] ρ'.asModule :=
    { ρ.asModuleEquiv.toAddEquiv.trans ρ'.asModuleEquiv.symm.toAddEquiv with
      map_smul' := fun a m => by
        apply ρ'.asModuleEquiv.injective
        rw [Representation.asModuleEquiv_map_smul]
        simp [Representation.asModuleEquiv_map_smul, key] }
  exact Module.Projective.of_equiv f
private theorem opOf_dc {R G P : Type} [CommRing R] [Group G] [AddCommGroup P] [Module R P] (ρ : Representation R G P)
    (K K1 : Subgroup G) [Fintype (K ⧸ K1.subgroupOf K)] (m : P) (hm : m ∈ fixd ρ K1) :
    dc ρ K K1 1 m = ∑ g : K ⧸ K1.subgroupOf K, ρ (g.out : K) m := by
  let f : K ⧸ K1.subgroupOf K → MulAction.orbit K ((1 : G) : G ⧸ K1) := fun g =>
    ⟨((g.out : K) : G), g.out, congrArg QuotientGroup.mk (mul_one _)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => ?_, ?_⟩
    · have h1 := QuotientGroup.eq.1 (congrArg Subtype.val hab)
      rw [← a.out_eq', ← b.out_eq']
      exact QuotientGroup.eq.2 h1
    · rintro ⟨_, k, rfl⟩
      refine ⟨(k : K ⧸ K1.subgroupOf K), Subtype.ext ?_⟩
      have h1 := QuotientGroup.eq.1 (QuotientGroup.out_eq' (k : K ⧸ K1.subgroupOf K))
      have h2 : (((k : K ⧸ K1.subgroupOf K).out : K) : G ⧸ K1) = ((k : G) : G ⧸ K1) := QuotientGroup.eq.2 h1
      exact h2.trans (congrArg (QuotientGroup.mk (s := K1)) (mul_one (k : G)).symm)
  unfold dc
  rw [← finsum_comp f hf, finsum_eq_sum_of_fintype, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul K1 ((g.out : K) : G)
  show ρ (((g.out : K) : G) : G ⧸ K1).out m = _
  rw [hu, map_mul, Module.End.mul_apply, hm u u.2]
private theorem opOf_tr {Λ R G P Γ σ : Type} [CommRing Λ] [CommRing R] [Algebra Λ R] [Group G] [AddCommGroup P]
    [Module R P] [Module Λ P] [IsScalarTower Λ R P] [Group Γ] [Finite Γ] (ρ : Representation R G P)
    (K K1 : Subgroup G) (hle : K1 ≤ K) [(K1.subgroupOf K).Normal]
    (ρ' : Representation Λ (K ⧸ K1.subgroupOf K) (fixd ρ K1))
    (hρ' : ∀ (u : K) f, (ρ' (u : K ⧸ K1.subgroupOf K) f : P) = ρ u f)
    (hP : Module.Projective (MonoidAlgebra Λ (K ⧸ K1.subgroupOf K)) ρ'.asModule)
    (e : Γ ≃* K ⧸ K1.subgroupOf K) (γ : σ → Γ) (hγ : Subgroup.closure (Set.range γ) = ⊤)
    (Y : σ → Module.End R (fixd ρ K1)) (hY : ∀ p m, ρ' (e (γ p)) m = m + Y p m)
    (tr : fixd ρ K1 →ₗ[R] fixd ρ K) (htr : ∀ m, (tr m : P) = dc ρ K K1 1 m) :
    Function.Surjective tr ∧ LinearMap.ker tr = ⨆ p, LinearMap.range (Y p) := by
  haveI : Finite (K ⧸ K1.subgroupOf K) := Finite.of_equiv Γ e.toEquiv
  letI := Fintype.ofFinite (K ⧸ K1.subgroupOf K)
  obtain ⟨h1, h2⟩ := projNorm Λ _ _ ρ' hP
  have hs : ∀ m, (tr m : P) = (∑ g, ρ' g m : fixd ρ K1) := fun m => by
    rw [htr, opOf_dc ρ K K1 m m.2, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← hρ', QuotientGroup.out_eq']
  refine ⟨fun v => ?_, le_antisymm (fun m hm => ?_) (iSup_le fun p => ?_)⟩
  · obtain ⟨m, hm⟩ := h1 ⟨v, fixd_anti ρ hle v.2⟩ fun g => by
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective g
      exact Subtype.ext ((hρ' u _).trans (v.2 u u.2))
    exact ⟨m, Subtype.ext (by rw [hs, hm])⟩
  · have h0 : ∑ g, ρ' g m = 0 := Subtype.ext (by rw [← hs, LinearMap.mem_ker.1 hm]; rfl)
    have hc : Subgroup.closure (Set.range fun p => e (γ p)) = ⊤ := by
      have := congrArg (Subgroup.map e.toMonoidHom) hγ
      rw [MonoidHom.map_closure, ← Set.range_comp, Subgroup.map_top_of_surjective _ e.surjective] at this
      exact this
    have h3 : (⨆ g ∈ Set.range fun p => e (γ p), LinearMap.range (ρ' g - 1)) ≤
        (⨆ p, LinearMap.range (Y p)).restrictScalars Λ := by
      refine iSup₂_le ?_
      rintro _ ⟨p, rfl⟩ _ ⟨v, rfl⟩
      refine Submodule.mem_iSup_of_mem (p := fun p => LinearMap.range (Y p)) p ⟨v, ?_⟩
      rw [LinearMap.sub_apply, hY, Module.End.one_apply, add_sub_cancel_left]
    exact h3 (h2 _ hc m h0)
  · rintro _ ⟨m, rfl⟩
    have h4 : tr (ρ' (e (γ p)) m) = tr m := Subtype.ext (by
      rw [hs, hs]
      congr 1
      refine Fintype.sum_equiv (Equiv.mulRight (e (γ p))) _ _ fun g => ?_
      rw [Equiv.coe_mulRight, map_mul, Module.End.mul_apply])
    rw [hY, map_add (f := _)] at h4
    exact add_eq_left.1 h4
private theorem opOf_gen {l q n : ℕ} (hl : l.Prime) (a : Fin q → ℕ) :
    Subgroup.closure (Set.range fun p : Fin q × Fin n => (Pi.mulSingle p (Multiplicative.ofAdd 1) : Del l n a)) = ⊤ := by
  haveI : ∀ p : Fin q × Fin n, NeZero (l ^ a p.1) := fun s => ⟨pow_ne_zero _ hl.ne_zero⟩
  refine eq_top_iff.2 fun g _ => ?_
  rw [← Finset.univ_prod_mulSingle g]
  refine Subgroup.prod_mem _ fun s _ => ?_
  have h1 : g s = Multiplicative.ofAdd (1 : ZMod (l ^ a s.1)) ^ (Multiplicative.toAdd (g s)).val := by
    rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
  rw [h1, Pi.mulSingle_pow]
  exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self s)) _
private theorem opOf_cop {L : Type} [Field L] [NumberField L] (w : Plc L) {l : ℕ} (hl : l.Prime)
    (hw : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) : l.Coprime (resCard (w.adicCompletion L)) := by
  have h1 : Valued.v (l : w.adicCompletion L) = 1 := by
    have e : (l : w.adicCompletion L) = algebraMap L _ (algebraMap (𝓞 L) L l) := by simp
    rw [e]
    refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).trans ?_
    exact (HeightOneSpectrum.valuation_of_algebraMap w _).trans (HeightOneSpectrum.intValuation_eq_one_iff.2 hw)
  have h2 : valuation (w.adicCompletion L) (l : w.adicCompletion L) = 1 := by
    haveI : (Valued.v : Valuation (w.adicCompletion L) _).Compatible := Valuation.Compatible.ofValuation _
    exact (ValuativeRel.isEquiv (valuation (w.adicCompletion L)) Valued.v).eq_one_iff_eq_one.2 h1
  have h3 : IsUnit (l : 𝒪[w.adicCompletion L]) :=
    (Valuation.integer.integers _).isUnit_iff_valuation_eq_one.2 (by simpa using h2)
  have h4 : (l : 𝓀[w.adicCompletion L]) ≠ 0 := by
    simpa using (h3.map (residue 𝒪[w.adicCompletion L])).ne_zero
  rw [hl.coprime_iff_not_dvd]
  intro hd
  letI := Fintype.ofFinite 𝓀[w.adicCompletion L]
  haveI := Fact.mk hl
  rw [resCard, Nat.card_eq_fintype_card] at hd
  exact h4 ((ringChar.spec _ _).2 (by
    have h5 := (prime_dvd_char_iff_dvd_card l).2 hd
    have h6 := CharP.char_is_prime 𝓀[w.adicCompletion L] (ringChar 𝓀[w.adicCompletion L])
    rw [(Nat.prime_dvd_prime_iff_eq hl h6).1 h5]))
private theorem opOf_le {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (C : Subgroup 𝓀[k]ˣ) : iwC k n C ≤ iwC k n ⊤ := by
  have h1 : unitsC k C ≤ unitsC k ⊤ := Subgroup.map_mono (Subgroup.comap_mono le_top)
  have h2 : torC k n C ≤ torC k n ⊤ := fun t ht i hi => h1 (ht i hi)
  exact sup_le_sup_left (Subgroup.map_mono h2) _
private theorem opOf_tow {Λ R P : Type} [CommRing Λ] [CommRing R] [Algebra Λ R] [AddCommGroup P]
    [Module R P] [Module Λ P] [IsScalarTower Λ R P] (S : Submodule R P) : IsScalarTower Λ R S := inferInstance
theorem UpperTheory.V.Pa.Lev.opOf_alt :
    _root_.UpperTheory.V.Pa.LocPAlt → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (D : ℕ) (b : TWBase (pairOf B.u) J Empty D) (V : s.Lev) (h : (globOf r V).Hom (globOf r V0)) (q : ℕ) (w : Fin q → Plc L) (A : LevMod b h w) (x δ : ∀ j, ((w j).adicCompletion L)ˣ), (∀ j, ((l : ℕ) : 𝓞 L) ∉ (w j).asIdeal) → (∀ j, IsUnif (x j)) → (∀ j, IsGenMod _ (ellC l _) (δ j)) → ∀ (ph ta : Fin q → (globOf r V).G₀) (N : ℕ), _root_.UpperTheory.V.Pa.Lev.LocalLevelConditions A x δ ph ta → (∀ j, qj w j ≡ 1 [MOD l ^ N]) → ∃ A' : OpMod b h q N, OpRel A' (qj w) ph ta n.factorial := by
  intro hP l hl L Ω _ _ _ _ _ _ s V0 O _ _ _ hO _ n r B J D b V h q w A x δ hw hx hδ ph ta N hok hN
  have hq : ∀ j, IsUnit (qj w j : A.R) := fun j => by
    haveI := hO.char
    have h1 : IsUnit (qj w j : ResidueField O) :=
      (CharP.isUnit_natCast_iff hl.out).2 (hl.out.coprime_iff_not_dvd.1 (opOf_cop (w j) hl.out (hw j)))
    have h2 : IsUnit (qj w j : O) := by
      rw [← map_natCast (residue O)] at h1
      exact (isUnit_map_iff _ _).1 h1
    simpa using h2.map (algebraMap O A.R)
  obtain ⟨T⟩ := thEx L n q w l A.R A.P A.ρ x δ hq
  obtain ⟨hn, ρ', hρ', hpr⟩ := A.proj
  obtain ⟨e, he⟩ := delIso L n q w l δ hδ
  obtain ⟨hy, tr, htr, hu⟩ := trOf L n q w l A.R A.P A.ρ x δ T hδ
  obtain ⟨h1, h2⟩ := _root_.UpperTheory.V.Z.Win.T2.level_relation_one_two hP l L Ω s V0 O n r B J D b V h q w A x δ hw hx hδ T ph ta hok
  have h3 := _root_.UpperTheory.V.Pa.Lev.twoOf_alt hP l L Ω s V0 O n r B J D b V h q w A x δ hw hx hδ T ph ta hok
  have hg : ∀ j i m, ρ' (e (Pi.mulSingle (j, i) (Multiplicative.ofAdd 1))) m = T.act1 (1 + yV A.R j i) m := fun j i m => by
    obtain ⟨g, hg1, hg2⟩ := he j i
    exact Subtype.ext (by rw [hg2, hρ', hg1]; exact (hy j i m).symm)
  have hle : UIw1 l n w ≤ UIw n w := fun g hg j hj => opOf_le _ (hg j hj)
  haveI : ∀ p : Fin q × Fin n, NeZero (l ^ padicValNat l (qj w p.1 - 1)) := fun s => ⟨pow_ne_zero _ hl.out.ne_zero⟩
  obtain ⟨hs, hk⟩ := opOf_tr A.ρ (UIw n w) (UIw1 l n w) hle ρ' hρ' hpr e
    (fun p : Fin q × Fin n => Pi.mulSingle p (Multiplicative.ofAdd 1)) (opOf_gen hl.out fun j => padicValNat l (qj w j - 1))
    (fun p : Fin q × Fin n => T.act1 (yV A.R p.1 p.2)) (fun p m => (hg p.1 p.2 m).trans (by rw [map_add (f := _), map_one]; rfl)) tr htr
  have ha : ∀ j, N ≤ padicValNat l (qj w j - 1) := fun j => by
    have h4 : 1 < qj w j := Finite.one_lt_card
    exact ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) (by omega)).1 ((Nat.modEq_iff_dvd' h4.le).1 (hN j).symm)
  exact ⟨{ rN := A.rN, compat := A.compat, R := A.R, p := A.p, segmentWeightExponent := A.segmentWeightExponent, β := A.β, β_pair := A.β_pair
           M1 := fixd A.ρ (UC n w fun _ => ellC l _), tow1 := opOf_tow _, fin1 := A.fin, Mw := fixd A.ρ (UC n w fun _ => ⊤)
           act1 := T.act1, actw := T.actw, a := fun j => padicValNat l (qj w j - 1), le_a := ha
           ρ := ρ'.comp e.toMonoidHom, ρ_gen := hg, proj := opOf_proj ρ' e hpr
           tr := tr, tr_surj := hs, tr_ker := hk, tr_u := hu }, h3, h1, h2⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.NewformAut0
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp
open UpperTheory.V.Af
open scoped Matrix
namespace UpperTheory.V.Af.NewformAutomorphy
end UpperTheory.V.Af.NewformAutomorphy
theorem UpperTheory.GalN.V.newformAut0_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → NewformAut0 := by
  intro P k hk f l hl Ω _ _ _ ι W j hf hW K _ _ _ _ _ _ hK hirr
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  exact _root_.UpperTheory.V.Sd.up_quad_of_printed_results P ℚ K Ω l ι hK 2 one_le_two W hW (_root_.UpperTheory.V.Af.newformAutR_alt P k hk f l Ω ι W j hf) hirr
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TTypeEx
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
theorem UpperTheory.V.Hi.exists_integral_type_for_residual_rep :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∃ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀ :=
  fun P => _root_.UpperTheory.NonzeroTypeTheory.exists_type_for_residual_rep' P.litN
end
end

