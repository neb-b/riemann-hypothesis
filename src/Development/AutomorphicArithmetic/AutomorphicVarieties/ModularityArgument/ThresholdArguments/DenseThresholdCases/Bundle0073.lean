module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0068
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0058
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.UnramifiedTwists.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.CompatTOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DualOfWeights
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0032
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0026
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0027
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0054
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0039
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0028
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.Narrow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.OddAOfUnl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0047
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0043
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0040
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0019
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.GaloisRepExistsTotallyRealGL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.ExtraV
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0041
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0053
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0069
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PaLevel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocalLanglandsGLOfPrints

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.JEnd1W
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
open UpperTheory.GalN.V
theorem UpperTheory.V.Hi.arithmeticPointDecomposition_of_isJ :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), V.S' = s.S → ∀ J : Ideal B.B, R.IsJ B K J → ArithmeticPointDecomposition B ι J := by
  intro H l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι B Λ R K _ J hJ
  have hpr : Function.Surjective V.pr := fun g => by
    obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
    obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
    exact ⟨σ, Subtype.ext hτ⟩
  have hunr : ∀ w : HeightOneSpectrum (𝓞 L),
      Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal := by
    intro w
    have h := GlobalTheory.RayFromArtin.unramIn_of_ine (K := Lp L) (Ω := Ω) L
      (v := w.under (𝓞 (Lp L))) fun A hA σ hσ => by
        obtain ⟨g, rfl⟩ := s.unr A _ hA hσ
        ext x
        apply (algebraMap L Ω).injective
        exact (AlgEquiv.restrictNormal_commutes (W.resP L Ω g) L x).trans (g.commutes x)
    have hbot : w.asIdeal.inertia Gal(L/Lp L) = ⊥ := by
      rw [eq_bot_iff]
      intro τ hτ
      exact h τ ⟨w.asIdeal, w.isPrime, ⟨rfl⟩, hτ⟩
    have he := UpperTheory.V.CF.ineCard.1 (Lp L) L w
    rw [hbot, Subgroup.card_bot] at he
    exact Ideal.ramificationIdx_eq_one_iff.1 he.symm
  refine fun x h hx ha => ?_
  · obtain ⟨lam, ρ, hc, hs, hP, hr⟩ := _root_.hecke_ideal_end H hn hJ x h hx ha
    have hc' : Continuous (ρ.comp V.pr) := hc.comp (V.pr_cont W.continuous_resP)
    have hs' : Formalism.MainNotions.N.IsSSRep (ρ.comp V.pr) := by
      intro M hM
      obtain ⟨M', hM', hcompl⟩ := hs M (fun g => by
        obtain ⟨g', rfl⟩ := hpr g
        exact hM g')
      exact ⟨M', fun g => hM' (V.pr g), hcompl⟩
    obtain ⟨σ, hσ, hlg, -⟩ := hP.aut
    exact ⟨_, hc', hs', hr,
      _root_.UpperTheory.V.Z.Win.Gu.endShape'_alt H L Ω hunr l s.odd ι n hn σ hσ _ hc' hs' hlg⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.JPTRow
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
open UpperTheory.GalN.V UpperTheory.V.Z.Win UpperTheory.V.Z.Desc.W UpperTheory.Zero.LLC
theorem UpperTheory.V.Z.Desc.W.same_of_prints_of_rT (P : _root_.UpperTheory.V.Af.Hypotheses') (hR : RowT) : Same :=
  _root_.UpperTheory.V.Z.Desc.W.same_of_statement P (_root_.UpperTheory.BaseChangeIdentities.bcSpeh_alt (_root_.UpperTheory.BaseChangeIdentities.bridge P.litN.aut.bc P.litN.loc.bern)) satTw (sumAEOf satTw (_root_.UpperTheory.V.Z.Desc.W.galAEOf_alt P hR)) _root_.UpperTheory.V.Z.Desc.W.splitSat_alt onePart
theorem UpperTheory.V.Z.Desc.W.point_property_of_isJ_arith_rep_autCsd : RowT →
    _root_.UpperTheory.V.Af.HypothesesH' → Z.Desc.DescWeak → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), V.S' = s.S → ∀ J : Ideal B.B, R.IsJ B K J →
    ∀ (x : B.Pt) (h : s.Wt n) (ρ : G L Ω →* GL (Fin n) (Qbar l)), 2 ≤ n → n ≤ 4 → x.Arith h →
    x.IsRep ρ → Continuous ρ → IsAutCsdA ι ρ → (∀ g ∈ Ine (F := L) (s.A s.v0), ρ g = 1) →
    (∀ v : Vl l L, W.HasFlag (ρ.comp (Dec (F := L) (s.A v)).subtype) (x.psi v) ∧
      ∀ i j, x.psi v i ≠ x.psi v j * (cycBar L Ω l).comp (Dec (F := L) (s.A v)).subtype) →
    J ≤ RingHom.ker x :=
  fun hR PH => _root_.UpperTheory.V.Z.Desc.W.jPT_of_alt recTExists (compatTOf hR plainRec) plainRec (_root_.UpperTheory.V.Z.Desc.W.same_of_prints_of_rT PH.toClassicalTheorems hR) _root_.UpperTheory.V.Z.Desc.W.sphT_alt _root_.UpperTheory.V.Z.Desc.W.pseudo_local_langlands_descent unlOf PH
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.KeepLevel
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Lev UpperTheory.V.Z.Win
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Keep
theorem levelCore_alt (P : _root_.UpperTheory.V.Af.Hypotheses') (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ) (hn : 2 ≤ n) (m : Fin n → ℤ)
    (M : ℕ) (hM : 1 ≤ M) (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ)
    (r : G K Ω →* GL (Fin n) (Qbar l)) (π : CuspSub K n) (hL : LevelF l M m r)
    (hU : ∀ w : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∈ w.asIdeal → Unl1 r w ∨ PotUnl r w) (hW : WitA ι r)
    (hreg : (CG.mk π).IsRegAlg) (hpol : ∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ) (ha : AttC ι r π) :
    (∀ τ, π.HasInfChar τ (infOf m)) ∧ HasFixed π.finPart (KLev K n M) ∧
      ∀ w : HeightOneSpectrum (𝓞 K), (l : 𝓞 K) ∉ w.asIdeal → ∀ B, (CG.mk π).HasSat w B → FrobEig ι r w (algSat n (normV w) B) := by
  obtain ⟨HT, hwt, hC⟩ := compatT (_root_.UpperTheory.Gal.SV.rowOf' P.litN.aut.gal) K Ω l ι n (by omega) r π hL.cont hreg hpol ha
  have hw' : ∀ w : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∉ w.asIdeal ∨ Unl1 r w ∨ PotUnl r w := fun w =>
    (em _).elim (fun e => Or.inr (hU w e)) Or.inl
  refine ⟨fun φ => ?_, ?_, fun w hw B hB => ?_⟩
  · let τ : K →+* Qbar l := ι.symm.toRingHom.comp φ
    have hφ : ι.toRingHom.comp τ = φ := RingHom.ext fun x => ι.apply_symm_apply _
    obtain ⟨w, hw, hτ⟩ := GlobalTheory.GalFirstClause.existsIsInduced l K Ω τ
    obtain ⟨A, hA, κ, hκ⟩ := hL.above w hw
    obtain ⟨O, _, _, _, Bw, hj⟩ := exists_bridge (l := l) hA hw
    obtain ⟨τ', hτ'⟩ := hτ A hA O Bw hj
    obtain ⟨⟨σ, hσ⟩, -⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P K n π w
    obtain ⟨rc, hrc⟩ := P.exists_reciprocity_dense hA
    have g := guard_of plainRec hreg ha hW (hw' w) (_root_.UpperTheory.V.Z.Desc.W.isRecT_of_isRecT P hrc) hσ
    have hJ := _root_.UpperTheory.V.Af.jumps_above_of_printed_results P K Ω l hl n M hM m r hL.cont w A hA O Bw hj κ hκ τ _
      (((hC w σ hσ).2 g.1 A hA O Bw hj).2 τ _ τ' hτ')
    have hw := hwt τ
    rw [hJ, hφ] at hw
    have hinf : (CG.mk π).infChar φ = infOf m := by
      have h := congrArg (Multiset.map fun z : ℂ => ((n : ℂ) - 1) / 2 - z) hw
      simp only [Multiset.map_map, Function.comp_def, sub_sub_cancel, Multiset.map_id'] at h
      rw [← h, infOf]
      exact Multiset.map_congr rfl fun i _ => by push_cast; ring
    rw [← hinf]
    exact ParLaws.hasInfChar_infChar (CG.mk π) φ
  · refine _root_.UpperTheory.V.Af.globFixed_alt P K n M hM _ π.finPart π.isSmooth_finPart fun w => ?_
    obtain ⟨⟨σ, hσ⟩, hi⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P K n π w
    refine ⟨σ, hi σ hσ, ?_⟩
    by_cases hw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal
    · obtain ⟨A, hA, κ, hκ⟩ := hL.above w hw
      obtain ⟨O, _, _, _, Bw, hj⟩ := exists_bridge (l := l) hA hw
      obtain ⟨rc, hrc⟩ := P.exists_reciprocity_dense hA
      have g := guard_of plainRec hreg ha hW (hw' w) (_root_.UpperTheory.V.Z.Desc.W.isRecT_of_isRecT P hrc) hσ
      obtain ⟨hp, he⟩ := ((hC w σ hσ).1 A hA rc (_root_.UpperTheory.V.Z.Desc.W.isRecT_of_isRecT P hrc)).2 O Bw hj g.2
      refine _root_.UpperTheory.V.Lev.fixedSs_of_prints P K Ω l ι n M hM m r hL.cont w A hA O Bw hj κ hκ hp rc hrc σ (fun _ s => by rw [he]) ?_
      by_cases hlM : l ∣ M
      · exact Or.inl hlM
      have hM' : (M : 𝓞 K) ∉ w.asIdeal := by
        intro h
        obtain ⟨a, b, e⟩ : IsCoprime (l : 𝓞 K) (M : 𝓞 K) :=
          Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hlM)
        exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
          (e ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left a hw) (w.asIdeal.mul_mem_left b h)))
      refine Or.inr (Or.inr fun _ => ?_)
      obtain ⟨μ, m1, m2, -⟩ := flagPol K Ω l ι n M hM m r hL.cont w A hA O Bw hj κ hκ hp
      refine sphV (_root_.UpperTheory.V.Z.Win.toV' hrc) σ g.2.2 n fun s => ?_
      rw [← he, m1]
      simp only [fun i => m2 i s (UpperTheory.inertia_fixes_roots_of_unity_prime_to_residue_char K Ω w A hA M hM' s s.2), Units.val_one, C_1,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    · obtain ⟨A, hA, χ, h1, h2⟩ := hL.away w hw
      obtain ⟨rc, hrc⟩ := P.exists_reciprocity_dense hA
      have g := guard_of plainRec hreg ha hW (hw' w) (_root_.UpperTheory.V.Z.Desc.W.isRecT_of_isRecT P hrc) hσ
      exact _root_.UpperTheory.V.Z.Win.T2.local_fixed_vectors_statement P K Ω n M hM w A hA rc hrc σ
        (_root_.UpperTheory.V.Af.weil_deligne_away_of_printed_results P K Ω l ι n M hM r hL.cont w hw A hA χ h1 h2 _
          ((((hC w σ hσ).1 A hA rc (_root_.UpperTheory.V.Z.Desc.W.isRecT_of_isRecT P hrc)).1 hw).isWDOf g.2))
  · obtain ⟨⟨σ, hσ⟩, hi⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P K n π w
    exact _root_.UpperTheory.V.Z.Desc.W.satFrobT_alt P K Ω l ι n r hL.cont w hw σ B (((_root_.UpperTheory.V.Af.satake_local_of_printed_results P K n w σ).2 _ π.finPart (hi σ hσ) B).1 hB)
      fun A h rc hrc => ((hC w σ hσ).1 A h rc hrc).1 hw
theorem levelPA_alt (P : _root_.UpperTheory.V.Af.Hypotheses') : LevelPA := by
  intro K _ _ _ _ n hn m _ M hM l _ hl Ω _ _ _ ι r π hL hs hW hreg hpol ha
  have h := _root_.UpperTheory.V.Keep.levelCore_alt P K n hn m M hM l hl Ω ι r π hL (fun w hw => hs.elim (fun a => Or.inr (a.2 w hw)) fun hg => by
    obtain ⟨A, hA, κ, hκ⟩ := hL.above w hw
    have hu := unlGap K Ω l n M hM m r w hw A hA κ hκ hg
    obtain ⟨χ, -, h2, -⟩ := hκ
    exact Or.inl (A4.unlOfOne K Ω l n r w A hA κ h2 hu)) hW hreg hpol ha
  exact ⟨⟨h.1, hpol, h.2.1⟩, h.2.2⟩
section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {n : ℕ}
variable [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {r : G F Ω →* GL (Fin n) (Qbar l)}
end
theorem levelKA_alt (P : _root_.UpperTheory.V.Af.Hypotheses') : LevelKA := by
  intro K _ _ _ n hn m _ M hM l _ hl Ω _ _ _ ι r π hL hU hW hreg hd ha
  have hpol : GlobalTheory.ContraPair.PolarizedPair π (quadChar K ^ n) :=
    ⟨fun v => by rw [locInf_pow, quadChar_locInf], by
      rw [map_pow, compNorm_quadChar, one_pow]; exact (GlobalTheory.ContraPair.dualIsConjBy_one π).2 hd⟩
  have h := _root_.UpperTheory.V.Keep.levelCore_alt P K n hn m M hM l hl Ω ι r π (LevelF.of_level hL) hU hW hreg ⟨_, hpol⟩ ha
  exact ⟨⟨h.1, hd, h.2.1⟩, h.2.2⟩
end UpperTheory.V.Keep
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCoreO
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V UpperTheory.V.Th
namespace UpperTheory.V.Th.NormTraceLemmas
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
private theorem coef_isCoef (l : ℕ) [hl : Fact l.Prime] (c : HV.Coef l) : Pa.IsCoef l c.O := by
  obtain ⟨hc, hf, hlm, -, -, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  refine ⟨hc, hf, (CharP.charP_iff_prime_eq_zero hl.out).2 ?_⟩
  rw [← map_natCast (IsLocalRing.residue c.O), IsLocalRing.residue_eq_zero_iff]
  exact hlm
private theorem locP_of (P : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : _root_.UpperTheory.V.Pa.LocPAlt :=
  ⟨P.loc.bz, P.loc.geo, GlobalTheory.Published.TameLocal_of_duality P.coh.lt⟩
private theorem chi_ofRep {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (GDet.repAlg ρ (Polynomial A) _).det = _
  rw [map_sub, MonoidAlgebra.mapRingHom_single, Matrix.charpoly]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [GDet.repAlg, Matrix.charmatrix, h, Matrix.one_apply, Matrix.diagonal_apply]
private theorem map_ofRep {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A)
    (f : A →+* B) : (GDet.ofRep ρ).map f = GDet.ofRep (f.mapMatrix.toMonoidHom.comp ρ) := by
  refine GDet.ext fun C _ _ x => ?_
  letI : Algebra A C := ((algebraMap B C).comp f).toAlgebra
  change (GDet.repAlg ρ C x).det = (GDet.repAlg _ C x).det
  congr 2
private theorem unip_pow (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (n m : ℕ)
    (M : Matrix (Fin n) (Fin n) O) (hM : (M.map (residue O)).charpoly = (Polynomial.X - 1) ^ n) (i j : Fin n) :
    (M ^ l ^ (n + m) - 1) i j ∈ maximalIdeal O ^ m := by
  have hl : l.Prime := Fact.out
  haveI : Nonempty (Fin n) := ⟨i⟩
  have h0 := Matrix.aeval_self_charpoly (M.map (residue O))
  rw [hM] at h0
  simp only [map_pow, map_sub, Polynomial.aeval_X, map_one] at h0
  have h1 : (residue O).mapMatrix (M ^ l ^ n) = 1 := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.lt_pow_self hl.one_lt (n := n)).le
    have h4 := sub_pow_char_pow_of_commute l n (Commute.one_right (M.map (residue O)))
    rw [one_pow] at h4
    rw [map_pow, ← sub_eq_zero]
    refine h4.symm.trans ?_
    rw [hd, pow_add, h0, zero_mul]
  have h2 : ∀ k, (residue O).mapMatrix (M ^ l ^ (n + k)) = 1 := fun k => by
    rw [pow_add, pow_mul, map_pow, h1, one_pow]
  induction m generalizing i j with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, pow_succ l, pow_mul, ← mul_geom_sum, Matrix.mul_apply, pow_succ]
    refine Ideal.sum_mem _ fun a _ => Ideal.mul_mem_mul (ih i a) ?_
    have h3 : (residue O).mapMatrix (∑ t ∈ Finset.range l, (M ^ l ^ (n + k)) ^ t) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_pow (residue O).mapMatrix (M ^ l ^ (n + k)), h2, one_pow]
      simp
    exact (residue_eq_zero_iff _).1 (congrFun (congrFun h3 a) j)
private theorem rhoPLO (l : ℕ) [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [CharP (ResidueField O) l] (n : ℕ) (ρ : F.G₀ →* GL (Fin n) O)
    (hc : ∀ i j, AdicCont (maximalIdeal O) fun g => mat ρ g i j) (H : OpenNormalSubgroup F.Γ)
    (hH : ∀ g ∈ H, ∃ h : F.η g = 1, ((mat ρ ⟨g, h⟩).map (residue O)).charpoly = (Polynomial.X - 1) ^ n)
    (g : F.G₀) (hg : (g : F.Γ) ∈ PL l H.toSubgroup) : ρ g = 1 := by
  have key : ∀ (m : ℕ) (i j : Fin n), (mat ρ g - 1) i j ∈ maximalIdeal O ^ m := by
    intro m
    let π := Ideal.Quotient.mk (maximalIdeal O ^ m)
    let Km : Subgroup F.G₀ := (π.mapMatrix.toMonoidHom.comp (mat ρ)).toHomUnits.ker
    have hKm : ∀ a : F.G₀, a ∈ Km ↔ ∀ i j, π (mat ρ a i j) = π ((1 : Matrix (Fin n) (Fin n) O) i j) := by
      intro a
      rw [MonoidHom.mem_ker, Units.ext_iff, MonoidHom.coe_toHomUnits, Units.val_one, ← map_one π.mapMatrix,
        ← Matrix.ext_iff]
      rfl
    have hKm' : ∀ a : F.G₀, a ∈ Km ↔ ∀ i j, (mat ρ a - 1) i j ∈ maximalIdeal O ^ m := by
      intro a
      simp only [hKm, Matrix.sub_apply, π, Ideal.Quotient.eq]
    have ho : IsOpen (Km : Set F.G₀) := by
      have : (Km : Set F.G₀) = ⋂ i, ⋂ j, {a | π (mat ρ a i j) = π ((1 : Matrix (Fin n) (Fin n) O) i j)} := by
        ext a
        simp only [SetLike.mem_coe, hKm, Set.mem_iInter, Set.mem_setOf_eq]
      rw [this]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (hc i j m).isOpen_fiber _
    let K' : Subgroup F.Γ := Km.map F.η.ker.subtype
    have ho' : IsOpen (K' : Set F.Γ) := F.η_open.isOpenMap_subtype_val _ ho
    haveI : Finite (F.Γ ⧸ K') := Subgroup.quotient_finite_of_isOpen K' ho'
    haveI : K'.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    have hc : IsOpen (K'.normalCore : Set F.Γ) :=
      Subgroup.isOpen_of_isClosed_of_finiteIndex _ (K'.normalCore_isClosed (K'.isClosed_of_isOpen ho'))
    let U : OpenNormalSubgroup F.Γ := ⟨⟨K'.normalCore, hc⟩, K'.normalCore_normal⟩
    have hU : ∀ h ∈ H.toSubgroup, ∃ e : ℕ, h ^ l ^ e ∈ U := by
      intro h hh
      refine ⟨n + m, fun b => ?_⟩
      obtain ⟨h1, h2⟩ := hH (b * h * b⁻¹) (H.isNormal'.conj_mem h hh b)
      refine ⟨(⟨b * h * b⁻¹, h1⟩ : F.G₀) ^ l ^ (n + m), ?_, ?_⟩
      · rw [SetLike.mem_coe, hKm', map_pow]
        exact unip_pow l O n m _ h2
      · simp only [Subgroup.coe_subtype, SubgroupClass.coe_pow, conj_pow]
    have h3 : (g : F.Γ) ∈ K'.normalCore := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hg U) hU
    obtain ⟨a, ha, hag⟩ := K'.normalCore_le h3
    obtain rfl : a = g := Subtype.ext hag
    exact (hKm' a).1 ha
  apply Units.ext
  ext1 i j
  have h0 : (mat ρ g - 1) i j ∈ (⨅ m : ℕ, maximalIdeal O ^ m) := Ideal.mem_iInf.2 fun m => key m i j
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal O).ne_top, Ideal.mem_bot, Matrix.sub_apply,
    sub_eq_zero] at h0
  exact h0
private theorem red_unip {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} {B : Type} [CommRing B] [Algebra O B]
    [IsCO O B] (u : Pair r B) (x : B →ₐ[O] O) (ρ : F.G₀ →* GL (Fin n) O) (h : u.D.map x.toRingHom = GDet.ofRep (mat ρ))
    (g : F.G₀) (hg : ∀ i, r.chib i g = 1) : ((mat ρ g).map (residue O)).charpoly = (Polynomial.X - 1) ^ n := by
  have e0 : (residue O).comp x.toRingHom = (res O B : B →+* ResidueField O) := RingHom.ext fun a =>
    ((res O O).commutes (x a)).symm.trans (res_map x a)
  have e3 : (GDet.ofRep (mat ρ)).map (residue O) = r.Dbar := by
    rw [← h, ← u.red, ← e0]
    rfl
  rw [map_ofRep, Resid.Dbar] at e3
  have e4 := congrArg (·.chi (MonoidAlgebra.single g 1)) e3
  simp only [chi_ofRep] at e4
  refine e4.trans ?_
  have e5 : W.diagRep r.chib g = 1 := by
    change Matrix.diagonal _ = _
    simp only [hg, Units.val_one, Matrix.diagonal_one]
  rw [e5, Matrix.charpoly_one, Fintype.card_fin]
end UpperTheory.V.Th.NormTraceLemmas
open UpperTheory.V.Th.NormTraceLemmas UpperTheory.V.Pa UpperTheory.V.W UpperTheory.V.Alg in
theorem UpperTheory.V.Th.core_o_of_literal_automorphy_n :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → _root_.UpperTheory.V.Th.OrdinaryMainCase := by
  intro hN l _ L Ω _ _ _ _ _ _ s V0 c n r B J y x h q sg al hS hn hLev hJ hAr hmap hN4 hsg hdet δ hδ h0
  have hC : Pa.CohP := ⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.gw, hN.coh.pt,
    GlobalTheory.Published.TameLocal_of_duality hN.coh.lt⟩
  haveI := coef_isCoef l c
  haveI := IsCoef.char (l := l) (O := c.O)
  haveI := IsCoef.finite (l := l) (O := c.O)
  haveI := IsCoef.complete (l := l) (O := c.O)
  obtain ⟨b, hb, hγ, hctrl⟩ := hLev
  obtain ⟨T, ⟨Pl⟩, rfl, hTs⟩ := (arPl hC l L Ω s V0 c.O n r hS).2 q sg fun j => (hsg j).1
  obtain rfl : T.sg = sg := funext hTs
  have hI := (ipEq l L Ω s V0 c.O n r).1
  have hgen : GenBy c.O (pairVals (pairOf B.u)) := fun N b => by
    obtain ⟨c, hc, hb⟩ := CA.exists_adjoin_coeff_character_sub_mem_maximalIdeal_pow r B N b
    refine ⟨c, Algebra.adjoin_mono ?_ hc, hb⟩
    rintro _ (⟨a, g, -, -, rfl⟩ | e)
    · exact Or.inl ⟨a, g, rfl⟩
    · exact Or.inr e
  have hmap' : (pairOf B.u).Maps x.toRingHom (GDet.ofRep (mat y.ρ)) y.ψ := hmap
  have hker : ∀ g : V0.frame.G₀, (g : V0.frame.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1 := by
    refine rhoPLO l (globOf r V0).frame c.O n y.ρ y.cont T.H fun g hg => ?_
    obtain ⟨e1, e2, -⟩ := (Pl.H_eq g).1 hg
    exact ⟨e1, red_unip (pairOf B.u) x y.ρ hmap'.1 ⟨g, e1⟩ e2⟩
  have heig : Eig y T al := fun j => (hsg j).2
  exact count l _ (globOf r V0) T n c.O (residOf r) B.B (pairOf B.u) J _ b y x al s.odd hn
    ⟨fun g hg a => ((Pl.H_eq g).1 hg).2.1 a, fun u => (hI u).2⟩
    (_root_.UpperTheory.V.Th.has_operator_statement (locP_of hN) l L Ω s V0 c.O n r B J _ b hb T Pl) hgen hmap' hJ
    (etOf l _ (globOf r V0) n c.O (residOf r) B.B (pairOf B.u) J _ b y x hn hmap' hgen (hctrl x h hAr)) hker heig
    (b1O hC l L Ω s V0 c n r T Pl y al hS (W.locCFT hN.aut.art hC l L Ω s) hn hker hN4 heig hdet)
    δ hδ fun k => h0 _ _ _ (hγ k)
end
end

