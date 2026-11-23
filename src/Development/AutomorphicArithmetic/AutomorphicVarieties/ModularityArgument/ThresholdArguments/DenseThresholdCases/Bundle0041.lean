module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0028
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0034
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0027
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.GaloisRepExistsTotallyRealGL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0040
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.SubquotientSupport.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.ExtraV
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0039
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.MemOfProdEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0054
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0059
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0052
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TwistedDualFrobeniusCompatibility
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0056
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0024
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0036
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BirthSeedB
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V UpperTheory.V.Ws.Pt UpperTheory.V.Z.Win
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp Formalism.BasicNotions Formalism.MainNotions.N
namespace UpperTheory.V.Z.Win.Birth
theorem ptAutR'_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (n : ℕ) (ι : PadicAlgCl l ≃+* ℂ) (r : G T.F Ω →* M4 (PadicAlgCl l)), (∀ g, IsGSp (algebraMap c'.O (PadicAlgCl l) (inc h (D.th (resQ T.F g)))) (r g)) → ∀ (κ : G T.L Ω →* (PadicAlgCl l)ˣ) (π : CuspSub T.L 4) (a : ℤ) (k : ℕ), Continuous κ → 0 < k → Even (a + n) → (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := T.L) A, (κ s ^ 2 * cycBar T.L Ω l s ^ (-a)) ^ k = 1) → CuspidalRankFourRegularAlgebraicTotallyComplex π → Af.AttC ι (Af.tw (r.comp (resLe T.F_le)).toHomUnits κ) π → (∀ w : HeightOneSpectrum (𝓞 T.L), ((l : ℕ) : 𝓞 T.L) ∈ w.asIdeal → PotUnl (K.rhoQ n r) w) → IsAutCsdA ι (K.rhoQ n r) := by
  intro hP Ω _ _ _ l _ c D T c' h K n ι r hr κ π a k hκ hk ha hw ⟨hreg, hwin⟩ hatt hpot
  have h1 := (_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hP T.L Ω l ι 4 _).2.1.2 ⟨π, hreg, hatt⟩
  have h2 : Af.IsAlgChar ι (K.twc n * κ⁻¹) := by
    refine (_root_.UpperTheory.V.Af.algOfCyc_s hP T.L Ω l ι).1 _ ((twc_cont K n).mul hκ.inv) fun w hlw => ?_
    obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
    have hl : A.valuation (l : Ω) < 1 := by
      have h1 := (hA ((l : ℕ) : 𝓞 T.L)).2 hlw
      have e : algebraMap T.L Ω (((l : ℕ) : 𝓞 T.L) : T.L) = (l : Ω) := by simp
      rwa [e] at h1
    obtain ⟨e, k', hk', he, H⟩ := twWts K n A hl
    obtain ⟨m, hm⟩ : Even (e - a) := by
      have := he.sub ha
      rwa [add_sub_add_right_eq_sub] at this
    have half_pow {M : Type} [CommGroup M] {x y u : M} {a e m : ℤ} {k k' : ℕ}
        (hm : e - a = m + m) (hx : (x ^ 2 * u ^ (-e)) ^ k' = 1)
        (hy : (y ^ 2 * u ^ (-a)) ^ k = 1) :
        (x * y⁻¹ * u ^ (-m)) ^ (2 * (k * k')) = 1 := by
      obtain rfl : e = a + m + m := by omega
      have hsq : (x * y⁻¹ * u ^ (-m)) ^ 2 =
          (x ^ 2 * u ^ (-(a + m + m))) * (y ^ 2 * u ^ (-a))⁻¹ := by
        rw [mul_inv, mul_mul_mul_comm, mul_pow, mul_pow, inv_pow]
        congr 1
        group
      have hx' : (x ^ 2 * u ^ (-(a + m + m))) ^ (k * k') = 1 := by
        rw [mul_comm k k', pow_mul, hx, one_pow]
      have hy' : (y ^ 2 * u ^ (-a)) ^ (k * k') = 1 := by
        rw [pow_mul, hy, one_pow]
      rw [pow_mul, hsq, mul_pow, inv_pow, hx', hy', inv_one, mul_one]
    exact ⟨A, hA, m, 2 * (k * k'), by positivity, fun s hs => half_pow hm (H s hs) (hw A hl s hs)⟩
  have h3 := _root_.UpperTheory.V.Af.twist_invariance_automorphic hP T.L Ω l ι 4 _ _ h1 h2
  have h4 : Af.tw (Af.tw (r.comp (resLe T.F_le)).toHomUnits κ) (K.twc n * κ⁻¹) = K.rhoQ n r := by
    ext g : 2
    rw [Af.tw_val, Af.tw_val, smul_smul, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul,
      Units.inv_mul_cancel_right, K.rho_val]
    rfl
  rw [h4] at h3
  obtain ⟨P, hPair⟩ := ptPair K n r hr
  haveI : IsAlgClosure T.L Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  have h5 : Sd.IsAlgChar ι (K.twc n * κ⁻¹) := by
    obtain ⟨χ, hc, art, a', b1, b2, b3⟩ := h2
    exact ⟨hc, art, χ, a', b1, b2, b3⟩
  have h6 := awTw T.L Ω l 4 (by norm_num) ι _ _ h5 ⟨π, hreg, hatt⟩ (awOne T.L Ω l 4 (by norm_num) ι _ π hatt hwin)
  rw [h4] at h6
  exact ⟨_root_.UpperTheory.GalN.V.csdOf0_alt hP (W.Lp T.L) T.L Ω inferInstance l ι 4 (by norm_num) _ K.s.c P K.s.hc h3 hPair, fun _ => h6.witA hpot⟩
end UpperTheory.V.Z.Win.Birth
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BirthSphOfUnrW
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af UpperTheory.V.Z.Gam
open UpperTheory.GalN.V GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Win.Birth
private theorem exists_polarized {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {l : ℕ} [Fact l.Prime] {n : ℕ} (H : _root_.UpperTheory.V.Af.HypothesesH') {ι : Qbar l ≃+* ℂ} (hn : 1 ≤ n) {r : G K Ω →* GL (Fin n) (Qbar l)}
    {π : CuspSub K n} (hp : Sol.Pol ι r) (ha : AttC ι r π) : ∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ := by
  haveI : IsAlgClosure (maximalRealSubfield K) Ω :=
    ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.trans (maximalRealSubfield K) K Ω⟩
  obtain ⟨μ, χ, c, P, hμ, hs, hc, hP⟩ := UpperTheory.cyclotomicCharacter_plusPart (_root_.UpperTheory.V.Af.algOfCyc_s H) UpperTheory.cyclotomic_char_conj_invariant K Ω l ι n r hp
  have hdual := _root_.UpperTheory.V.Af.self_dual_complex_of_printed_hida H K Ω l ι n hn r π ha χ μ hμ c P hc hP
  have hsign := UpperTheory.sign_at_infinity_of_parallel_weight UpperTheory.adelicSolution_parallel _ Ω l ι χ μ hμ hs
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace (maximalRealSubfield K)) := inferInstance
  have hsq : ((χ.locInf v₀ (-1) : ℂˣ) : ℂ) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, neg_one_sq, map_one, Units.val_one]
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ∀ v, χ.locInf v (-1) = (-1) ^ m := by
    rcases sq_eq_one_iff.1 hsq with e | e
    · exact ⟨0, fun u => (hsign u v₀).trans (Units.ext (by simpa using e))⟩
    · exact ⟨1, fun u => (hsign u v₀).trans (Units.ext (by simpa using e))⟩
  have hnorm : compNorm K (χ * quadChar K ^ (m + n)) = compNorm K χ := by
    rw [map_mul, map_pow, compNorm_quadChar, one_pow, mul_one]
  refine ⟨χ * quadChar K ^ (m + n), fun v => ?_, hnorm ▸ hdual⟩
  change χ.locInf v (-1) * (quadChar K ^ (m + n)).locInf v (-1) = (-1) ^ n
  rw [locInf_pow, hm, quadChar_locInf, ← pow_add, ← add_assoc, pow_add, ← two_mul, pow_mul]
  simp
private theorem unram_of_charPol {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion E)ˣ}
    (ha : IsLocalArtin h a) {n : ℕ} (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ))
    (H : ∀ g : Weil h, deg g = 0 → ∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ)) = (X - 1 : ℂ[X]) ^ n) (j : Fin n)
    (x : (w.adicCompletion E)ˣ) (hx : ord (w.adicCompletion E) x = 0) : ξ j x = 1 := by
  obtain ⟨g, rfl⟩ := ha.surj x
  have h0 : deg g = 0 := by
    have := ha.ord_eq g
    rw [hx] at this
    omega
  have e := congrArg (Polynomial.eval ((ξ j (a g) : ℂˣ) : ℂ)) (H g h0)
  rw [Polynomial.eval_prod, Finset.prod_eq_zero (Finset.mem_univ j) (by simp)] at e
  have e2 : ((ξ j (a g) : ℂˣ) : ℂ) - 1 = 0 := by
    have := e.symm
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one] at this
    exact (pow_eq_zero_iff j.pos.ne').1 this
  exact Units.ext (by simpa [sub_eq_zero] using e2)
end UpperTheory.V.Z.Win.Birth
open UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Birth in
theorem UpperTheory.V.Z.Win.Birth.sphOfUnrW_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Z.Win.Birth.SphOfUnrW := by
  intro H M Ω _ _ _ _ _ _ l _ ι n hn r π hr hpol hreg hatt hW w hw A hA hu
  have hRow : RowT := _root_.UpperTheory.Gal.SV.rowOf' H.litN.aut.gal
  have hpp := exists_polarized H hn hpol hatt
  obtain ⟨HT, -, hC⟩ := compatTOf hRow plainRec M Ω l ι n hn r π hr hreg hpp hatt
  obtain ⟨t, ht⟩ := hW π hreg hatt
  refine winSph M n hn π t w (ht w) ?_
  rintro s ⟨σ, hσ, hsup⟩ ζ ⟨hζ, hmem⟩
  haveI : CharZero (w.adicCompletion M) := charZero_of_injective_algebraMap (algebraMap M _).injective
  obtain ⟨rc, hrc⟩ := UpperTheory.Zero.LLC.recTExists M Ω A w hA
  obtain ⟨hPT, hTor, hMono⟩ := plainRec M Ω A w hA rc hrc n π t (ht w) σ hσ
  have hwd : IsWDOf ι r (rc (algNorm σ)) := (((hC w σ hσ).1 A hA rc hrc).1 hw).isWDOf ⟨hTor, hMono⟩
  have hpolW : ∀ g : Weil hA, (rc (algNorm σ)).charPol g = ((r g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly).map ι.toRingHom := fun g => by
    rw [← hwd.wdOf_eq hw]
    exact charPol_wdOf hw ι (Units.continuous_val.comp hr) g
  obtain ⟨a, ha, hLaws⟩ := hrc
  obtain ⟨ξ, hξ, hsupx, -⟩ := GlobalTheory.RoadU.plainTor_exists_chars (w.adicCompletion M) (IrrGL.of σ.ρ σ.smooth σ.irred) hPT
  let c : ℂ := (((1 - (n : ℝ)) / 2 : ℝ) : ℂ)
  let ξ' : Fin n → ((w.adicCompletion M)ˣ →* ℂˣ) := fun j => ξ j * absPow _ c
  have hξ' : ∀ j, IsSmoothChar (ξ' j) := fun j => (hξ j).mul (GlobalTheory.LocGL.isSmoothChar_absPow _)
  have hsup' : HasSupport (algNorm σ).rep (GlobalTheory.RoadU.chars ξ' hξ') :=
    (GlobalTheory.RoadU.TwistSupp.supp_nu_chars (w.adicCompletion M) (IrrGL.of σ.ρ σ.smooth σ.irred) n ξ ξ' hξ hξ' c fun _ => rfl).1.1 hsupx
  obtain ⟨hG, hZ⟩ := GlobalTheory.geometricLemma_and_zelevinskyPolynomialRing
  have hse : s = GlobalTheory.RoadU.chars ξ hξ := GlobalTheory.LocGL.SupportUnique.hasSupport_unique hG GlobalTheory.Laid.bzfin_holds hZ _
    (IrrGL.of σ.ρ σ.smooth σ.irred) _ _ (hsup.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred)) hsupx
  obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 (hse ▸ hmem)
  have hζj : ξ j = ζ := IrrGL.ofChar_inj.1 hj
  have hIne : ∀ g : Weil hA, deg g = 0 → ∏ j, (X - C ((ξ' j (a g) : ℂˣ) : ℂ)) = (X - 1 : ℂ[X]) ^ n := fun g hg => by
    have hI : (g : G M Ω) ∈ Ine (F := M) A := deg_eq_zero_iff.1 hg
    rw [← charPol_of_chars hLaws _ ξ' hξ' hsup' g, hpolW, hu _ hI]
    simp [Matrix.charpoly_one]
  intro x hx
  have e := unram_of_charPol ha ξ' hIne j x (ord_eq_zero_iff.2 hx)
  have e' : ξ' j x = ξ j x := by
    simp only [ξ', MonoidHom.mul_apply, isUnram_absPow _ c x hx, mul_one]
  rw [← hζj, ← e', e]
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CharPolOfChar
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {rc : IrrGL (k := w.adicCompletion E) → WD h}
private theorem charPol_supp (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) (H : UpperTheory.Zero.LLC.LawsT a ha rc)
    (x : IrrGL (k := w.adicCompletion E)) (s : Multiset (IrrGL (k := w.adicCompletion E))) (hs : HasSupport x.rep s) (g : Weil h) :
    (rc x).charPol g = (s.map fun y => (rc y).charPol g).prod := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨𝔪, hm⟩ := GlobalTheory.langlandsExhaustionGL_holds (w.adicCompletion E) x
  have hs' : HasSupport x.rep (msupp 𝔪) := GlobalTheory.LocGL.hasSupport_msupp_of_isL hZ _ 𝔪 x hm
  have he : s = msupp 𝔪 :=
    GlobalTheory.LocGL.SupportUnique.hasSupport_unique GlobalTheory.RecT.geometricLemma_holds GlobalTheory.bernsteinZelevinskyFiniteness_holds
      hZ _ x _ _ hs hs'
  rw [he, H.langlands 𝔪.toList x (by rw [Multiset.coe_toList]; exact hm), segSum, CuspExt.charPol_sumList, List.map_map,
    msupp, Multiset.map_bind, Multiset.prod_bind]
  have hl : ∀ (l : List (Segment (w.adicCompletion E))) (F : Segment (w.adicCompletion E) → ℂ[X]),
      (l.map F).prod = ((l : Multiset _).map F).prod := fun l F => by rw [Multiset.map_coe, Multiset.prod_coe]
  rw [hl, Multiset.coe_toList]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun Δ _ => GlobalTheory.RoadU.CharSupport.charPol_seg H Δ g)
private theorem charPol_ofChar (H : UpperTheory.Zero.LLC.LawsT a ha rc) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ)
    (g : Weil h) : (rc (IrrGL.ofChar χ hχ)).charPol g = X - C (χ (a g) : ℂ) := by
  rw [H.one, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
  simp
end
theorem UpperTheory.V.Z.Sym.W.eigW_alt :
    _root_.UpperTheory.V.Z.Sym.W.EigWAlt := by
  intro P L Ω _ _ _ _ _ l _ ι n r w hl A h a ha τ hτ hP ψ hψ hsub s
  have Q := P.litN
  obtain ⟨rc, hrc⟩ := UpperTheory.Zero.LLC.recTExists L Ω A w h
  have hg : UpperTheory.V.Z.Win.Gd (rc (algNorm τ)) := UpperTheory.V.Z.Win.Gu.plainGd L Ω A w h rc hrc n τ hP
  have hx := ((hτ A h rc hrc).1 hl).isWDOf hg
  have hw := hx.wdOf_eq hl
  obtain ⟨t, ht, φ, hφ, N, b, hN, -⟩ := hx
  have hpol : (rc (algNorm τ)).charPol s =
      (r (s : G L Ω)).val.charpoly.map ι.toRingHom := by
    rw [← hw]; exact hN.charPol_wdOf hl ht ι s
  obtain ⟨a', ha', H⟩ := hrc
  obtain rfl : a' = a := by
    obtain ⟨art, hart⟩ := Q.aut.art L Ω
    have hinj := GlobalTheory.ArtinLocalInj.artin_localIdele_injective Q.loc.chev L Ω art hart w
    exact MonoidHom.ext fun σ => hinj ((ha'.glob art hart _).trans (ha.glob art hart _).symm)
  haveI : CharZero (w.adicCompletion L) := algebraRat.charZero _
  let τ' : IrrRep (GL (Fin n) (w.adicCompletion L)) := ⟨_, τ.ρ, τ.smooth, τ.irred⟩
  have h1 := (hasSupport_of_isSubquotient_prinSeries _ n _ hψ τ' hsub).of_equiv (IrrGL.equivOf τ.ρ τ.smooth τ.irred)
  have h2 := SupportRing.hasSupport_nu h1 (((1 - (n : ℝ)) / 2 : ℝ) : ℂ)
  have hc := charPol_supp Q.loc.zel H (algNorm τ) _ h2 s
  have e0 : (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) = -(((n : ℂ) - 1) / 2) := by push_cast; ring
  rw [← hpol, hc, UpperTheory.V.Z.Sym.W.psPol, Finset.prod_eq_multiset_prod]
  simp only [Multiset.map_map, Function.comp_def]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun i _ => ?_)
  have e1 : (IrrGL.ofChar (ψ i) (hψ i)).nu (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) =
      IrrGL.ofChar (ψ i * absPow (w.adicCompletion L) (((1 - (n : ℝ)) / 2 : ℝ) : ℂ))
        ((hψ i).mul (isSmoothChar_absPow _)) := IrrGL.tw_ofChar _ _ _ _
  rw [e1, charPol_ofChar H]
  simp only [e0, MonoidHom.mul_apply]
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EqOneOfDvd
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem eq_one_of_dvd {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (hf : f.IsSemisimple) {n : ℕ} (hd : f.charpoly ∣ (X - C 1) ^ n) : f = 1 := by
  obtain ⟨q, hq⟩ := hd
  have h0 := congrArg (Polynomial.aeval f) hq
  rw [map_mul, LinearMap.aeval_self_charpoly, zero_mul, map_pow, map_sub, Polynomial.aeval_X,
    Polynomial.aeval_C] at h0
  have hs : (f - algebraMap ℂ (Module.End ℂ V) 1).IsSemisimple :=
    Module.End.isSemisimple_sub_algebraMap_iff.2 hf
  have := sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨_, h0⟩ hs)
  rwa [map_one] at this
section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
private theorem link {n m : ℕ} (b : WDRep h (Fin m → ℂ)) (μ : Fin n → Weil h →* ℂˣ)
    (hp : ∀ s, (b.ρ s).charpoly = ∏ i, (X - C (μ i s : ℂ))) (hN : b.N ≠ 0) :
    ∃ i j, (μ i (frob h) : ℂ) = ((normV w : ℕ) : ℂ) * μ j (frob h) := by
  have hs := b.semisimple (frob h)
  have htop : ⨆ c, Module.End.eigenspace (b.ρ (frob h)) c = ⊤ := by
    have h1 := Module.End.iSup_maxGenEigenspace_eq_top (b.ρ (frob h))
    simpa only [hs.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] using h1
  obtain ⟨c, v, hv, hNv⟩ : ∃ c v, v ∈ Module.End.eigenspace (b.ρ (frob h)) c ∧ b.N v ≠ 0 := by
    by_contra hc
    push_neg at hc
    refine hN (LinearMap.ker_eq_top.1 (top_le_iff.1 ?_))
    rw [← htop]
    exact iSup_le fun c v hv => hc c v hv
  have hfv : b.ρ (frob h) v = c • v := Module.End.mem_eigenspace_iff.1 hv
  have hv0 : v ≠ 0 := fun e => hNv (by rw [e, map_zero])
  have root : ∀ z u, u ≠ 0 → b.ρ (frob h) u = z • u → ∃ i, z = (μ i (frob h) : ℂ) := fun z u hu e => by
    have h1 : Module.End.HasEigenvalue (b.ρ (frob h)) z :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 e, hu⟩
    have h2 := Module.End.hasEigenvalue_iff_isRoot_charpoly _ _ |>.1 h1
    rw [hp, Polynomial.IsRoot.def, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h2
    obtain ⟨i, -, hi⟩ := h2
    exact ⟨i, by simpa [sub_eq_zero] using hi⟩
  have hc2 : b.ρ (frob h) (b.N v) = (((normV w : ℕ) : ℂ) * c) • b.N v := by
    rw [b.comm_apply, deg_frob, zpow_one, hfv, map_smul, smul_smul]
  obtain ⟨j, hj⟩ := root _ _ hv0 hfv
  obtain ⟨i, hi⟩ := root _ _ hNv hc2
  exact ⟨i, j, by rw [← hi, ← hj]⟩
private theorem link_all {n : ℕ} (μ : Fin n → Weil h →* ℂˣ) (hu : ∀ i (s : Ine (F := E) A), μ i (ineIncl h s) = 1)
    {i j : Fin n} (e : (μ i (frob h) : ℂ) = ((normV w : ℕ) : ℂ) * μ j (frob h)) (s : Weil h) :
    (μ i s : ℂ) = ((normV w : ℕ) : ℂ) ^ deg s * μ j s := by
  obtain ⟨t, ht⟩ := exists_eq_zpow_mul (deg_frob (h := h)) s
  have hv : ∀ k, (μ k s : ℂ) = (μ k (frob h) : ℂ) ^ deg s := fun k => by
    conv_lhs => rw [ht]
    rw [map_mul, map_zpow, hu, mul_one, Units.val_zpow_eq_zpow_val]
  rw [hv, hv, e, mul_zpow]
end
theorem UpperTheory.V.Z.Win.T2.fixedUnr_alt :
    _root_.UpperTheory.V.Lev.fixedUnr_s_ty := by
  intro P F Ω _ _ _ _ _ n w A h rc hrc σ μ hp hu
  obtain ⟨a, ha, ε, H⟩ := _root_.UpperTheory.V.Z.Win.toV' hrc
  haveI : CharZero (w.adicCompletion F) := algebraRat.charZero _
  have hine : ∀ t : Ine (F := F) A, (rc (algNorm σ)).charPol (ineIncl h t) = (X - C 1) ^ n := fun t => by
    rw [hp]
    simp [hu]
  constructor
  · have hfx : fixed (algNorm σ).rep (iwahori (w.adicCompletion F) (Fin (algNorm σ).1)) ≠ ⊥ := by
      refine UnramSupport.fixed_iwahori_ne_bot P.litN.loc.geo P.litN.loc.zel P.litN.loc.bz _ _ _ _
        (algNorm σ).2.rep.smooth (algNorm σ).2.rep.irr fun s hs y hy => ?_
      have hyc : y.IsCusp := hs.isCusp hy
      obtain ⟨m, b, hb, hirr⟩ := id ((H.cusp y).1 hyc)
      have hN : b.N = 0 := by
        have h0 := TemperedRec.monodromy_zero_of_irreducible_weilDeligne F Ω A w h (rc y) ((H.cusp y).1 hyc)
        rwa [← hb, WD.monodromyZero_ofWeilDeligneRepClass_iff] at h0
      have hI : ∀ t : Ine (F := F) A, b.ρ (ineIncl h t) = 1 := fun t => by
        refine eq_one_of_dvd _ (b.semisimple _) (n := n) ?_
        rw [← WD.charPol_mk, hb, ← hine t, H.supp _ s hs]
        exact Multiset.dvd_prod (Multiset.mem_map_of_mem (fun y => (rc y).charPol (ineIncl h t)) hy)
      have hunr : (rc y).unr := by
        rw [← hb, WD.unr_mk]
        exact ⟨hN, hI⟩
      exact isUnramChar_of_isCusp_of_isSpherical P.litN.loc.geo P.litN.loc.bz P.litN.loc.zel _ y hyc
        ((H.sph y).2 hunr)
    have hfx' : fixed (IrrGL.of σ.ρ σ.smooth σ.irred).rep (iwahori (w.adicCompletion F) (Fin n)) ≠ ⊥ :=
      GlobalTheory.AboveL.IwaFix.fixed_iwahori_ne_bot_of_twist _
        ((IrrGL.of σ.ρ σ.smooth σ.irred).twEquiv _ (isSmoothChar_absPow _)) hfx
    exact fixed_ne_bot_of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm hfx'
  · intro hne
    obtain ⟨m, b, hb⟩ := (rc (algNorm σ)).exists_rep
    have hpb : ∀ s, (b.ρ s).charpoly = ∏ i, (X - C (μ i s : ℂ)) := fun s => by
      rw [← WD.charPol_mk, hb]
      exact hp s
    have hN : b.N = 0 := by
      by_contra h0
      obtain ⟨i, j, e⟩ := link b μ hpb h0
      obtain ⟨s, hs⟩ := hne i j
      exact hs (link_all μ hu e s)
    have hunr : (rc (algNorm σ)).unr := by
      rw [← hb, WD.unr_mk]
      refine ⟨hN, fun t => eq_one_of_dvd _ (b.semisimple _) (n := n) ?_⟩
      rw [← WD.charPol_mk, hb, hine t]
    obtain ⟨v, hv0, hv⟩ := UpperTheory.hasFixed_of_algNorm_fixed_ne_bot F w n σ _ le_rfl ((H.sph _).2 hunr)
    exact (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.Parabolic.mem_fixed.2 hv, hv0⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsRec
section
noncomputable abbrev UpperTheory.V.Af.Hypotheses'.exists_reciprocity_dense := @UpperTheory.V.Z.Win.exists_rec_alt_alt_alt
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsResidualRepQuadratic
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc UpperTheory.V.Af.Sol
namespace UpperTheory.V.Z.Bc
theorem exists_residual_rep_quadratic_alt (P : _root_.UpperTheory.V.Af.HypothesesH') : ExRTwo := fun F Ω _ _ _ _ _ _ l _ ι π χ h1 h2 =>
  let ⟨r, _, _, H, h, _⟩ := _root_.UpperTheory.Gal.SV.exRS_alt P.toClassicalTheorems F Ω l ι 2 one_le_two π χ h1 h2
  ⟨r, H.cont, h⟩
end UpperTheory.V.Z.Bc
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GalUnitaryT
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V.Af UpperTheory.V.Af.Gu
namespace UpperTheory.V.Z.Win.Gu
theorem half_alt (H : _root_.UpperTheory.V.Af.HypothesesH') (hR : RowT) : HalfG := halfG UpperTheory.twist_local_components_compatible (_root_.UpperTheory.V.Z.Win.Gu.polG_of_printsH_of_rT H hR)
theorem recTotT_of_printsH (H : _root_.UpperTheory.V.Af.HypothesesH') : RecTotT := recTotT (_root_.UpperTheory.V.Z.Win.Gu.prodT_alt H extraV) (_root_.UpperTheory.V.Z.Win.Gu.spehT_alt H extraV)
theorem galUnitaryT_of_printsH_of_bcSpeh_of_rT (H : _root_.UpperTheory.V.Af.HypothesesH') (hB : GlobalTheory.BcSpeh.BcSpeh) (hR : RowT) : GalUnitaryT :=
  _root_.UpperTheory.V.Z.Win.Gu.assemble_s H hB (sumFamG (_root_.UpperTheory.V.Z.Win.Gu.sumTwoG_of_printsH_gdLaws_sumAway_sumHTAt H gdLaws UpperTheory.galoisRep_direct_sum_away_from_places sumHTAt) UpperTheory.finiteSum_reduction) (_root_.UpperTheory.V.Z.Win.Gu.half_alt H hR) UpperTheory.speh_parameter_strings UpperTheory.building_component_uniqueness
    (_root_.UpperTheory.V.Z.Win.Gu.recTotT_of_printsH H) (_root_.UpperTheory.V.Z.Win.Gu.frobTotT_alt H extraV gdLaws) (UpperTheory.twistedDual_frobenius_compatibility (_root_.UpperTheory.V.Af.iso_of_frobenius_of_printed_results H.toClassicalTheorems)) (_root_.UpperTheory.satake_galois_link_of_printed_hida H) UpperTheory.satake_parameters_complex_conjugate
    (_root_.UpperTheory.V.Z.Win.Gu.irrCaseT_alt H) plainGd
theorem endShapeT' (H : _root_.UpperTheory.V.Af.HypothesesH') (hB : GlobalTheory.BcSpeh.BcSpeh) (hR : RowT) :
    type_of% (endShape_of hB (_root_.UpperTheory.satake_galois_link_of_printed_hida H) (_root_.UpperTheory.V.Z.Win.Gu.half_alt H hR) (_root_.UpperTheory.V.Z.Win.Gu.recTotT_of_printsH H) (_root_.UpperTheory.V.Z.Win.Gu.frobTotT_alt H extraV gdLaws) (frobTwT extraV gdLaws)) :=
  endShape_of hB (_root_.UpperTheory.satake_galois_link_of_printed_hida H) (_root_.UpperTheory.V.Z.Win.Gu.half_alt H hR) (_root_.UpperTheory.V.Z.Win.Gu.recTotT_of_printsH H) (_root_.UpperTheory.V.Z.Win.Gu.frobTotT_alt H extraV gdLaws) (frobTwT extraV gdLaws)
end UpperTheory.V.Z.Win.Gu
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LQuot
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Win.T2
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {rc : IrrGL (k := w.adicCompletion E) → WD h}
private theorem segmentV {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A}
    (H : _root_.UpperTheory.V.Z.Win.LawsV a ha ε rc)
    {Δ : Segment (w.adicCompletion E)} {x : IrrGL (k := w.adicCompletion E)}
    (hx : IsLSeg Δ x.rep) :
    rc x = ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len) :=
  (H.langlands [Δ] x hx.isL).trans (WD.lpSum_zero _)
end UpperTheory.V.Z.Win.T2
theorem UpperTheory.V.Z.Win.T2.lQuot_alt :
    _root_.GlobalTheory.LocLanglands.IsRec.langlandsQuotient_s_ty := by
  intro E Ω i₁ i₂ i₃ i₄ i₅ A w h rc hrc 𝔪 s N δ hδ hd π hπ
  have h1 : IsL 𝔪 (GlobalTheory.LocLanglands.cls π).rep := IsL.of_equiv ⟨s, δ, hd, hδ, hπ⟩ (equivRep π)
  obtain ⟨Δ, ⟨hm, -⟩, hΔ⟩ := hδ
  obtain ⟨a, ha, ε, H⟩ := _root_.UpperTheory.V.Z.Win.toV' hrc
  simp only [fun i => UpperTheory.V.Z.Win.T2.segmentV H (hΔ i)]
  rw [H.langlands (List.ofFn Δ) (GlobalTheory.LocLanglands.cls π) (by rwa [← Fin.univ_val_map, hm]), List.map_ofFn]
  rfl
end
end
end

