module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1890
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1925
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0729
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1973
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1984
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1985
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1978
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1691
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulShortNonneg
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IndexRangeMatrix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1995
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLbOfGeneratedSystem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0490
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1155
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1138
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1129
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0576
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2014
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedIntegerGoodCoverThetaSeriesIntegral
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.CovInt IsDedekindDomain

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovInt


set_option maxHeartbeats 1000000 in
theorem integral_smul_thLa : ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o Lb : ℝ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.CovGmin.Hyp D T j Y e o Lb a n → ∀ [StarRing (𝓞 D.host.E)] (nab : NabV Y.d.Xo₂ Y.d.c₂), IsNab Y.d.Xo₂ Y.d.c₂ nab → ∃ Na : ℕ, 0 < Na ∧ Real.log Na ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n ∧ ∀ (x0 : Fin n → LevQc (T.Q.Dw j) Y.d.l₂) (La : GenLat D.host.E n) (N : ℕ) (P : MvPolynomial (LtN (T.Q.Dw j) n) Y.d.c₂.F), La.Unimod → La.TrivAt (GlobalTheory.CovGmin.badC Y) → La.TrivAt Y.d.l₂.M → La.LevOK N Y.d.l₂.M → P ∈ harmL Y.d.c₂ La a → ∀ y : Y.V (wtZ a n), (∀ (p : TRing Y.d.c₂.F) (y' : FrPt Y.d.Xo₂ Y.d.c₂ p.R), thLaValAt Y.d.Xo₂ Y.d.c₂ nab (phiHat Y.d.c₂ (indPhi Y.d.c₂ x0)) La N P y' ((y : Rul Y.d.Xo₂ Y.d.c₂) p y')) → ∀ s : Y.d.c₂.F, Submodule.span (𝓞 Y.d.c₂.F) {s} * ∏ τ : D.host.E →+* ℂ, idealAt Y.d.c₂ La.Ln τ ^ (T.Q.Dw j).mult τ ≤ ∏ τ : D.host.E →+* ℂ, idealAt Y.d.c₂ La.La τ ^ (T.Q.Dw j).mult τ → ∀ y₁ : Y.V (wtZ a n), (y₁ : Rul Y.d.Xo₂ Y.d.c₂) = s • (y : Rul Y.d.Xo₂ Y.d.c₂) → Na • y₁ ∈ AllWt.latW Y.U (wtZ a n) := by
  obtain ⟨C, hC0, hC⟩ := _root_.GlobalTheory.CovIntNum.intZ_log_le
  refine ⟨2 * C, by positivity, ?_⟩
  intro D T j Y e o Lb a n hH _ nab hnab
  obtain ⟨hpos, hlog⟩ := hC D T j Y e o Lb a n hH
  refine ⟨intZ D (T.Q.Dw j) Y.d.l₂ n a ^ 2, pow_pos hpos 2, ?_, ?_⟩
  · rw [Nat.cast_pow, Real.log_pow]
    push_cast
    nlinarith
  · intro x0 La N P hU hTb hTM hN hP y hval s hs y₁ hy₁
    choose x0' hx0' using fun b => Submodule.Quotient.mk_surjective _ (x0 b)
    have hx : x0 = fun b => (Submodule.Quotient.mk (x0' b) : LevQc (T.Q.Dw j) Y.d.l₂) := funext fun b => (hx0' b).symm
    subst hx
    rw [GlobalTheory.RawSpan.phiHat_indPhi_mk] at hval
    have hsec : (y : Rul Y.d.Xo₂ Y.d.c₂) ∈ sec Y.d.Xo₂ Y.d.c₂ a n := by
      have := GlobalTheory.AllWt.cuspW_le_secZ (U := Y.U) (wtZ a n) y.2
      rwa [GlobalTheory.AllWt.exZ_wtZ, GlobalTheory.AllWt.secZ_nat] at this
    have hR := GlobalTheory.RawSpan.isShortRule_of_raw nab hnab hU hTM hN hP x0' _ hsec hval
    obtain ⟨-, hp1, -, hfr, -, -, -, -, -, -, -, -, -, hn8, -, -⟩ := hH
    have hM0 : Y.d.l₂.M ≠ 0 := by
      intro h0
      have hc := GlobalTheory.PlaceInt.card_fun_levQ _ _ (T.Q.Dw j) Y.d.l₂ n
      have hex : Module.finrank ℚ D.host.E / 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) * n ≠ 0 := by
        refine mul_ne_zero (mul_ne_zero (by omega) (by omega)) (by omega)
      rw [h0, zero_pow hex] at hc
      have : intZ D (T.Q.Dw j) Y.d.l₂ n a = 0 := by unfold intZ; rw [hc]; simp
      omega
    have hβ : betaH (Dw := T.Q.Dw j) Y.d.c₂ La ≠ 0 := GlobalTheory.RawSpan.betaH_ne_zero La
    have hg := Submodule.smul_mem _ (betaH (Dw := T.Q.Dw j) Y.d.c₂ La)⁻¹ hsec
    have hlevI := GlobalTheory.RawSpan.idCover_isLev nab n
    obtain ⟨Z, hZ⟩ : ∃ Z, Z = intZ D (T.Q.Dw j) Y.d.l₂ n a := ⟨_, rfl⟩
    rw [← hZ]
    refine GlobalTheory.AllWt.mem_supLat.2 ?_
    intro la v hv
    rw [Submodule.coe_smul_of_tower, ← Nat.cast_smul_eq_nsmul Y.d.c₂.F, hy₁]
    have hV := isVal_valSet la v hv
    have hZ0 : Z ≠ 0 := by rw [hZ]; exact hpos.ne'
    by_cases hb : ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 Y.d.c₂.F) ∈ la.asIdeal ∧ ℓ ∣ Y.d.l₂.M
    · obtain ⟨ℓ₀, hℓ₀, hm₀, hd₀⟩ := hb
      have hsI := _root_.GlobalTheory.LatticeIndex.intersected_trivAt_integral D.host.E _ (T.Q.Dw j) _ Y.d.c₂ n La ℓ₀ hℓ₀ (GlobalTheory.IntCuspLat.trivAt_of_dvd hTM hd₀) la hm₀ s hs
      rw [smul_comm]
      refine GlobalTheory.IdemInt.nonneg_smul hV hsI ?_
      have hyZ : ((Z ^ 2 : ℕ) : Y.d.c₂.F) • (y : Rul Y.d.Xo₂ Y.d.c₂) =
          ((Z : Y.d.c₂.F)) • ((betaH (Dw := T.Q.Dw j) Y.d.c₂ La * (Z : Y.d.c₂.F)) •
            ((betaH (Dw := T.Q.Dw j) Y.d.c₂ La)⁻¹ • (y : Rul Y.d.Xo₂ Y.d.c₂))) := by
        rw [smul_smul, smul_smul]
        congr 1
        field_simp
        push_cast
        ring
      have hyZ2 : ((Z ^ 2 : ℕ) : Y.d.c₂.F) • (y : Rul Y.d.Xo₂ Y.d.c₂) =
          (betaH (Dw := T.Q.Dw j) Y.d.c₂ La * ((Z ^ 2 : ℕ) : Y.d.c₂.F)) •
          ((betaH (Dw := T.Q.Dw j) Y.d.c₂ La)⁻¹ • (y : Rul Y.d.Xo₂ Y.d.c₂)) := by
        rw [smul_smul]
        congr 1
        field_simp
      by_cases h : ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 Y.d.c₂.F) ∈ la.asIdeal ∧ ℓ ^ 2 ∣ Y.d.l₂.M
      · obtain ⟨ℓ, hℓ, hm, hsq⟩ := h
        have htr : La.TrivAt ℓ := GlobalTheory.IntCuspLat.trivAt_of_dvd hTM
          (dvd_trans (dvd_pow_self ℓ two_ne_zero) hsq)
        rw [hyZ2, hZ]
        exact GlobalTheory.CovInt.SqLev.smul_intZ_sq_nonneg_of_sq_dvd D _ _ _ _ _ n (GlobalTheory.RawSpan.idCover nab n) hlevI hnab (fun k _ _ y₂ => GlobalTheory.RawSpan.evR_one_field k y₂)
          (fun x0 q => by rw [GlobalTheory.LevelCoverDatum.noDelta_w]; exact isIntegral_fourierCoeff_classIndicator_levelPoint _ hM0 x0 q) hM0 La N hU hTM hN a P hP x0' _ hg hR
          la ℓ hℓ hm hsq htr v hv
      · push_neg at h
        rw [hyZ, hV.smul _ _ (by exact_mod_cast hZ0)]
        have h1 := vAdd_int_nonneg la (a := (Z : 𝓞 Y.d.c₂.F)) (by exact_mod_cast hZ0)
        refine add_nonneg (by exact_mod_cast h1) ?_
        rw [hZ]
        exact GlobalTheory.CovInt.smul_intZ_nonneg_away D _ _ _ _ _ n (GlobalTheory.RawSpan.idCover nab n) hlevI hnab (fun k _ _ y₂ => GlobalTheory.RawSpan.evR_one_field k y₂)
          (fun x0 q => by rw [GlobalTheory.LevelCoverDatum.noDelta_w]; exact isIntegral_fourierCoeff_classIndicator_levelPoint _ hM0 x0 q) hM0 La N hU hTM hN a P hP x0' _ hg hR
          la h v hv
    · push_neg at hb
      have hyZ : ((Z ^ 2 : ℕ) : Y.d.c₂.F) • (s • (y : Rul Y.d.Xo₂ Y.d.c₂)) =
          ((Z : Y.d.c₂.F)) • ((s * betaH (Dw := T.Q.Dw j) Y.d.c₂ La * (Z : Y.d.c₂.F)) •
            ((betaH (Dw := T.Q.Dw j) Y.d.c₂ La)⁻¹ • (y : Rul Y.d.Xo₂ Y.d.c₂))) := by
        rw [smul_smul, smul_smul, smul_smul]
        congr 1
        field_simp
        push_cast
        ring
      rw [hyZ, hV.smul _ _ (by exact_mod_cast hZ0)]
      have h1 := vAdd_int_nonneg la (a := (Z : 𝓞 Y.d.c₂.F)) (by exact_mod_cast hZ0)
      refine add_nonneg (by exact_mod_cast h1) ?_
      rw [hZ]
      exact GlobalTheory.T.clearingInteger_shortSeries_integral_coprimeLevel D _ _ _ _ _ n (GlobalTheory.RawSpan.idCover nab n) hlevI hnab (fun k _ _ y₂ => GlobalTheory.RawSpan.evR_one_field k y₂)
        (fun x0 q => by rw [GlobalTheory.LevelCoverDatum.noDelta_w]; exact isIntegral_fourierCoeff_classIndicator_levelPoint _ hM0 x0 q) hM0 La N hU hTM hN a P hP x0' _ hg hR
        la hb s hs v hv

end GlobalTheory.CovInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierSectionLocusOfAmpleSpan
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.Desc

theorem unitAt_of_mul_right {X : Scheme.{0}} [IsIntegral X] {x : X} {a b : X.functionField}
    (ha : RegAt x a) (hb : RegAt x b) (h : UnitAt x (a * b)) : UnitAt x b := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  obtain ⟨w, hw, e⟩ := h
  rw [← map_mul] at e
  obtain rfl := IsFractionRing.injective (X.presheaf.stalk x) X.functionField e
  exact ⟨b', isUnit_of_mul_isUnit_right hw, rfl⟩

theorem regAt_cst {R : Type} [CommRing R] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp R) (x : X) (r : R) :
    RegAt x (cst p r) :=
  regAt_fnOf (x := x) (U := ⊤) trivial trivial _

theorem exists_locus_of_span : ∀ (R₁ F : Type) [CommRing R₁] [Field F] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp R₁) (θ : F →+* Y.functionField) (N : ℕ → Set F) (D₁ : CartierDiv Y), AmpleDiv D₁ → (∀ k, Sec D₁ k = spanBy (GlobalTheory.Desc.cst q) (θ '' N k)) → ∀ y : Y, ∃ k, 1 ≤ k ∧ ∃ b ∈ N k, y ∈ locus D₁ k (θ b) := by
  intro R₁ F _ _ Y _ q θ N D₁ hA hS y
  obtain ⟨k, hk, u, hu, U, -, hU, hy⟩ := hA y
  have hyu : y ∈ locus D₁ k u := hU ▸ hy
  have hu' : u ∈ spanBy (cst q) (θ '' N k) := hS k ▸ hu
  obtain ⟨n, r, t, ht, rfl⟩ := hu'
  obtain ⟨g, hg⟩ := (k • D₁).exists_isEqn y
  have hunit : UnitAt y ((∑ i, cst q (r i) * t i) * g) := hg.generatesAt_iff.1 hyu
  have hsec : ∀ i, RegAt y (t i * g) := fun i => by
    have : t i ∈ Sec D₁ k := by rw [hS k]; exact subset_spanBy _ _ (ht i)
    exact hg.regularAt_iff.1 (this y)
  by_contra hne
  push_neg at hne
  apply (zeroAt_iff.1 ?_).2 hunit
  rw [Finset.sum_mul]
  refine Finset.sum_induction _ (ZeroAt y) (fun _ _ => ZeroAt.add) (zeroAt_zero y) fun i _ => ?_
  rw [_root_.mul_assoc]
  refine zeroAt_iff.2 ⟨(regAt_cst q y (r i)).mul (hsec i), fun hu => ?_⟩
  obtain ⟨b, hb, hbt⟩ := ht i
  apply hne k hk b hb
  show (k • D₁).GeneratesAt y (θ b)
  rw [hg.generatesAt_iff, hbt]
  exact unitAt_of_mul_right (regAt_cst q y (r i)) (hsec i) hu

end GlobalTheory.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechPicardGlueFiniteDisjointCoverStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cechPicard_glue_finite_disjoint_cover : ∀ {Y : Scheme.{0}} {κ : Type} [Finite κ] {Z : κ → Scheme.{0}} (f : ∀ i, Z i ⟶ Y) [∀ i, IsOpenImmersion (f i)], (⨆ i, (f i).opensRange = ⊤) → (Pairwise fun i i' => Disjoint (f i).opensRange (f i').opensRange) → ∀ c : ∀ i, Pic (Z i), ∃ d : Pic Y, ∀ i, GlobalTheory.CechPic.pull (f i) d = c i := by
  first | exact @GlobalTheory.CechPic.Glue.exists_pic_glue | exact GlobalTheory.CechPic.Glue.exists_pic_glue | (intros; apply GlobalTheory.CechPic.Glue.exists_pic_glue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartCocycleOfPullbackPowerStandard
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem GlobalTheory.FormalAlg.exists_chart_cocycle_of_pull : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (H₀ : LB (Y 0).left) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → ((∀ i, C.D 0 i = nonzeroLocus (s₀ i)) ∧ ∀ i j (m : H₀.ι), rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ j).f m) = rs (Y 0).left (inf_le_left : C.D 0 i ⊓ H₀.U m ≤ C.D 0 i) (C.ρ 0 i j) * rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ i).f m)) → ∀ γ : ∀ e, (Y 0).left ⟶ (Y e).left, γ 0 = 𝟙 _ → (∀ e, γ e ≫ β e = γ (e + 1)) → ∀ (e k : ℕ) (L : LB (Y e).left), L.IsLB → LBIso (L.pull (γ e)) (GlobalTheory.AbLaw.pw H₀ k) → ∃ g : ∀ i j, Γ((Y e).left, C.D e i ⊓ C.D e j)ˣ, (⟨Fin (n + 1), C.D e, g⟩ : LB (Y e).left).IsLB ∧ LBIso L ⟨Fin (n + 1), C.D e, g⟩ ∧ ∀ i j, (g i j).val - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k ∈ towerIdeal Y e I (C.D e i ⊓ C.D e j) := by
  rintro R _ I Y β hβ n C H₀ s₀ hH₀ ⟨hD, hρs⟩ γ hγ0 hγs e k L hL ⟨w, hw⟩
  have hpb : IsPullback (γ e) (Y 0).hom ((Y e).hom ≫ thick R I e) (thick R I 0) :=
    (_root_.GlobalTheory.FormalAlg.towerSquares R I Y β hβ).2 γ hγ0 hγs e
  have hsurj : ∀ e, Surjective (γ e) := by
    intro e
    induction e with
    | zero => rw [hγ0]; infer_instance
    | succ e ih =>
      rw [← hγs e]
      have := MorphismProperty.of_isPullback (P := @Surjective) (hβ e).flip (GlobalTheory.GenSystem.surjective_thickTrans R I e)
      infer_instance
  have hpre := fun i => _root_.GlobalTheory.FormalAlg.Charts.tower_preimage_germ R I Y β n C γ hγ0 hγs e i
  have hu := fun i => _root_.GlobalTheory.Div.FramePull.frame_pull _ _ (γ e) H₀ (s₀ i) k L hL hH₀ w hw (C.D e i) ((hpre i).1.trans (hD i))
  choose u hu1 hu2 using hu
  have ht := fun i => _root_.GlobalTheory.FormalAlg.lift_localUnits_of_thickening R (I ^ (0 + 1)) (Y e).left (Y 0).left ((Y e).hom ≫ thick R I e) (γ e) (Y 0).hom
    hpb (hsurj e) L hL (C.D e i) (C.aff e i) (u i) (hu1 i)
  choose τ hτ1 hτ2 using ht
  obtain ⟨g, hgLB, hgIso, hg⟩ := _root_.GlobalTheory.FramesBundle.frames_bundle (Y e).left L hL n (C.D e) (C.cover e) τ hτ2
  refine ⟨g, hgLB, hgIso, fun i j => ?_⟩
  have hVaff : IsAffineOpen (C.D e i ⊓ C.D e j) := by
    have := (C.aff e i).basicOpen (C.ρ e i j)
    rwa [(_root_.GlobalTheory.FormalAlg.LiftRatios.lifted_ratios_mod R I Y β hβ n C).1 e i j] at this
  obtain ⟨-, -, hker⟩ := _root_.GlobalTheory.FormalAlg.baseChange_quotient R (I ^ (0 + 1)) (Y e).left (Y 0).left ((Y e).hom ≫ thick R I e) (γ e) (Y 0).hom hpb
  have hk := (hker _ hVaff).2

  have hτu : ∀ i m z (hz : γ e z ∈ C.D e i ⊓ L.U m), gm (γ e) z _ (τ i m) = gm (𝟙 _) z _ (u i m) := by
    intro i m z hz
    have h1 := gm_pull (𝟙 _) (γ e) z _ hz (τ i m)
    rw [Category.id_comp] at h1
    rw [← h1]
    congr 1
    exact Units.ext (hτ1 i m)
  have hmem : (g i j).val - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k ∈
      RingHom.ker ((γ e).app (C.D e i ⊓ C.D e j)).hom := by
    rw [RingHom.mem_ker]
    apply fn_ext
    intro z hz
    have hz' : γ e z ∈ C.D e i ⊓ C.D e j := hz
    obtain ⟨m, hm⟩ := exists_chart hL (γ e z)
    obtain ⟨a, ha⟩ := exists_chart hH₀ z
    have hzi : z ∈ C.D 0 i := (hpre i).1 ▸ hz'.1
    have hzj : z ∈ C.D 0 j := (hpre j).1 ▸ hz'.2
    have hm3 : γ e z ∈ C.D e i ⊓ C.D e j ⊓ L.U m := ⟨hz', hm⟩

    have hgz : gs (γ e) z _ (g i j).val = (gm (𝟙 _) z _ (u j m)).val * ((gm (𝟙 _) z _ (u i m))⁻¹).val := by
      rw [gs_unit _ z _ hz', ← gm_res (γ e) z (inf_le_left : C.D e i ⊓ C.D e j ⊓ L.U m ≤ C.D e i ⊓ C.D e j) hm3,
        hg i j m, map_mul, map_inv, gm_res _ z _ hm3, gm_res _ z _ hm3, hτu j m z ⟨hz'.2, hm⟩,
        hτu i m z ⟨hz'.1, hm⟩, Units.val_mul]

    have hsj := hu2 j z m a ⟨hz'.2, hm⟩ ha
    have hsi := hu2 i z m a ⟨hz'.1, hm⟩ ha
    have hrel : gs (𝟙 _) z _ ((s₀ j).f a) = gs (𝟙 _) z _ (C.ρ 0 i j) * gs (𝟙 _) z _ ((s₀ i).f a) := by
      have h := congrArg (gs (𝟙 _) z (C.D 0 i ⊓ H₀.U a)) (hρs i j a)
      have hmz : (𝟙 (Y 0).left) z ∈ C.D 0 i ⊓ H₀.U a := ⟨hzi, ha⟩
      rwa [gs_mul _ z _ hmz, gs_res _ z _ hmz, gs_res _ z _ hmz, gs_res _ z _ hmz] at h
    have hρz : gs (γ e) z _ (rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k) =
        gs (𝟙 _) z _ (C.ρ 0 i j) ^ k := by
      rw [gs_eq _ z _ hz', map_pow, map_pow, ← gs_eq _ z _ hz', gs_res _ z _ hz', (hpre i).2 j z hzi]
    have hu' : (gm (𝟙 _) z _ (u j m)).val = gs (𝟙 _) z _ (C.ρ 0 i j) ^ k * (gm (𝟙 _) z _ (u i m)).val := by
      have hW := (gm (𝟙 (Y 0).left) z _ (w.s (a, fun _ => m))).isUnit
      apply hW.mul_left_cancel
      rw [mul_comm _ (gm (𝟙 _) z _ (u j m)).val, ← hsj, hrel, mul_pow, hsi]
      ring
    have hsub := gs_pull (𝟙 _) (γ e) z (C.D e i ⊓ C.D e j) hz' ((g i j).val - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k)
    rw [Category.id_comp] at hsub
    have h0 : gs (𝟙 _) z (γ e ⁻¹ᵁ (C.D e i ⊓ C.D e j)) 0 = 0 := by rw [gs_eq _ z _ hz, map_zero, map_zero]
    rw [h0, hsub, gs_eq _ z _ hz', map_sub, map_sub, ← gs_eq _ z _ hz', ← gs_eq _ z _ hz', hgz, hρz, hu']
    rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one, sub_self]
  rw [hk] at hmem
  simpa only [towerIdeal, zero_add, pow_one] using hmem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartFiniteEtaleCoverGenericPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

noncomputable section
namespace GlobalTheory.Poinc.Chart

theorem stalkMap_finite_of_chart (K A : Type) [Field K] [CommRing A] {X Y : Scheme.{0}} (q : Y ⟶ X) (j : Sp A ⟶ Y)
    (φ : A →+* K) [IsFinite q] [IsOpenImmersion j] (hφ : ∀ z : K, ∃ a c : A, z = φ a / φ c) (g : Sp K ⟶ X)
    (hg : g = spMap φ ≫ j ≫ q) : (g.stalkMap (genericPoint (Sp K))).hom.Finite := by
  rw [← Category.assoc] at hg
  subst hg
  have hpt : genericPoint (Sp K) = closedPoint (CommRingCat.of K) := Subsingleton.elim _ _
  rw [hpt]
  have h1 : ((spMap φ ≫ j) ≫ q).stalkMap (closedPoint (CommRingCat.of K)) =
      Scheme.stalkClosedPointTo ((spMap φ ≫ j) ≫ q) ≫ (stalkClosedPointIso (CommRingCat.of K)).inv :=
    (Iso.eq_comp_inv _).2 rfl
  rw [h1]
  refine RingHom.Finite.comp (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (CommRingCat.of K)).inv).2) ?_
  rw [Scheme.stalkClosedPointTo_comp]
  set τ := Scheme.stalkClosedPointTo (spMap φ ≫ j) with hτdef
  have h2 : q.stalkMap _ ≫ τ = (X.residue _ ≫ q.residueFieldMap _) ≫ Y.descResidueField τ := by
    rw [Scheme.residue_residueFieldMap, Category.assoc, Scheme.residue_descResidueField]
  have hτ : ∀ a : A, ∃ s, τ.hom s = φ a := by
    intro a
    have h3 : τ = j.stalkMap _ ≫ Scheme.stalkClosedPointTo (spMap φ) := Scheme.stalkClosedPointTo_comp _ _
    have h5 : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (Spec (CommRingCat.of A)).presheaf.germ ⊤ ((spMap φ) (closedPoint (CommRingCat.of K))) trivial ≫
        inv (j.stalkMap ((spMap φ) (closedPoint (CommRingCat.of K)))) ≫
        j.stalkMap ((spMap φ) (closedPoint (CommRingCat.of K))) ≫ Scheme.stalkClosedPointTo (spMap φ) =
        CommRingCat.ofHom φ := by
      rw [IsIso.inv_hom_id_assoc, Scheme.germ_stalkClosedPointTo_Spec, Iso.inv_hom_id_assoc]
    refine ⟨((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (Spec (CommRingCat.of A)).presheaf.germ ⊤ ((spMap φ) (closedPoint (CommRingCat.of K))) trivial ≫
        inv (j.stalkMap ((spMap φ) (closedPoint (CommRingCat.of K))))).hom a, ?_⟩
    rw [h3]
    exact congrArg (fun m => m.hom a) h5
  have hsurj : Function.Surjective (Y.descResidueField τ).hom := by
    intro z
    obtain ⟨a, c, rfl⟩ := hφ z
    obtain ⟨s, hs⟩ := hτ a
    obtain ⟨t, ht⟩ := hτ c
    refine ⟨Y.residue _ s / Y.residue _ t, ?_⟩
    rw [map_div₀, ← hs, ← ht]
    rfl
  rw [h2]
  exact (RingHom.Finite.of_surjective _ hsurj).comp ((GlobalTheory.residueFieldMap_finite_of_locallyQuasiFinite q _).comp
    (RingHom.Finite.of_surjective _ (Scheme.residue_surjective X _)))

theorem exists_chart : ∀ (n N : ℕ) (X Y : Scheme.{0}) (sX : X ⟶ Sp (cycAway n)) (sY : Y ⟶ Sp (cycAway N)) (q : Y ⟶ X), 0 < n → 0 < N → Smooth sX → Smooth sY → IsFinite q → Etale q → Surjective q → ∀ η ∈ genericPoints X, ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra (cycAway N) Ω) (_ : ArithBase (cycAway N) Ω) (R : Subalgebra (cycAway N) Ω) (y : Sp R ⟶ Y), R.FG ∧ (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) ∧ y ≫ sY = spMap (algebraMap (cycAway N) R) ∧ (∀ w, (spMap R.val.toRingHom ≫ y ≫ q) w = η) ∧ ((spMap R.val.toRingHom ≫ y ≫ q).stalkMap (genericPoint (Sp Ω))).hom.Finite := by
  intro n N X Y sX sY q hn hN hsX hsY hq he hs η hη
  obtain ⟨η', hη', rfl⟩ := GlobalTheory.QuotTriple.genericPoints_subset_image (π := q) hη
  have hgen : (sY η').asIdeal = ⊥ := by
    let b : Sp (cycAway N) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (cycAway N))
    have hb : b ⤳ sY η' := (PrimeSpectrum.le_iff_specializes _ _).1 (show (⊥ : Ideal _) ≤ _ from bot_le)
    obtain ⟨z', hz', e⟩ := Flat.generalizingMap sY hb
    have h1 : closure {η'} ⊆ closure ({z'} : Set Y) := hz'.closure_subset
    have h2 : closure ({z'} : Set Y) ⊆ closure {η'} := hη'.2 isIrreducible_singleton.closure h1
    have h3 : η' ⤳ z' := specializes_iff_closure_subset.2 h2
    have : z' = η' := (hz'.antisymm h3).eq
    rw [← this, e]
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ η') isOpen_univ
  replace hU : IsAffineOpen U := hU
  haveI : LocallyOfFiniteType sY := inferInstance
  let P : PrimeSpectrum Γ(Y, U) := hU.primeIdealOf ⟨η', hηU⟩
  have hP : hU.fromSpec P = η' := hU.fromSpec_primeIdealOf _
  let ψ : cycAway N →+* Γ(Y, U) := (Spec.preimage (hU.fromSpec ≫ sY)).hom
  have hψ : spMap ψ = hU.fromSpec ≫ sY := Spec.map_preimage _
  have hft : ψ.FiniteType := by
    have : LocallyOfFiniteType (spMap ψ) := by rw [hψ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have hker : Ideal.comap ψ P.asIdeal = ⊥ := by
    have h1 : spMap ψ P = sY (hU.fromSpec P) := by rw [hψ]; rfl
    change (spMap ψ P).asIdeal = ⊥
    rw [h1, hP]; exact hgen
  letI : Algebra (cycAway N) Γ(Y, U) := ψ.toAlgebra
  let Ω := FractionRing (Γ(Y, U) ⧸ P.asIdeal)
  let φ : Γ(Y, U) →+* Ω := (algebraMap (Γ(Y, U) ⧸ P.asIdeal) Ω).comp (Ideal.Quotient.mk P.asIdeal)
  have hφker : ∀ a, φ a = 0 ↔ a ∈ P.asIdeal := fun a => by
    simp only [φ, RingHom.comp_apply]
    rw [(IsFractionRing.injective (Γ(Y, U) ⧸ P.asIdeal) Ω).eq_iff' (map_zero _), Ideal.Quotient.eq_zero_iff_mem]
  letI : Algebra (cycAway N) Ω := (φ.comp ψ).toAlgebra
  let f : Γ(Y, U) →ₐ[cycAway N] Ω := { φ with commutes' := fun _ => rfl }
  have hinj : Function.Injective (algebraMap (cycAway N) Ω) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have : x ∈ Ideal.comap ψ P.asIdeal := (hφker (ψ x)).1 hx
    rwa [hker, Ideal.mem_bot] at this
  haveI : CharZero Ω := charZero_of_injective_algebraMap hinj
  haveI : ArithBase (cycAway N) Ω := ⟨GlobalTheory.CycAwayReg.isDedekindDomain_cycAway N, finiteType_cycAway N, inferInstance, hinj⟩
  refine ⟨Ω, inferInstance, inferInstance, inferInstance, f.range, spMap f.rangeRestrict.toRingHom ≫ hU.fromSpec,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Algebra.map_top]
    haveI : Algebra.FiniteType (cycAway N) Γ(Y, U) := hft
    exact Algebra.FiniteType.out.map f
  · intro z
    obtain ⟨x, s, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Y, U) ⧸ P.asIdeal) z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective s
    exact ⟨f a, ⟨a, rfl⟩, f c, ⟨c, rfl⟩, rfl⟩
  · rw [Category.assoc, ← hψ, ← Spec.map_comp]
    rfl
  · intro w
    have hw : spMap f.rangeRestrict.toRingHom (spMap f.range.val.toRingHom w) = P := by
      refine PrimeSpectrum.ext ?_
      change Ideal.comap (f.rangeRestrict.toRingHom) (Ideal.comap f.range.val.toRingHom w.asIdeal) = P.asIdeal
      rw [@Ideal.eq_bot_of_prime _ _ w.asIdeal (PrimeSpectrum.isPrime (show PrimeSpectrum Ω from w))]
      ext a
      simp only [Ideal.mem_comap, Ideal.mem_bot]
      exact hφker a
    show q (hU.fromSpec (spMap f.rangeRestrict.toRingHom (spMap f.range.val.toRingHom w))) = q η'
    rw [hw, hP]
  · have e : spMap f.range.val.toRingHom ≫ spMap f.rangeRestrict.toRingHom =
        spMap (f.range.val.toRingHom.comp f.rangeRestrict.toRingHom) := (Spec.map_comp _ _).symm
    refine stalkMap_finite_of_chart Ω Γ(Y, U) q hU.fromSpec (f.range.val.toRingHom.comp f.rangeRestrict.toRingHom)
      (fun z => ?_) _ (by rw [← e]; simp only [Category.assoc])
    obtain ⟨x, s, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Y, U) ⧸ P.asIdeal) z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective s
    exact ⟨a, c, rfl⟩

end GlobalTheory.Poinc.Chart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalPointCentredClosedPointArithmetic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem flat_and_lft_toInt {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [h : ArithBase o Ω] (M : RatModel o Ω) :
    Flat (M.s ≫ spMap (algebraMap ℤ o)) ∧ LocallyOfFiniteType (M.s ≫ spMap (algebraMap ℤ o)) := by
  have := h.ded
  have hΩ := h.char
  have : CharZero o := ⟨fun a b hab => by
    have := congrArg (algebraMap o Ω) hab
    simpa using this⟩
  have hft := h.ft
  have := M.lft
  have : Flat M.s := GlobalTheory.ModelOfOutput.flat_ratModel M
  have : Flat (spMap (algebraMap ℤ o)) :=
    Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : LocallyOfFiniteType (spMap (algebraMap ℤ o)) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 hft
  exact ⟨inferInstance, inferInstance⟩

theorem exists_cen (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω) (x : M.Z)
    (hx : IsClosed ({x} : Set M.Z)) (U : M.Z.Opens) (hU : (U : Set M.Z).Nonempty) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U x y := by
  obtain ⟨h1, h2⟩ := flat_and_lft_toInt M
  exact GlobalTheory.padicAlgCl_integral_points.1 M.Z (M.s ≫ spMap (algebraMap ℤ o)) x hx U hU

theorem exists_cen_main : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω) (x : M.Z),
    IsClosed ({x} : Set M.Z) → ∀ U : M.Z.Opens, (U : Set M.Z).Nonempty →
      ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U x y :=
  fun o Ω _ _ _ _ M x hx U hU => exists_cen o Ω M x hx U hU

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeAwayOfAtPrimeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteType_away_of_finiteType_atPrime : ∀ (R C : Type) [CommRing R] [IsNoetherianRing R] [CommRing C] [IsDomain C] [Algebra R C] (f : R) (𝔭 : Ideal R) [𝔭.IsPrime], algebraMap R C f ≠ 0 → Algebra.FiniteType R (Localization.Away (algebraMap R C f)) → Algebra.FiniteType (Localization.AtPrime 𝔭) (TensorProduct R (Localization.AtPrime 𝔭) C) → ∃ g : R, g ∉ 𝔭 ∧ Algebra.FiniteType R (Localization.Away (algebraMap R C g)) := by
  first | exact @GlobalTheory.Desc.exists_finiteType_away_of_atPrime | exact GlobalTheory.Desc.exists_finiteType_away_of_atPrime | (intros; apply GlobalTheory.Desc.exists_finiteType_away_of_atPrime <;> assumption)
end

