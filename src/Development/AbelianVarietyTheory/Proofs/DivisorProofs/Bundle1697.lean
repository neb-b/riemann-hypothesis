module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1571
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1660
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0898
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0439
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1591
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1590
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1657
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1529
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1587
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1518
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1538
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1675
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomPairsWeightsEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.BottomWeights

theorem mul_n_eq {D : D7} {N N' : ℕ} (χ : HeckeU D N) (χ' : HeckeU D N') (e e' : ℤ)
    (h : ∀ x, χ.f x ^ e = χ'.f x ^ e') (τ : D.what₂.Tau) : e * χ.n τ = e' * χ'.n τ := by
  have hc := GlobalTheory.SplitWeight.exps_eq_zero (Formalism.L2.Host.embTau D) (GlobalTheory.SplitWeight.embTau_inj D)
    (GlobalTheory.SplitWeight.embTau_ne_conj D) (fun τ => e * χ.n τ - e' * χ'.n τ) (fun a ha => by
      set u := Units.mk0 a ha
      set φ := Formalism.L2.Host.embTau D
      have hne : ∀ τ, φ τ a ≠ 0 := fun τ => by simpa using ha
      have hu : ∀ τ, φ τ a / ((‖φ τ a‖ : ℝ) : ℂ) ≠ 0 := fun τ =>
        div_ne_zero (hne τ) (by exact_mod_cast norm_ne_zero_iff.2 (hne τ))
      have hA : ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) *
          ∏ τ, (φ τ a / ((‖φ τ a‖ : ℝ) : ℂ)) ^ (χ.n τ) = 1 := χ.aut u
      have hB : ((χ'.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) *
          ∏ τ, (φ τ a / ((‖φ τ a‖ : ℝ) : ℂ)) ^ (χ'.n τ) = 1 := χ'.aut u
      have hE := congrArg Units.val (h (Units.map (inc D).toMonoidHom u))
      simp only [Units.val_zpow_eq_zpow_val] at hE
      rw [eq_inv_of_mul_eq_one_left hA, eq_inv_of_mul_eq_one_left hB, inv_zpow, inv_zpow, inv_inj,
        ← Finset.prod_zpow, ← Finset.prod_zpow] at hE
      simp_rw [zpow_sub₀ (hu _), Finset.prod_div_distrib, mul_comm e, mul_comm e', zpow_mul]
      rw [hE]
      exact div_self (Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (zpow_ne_zero _ (hu τ))))
  exact sub_eq_zero.1 (congrFun hc τ)

theorem isBottom_n_eq : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (t : T) (i j : Fin D.R.m)
    (𝔪 : Ideal (𝓞 D.host.E)) {δ t0 : ℂ} {Q : ℕ} (P P' : Pair D ⊤ δ t0 Q), IsBottom G t i j 𝔪 P P' → P'.n = P.n := by
  intro D T Lc sc G t i j 𝔪 δ t0 Q P P' h
  funext τ
  have h1 := mul_n_eq P.W.chV' P'.W.chV' P.W.ep' P'.W.ep' (fun x => (h.chars.2 x).trans (h.chars'.2 x).symm) τ
  have h2 := P.wt τ
  have h3 := P'.wt τ
  have h4 : P'.d = P.d := h.rank.2.2.2
  omega

end GlobalTheory.BottomWeights

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuTwistedTupleIsCMValueHeckeCharacter
section
open NumberField IsDedekindDomain
open Classical

noncomputable section

namespace GlobalTheory.SqTop.TwVal

open Formalism.BasicNotions Formalism.IndefR.Links
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

variable {D : D7}

theorem under_eq_of_conj {P P' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.IndefR.Lev.IsConjPl P P') :
    P.under (𝓞 D.host.F) = P'.under (𝓞 D.host.F) := by
  refine HeightOneSpectrum.ext ((P.under (𝓞 D.host.F)).isMaximal.eq_of_le (P'.under (𝓞 D.host.F)).isPrime.ne_top
    fun a ha => ?_)
  obtain ⟨c', h1, h2⟩ := h (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) ha
  have hfix : star (algebraMap D.host.F D.host.E (a : D.host.F)) = algebraMap D.host.F D.host.E (a : D.host.F) :=
    (D.sp.cm.fixed _).2 ⟨_, rfl⟩
  have e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a = c' := RingOfIntegers.ext (h2.trans hfix).symm
  change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a ∈ P'.asIdeal
  rwa [e]

theorem expAt_mul_unr {χ ξ : HChar D.host.E} {P : HeightOneSpectrum (𝓞 D.host.E)} {n : ℕ}
    (h : GlobalTheory.CMVal.ExpAt χ P n) (hξ : ξ.UnrAt P) : GlobalTheory.CMVal.ExpAt (χ * ξ) P n := by
  intro m
  have hm : ξ.LevelLe P m := hξ.levelLe m
  refine ⟨fun hx => (h m).1 ?_, fun hn => ((h m).2 hn).mul hm⟩
  have := hx.mul hm.inv
  rwa [mul_inv_cancel_right] at this

theorem expAt_mul_low {χ ξ : HChar D.host.E} {P : HeightOneSpectrum (𝓞 D.host.E)} {n k : ℕ}
    (h : GlobalTheory.CMVal.ExpAt χ P n) (hξ : ξ.LevelLe P k) (hk : k < n) : GlobalTheory.CMVal.ExpAt (χ * ξ) P n := by
  intro m
  refine ⟨fun hx => ?_, fun hn => ((h m).2 hn).mul (Model.levelLe_mono hξ (by omega))⟩
  by_contra c
  have a := Model.levelLe_mono hx (le_max_left m k)
  have b := Model.levelLe_mono hξ (le_max_right m k)
  have := a.mul b.inv
  rw [mul_inv_cancel_right] at this
  have := (h _).1 this
  omega

theorem isValChar_nu_twist {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) {s : ℕ} (hs : s ≤ halfRank D i j) :
    GlobalTheory.CMVal.IsValChar (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl)
      ((GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F)) (nuH G t i j) := by
  have e : nuH G t i j = nuH G μ₀ i j * L.xiH t := by
    simp only [nuH, hL.xi_base, mul_one]
    rw [div_mul_eq_mul_div]
  obtain ⟨n, hn, hf⟩ := hL.xi_fin t
  obtain ⟨hu0, htr0, hinf0, hloc0⟩ := (Model.isValChar_nu hL G i j hs).1
  have unipotent_character_trivial_off_S0 : ∀ PP ∈ GlobalTheory.SqTop.twPl G t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∉ G.pl.S0 := fun PP hPP hS => by
    simp only [GlobalTheory.SqTop.twPl, GlobalTheory.FunObj.locPl, Finset.mem_filter, Finset.mem_union] at hPP
    have hQ : PP ∈ L.Q t := hPP.1.resolve_left hPP.2
    rcases G.pl.mem_S0_of_sum_eq.1 hS with h | h
    · exact G.pl.levelPlace_ne_basePlace t PP hQ h
    · exact hPP.2 (by rw [G.pl.w_Q t PP hQ h]; exact Finset.mem_image_of_mem _ hS)
  have ram : ∀ PP : HeightOneSpectrum (𝓞 D.host.E), ¬ (L.xiH t).UnrAt PP →
      (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ S1 D ∨
        (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ (GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F) := by
    intro PP hPP
    obtain ⟨P', hP', hu⟩ : ∃ P' ∈ L.Q t, P'.under (𝓞 D.host.F) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) := by
      rcases (hL.Q_ram t PP).1 hPP with h | ⟨P', h, hc⟩
      · exact ⟨PP, h, rfl⟩
      · exact ⟨P', h, under_eq_of_conj hc⟩
    by_cases hW : P' ∈ G.pl.W0
    · left
      obtain ⟨u, hu', rfl⟩ := Finset.mem_image.1 hW
      rw [← hu, G.pl.under_w hu']
      exact (G.pl.mem_S0_of_sum_eq.1 hu').resolve_left fun h => G.pl.levelPlace_ne_basePlace t _ hP' ((G.pl.under_w hu').trans h)
    · right
      exact Finset.mem_image.2 ⟨P', by
        simp only [GlobalTheory.SqTop.twPl, GlobalTheory.FunObj.locPl, Finset.mem_filter, Finset.mem_union]; exact ⟨Or.inr hP', hW⟩, hu⟩
  rw [e]
  refine ⟨hu0.mul (HChar.isUnitary_of_order hn hf), htr0.mul (hL.xi_triv t), fun k => ?_,
    fun v P hP => ⟨fun hv => ?_, fun hv => ?_⟩⟩
  · rw [HChar.inf_mul, GlobalTheory.TypeValues.inf_eq_one (L.xiH t) hn hf k, mul_one]
    exact hinf0 k
  · obtain rfl : P.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hP
    obtain ⟨PP, hPP, hu⟩ := Finset.mem_image.1 hv
    have h0 := (hloc0 _ P hP).2 (Finset.notMem_empty _)
    rw [Model.expIn_condF, if_neg (hu ▸ unipotent_character_trivial_off_S0 PP hPP)] at h0
    exact (Model.levelLe_mono ((h0 0).2 le_rfl) (Nat.zero_le 1)).mul (hL.xi_tame t P)
  · obtain rfl : P.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hP
    have h0 := (hloc0 _ P hP).2 (Finset.notMem_empty _)
    by_cases hr : (L.xiH t).UnrAt P
    · exact expAt_mul_unr h0 hr
    · have hS1 := (ram P hr).resolve_right hv
      refine expAt_mul_low h0 (hL.xi_tame t P) ?_
      rw [Model.expIn_condF, if_pos (G.pl.mem_S0_of_sum_eq.2 (Or.inr hS1)), condExp,
        if_neg fun (e : P.under (𝓞 D.host.F) = G.pl.v0) => G.ch.basePlace_not_mem_chiGridBadPlaces (e ▸ hS1)]
      norm_num

end GlobalTheory.SqTop.TwVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuTwistedTupleRamifiedAtTwistPlace
section
open NumberField IsDedekindDomain
open Classical

namespace GlobalTheory.SqTop

open Formalism.BasicNotions Formalism.IndefR.Links Formalism.L2.Host GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

theorem nuH_not_unrAt_twPl : ∀ {D : Formalism.BasicNotions.D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GlobalTheory.ChiGrid.GridData L sc) {μ₀ : T}, L.Is μ₀ → ∀ (t : T) (i j : Fin D.R.m), ∀ P ∈ GlobalTheory.SqTop.twPl G t, ¬ (GlobalTheory.FunObj.SqNum.nuH G t i j).UnrAt P := by
  intro D T L sc G μ₀ hL t i j P hP
  classical
  have hP' : P ∈ L.Q t ∧ P ∉ G.pl.W0 := by
    simp only [twPl, GlobalTheory.FunObj.locPl, Finset.mem_filter, Finset.mem_union] at hP
    exact ⟨hP.1.resolve_left hP.2, hP.2⟩
  have hxi : ¬ (L.xiH t).UnrAt P := (hL.Q_ram t P).2 (Or.inl hP'.1)
  have hS1 : P.under (𝓞 D.host.F) ∉ S1 D := fun h => by
    have e := G.pl.w_Q t P hP'.1 h
    refine hP'.2 ?_
    rw [e]
    exact Finset.mem_image_of_mem _ (G.pl.mem_S0_of_sum_eq.2 (Or.inr h))
  have hS0 : P.under (𝓞 D.host.F) ∉ G.pl.S0 := fun h =>
    (G.pl.mem_S0_of_sum_eq.1 h).elim (G.pl.levelPlace_ne_basePlace t P hP'.1) hS1
  have a1 : 1 ≤ D.R.m - i := by have := i.2; omega
  have a2 : D.R.m - i ≤ D.R.m := by omega
  have hmu : (L.C.mu0 j).UnrAt P := (L.C.isMu0 j).unr P fun k hk => hS1 ((S1_mem_OmF D).2 ?_)
  · have hchi : (G.ch.chiH (D.R.m - i)).UnrAt P := G.ch.unr _ a1 a2 P hS0
    intro hnu
    apply hxi
    have e : L.xiH t = nuH G t i j * (L.C.mu0 j)⁻¹ * G.ch.chiH (D.R.m - i) := by
      rw [nuH]
      have key : ∀ {M : Type} [CommGroup M] (a x c : M), x = a * x / c * a⁻¹ * c := fun a x c => by
        rw [div_mul_eq_mul_div, div_mul_cancel, mul_comm a x, mul_inv_cancel_right]
      exact key _ _ _
    rw [e]
    exact (hnu.mul hmu.inv).mul hchi
  · have : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by
      show algebraMap _ (𝓞 D.host.E) _ ∈ P.asIdeal
      rw [map_natCast]; exact hk
    fin_cases k
    · exact Or.inl this
    · exact Or.inr (Or.inl this)

end GlobalTheory.SqTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkMapInjective
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HSApp.ValCrit

open IsLocalRing

theorem exists_valuation (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] :
    ∃ μ : Valuation R (WithZero (Multiplicative ℤ)),
      (∀ a, μ a ≤ 1) ∧ (∀ a ∈ maximalIdeal R, μ a < 1) ∧ ∀ a, μ a = 0 → a = 0 := by
  classical
  by_cases hf : IsField R
  · refine ⟨1, fun a => ?_, fun a ha => ?_, fun a ha => ?_⟩
    · by_cases h : a = 0
      · simp [h]
      · rw [Valuation.one_apply_of_ne_zero h]
    · have : a = 0 := by
        rw [isField_iff_maximalIdeal_eq.1 hf] at ha
        exact ha
      simp [this]
    · by_contra h
      rw [Valuation.one_apply_of_ne_zero h] at ha
      exact one_ne_zero ha
  · obtain ⟨V, hV, hd⟩ := exists_discreteValuationSubring_dominating R (FractionRing R) (FractionRing R) hf
    obtain ⟨h1, h2⟩ := (localSubring_range_le_valuationSubring_iff_isLocalHom _ _).1 hd
    let ρ : R →+* V := (algebraMap R (FractionRing R)).codRestrict V h1
    have hρ : Function.Injective ρ := fun a b hab =>
      IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val hab)
    let v : IsDedekindDomain.HeightOneSpectrum V :=
      ⟨maximalIdeal V, inferInstance, IsDiscreteValuationRing.not_a_field V⟩
    refine ⟨v.intValuation.comap ρ, fun a => v.intValuation_le_one _, fun a ha => ?_, fun a ha => ?_⟩
    · refine (v.intValuation_lt_one_iff_mem _).2 ?_
      exact (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit ρ a hu)
    · by_contra h
      exact v.intValuation_ne_zero _ (fun e => h (hρ (e.trans (map_zero ρ).symm))) ha

variable {k : Type} [Field k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {U : Y.Opens} {D : ℕ}

theorem isIntegral_X [IsIntegral Y] (M : Modif p U D) [Nonempty M.X] : IsIntegral M.X := by
  haveI : Smooth M.str := SmoothOfRelativeDimension.smooth D M.str
  haveI : IsReduced M.X := isReduced_of_smooth M.str
  obtain ⟨x, hx⟩ := M.dense.nonempty
  haveI : Nonempty (M.σ ⁻¹ᵁ U) := ⟨⟨x, hx⟩⟩
  haveI : Nonempty U := ⟨⟨M.σ x, hx⟩⟩
  haveI := M.iso
  haveI : IsIntegral (M.σ ⁻¹ᵁ U : Scheme) := isIntegral_of_isOpenImmersion (M.σ ∣_ U)
  have h1 : IsIrreducible ((M.σ ⁻¹ᵁ U : M.X.Opens) : Set M.X) := by
    have := (IrreducibleSpace.isIrreducible_univ (M.σ ⁻¹ᵁ U : Scheme)).image (⇑(M.σ ⁻¹ᵁ U).ι)
      (M.σ ⁻¹ᵁ U).ι.continuous.continuousOn
    rwa [Set.image_univ, Scheme.Opens.range_ι] at this
  have h2 := h1.closure
  rw [M.dense.closure_eq] at h2
  haveI : IrreducibleSpace M.X := (irreducibleSpace_def _).2 h2
  exact isIntegral_of_irreducibleSpace_of_isReduced M.X

end GlobalTheory.HSApp.ValCrit

namespace GlobalTheory.HSApp

end GlobalTheory.HSApp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCharacterAlmostUnramified
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.PsiStdCond

theorem psi_std_conductor : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    (∀ᶠ v in cofinite, PsiUnr ψ v) ∧ ∀ v : Pl (F := F), ∃ x, psiLoc ψ v x ≠ 1 := by
  classical
  intro F _ _ ψ hψ
  refine ⟨?_, ?_⟩
  · have hfin : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ differentIdeal ℤ (𝓞 F)}.Finite :=
      Ideal.finite_factors differentIdeal_ne_bot
    refine Filter.eventually_cofinite.2 (hfin.subset fun v hv => ?_)
    by_contra h
    exact hv (GlobalTheory.StdCharUnrF.psiUnr_of_not_le F ψ hψ v fun h' => h (Ideal.dvd_iff_le.2 h'))
  · intro v
    by_contra hcon
    push_neg at hcon
    obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer F v
    set c : ℤ := FractionalIdeal.count F v (GlobalTheory.StdDual.codiff F) with hc
    set x : Fv F v := algebraMap F (Fv F v) (π ^ (c - 1)) with hx
    have hmem := (GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (GlobalTheory.LatVacArith.psi_fin_rat hψ)
      (GlobalTheory.AdelicU.singleFin v x)).2 (fun β hβ => by
        have e : β * GlobalTheory.AdelicU.singleFin v x = GlobalTheory.AdelicU.singleFin v (x * β v) := by
          apply GlobalTheory.AdelicU.af_ext
          intro u
          by_cases hu : u = v
          · subst hu
            rw [map_mul, GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self]
            change β u * x = x * β u
            ring
          · rw [map_mul, GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu, mul_zero]
        rw [e]
        exact hcon _)
    have h1 := (GlobalTheory.Idele.mem_adelicIdeal_iff GlobalTheory.StdDual.codiff_ne_zero).1 hmem v
    have h2 : Valued.v (GlobalTheory.AdelicU.singleFin v x v) = Valued.v x := by
      change Valued.v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ v (GlobalTheory.AdelicU.singleFin v x)) = _
      rw [GlobalTheory.AdelicU.evalV_singleFin_self]
    have h3 : Valued.v x = WithZero.exp (-(c - 1)) := by
      rw [hx, GlobalTheory.Idele.valued_algebraMap, map_zpow₀, hπ, ← WithZero.exp_zsmul]
      congr 1
      simp
    rw [← hc] at h1
    rw [h2, h3, WithZero.exp_le_exp] at h1
    omega

end GlobalTheory.PsiStdCond
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardThetaDatumPresentationLevelNorm
section
noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.FunObj.StdDatum

theorem pres_stdSum : ∀ (D : D7) (δ t0 : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), oddE0 D ⊤ δ t0 a d e0 → a ≤ d → ∀ (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → IsCoprime 𝔪 D.host.𝔟 → (∀ u, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) → ∀ R : Finset (GA D a), (∀ r ∈ R, r ∈ intG D a) → (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) → (∀ k ∈ intG D a, W.Om k 1 (stdSum W 𝔪 0 R) = stdSum W 𝔪 0 R) → Pres D ⊤ δ (Ideal.absNorm 𝔪) e0 (stdSum W 𝔪 0 R) := by
  intro D δ t0 hc a d e0 hv had W 𝔪 h𝔪 hco hb _hchar R hR huniq _hfix
  have he : e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) := hv.1
  have hN0 : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 h𝔪)
  have hidx := _root_.GlobalTheory.SkewIndex.index_inter_skew D δ hc 𝔪 h𝔪 hco a d
  haveI hfin : Finite (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) ⧸
      (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) :=
    AddSubgroup.index_ne_zero_iff_finite.1 (by rw [hidx]; positivity)
  letI : Fintype (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) ⧸
      (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) := Fintype.ofFinite _
  have wsm : ∀ (x : VC D a d) (c : ℂ) (G : VC D a d → ℂ), Wd D (tor0 D ⊤ δ) x (c • G) = c • Wd D (tor0 D ⊤ δ) x G := by
    intro x c G; funext z; simp only [Wd, U, Pi.smul_apply, smul_eq_mul]; ring
  have hr : ∀ i : R, ∃ (c : ℂ) (x : Matrix (Fin d) (Fin a) D.host.E), (∃ m : ℕ, 0 < m ∧ c ^ m = 1) ∧
      pt D (tor0 D ⊤ δ) δ x ∈ La0 D (tor0 D ⊤ δ) a d ∧
      (∀ i' j, (x.map (inc D) - (unitBlock D 0 a d).map (inc D) *
        ((((i : GA D a)⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i' j ∈ hatId D 𝔪) ∧
      W.Om i 1 (cosetV D δ 𝔪 0 a d e0) = ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ •
        (c • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x)
          (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0)) := by
    intro i
    obtain ⟨c, hcm, hce⟩ := _root_.GlobalTheory.FunObj.StdDatum.vacuum_int_root_of_unity D δ hc e0 he W i (hR i i.2)
    obtain ⟨x, hx, hxc, hom⟩ := _root_.GlobalTheory.FunObj.StdDatum.LiftCoset.om_cosetV_eq D δ hc e0 he W 𝔪 h𝔪 i (hR i i.2)
    refine ⟨c, x, hcm, hx, hxc, ?_⟩
    rw [hom, _root_.GlobalTheory.FunObj.EigUnit.eig_unit D δ hc e0 he W 𝔪 h𝔪 i (hR i i.2) c hce, wsm]
  choose c x hcm hx hxc hom using hr
  choose χ hχ using fun i : R => _root_.GlobalTheory.CommPhase.chars D δ hc 𝔪 (pt D (tor0 D ⊤ δ) δ (x i)) (hx i)
  have hone : ∀ k : GA D a, CongOne D 𝔪 (k⁻¹ * k) := by
    intro k i' j
    rw [inv_mul_cancel]
    simp
  have hinj : Function.Injective χ := by
    intro i j hij
    have hk : ∀ y ∈ La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d),
        Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (x i)) y =
          Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (x j)) y := by
      intro y hy
      rw [← hχ i ⟨y, hy⟩, ← hχ j ⟨y, hy⟩, hij]
    have h1 := GlobalTheory.T.stabilizer_congruent_of_commutatorPhase_eq D δ hc 𝔪 h𝔪 hco hb had i j (hR i i.2) (hR j j.2) (x i) (x j) (hx i) (hx j) (hxc i) (hxc j) hk
    exact Subtype.ext ((huniq j (hR j j.2)).unique ⟨i.2, h1⟩ ⟨j.2, hone j⟩)
  have hcard : Fintype.card R ≤ Ideal.absNorm 𝔪 ^ (a * d) := by
    rw [Fintype.card_coe]
    refine (_root_.GlobalTheory.card_congRep_le D 𝔪 h𝔪 a R hR huniq).trans (Nat.pow_le_pow_right hN0 ?_)
    rw [pow_two]; exact Nat.mul_le_mul_left a had
  obtain ⟨rr, hrr, hint, hρ⟩ := _root_.GlobalTheory.ParsevalRootsOfUnity.exists_integral_coeffs_sum_norm_sq_le_of_rootOfUnity (Ideal.absNorm 𝔪) (a * d) c χ hN0 hcm hinj
    (by rw [← hidx, AddSubgroup.index_eq_card, Nat.card_eq_fintype_card]) hcard
  choose z hz hzN using fun q : (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) ⧸
      (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) =>
    _root_.GlobalTheory.FunObj.StdDatum.SkewPoints.points D δ hc 𝔪 h𝔪 _ (Quotient.out q).2
  set e := Fintype.equivFin (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) ⧸
      (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)))
  refine ⟨_, fun i => rr (e.symm i), fun i => z (e.symm i), fun i => hzN _, fun i => hint _, fun ρ => ?_, ?_⟩
  · rw [e.symm.sum_comp (fun q => ‖ρ (rr q)‖)]; exact hρ ρ
  funext y
  rw [e.symm.sum_comp (fun q => ((rr q : Qbar) : ℂ) * Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (z q)) e0 y)]
  simp only [stdSum, Finset.sum_apply]
  rw [← Finset.sum_coe_sort R]
  simp only [hom, Pi.smul_apply, smul_eq_mul, _root_.GlobalTheory.FunObj.TransExp.wd_iop_expand D δ hc 𝔪 h𝔪 e0 he _ (hx _), hidx,
    finsum_eq_sum_of_fintype, hrr, ← hz]
  have hs : ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ *
      ((Real.sqrt (((Ideal.absNorm 𝔪 ^ (a * d) : ℕ) : ℝ)) : ℂ))⁻¹ = (((Ideal.absNorm 𝔪 : ℂ)) ^ (a * d))⁻¹ := by
    have h1 : (((Ideal.absNorm 𝔪 ^ (a * d) : ℕ) : ℝ)) = (Ideal.absNorm 𝔪 : ℝ) ^ (a * d) := by push_cast; rfl
    rw [h1, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast; rfl
  have hχq : ∀ (i : R) q, χ i q = Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (x i))
      ((Quotient.out q : La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) : VC D a d) := by
    intro i q
    rw [← hχ i, QuotientAddGroup.out_eq']
  simp only [hχq, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_
  rw [← hs]; ring

end GlobalTheory.FunObj.StdDatum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelArchimedeanUnipotentSupportStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_kernel_archimedean_unipotent_support : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (S : Finset (Pl (F := F))) (g : UA σ G.V'.J) (h : UA σ G.W.J),
    (∀ u : AF F, At (evI F) u → u • (mat g - 1) = 0) → (∀ u : AF F, At (evI F) u → u • (mat h - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, At (evFin F w) u → u • (mat g - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, At (evFin F w) u → u • (mat h - 1) = 0) →
    ∀ Φ ∈ schA F (Fin a' × Fin (a + a')), ∀ u : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    (∀ t : AF F, evI F t = 0 → (∀ w ∈ S, evFin F w t = 0) → t • u = 0) →
    ∀ μ : @MeasureTheory.Measure (Fin a' × Fin (a + a') → AF F) (borel _),
      @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      (@MeasureTheory.integral _ ℂ _ _ (borel _) μ fun x =>
          om' (g, h) Φ x * starRingEnd ℂ (G.M'.co.rho B.ψ u (om' (g, h) Φ) x)) =
        @MeasureTheory.integral _ ℂ _ _ (borel _) μ fun x => Φ x * starRingEnd ℂ (G.M'.co.rho B.ψ u Φ x) := by
  first | exact @GlobalTheory.CptCoeff.matrix_coeff | exact GlobalTheory.CptCoeff.matrix_coeff | (intros; apply GlobalTheory.CptCoeff.matrix_coeff <;> assumption)
end

