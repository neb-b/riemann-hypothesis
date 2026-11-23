module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoordIntOfJets
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationDenominatorsAndHostFieldSizes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeIsIntegralOverStandardLatticeStabilis
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0898
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0439
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1697
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1701
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0271
public import Formalism.SharpRestriction.Divisibility.JetPolynomialLogs.AnnihilatorMulRelativeDifferent
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0572
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0601
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0583
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0571
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0377
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0315
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSumPairCoordinateAlgebraic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.NormSum.CoordAlg

open Classical Formalism.UG Formalism.UG.P Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.NormSum.IntOver GlobalTheory.NormSum.RepAt GlobalTheory.NormSum.PtsMem

theorem exists_prime_integralOver_gt (D : D7) (N : ℕ) (h : GA D N) (Q : ℕ) :
    ∃ p : ℕ, Q < p ∧ p.Prime ∧ IntegralOver D p h := by
  set g : Matrix (Fin N) (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D) := ((h : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin N) (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) with hg
  choose m hm0 hm using fun ij : Fin N × Fin N => denom (F := ℚ) (E := D.host.E) (g ij.1 ij.2)
  set M := ∏ ij, m ij with hMdef
  have hM0 : 0 < M := Finset.prod_pos fun ij _ => hm0 ij
  obtain ⟨p, hpM, hp⟩ := Nat.exists_infinite_primes (M + Q + 1)
  have hpM' : ¬ p ∣ M := fun hd => by have := Nat.le_of_dvd hM0 hd; omega
  obtain ⟨v, hv, hw⟩ := exists_place p hp
  have hMv : ((M : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
    intro hm'
    obtain ⟨x, y, e⟩ := (Nat.isCoprime_iff_coprime.2 (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM'))).map
      (Int.castRingHom (𝓞 ℚ))
    refine v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    rw [← e]
    exact add_mem (Ideal.mul_mem_left _ _ (by simpa using hm')) (Ideal.mul_mem_left _ _ (by simpa using hv))
  have hi : ∀ i j, afsplitEps D.host.E v * g i j ∈ OhE D := fun i j => eps_mul_mem v M hMv _ (by
    rw [hMdef, ← Finset.prod_erase_mul _ _ (Finset.mem_univ (i, j)), Nat.cast_mul, mul_assoc]
    exact mul_mem (natCast_mem _ _) (hm (i, j)))
  obtain ⟨k, hk, hint, htriv⟩ := exists_int (F := ℚ) (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) v
    (h : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) h.2 (Units.inv_eq_of_mul_eq_one_left ((mem_GA D _).1 h.2)) hi
  refine ⟨p, by omega, hp, ⟨k, hk⟩, (mem_intG _).2 hint, fun i j l => ?_⟩
  have := zero_at (F := ℚ) (E := D.host.E) v p hp hw (g i j - (1 : Matrix (Fin N) (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j) l
  rw [← htriv i j] at this
  exact this

end GlobalTheory.NormSum.CoordAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalFormToricRatio
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.RowEx.RatioField

open GlobalTheory.FunObj.SqNum GlobalTheory.CMVal

theorem kap_add_big (D : D7) (C : ℝ) (i j : Fin D.R.m) (τ : D.what₂.Tau) {s : ℕ} (hs : s ≤ bigN D + 1) :
    (kap D C i j s τ : ℤ) + s = (num D C τ).e (j + 1) + cen D C τ (D.R.m - i) ∧ 0 < kap D C i j s τ := by
  have h := SqNum.Model.gap_le D C i j τ
  have h2 := (GlobalTheory.ChiGrid.isLeast_gap D C).1.2.1
  have h4 : bigN D ≤ bigN D ^ 3 := Nat.le_self_pow (by norm_num) _
  unfold kap
  omega

theorem isValChar_shift {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} {s s' : ℕ}
    {κ κ' : I → ℕ} {𝔣 : Ideal (OF E)} {Q : Finset (HeightOneSpectrum (OF E))} {χ : HChar E}
    (h : IsValChar φ s κ 𝔣 Q χ) (e : ∀ i, (κ i : ℤ) + s = κ' i + s') : IsValChar φ s' κ' 𝔣 Q χ := by
  obtain ⟨a, b, c, d⟩ := h
  have : (fun i => (κ' i : ℤ) + s') = fun i => (κ i : ℤ) + s := funext fun i => (e i).symm
  exact ⟨a, b, this ▸ c, d⟩

theorem cmPhi_comp_eq {D : D7} (hfd : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (cmPhi D)) (τ τ' : D.what₂.Tau) :
    (cmPhi D τ).comp (algebraMap D.host.K D.host.E) = (cmPhi D τ').comp (algebraMap D.host.K D.host.E) := by
  obtain ⟨w, hw, hφw⟩ := hfd.2.2.2.2.2.2.2
  refine GlobalTheory.ToricRatioBridge.comp_eq_of_sqrt D.host _ _ ?_
  have hs := Formalism.BasicNotions.Host.sqrtMinusD_sq D.host
  have h0 : (D.host.sqrtMinusD - w) * (D.host.sqrtMinusD + w) = 0 := by linear_combination hs - hw
  rcases mul_eq_zero.1 h0 with h | h
  · rw [sub_eq_zero.1 h, hφw, hφw]
  · rw [eq_neg_of_add_eq_zero_left h, map_neg, map_neg, hφw, hφw]


open Classical in
theorem ratio_algebraic (hTR : GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates) {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts}
    {μ₀ : T} (hL : Lc.Is μ₀) (G : GridData Lc sc) (hcm : IsCMField D.host.E)
    (hfd : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (cmPhi D)) (hbc : IsBaseCond (condF G.pl))
    (i j : Fin D.R.m) (t : T) (s : ℕ) (hs1 : 1 ≤ s) (hs2 : s ≤ bigN D + 1) (Λ Λ₀ : ℂ → ℂ)
    (hΛ : IsHeckeL (nuH G t i j) Λ) (hΛ₀ : IsHeckeL (nuH G μ₀ i j) Λ₀) :
    IsAlgebraic ℚ (Λ s / Λ₀ s) := by
  haveI := hcm
  have hU : UnramFin D.host.E := hfd.2.2.1
  have hφ : IsCMType (cmPhi D) := hfd.2.2.2.2.2.2.1
  have e : ∀ τ, (kap D sc.cGap i j 0 τ : ℤ) + ((0 : ℕ) : ℤ) = kap D sc.cGap i j s τ + s := fun τ =>
    (SqNum.Model.kap_add D sc.cGap i j τ (Nat.zero_le _)).1.trans (kap_add_big D sc.cGap i j τ hs2).1.symm
  have hv0 : IsValChar (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) ∅ (nuH G μ₀ i j) :=
    isValChar_shift (SqNum.Model.isValChar_nu hL G i j (Nat.zero_le _)).1 e
  obtain ⟨Q, hQdef⟩ : ∃ Q : Finset (HeightOneSpectrum (OF D.host.E)),
      Q = (GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F) := ⟨_, rfl⟩
  have hvt : IsValChar (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) Q (nuH G t i j) :=
    hQdef ▸ isValChar_shift (GlobalTheory.SqTop.TwVal.isValChar_nu_twist G hL t i j (Nat.zero_le _)) e
  have hQaux : IsFinSetSplitPlacesCoprimeConductor (condF G.pl) Q := hQdef ▸ GlobalTheory.KummerTwistLemmas.twist_places_under_split_coprime_conductor G hL t
  have hQram := GlobalTheory.SqTop.nuH_not_unrAt_twPl G hL t i j
  have hex : ∀ q ∈ Q, ∃ P ∈ GlobalTheory.SqTop.twPl G t, P.under (𝓞 D.host.F) = q := fun q hq => by
    rw [hQdef] at hq
    exact Finset.mem_image.1 hq
  let Pq : HeightOneSpectrum (OF D.host.E) → HeightOneSpectrum (𝓞 D.host.E) := fun q =>
    if h : ∃ P ∈ GlobalTheory.SqTop.twPl G t, P.under (𝓞 D.host.F) = q then h.choose else G.pl.w G.pl.v0
  have hPq : ∀ q ∈ Q, Pq q ∈ GlobalTheory.SqTop.twPl G t ∧ (Pq q).under (𝓞 D.host.F) = q := fun q hq => by
    have h := hex q hq
    simp only [Pq, dif_pos h]
    exact h.choose_spec
  have hov : ∀ q ∈ Q, Over (Pq q) q := fun q hq =>
    (show Over (Pq q) ((Pq q).under (OF D.host.E)) from rfl).trans (congrArg HeightOneSpectrum.asIdeal (hPq q hq).2)

  have htor := GlobalTheory.ToricSumValue.toricSum_eq GlobalTheory.Published.HeckeEntire_holds D.host.E D.what₂.Tau (cmPhi D) hφ s
    (kap D sc.cGap i j s) (condF G.pl) Q (nuH G t i j) Pq Λ hU hs1 hbc hQaux hvt hov hΛ
  rw [Finset.filter_false_of_mem (fun q hq => hQram _ (hPq q hq).1), Finset.prod_empty, mul_one] at htor

  have htor0 := GlobalTheory.ToricSumValue.toricSum_eq GlobalTheory.Published.HeckeEntire_holds D.host.E D.what₂.Tau (cmPhi D) hφ s
    (kap D sc.cGap i j s) (condF G.pl) ∅ (nuH G μ₀ i j) (fun _ => G.pl.w G.pl.v0) Λ₀ hU hs1 hbc
    (fun q hq => absurd hq (Finset.notMem_empty q)) hv0 (fun q hq => absurd hq (Finset.notMem_empty q)) hΛ₀
  simp only [condQ, Finset.prod_empty, mul_one, Finset.filter_empty] at htor0

  have hnu : nuH G t i j = nuH G μ₀ i j * Lc.xiH t := by
    rw [nuH, nuH, hL.xi_base, mul_one, div_mul_eq_mul_div]

  obtain ⟨k, hk, hko⟩ := hL.xi_fin t
  have hinf : ∀ y : D.host.Eˣ, (Lc.xiH t).inf y = 1 := fun y => GlobalTheory.TypeValues.inf_eq_one _ hk hko y
  have hu : ∀ u ∈ hatOUnits (condQ (condF G.pl) Q), finPart (Lc.xiH t) u = 1 := fun u hu => by
    have a := GlobalTheory.CMVal.OrderUnits.finPart_eq_one D.host.E D.what₂.Tau (cmPhi D) hφ s (kap D sc.cGap i j s)
      (condF G.pl) Q (nuH G t i j) hU hbc hQaux hvt u hu
    have hle : condQ (condF G.pl) Q ≤ condQ (condF G.pl) ∅ := by
      simp only [condQ, Finset.prod_empty, mul_one]
      exact Ideal.mul_le_left
    have b := GlobalTheory.CMVal.OrderUnits.finPart_eq_one D.host.E D.what₂.Tau (cmPhi D) hφ s (kap D sc.cGap i j s)
      (condF G.pl) ∅ (nuH G μ₀ i j) hU hbc (fun q hq => absurd hq (Finset.notMem_empty q)) hv0 u
      (hatOUnits_mono hle hu)
    rw [hnu, finPart_mul, b, one_mul] at a
    exact a
  have hker : princ ⊔ hatOUnits (condQ (condF G.pl) Q) ≤ (finPart (Lc.xiH t)).ker := by
    refine sup_le ?_ fun u hu' => hu u hu'
    rintro _ ⟨a, rfl⟩
    have := finPart_mul_inf (Lc.xiH t) a
    rw [hinf a, mul_one] at this
    exact this
  let ψ : PicO (condQ (condF G.pl) Q) →* ℂˣ := QuotientGroup.lift _ (finPart (Lc.xiH t)) hker

  haveI : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by have := hfd.2.2.2.2.2.1; omega)
  let τ₀ : D.what₂.Tau := Classical.arbitrary _
  have hK2 : Module.finrank ℚ D.host.K = 2 := Formalism.MainNotions.DIV.Bridge.LogAbsNormDifferent.finrank_K D
  let δ : D.host.K := ⟨D.host.sqrtMinusD, GlobalTheory.Mem.Col2.HostK.sqrt_mem D.host⟩
  have hδ : δ ^ 2 = -(D.host.d : D.host.K) := Subtype.ext (by simpa using Formalism.BasicNotions.Host.sqrtMinusD_sq D.host)
  obtain ⟨T₀, Tf, hT₀, -, hTw, hAlg, -⟩ := hTR D.host.E D.host.K D.host.d δ
    ((cmPhi D τ₀).comp (algebraMap D.host.K D.host.E)) D.what₂.Tau (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) Q
    (nuH G μ₀ i j) hU hK2 hfd.1.pos hδ hφ (fun τ => cmPhi_comp_eq hfd τ τ₀) hs1
    (fun τ => (kap_add_big D sc.cGap i j τ hs2).2) hbc hQaux hv0
  have e1 : T₀ = Λ₀ s := hT₀.unique htor0
  have e2 : Tf ψ = Λ s :=
    ((GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.isTwistedSum_iff_isToricSum (ξ := Lc.xiH t) (fun y => rfl) _).1 (hTw ψ)).unique (hnu ▸ htor)
  rw [← e1, ← e2]
  exact hAlg ψ

end GlobalTheory.RowEx.RatioField

namespace GlobalTheory.RowEx.RatioField

open GlobalTheory.FunObj.SqNum GlobalTheory.CMVal

theorem inNF_ratios (hTR : GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates) {D : D7} {T : Type} [Finite T] {Lc : LevCh D T} {sc : Consts}
    {μ₀ : T} (hL : Lc.Is μ₀) (G : GridData Lc sc) (hcm : IsCMField D.host.E)
    (hfd : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (cmPhi D)) (hbc : IsBaseCond (condF G.pl)) :
    InNF fun _ σ => ∀ i j, LRatiosIn G σ μ₀ i j := by
  let S : Set ℂ := ⋃ (i : Fin D.R.m) (j : Fin D.R.m) (t : T) (s ∈ Set.Icc 1 (bigN D + 1)),
    {z | ∃ Λ Λ₀ : ℂ → ℂ, IsHeckeL (nuH G t i j) Λ ∧ IsHeckeL (nuH G μ₀ i j) Λ₀ ∧ z = Λ s / Λ₀ s}
  have hS : S.Finite := by
    refine Set.finite_iUnion fun i => Set.finite_iUnion fun j => Set.finite_iUnion fun t =>
      (Set.finite_Icc _ _).biUnion fun s _ => Set.Subsingleton.finite ?_
    rintro _ ⟨Λ, Λ₀, h1, h2, rfl⟩ _ ⟨Λ', Λ₀', h1', h2', rfl⟩
    rw [h1.unique h1', h2.unique h2']
  have hSa : ∀ z ∈ S, IsAlgebraic ℚ z := by
    intro z hz
    simp only [S, Set.mem_iUnion, Set.mem_setOf_eq] at hz
    obtain ⟨i, j, t, s, ⟨h1, h2⟩, Λ, Λ₀, hΛ, hΛ₀, rfl⟩ := hz
    exact ratio_algebraic hTR hL G hcm hfd hbc i j t s h1 h2 Λ Λ₀ hΛ hΛ₀
  haveI : Finite S := hS.to_subtype
  refine ⟨IntermediateField.adjoin ℚ S, IntermediateField.finiteDimensional_adjoin fun z hz => (hSa z hz).isIntegral,
    fun i j t Λ Λ₀ hΛ hΛ₀ s h1 h2 _ => ⟨⟨Λ s / Λ₀ s, IntermediateField.subset_adjoin ℚ S ?_⟩, rfl⟩⟩
  simp only [S, Set.mem_iUnion, Set.mem_setOf_eq]
  exact ⟨i, j, t, s, ⟨h1, h2⟩, Λ, Λ₀, hΛ, hΛ₀, rfl⟩

end GlobalTheory.RowEx.RatioField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PGEquivOfBaseW
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GEquivCx


set_option maxHeartbeats 400000 in
theorem pGEquiv_of_baseW : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.toRealDat.BaseW F.lv2 → R.toRealDat.ExAt → R.PGEquiv F := by
  intro hCR D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hB hE
  have hC : GlobalTheory.Hk3.Core R.toRealDat F.lv2 :=
    ⟨hB.lev, hB.grp, hB.fam, hB.models, RealDat.chain_of_weak hB.chain hE, RealDat.thP_of_weak hB.thP hE⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.LiftGroupEquiv.th_thG_act hCR R.toRealDat F.lv2 hC
  refine ⟨fun t g x => ?_, fun j t g x => ?_⟩
  · exact h1 t g x
  · have e : cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) • R.thG j t (R.jV j t ((A3.A.fam.L j t).r g x)) =
        R.gW j (sg0 D A3.A) g (cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) • R.thG j t (R.jV j t x)) :=
      (congrArg (fun y => cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) • y) (h2 j t g x)).trans
        (LinearMap.map_smul _ _ _).symm
    exact e

end GlobalTheory.GEquivCx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchKapX
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section

namespace GlobalTheory.SquareAgree

theorem conjU_one_eq {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (h : J = c • V.gram) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c h 1 = 1 := by
  apply Subtype.ext
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU]

end GlobalTheory.SquareAgree

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestHilbertModelsOfChoiceClaims
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowClaim

namespace GlobalTheory.RowTestFromClaims

open GlobalTheory.RowTest

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem sum_gE (R : RealDat D A Ks) (hE : R.models_HE) (hg : R.models_gE) (y : R.HE.H) :
    ∑ g, D.what₂.embLL ((idemOf A.X).coeff g) • R.gE g y = y := by
  have hmem : R.HE.e y ∈ R.EEat R.triv := hE.2.1 ▸ LinearMap.mem_range_self _ _
  have hfix := ((mem_goodPart _ _ _ _ _ _).1 hmem).2
  apply hE.1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp_rw [map_smul, hg]
  ext v
  rw [← hfix v]
  simp only [RealDat.e0, gaL, RealDat.eC, LinearMap.sum_apply, LinearMap.smul_apply,
    MultilinearMap.sum_apply, MultilinearMap.smul_apply, postOn_apply]
  rfl

theorem rat_of_formula {K : Type} [Field K] (σ : K →+* ℂ) {z : K} {c c₀ κ p w : ℂ} (hz : σ z ≠ 0) (hc : c ≠ 0) (hc₀ : c₀ ≠ 0)
    (hκ : κ ≠ 0) (h : σ z * c * p = κ * w) (hw : w ∈ Set.range σ) (hr : c / c₀ ∈ Set.range σ) : ∃ y, σ y = c₀ * κ⁻¹ * p := by
  obtain ⟨w', rfl⟩ := hw
  obtain ⟨r', hr'⟩ := hr
  refine ⟨w' / (z * r'), ?_⟩
  rw [map_div₀, map_mul, hr']
  have hp : p = κ * σ w' / (σ z * c) := by
    rw [eq_div_iff (mul_ne_zero hz hc), ← h]
    ring
  rw [hp]
  field_simp


set_option maxHeartbeats 1000000 in
theorem exists_good (hP : GlobalTheory.Published.CuspRapidDecay) (R : RealDat D A Ks) (F : Face D A) (hC : GlobalTheory.Hk3.Core R F) (t : T0)
    (x : A.fam.amb.FR t) :
    ∃ x' : A.fam.amb.FR t, x' ∈ (A.fam.R t).goodF A.fam.X ∧ R.Th t (R.jX t x') = R.Th t (R.jX t x) := by
  obtain ⟨hth, -⟩ := GlobalTheory.LiftGroupEquiv.th_thG_act hP R F hC
  have hga : goodAt A.fam.X (⊥ : Subgroup G) 1 = idemOf A.X := Formalism.IndefR.CxPass.LevelOperators.goodAt_bot _ _
  have hmem : (A.fam.R t).S.gaOp (A.fam.R t).r (idemOf A.X) x ∈ (A.fam.R t).goodF A.fam.X := by
    unfold BlockDat.goodF
    rw [hga]
    exact LinearMap.mem_range_self _ x
  refine ⟨_, hmem, ?_⟩
  conv_rhs => rw [← sum_gE R hC.models.HE hC.models.gE (R.Th t (R.jX t x))]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [CSD.gaOp, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, LinearMap.map_smulₛₗ, map_smul]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [hth t g x]

private theorem exists_linearMap_eq_psiK {R : RealDat D A Ks} (ch : Choice R) (hlin : ∀ a u, ConvK ch a u) :
    ∃ f : Fin ch.n → (R.HE.H →ₗ[ℂ] ℂ), ∀ a u, f a u = psiK ch a u :=
  ⟨fun a =>
    { toFun := psiK ch a
      map_add' := fun u u' => by
        simp only [psiK, map_add (f := _)]
        exact GlobalTheory.FunObj.fPsiPhi_add ch.W ch.M (hlin a u) (hlin a u')
      map_smul' := fun b u => by
        have h1 := GlobalTheory.FunObj.fPsiPhi_smul ch.W ch.M ch.ρ ch.ξ 1 b (ch.col a) (ch.Phi a) (ch.form u)
        rw [one_smul, one_mul] at h1
        simp only [psiK, map_smul, RingHom.id_apply, smul_eq_mul]
        exact h1 }, fun _ _ => rfl⟩

private theorem rowTestModel_of_scaled_values_rational {R : RealDat D A Ks} (ch : Choice R) (hlin : ∀ a u, ConvK ch a u)
    (hinj : ∀ u, (∀ a, psiK ch a u = 0) → u = 0) {k : ℂ} (hk : k ≠ 0)
    (hval : ∀ t x a, ∃ z : D.what₂.LL, D.what₂.embLL z = k * psiK ch a (R.Th t (R.jX t x))) :
    GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.RowTestModel R := by
  obtain ⟨f, hf⟩ := exists_linearMap_eq_psiK ch hlin
  refine ⟨ch.n, fun a => k • f a, ?_, ?_⟩
  · intro e he
    apply hinj
    intro a
    have h1 := he a
    rw [LinearMap.smul_apply, hf, smul_eq_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left hk
  · intro t x a
    obtain ⟨z, hz⟩ := hval t x a
    refine ⟨z, hz.trans ?_⟩
    exact (((LinearMap.smul_apply k (f a) _).trans (congrArg (k • ·) (hf a _))).trans (smul_eq_mul k _)).symm

set_option maxHeartbeats 1600000 in
private theorem exists_embLL_mul_psiK_eq_vK_of_formulaAt (hP : GlobalTheory.Published.CuspRapidDecay) {R : RealDat D A Ks} {F : Face D A} (hC : GlobalTheory.Hk3.Core R F)
    (ch : Choice R) {κ : ℂ} {ze : T0 → D.what₂.LL} (hF : FormulaAt ch κ ze) (t : T0) (x : A.fam.amb.FR t) (a : Fin ch.n) :
    ∃ x' : A.fam.amb.FR t, D.what₂.embLL (ze t) * cTot ch t * psiK ch a (R.Th t (R.jX t x)) = κ * vK ch t x' a := by
  obtain ⟨x', hx', hxx⟩ := exists_good hP R F hC t x
  refine ⟨x', ?_⟩
  rw [← hxx]
  exact hF.2 t x' hx' a


set_option maxHeartbeats 1600000 in
theorem rowTest_of_choice (hP : GlobalTheory.Published.CuspRapidDecay) {R : RealDat D A Ks} {F : Face D A} (hC : GlobalTheory.Hk3.Core R F)
    (ch : Choice R) (hlin : ∀ a u, ConvK ch a u) (hinj : ∀ u, (∀ a, psiK ch a u = 0) → u = 0)
    (hc : ∀ i j t, ch.c i j t ≠ 0) {κ : ℂ} {ze : T0 → D.what₂.LL} (hF : FormulaAt ch κ ze)
    (hv : ∀ t x a, vK ch t x a ∈ Set.range D.what₂.embLL) (hr : ∀ i j t, sqRatio ch i j t ∈ Set.range D.what₂.embLL) :
    GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.RowTestModel R := by
  have hcT : ∀ t, cTot ch t ≠ 0 := fun t =>
    Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => hc i j t
  have hz0 : ∀ t, D.what₂.embLL (ze t) ≠ 0 := by
    intro t
    obtain ⟨n, hn, hze⟩ := hF.1 t
    rw [map_ne_zero]
    rintro h0
    rw [h0, zero_pow hn.ne'] at hze
    exact zero_ne_one hze
  by_cases hκ : κ = 0
  · subst hκ
    refine rowTestModel_of_scaled_values_rational ch hlin hinj one_ne_zero fun t x a => ?_
    obtain ⟨x', hfo⟩ := exists_embLL_mul_psiK_eq_vK_of_formulaAt hP hC ch hF t x a
    have hp : psiK ch a (R.Th t (R.jX t x)) = 0 :=
      (mul_eq_zero.1 (hfo.trans (zero_mul _))).resolve_left (mul_ne_zero (hz0 t) (hcT t))
    exact ⟨0, (map_zero D.what₂.embLL).trans (hp.symm.trans (one_mul _).symm)⟩
  · refine rowTestModel_of_scaled_values_rational ch hlin hinj (mul_ne_zero (hcT A.μ0) (inv_ne_zero hκ)) fun t x a => ?_
    obtain ⟨x', hfo⟩ := exists_embLL_mul_psiK_eq_vK_of_formulaAt hP hC ch hF t x a
    have hrat : cTot ch t / cTot ch A.μ0 ∈ Set.range D.what₂.embLL := by
      have he : cTot ch t / cTot ch A.μ0 = ∏ i, ∏ j, sqRatio ch i j t := by
        simp only [cTot, sqRatio, Finset.prod_div_distrib]
      rw [he]
      exact RingHom.mem_fieldRange.1 (Subfield.prod_mem _ fun i _ =>
        Subfield.prod_mem _ fun j _ => RingHom.mem_fieldRange.2 (hr i j t))
    exact rat_of_formula D.what₂.embLL (hz0 t) (hcT t) (hcT _) hκ hfo (hv t x' a) hrat


set_option maxHeartbeats 1000000 in
theorem rowTestModel_of_claims : GlobalTheory.Published.CuspRapidDecay → LinK → InjK → ConstK → SumOKK → Formula2K → SumRatK → RatioK → ∃ CF0 : ℝ, ∀ ε CF : ℝ, CF0 ≤ CF → ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x → ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.RowClaim.HidaSetting large₂ R F → (∃ ch : GlobalTheory.RowTest.Choice R, ch.Is ∧ ch.AtScale CF large₂.sc.b ∧ ch.FieldOK) → GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.RowTestModel R := by
  intro hP hL hI hC _ hF hR hRa
  obtain ⟨CF0, h⟩ := Big.and (Big.and (Big.and (Big.and (Big.and hL hI) hC) hF) hR) hRa
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := h ε CF hCF
  refine ⟨x₀, fun D large₂ hε hxl G _ _ Pl0 T0 A Ks _ _ _ R F hSet => ?_⟩
  rintro ⟨ch, hch, hsc, hfld⟩
  obtain ⟨⟨⟨⟨⟨hlin, hinj⟩, hcst⟩, hfor⟩, hrat⟩, hra⟩ := hx D large₂ hε hxl G Pl0 T0 A Ks R F hSet ch hch hsc
  obtain ⟨κ, ze, hFo⟩ := hfor hfld
  exact rowTest_of_choice hP hSet.core ch hlin hinj (fun i j t => (hcst i j t).2) hFo (hrat hfld) (hra hfld)

end GlobalTheory.RowTestFromClaims
end

