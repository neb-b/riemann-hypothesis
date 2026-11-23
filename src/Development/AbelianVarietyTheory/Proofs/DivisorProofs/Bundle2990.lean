module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2963
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2866
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2558
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0506
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2175
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2407
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDataBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

noncomputable section

namespace GlobalTheory.FunDat

section Val

variable {D : D7}

theorem lossLe_one (w : PlL D) : LossLe w 1 0 := ⟨1, map_one _, Or.inr (by simp [Formalism.DivisionValues.ValuationRepresentative.vw_one])⟩

theorem lossLe_mul {w : PlL D} {z z' : ℂ} {a a' : ℝ} (h : LossLe w z a) (h' : LossLe w z' a') :
    LossLe w (z * z') (a + a') := by
  obtain ⟨y, rfl, hy⟩ := h
  obtain ⟨y', rfl, hy'⟩ := h'
  refine ⟨y * y', map_mul _ _ _, ?_⟩
  by_cases h0 : y = 0
  · exact Or.inl (by simp [h0])
  by_cases h0' : y' = 0
  · exact Or.inl (by simp [h0'])
  rcases hy with h1 | h1
  · exact absurd h1 h0
  rcases hy' with h2 | h2
  · exact absurd h2 h0'
  refine Or.inr ?_
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ h0 h0', Int.cast_add]
  linarith

theorem lossLe_prod {w : PlL D} {ι : Type*} (s : Finset ι) (z : ι → ℂ) (a : ι → ℝ) (h : ∀ i ∈ s, LossLe w (z i) (a i)) :
    LossLe w (∏ i ∈ s, z i) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lossLe_one w
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact lossLe_mul (h i (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem loss_mono {dl : PlL D → ℝ} {B B' : ℝ} (h : Loss dl B) (hB : B ≤ B') : Loss dl B' :=
  ⟨h.1, h.2.1, fun s => (h.2.2 s).trans hB⟩

end Val

section Sum

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

def dlD (K : ℝ) (w : PlL D) : ℝ := ∑ P ∈ G.pl.W0, K * (cosExp G P : ℝ) * (vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) : ℝ)

theorem sum_cosExp_le : ∑ P ∈ G.pl.W0, (cosExp G P : ℝ) * Real.log (resCard (Kw P) : ℕ) ≤ 2 * sig G := by
  classical
  have hinj : Set.InjOn G.pl.w (G.pl.S0 : Set (Pl D.host.F)) := fun v hv v' hv' h =>
    (G.pl.under_w hv).symm.trans ((congrArg _ h).trans (G.pl.under_w hv'))
  rw [Places.W0, Finset.sum_image hinj, sig, Finset.mul_sum]
  refine Finset.sum_le_sum fun v hv => ?_
  obtain ⟨h1, -⟩ := depthAt_w G hv
  rw [h1, ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.ResCardPlace.resCard_Kw]
  have h2 := ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.log_absNorm_le (G.pl.w v)
  rw [G.pl.under_w hv] at h2
  have h3 : (0 : ℝ) ≤ (G.pl.depth sc v : ℝ) := by positivity
  calc (G.pl.depth sc v : ℝ) * Real.log (Ideal.absNorm (G.pl.w v).asIdeal : ℕ)
      ≤ (G.pl.depth sc v : ℝ) * (2 * Real.log (Ideal.absNorm v.asIdeal)) := mul_le_mul_of_nonneg_left h2 h3
    _ = _ := by ring

theorem loss_dlD {K : ℝ} (hK : 0 ≤ K) : Loss (dlD G K) (2 * K * sig G) := by
  classical
  refine ⟨fun w => Finset.sum_nonneg fun P _ => mul_nonneg (by positivity) ?_, ?_, fun s => ?_⟩
  · exact_mod_cast ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_nat_nonneg w _
  · refine ((G.pl.W0.finite_toSet.biUnion fun P _ =>
      ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.finite_vw_ne (K := D.what₂.LL) (resCard (Kw P))
        (ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.resCard_ne P))).subset fun w hw => ?_
    by_contra h
    refine hw (Finset.sum_eq_zero fun P hP => ?_)
    have : vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) = 0 := by
      by_contra h'
      exact h (Set.mem_biUnion hP h')
    simp [this]
  · have h1 : ∑ w ∈ s, lw w * dlD G K w =
        ∑ P ∈ G.pl.W0, K * (cosExp G P : ℝ) * ∑ w ∈ s, lw w * (vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) : ℝ) := by
      simp only [dlD, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun w _ => by ring
    have h2 : ∑ w ∈ s, lw w * dlD G K w ≤ ∑ P ∈ G.pl.W0, K * (cosExp G P : ℝ) * Real.log (resCard (Kw P) : ℕ) := by
      rw [h1]
      exact Finset.sum_le_sum fun P _ => mul_le_mul_of_nonneg_left
        (Formalism.EigenvalueLevelCeiling.sum_lw_vw_natCast_le s _ (ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.resCard_ne P)) (by positivity)
    calc ∑ w ∈ s, lw w * dlD G K w ≤ _ := h2
      _ = K * ∑ P ∈ G.pl.W0, (cosExp G P : ℝ) * Real.log (resCard (Kw P) : ℕ) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun P _ => by ring
      _ ≤ K * (2 * sig G) := mul_le_mul_of_nonneg_left (sum_cosExp_le G) hK
      _ = 2 * K * sig G := by ring

end Sum

end GlobalTheory.FunDat

end

noncomputable section

namespace GlobalTheory.FunDat

section Cases

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

theorem away_cases {t : T} {w : PlL D} (hA : Away G t w) {P : Pl D.host.E} (hl : P ∈ locPl G t) :
    P ∈ G.pl.W0 ∨ ((Formalism.EigenvalueLevelCeiling.plc P : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal := by
  classical
  by_cases hP : P ∈ G.pl.W0
  · exact Or.inl hP
  have hQ : P ∈ L.Q t := by
    rcases Finset.mem_union.1 hl with h | h
    · exact absurd h hP
    · exact h
  refine Or.inr ?_
  rcases hA P hQ with h | h
  · exfalso
    rcases G.pl.mem_S0_of_sum_eq.1 h with h | h
    · exact G.pl.levelPlace_ne_basePlace t P hQ h
    · exact hP (by
        rw [G.pl.w_Q t P hQ h]
        exact Finset.mem_image_of_mem _ (G.pl.mem_S0_of_sum_eq.2 (Or.inr h)))
  · exact h _ (Formalism.EigenvalueLevelCeiling.plc_prime P) (Formalism.EigenvalueLevelCeiling.plc_mem P)

theorem sum_locPl (t : T) (K : ℝ) (w : PlL D) :
    ∑ v : locPl G t, K * (cosExp G v : ℝ) * (vw w ((resCard (Kw (v : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ) = dlD G K w := by
  classical
  rw [Finset.sum_coe_sort (locPl G t) fun P => K * (cosExp G P : ℝ) * (vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) : ℝ), dlD]
  refine (Finset.sum_subset Finset.subset_union_left fun P _ hn => ?_).symm
  simp [(depthAt_of_notMem G hn).1]

end Cases

theorem finDatK_of (hA : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ c₁ : ℝ, ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK →
      ∀ (t : T) (Φ : ch.G.Datum) (P : Pl D.host.E), P ∈ locPl ch.G t → ∀ w : PlL D,
        (P ∈ ch.G.pl.W0 ∨ ((Formalism.EigenvalueLevelCeiling.plc P : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal) →
        ∀ z, LossLe w (Tflip ch.W ch.S.B t Φ P z) (c₁ * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * large₂.sc.b * (cosExp ch.G P : ℝ) *
          (vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) : ℝ))) (hB : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ c₂ : ℝ, ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK →
      ∀ (t : T) (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp t Φ, ∀ (P : locPl ch.G t) (w : PlL D),
        ((P : Pl D.host.E) ∈ ch.G.pl.W0 ∨ ((Formalism.EigenvalueLevelCeiling.plc (P : Pl D.host.E) : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal) →
        ∀ c : ℝ, 0 ≤ c → (∀ z, LossLe w (Tflip ch.W ch.S.B t Φ P z) c) →
        ∀ X Y, LossLe w ((ch.S.term t Φ β P).datum X Y) (c + c₂ * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * (cosExp ch.G P : ℝ) *
          (vw w ((resCard (Kw (P : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ))) : FinDatK := by
  obtain ⟨CFa, hA⟩ := hA
  obtain ⟨CFb, hB⟩ := hB
  refine ⟨max CFa CFb, fun CF hCF => ?_⟩
  obtain ⟨c₁, hA⟩ := hA CF ((le_max_left _ _).trans hCF)
  obtain ⟨c₂, hB⟩ := hB CF ((le_max_right _ _).trans hCF)
  refine ⟨max 2 (2 * (max c₁ 0 + max c₂ 0)), fun ε C hC => ?_⟩
  obtain ⟨xa, hA⟩ := hA ε
  obtain ⟨xb, hB⟩ := hB ε
  refine ⟨max xa xb, fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hIs hSc hF => ?_⟩
  have hA := hA D large₂ hε ((le_max_left _ _).trans hx) Γ Pl0 T A Ks R F s ch hIs hSc hF
  have hB := hB D large₂ hε ((le_max_right _ _).trans hx) Γ Pl0 T A Ks R F s ch hIs hSc hF
  have hb : 1 ≤ large₂.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _)
  have hf : (1 : ℝ) ≤ D.R.f := by
    have h1 : D.R.m ≤ D.R.f := D.R.m_le_f
    have h2 := D.R.two_le_m
    exact_mod_cast (show 1 ≤ D.R.f by omega)
  set K0 : ℝ := max c₁ 0 + max c₂ 0 with hK0
  have hK0' : 0 ≤ K0 := add_nonneg (le_max_right _ _) (le_max_right _ _)
  set M : ℝ := (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 with hM
  have hM0 : 0 ≤ M := by positivity
  set K : ℝ := K0 * M * large₂.sc.b with hK
  have hK' : 0 ≤ K := mul_nonneg (mul_nonneg hK0' hM0) (by linarith)
  have hC2 : 2 * K0 ≤ C := (le_max_right _ _).trans hC
  have hC0 : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 2).trans ((le_max_left _ _).trans hC)
  have hsig := ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.sig_nonneg ch.G
  have hlb : 0 ≤ Real.log large₂.sc.b := Real.log_nonneg hb
  have hbound : 2 * K * sig ch.G ≤ D.R.m * bOne ch.G C large₂.sc.b := by
    have h1 : 2 * K0 * sig ch.G ≤ C * D.R.f * (Real.log large₂.sc.b + sig ch.G) := by
      have h2 : 2 * K0 * sig ch.G ≤ C * sig ch.G := mul_le_mul_of_nonneg_right hC2 hsig
      have h3 : C * sig ch.G ≤ C * D.R.f * (Real.log large₂.sc.b + sig ch.G) := by
        have h4 : sig ch.G ≤ D.R.f * (Real.log large₂.sc.b + sig ch.G) := by nlinarith
        calc C * sig ch.G ≤ C * (D.R.f * (Real.log large₂.sc.b + sig ch.G)) := mul_le_mul_of_nonneg_left h4 hC0
          _ = _ := by ring
      linarith
    have h5 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hM0 (by linarith : (0 : ℝ) ≤ large₂.sc.b))
    calc 2 * K * sig ch.G = 2 * K0 * sig ch.G * (M * large₂.sc.b) := by rw [hK]; ring
      _ ≤ C * D.R.f * (Real.log large₂.sc.b + sig ch.G) * (M * large₂.sc.b) := h5
      _ = D.R.m * bOne ch.G C large₂.sc.b := by rw [bOne, hM]; ring
  refine ⟨dlD ch.G K, loss_mono (loss_dlD ch.G hK') hbound, fun t w hAw Φ β hβ x y => ?_⟩
  have key : ∀ v : locPl ch.G t, LossLe w ((ch.S.term t Φ β v).datum (ch.S.colAt t v x) (ch.S.rowAt t v y))
      (K * (cosExp ch.G v : ℝ) * (vw w ((resCard (Kw (v : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ)) := by
    intro v
    have hcase := away_cases ch.G hAw v.2
    set e : ℝ := (cosExp ch.G v : ℝ) with he
    set q : ℝ := (vw w ((resCard (Kw (v : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ) with hq
    have he0 : 0 ≤ e := by positivity
    have hq0 : 0 ≤ q := by
      rw [hq]; exact_mod_cast ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_nat_nonneg w _
    have hX : 0 ≤ M * large₂.sc.b * e * q := mul_nonneg (mul_nonneg (mul_nonneg hM0 (by linarith)) he0) hq0
    set c : ℝ := max c₁ 0 * M * large₂.sc.b * e * q with hc
    have hc0 : 0 ≤ c := by
      have : c = max c₁ 0 * (M * large₂.sc.b * e * q) := by rw [hc]; ring
      rw [this]; exact mul_nonneg (le_max_right _ _) hX
    have h1 : ∀ z, LossLe w (Tflip ch.W ch.S.B t Φ v z) c := fun z => (hA t Φ v v.2 w hcase z).mono (by
      have e1 : c₁ * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * large₂.sc.b * e * q = c₁ * (M * large₂.sc.b * e * q) := by rw [hM]; ring
      have e2 : c = max c₁ 0 * (M * large₂.sc.b * e * q) := by rw [hc]; ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hX)
    refine (hB t Φ β hβ v w hcase c hc0 h1 _ _).mono ?_
    have e3 : c₂ * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * e * q ≤ max c₂ 0 * M * large₂.sc.b * e * q := by
      have hY : 0 ≤ M * e * q := mul_nonneg (mul_nonneg hM0 he0) hq0
      calc c₂ * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * e * q = c₂ * (M * e * q) := by rw [hM]; ring
        _ ≤ max c₂ 0 * (M * e * q) := mul_le_mul_of_nonneg_right (le_max_left _ _) hY
        _ ≤ max c₂ 0 * (M * e * q) * large₂.sc.b := le_mul_of_one_le_right (mul_nonneg (le_max_right _ _) hY) hb
        _ = max c₂ 0 * M * large₂.sc.b * e * q := by ring
    calc c + c₂ * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * e * q ≤ c + max c₂ 0 * M * large₂.sc.b * e * q := by linarith
      _ = K * e * q := by rw [hc, hK, hK0]; ring
  have hP := lossLe_prod Finset.univ _ _ fun v _ => key v
  rw [sum_locPl ch.G t K w] at hP
  exact hP

end GlobalTheory.FunDat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitenessOfClosedSubscheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.KernelRepFinite

theorem isClosedImmersion_pullback_map {S S' : Scheme.{0}} (f : S' ⟶ S) {A B : Over S} (k : A ⟶ B)
    [IsClosedImmersion k.left] : IsClosedImmersion ((Over.pullback f).map k).left := by
  exact MorphismProperty.overPullbackMap (P := @IsClosedImmersion) f k inferInstance

theorem lbIso_diag {S T : Scheme.{0}} (A : Over S) (B : Over T) (β : B.left ⟶ A.left)
    (β₂ : (G2 B).left ⟶ (G2 A).left) (hs : IsSquare β β₂) {P : LB (G2 A).left} (hP : P.IsLB) :
    LBIso ((P.pull β₂).pull (lift (𝟙 B) (𝟙 B)).left) ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull β) := by
  have e₁ : LBIso ((P.pull β₂).pull (lift (𝟙 B) (𝟙 B)).left) (P.pull ((lift (𝟙 B) (𝟙 B)).left ≫ β₂)) :=
    GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP β₂)) _
  have e₂ : LBIso ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull β) (P.pull (β ≫ (lift (𝟙 A) (𝟙 A)).left)) :=
    GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP _)) _
  rw [GlobalTheory.DiagAmpleBC.diag_comp A B β β₂ hs] at e₁
  exact LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) e₁ e₂.symm

theorem isFinite_restrict : ∀ (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → ∀ V₀ : S'.Opens, IsAffineOpen V₀ → Out.RelAmple ((Over.pullback V₀.ι).obj G) ((P.pull (Pdiv.PullbackComparison.pφ₂ V₀.ι G)).pull (lift (𝟙 ((Over.pullback V₀.ι).obj G)) (𝟙 ((Over.pullback V₀.ι).obj G))).left) → ∀ (Z : Over S') (i : Z ⟶ G), IsClosedImmersion i.left → (∀ (T : Over S') (z : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → GlobalTheory.MemKL G (P.pull (lift (𝟙 G) (𝟙 G)).left) (z ≫ i)) → IsFinite (Z.hom ∣_ V₀) := by
  intro S' _ G _ _ P hA hP V₀ hV hRel Z i hi hZ
  haveI : IsNoetherianRing Γ(S', V₀) := IsLocallyNoetherian.component_noetherian ⟨V₀, hV⟩
  let t : Sp Γ(S', V₀) ⟶ V₀.toScheme := hV.isoSpec.inv
  let GV := (Over.pullback V₀.ι).obj G
  let B := (Over.pullback t).obj GV
  have hAV : IsAbelianScheme GV := GlobalTheory.isAbelianScheme_pullback_obj _ G hA
  have hAB : IsAbelianScheme B := GlobalTheory.isAbelianScheme_pullback_obj _ GV hAV
  let PV := P.pull (Pdiv.PullbackComparison.pφ₂ V₀.ι G)
  have hPV : PV.IsLB := pull_isLB hP _
  have h₁ := Pdiv.PullbackComparison.isGrpPullback V₀.ι G
  have h₂ := Pdiv.PullbackComparison.isGrpPullback t GV
  have hRelB : Out.RelAmple B ((PV.pull (Pdiv.PullbackComparison.pφ₂ t GV)).pull (lift (𝟙 B) (𝟙 B)).left) :=
    GlobalTheory.DiagAmpleBC.relAmple_diag_pull _ _ GV hAV PV hPV hRel t B (Pdiv.PullbackComparison.pφ t GV)
      (Pdiv.PullbackComparison.pφ₂ t GV) h₂.1 (Pdiv.PullbackComparison.isSquare t GV)
  obtain ⟨ZL, iL, hiL, hfinL, -, hrep⟩ := GlobalTheory.kernelFiniteFlat_holds _ B hAB _
    (pull_isLB (pull_isLB hPV _) _) hRelB
  let ZV := (Over.pullback V₀.ι).obj Z
  let ZB := (Over.pullback t).obj ZV
  let iV : ZV ⟶ GV := (Over.pullback V₀.ι).map i
  let iB : ZB ⟶ B := (Over.pullback t).map iV
  have hmem : GlobalTheory.MemKL B ((PV.pull (Pdiv.PullbackComparison.pφ₂ t GV)).pull (lift (𝟙 B) (𝟙 B)).left) iB := by
    refine GlobalTheory.memKL_of_push h₂ (pull_isLB hPV _) (pull_isLB (pull_isLB hPV _) _)
      (lbIso_diag GV B _ _ (Pdiv.PullbackComparison.isSquare t GV) hPV) iB ?_
    refine GlobalTheory.memKL_of_push h₁ (pull_isLB hP _) (pull_isLB hPV _)
      (lbIso_diag G GV _ _ (Pdiv.PullbackComparison.isSquare V₀.ι G) hP) _ ?_
    let zz : Over.mk ((ZB.hom ≫ t) ≫ V₀.ι) ⟶ Z :=
      Over.homMk (pullback.fst ZV.hom t ≫ pullback.fst Z.hom V₀.ι) (by
        show (pullback.fst ZV.hom t ≫ pullback.fst Z.hom V₀.ι) ≫ Z.hom = (pullback.snd ZV.hom t ≫ t) ≫ V₀.ι
        rw [Category.assoc, pullback.condition, ← Category.assoc]
        congr 1
        exact pullback.condition)
    have e : ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushPt h₁.1.w (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushPt h₂.1.w iB) = zz ≫ i := by
      apply Over.OverMorphism.ext
      show (iB.left ≫ Pdiv.PullbackComparison.pφ t GV) ≫ Pdiv.PullbackComparison.pφ V₀.ι G =
        (pullback.fst ZV.hom t ≫ pullback.fst Z.hom V₀.ι) ≫ i.left
      simp only [Pdiv.PullbackComparison.pφ]
      rw [Pdiv.PullbackComparison.pullback_map_left_fst' t iV, Category.assoc,
        Pdiv.PullbackComparison.pullback_map_left_fst' V₀.ι i, Category.assoc]
    rw [e]
    apply hZ
    rintro _ ⟨y, rfl⟩
    show (((ZB.hom ≫ t) ≫ V₀.ι).base y) ∈ V₀
    exact (Scheme.Opens.range_ι V₀).subset ⟨(ZB.hom ≫ t).base y, rfl⟩
  obtain ⟨z, hz⟩ := (hrep ZB iB).1 hmem
  haveI : IsClosedImmersion iV.left := isClosedImmersion_pullback_map _ i
  haveI : IsClosedImmersion iB.left := isClosedImmersion_pullback_map _ iV
  have hz' : z.left ≫ iL.left = iB.left := congrArg (fun q => q.left) hz
  haveI : IsClosedImmersion (z.left ≫ iL.left) := by rw [hz']; infer_instance
  haveI : IsClosedImmersion z.left := IsClosedImmersion.of_comp z.left iL.left
  have hZB : IsFinite ZB.hom := by
    rw [← Over.w z]; infer_instance
  have hV' : IsFinite ZV.hom := by
    have ec : ZV.hom = inv (pullback.fst ZV.hom t) ≫ pullback.snd ZV.hom t ≫ t := by
      rw [← pullback.condition, IsIso.inv_hom_id_assoc]
    rw [ec]
    haveI : IsFinite (pullback.snd ZV.hom t) := hZB
    infer_instance
  rw [← (isPullback_morphismRestrict Z.hom V₀).flip.isoPullback_hom_snd]
  haveI : IsFinite (pullback.snd Z.hom V₀.ι) := hV'
  infer_instance

end GlobalTheory.KernelRepFinite
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatIntOfIntegralSchemeGenericPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.IntFlat

theorem flat_of_generic_zero : ∀ {X : Scheme.{0}} [IsIntegral X] (s : X ⟶ Spec (CommRingCat.of ℤ)) (x : X), (s x).asIdeal = ⊥ → Flat s := by
  intro X _ s x hx
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
  refine IsZariskiLocalAtSource.of_openCover (P := @Flat) X.affineOpenCover.openCover fun i => ?_
  let R := X.affineOpenCover.X i
  let j : Spec R ⟶ X := X.affineOpenCover.f i
  have : IsOpenImmersion j := X.affineOpenCover.map_prop i
  change Flat (j ≫ s)
  rcases isEmpty_or_nonempty (Spec R) with h | h
  · infer_instance
  have : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion j
  have : IsDomain R := (affine_isIntegral_iff R).1 this
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (j ≫ s)
  let p0 : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  have hg : genericPoint X ∈ Set.range j :=
    (genericPoint_specializes (j (Classical.arbitrary (Spec R)))).mem_open
      j.isOpenEmbedding.isOpen_range ⟨_, rfl⟩
  obtain ⟨q, hq⟩ := hg
  have h1 : p0 ⤳ q := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  have h2 : j p0 ⤳ x := hq ▸ (h1.map j.continuous) |>.trans (genericPoint_specializes x)
  have h3 : (j ≫ s) p0 ⤳ s x := h2.map s.continuous
  have h4 : ((j ≫ s) p0).asIdeal ≤ ⊥ := hx ▸ (PrimeSpectrum.le_iff_specializes _ _).2 h3
  rw [← hφ] at h4
  have hinj : Function.Injective φ.hom := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro n hn
    have : n ∈ ((Spec.map φ) p0).asIdeal := by
      show n ∈ Ideal.comap φ.hom ⊥
      simp [hn]
    simpa using h4 this
  have e : φ.hom = algebraMap ℤ R := RingHom.ext_int _ _
  have : CharZero R := charZero_of_injective_algebraMap (e ▸ hinj)
  rw [← hφ, HasRingHomProperty.Spec_iff (P := @Flat)]
  rw [e, RingHom.flat_algebraMap_iff]
  infer_instance

end GlobalTheory.IntFlat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBaseIdentityAlongMorphism
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UChart.FromBaseAlong

theorem gm_comp_map {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (f z) ∈ U)
    (a : Γ(X, U)ˣ) :
    Units.map (f.stalkMap z).hom.toMonoidHom (gm g (f z) U a) = gm (f ≫ g) z U a := by
  apply Units.ext
  show (f.stalkMap z).hom (gm g (f z) U a).val = _
  rw [← gs_unit (f ≫ g) z U h, ← gs_unit g (f z) U h, ← gs_pull f g z U h, gs_eq f z (g ⁻¹ᵁ U) h, gs_eq g (f z) U h]
  exact Scheme.Hom.germ_stalkMap_apply f (g ⁻¹ᵁ U) z h _

theorem val_comp_map {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y') (g : Y' ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    Units.map (r.stalkMap z).hom.toMonoidHom (val t g (r z) (fun ψ => J (r ≫ ψ))) = val t (r ≫ g) z J := by
  rw [val_of t (r ≫ g) z J (fun k => J (r ≫ g ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gm_comp_map r g z _ (Set.mem_iInter.2 fun k => hJ (r ≫ g ≫ φ k)) _

theorem fromBase_along : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) (τ₀ : Gens Q) {W₀ : Type} [CommRing W₀] (ιb : W₀ →+* R), FromBase Q τ₀ ιb → ∃ (B₀ : Over (Sp W₀)) (_ : GrpObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (Sp W₀ ⟶ B₀.left)) (τ₁ : ∀ a b : Q.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1])) (β : Q.P.A.left ⟶ B₀.left) (w : LB.Iso Q.P.L (M₀.pull β)), IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback Q.P.A B₀ (spMap ιb) β ∧ w.IsGen ∧ (∀ a, cpt Q a ≫ β = spMap ιb ≫ c₀ a) ∧ (∀ a b, (τ₁ a b).IsGen) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp R) (a b : Q.X) (zz : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι) (J₀ : (Z ⟶ B₀.left) → M₀.ι), Good Q.P.L zz J → Good M₀ zz J₀ → val (τ₀ a b) r zz J = gm (r ≫ cpt Q (a + b)) zz _ (w.s (fun _ => J₀ (r ≫ cpt Q (a + b) ≫ β), J (r ≫ cpt Q (a + b)))) * (gm (r ≫ cpt Q a) zz _ (w.s (fun _ => J₀ (r ≫ cpt Q a ≫ β), J (r ≫ cpt Q a))))⁻¹ * (gm (r ≫ cpt Q b) zz _ (w.s (fun _ => J₀ (r ≫ cpt Q b ≫ β), J (r ≫ cpt Q b))))⁻¹ * gm (r ≫ cpt Q 0) zz _ (w.s (fun _ => J₀ (r ≫ cpt Q 0 ≫ β), J (r ≫ cpt Q 0))) * val (τ₁ a b) (r ≫ spMap ιb) zz J₀ := by
  intro R _ _ Q τ₀ W₀ _ ιb ⟨B₀, i, M₀, c₀, τ₁, β, w, h₁, h₂, h₃, h₄, h₅, h₆, h⟩
  refine ⟨B₀, i, M₀, c₀, τ₁, β, w, h₁, h₂, h₃, h₄, h₅, h₆, fun Z r a b zz J J₀ hJ hJ₀ => ?_⟩
  have e := congrArg (Units.map (r.stalkMap zz).hom.toMonoidHom)
    (h a b (r zz) (fun ψ => J (r ≫ ψ)) (fun ψ => J₀ (r ≫ ψ)) (fun ψ => hJ (r ≫ ψ)) (fun ψ => hJ₀ (r ≫ ψ)))
  have g : ∀ x : Q.X, Units.map (r.stalkMap zz).hom.toMonoidHom
      (gm (cpt Q x) (r zz) _ (w.s (fun _ => J₀ (r ≫ cpt Q x ≫ β), J (r ≫ cpt Q x)))) =
      gm (r ≫ cpt Q x) zz _ (w.s (fun _ => J₀ (r ≫ cpt Q x ≫ β), J (r ≫ cpt Q x))) := fun x =>
    gm_comp_map r (cpt Q x) zz _
      (show cpt Q x (r zz) ∈ (M₀.pull β).U (fun _ => J₀ (r ≫ cpt Q x ≫ β)) ⊓ Q.P.L.U (J (r ≫ cpt Q x)) from
        ⟨Set.mem_iInter.2 fun _ => hJ₀ (r ≫ cpt Q x ≫ β), hJ (r ≫ cpt Q x)⟩) _
  have v₀ := val_comp_map (τ₀ a b) r (𝟙 _) zz hJ
  have v₁ := val_comp_map (τ₁ a b) r (spMap ιb) zz hJ₀
  rw [Category.comp_id] at v₀
  rw [map_mul, map_mul, map_mul, map_mul, map_inv, map_inv] at e
  exact v₀.symm.trans (e.trans (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·)
    (g (a + b)) (congrArg (·⁻¹) (g a))) (congrArg (·⁻¹) (g b))) (g 0)) v₁))

end GlobalTheory.UChart.FromBaseAlong
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBaseWith
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

noncomputable section

namespace GlobalTheory.USep.EvG

def FromBaseWith {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) (τ₀ : GlobalTheory.UChart.Gens Q) {W₀ : Type} [CommRing W₀]
    (ιb : W₀ →+* V) (B₀ : Over (Sp W₀)) [GrpObj B₀] (M₀ : LB B₀.left) (c₀ : Q.X → (Sp W₀ ⟶ B₀.left))
    (τ₁ : ∀ a b : Q.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
    (β : Q.P.A.left ⟶ B₀.left) (w : LB.Iso Q.P.L (M₀.pull β)) : Prop :=
  IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback Q.P.A B₀ (spMap ιb) β ∧ w.IsGen ∧
    (∀ a, GlobalTheory.UChart.cpt Q a ≫ β = spMap ιb ≫ c₀ a) ∧ (∀ a b, (τ₁ a b).IsGen) ∧
    ∀ (a b : Q.X) zz (J : (Sp V ⟶ Q.P.A.left) → Q.P.L.ι) (J₀ : (Sp V ⟶ B₀.left) → M₀.ι),
      Good Q.P.L zz J → Good M₀ zz J₀ →
      val (τ₀ a b) (𝟙 (Sp V)) zz J =
        gm (GlobalTheory.UChart.cpt Q (a + b)) zz _
            (w.s (fun _ => J₀ (GlobalTheory.UChart.cpt Q (a + b) ≫ β), J (GlobalTheory.UChart.cpt Q (a + b)))) *
        (gm (GlobalTheory.UChart.cpt Q a) zz _ (w.s (fun _ => J₀ (GlobalTheory.UChart.cpt Q a ≫ β), J (GlobalTheory.UChart.cpt Q a))))⁻¹ *
        (gm (GlobalTheory.UChart.cpt Q b) zz _ (w.s (fun _ => J₀ (GlobalTheory.UChart.cpt Q b ≫ β), J (GlobalTheory.UChart.cpt Q b))))⁻¹ *
        gm (GlobalTheory.UChart.cpt Q 0) zz _ (w.s (fun _ => J₀ (GlobalTheory.UChart.cpt Q 0 ≫ β), J (GlobalTheory.UChart.cpt Q 0))) *
        val (τ₁ a b) (spMap ιb) zz J₀

theorem fromBase_iff {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) (τ₀ : GlobalTheory.UChart.Gens Q) {W₀ : Type}
    [CommRing W₀] (ιb : W₀ →+* V) :
    GlobalTheory.UChart.FromBase Q τ₀ ιb ↔ ∃ (B₀ : Over (Sp W₀)) (_ : GrpObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : Q.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : Q.P.A.left ⟶ B₀.left) (w : LB.Iso Q.P.L (M₀.pull β)), FromBaseWith Q τ₀ ιb B₀ M₀ c₀ τ₁ β w :=
  Iff.rfl

abbrev gwx {X' X Y : Scheme.{0}} {L' : LB X'} {L : LB X} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F)) (y : Y)
    (J : (Y ⟶ X') → L'.ι) (J₀ : (Y ⟶ X) → L.ι) (x : Y ⟶ X') : (Y.presheaf.stalk y)ˣ :=
  gw w x y (J₀ (x ≫ F)) (J x)

end GlobalTheory.USep.EvG
end
end

