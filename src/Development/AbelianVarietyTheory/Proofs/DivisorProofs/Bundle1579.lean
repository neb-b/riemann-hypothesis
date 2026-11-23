module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1563
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishing
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0001
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0002
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsEvalNeZeroOfTotalDegreeLt
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.FiniteDetAddSmulOneEqZero
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1294
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1289
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuAllData
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
public import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
public import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle0001
public import Formalism.PolynomialDimension.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeDeterminantLineTwoHermitianLattices
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1556
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatIntegrableAaVacOfConductor
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.FunObj

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

section Gen
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem apow_zpow (x : kˣ) (n : ℤ) (z : ℂ) : apow (x ^ n) z = apow x (n * z) := by
  induction n using Int.induction_on with
  | zero => simp [apow, nabs_one]
  | succ n ih =>
    rw [_root_.zpow_add_one, apow_mul, ih, ← apow_add]
    congr 1; push_cast; ring
  | pred n ih =>
    rw [_root_.zpow_sub_one, apow_mul, ih, apow_inv, ← apow_add]
    congr 1; push_cast; ring

theorem prod_apow {α : Type*} (x : kˣ) (f : α → ℂ) (l : List α) :
    (l.map fun b => apow x (f b)).prod = apow x (l.map f).sum := by
  induction l with
  | nil => simp [apow]
  | cons b l ih => rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.sum_cons, apow_add]

end Gen

theorem even_mul_add_odd (a d : ℕ) (hd : Odd d) : Even (a * (a + d)) := by
  rcases Nat.even_or_odd a with h | h
  · exact h.mul_right _
  · exact (h.add_odd hd).mul_left _

theorem even_sum_of_even {α : Type*} (P : α → ℕ) : ∀ l : List α, (∀ b ∈ l, Even (P b)) → Even (l.map P).sum
  | [], _ => by simp
  | b :: l, h => by
    rw [List.map_cons, List.sum_cons]
    exact (h b List.mem_cons_self).add (even_sum_of_even P l fun c hc => h c (List.mem_cons_of_mem _ hc))

variable {D : D7}

theorem mem_oppositePath {m : ℕ} {b : Edge} : b ∈ oppositePath m ↔ (∃ i < m, b = .ex i m) ∨ ∃ j < m, b = .theta m j := by
  simp only [oppositePath, List.mem_append, List.mem_map, List.mem_range, List.mem_reverse]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr ⟨j, hj, rfl⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr ⟨j, hj, rfl⟩

theorem even_rank_mul_path (w : Pl D.host.E) {b : Edge} (hb : b ∈ oppositePath (bareGrid w).m) :
    Even ((bareGrid w).rank b.src * (bareGrid w).rank b.tgt) := by
  rcases mem_oppositePath.1 hb with ⟨i, -, rfl⟩ | ⟨j, -, rfl⟩
  · have := even_mul_add_odd ((bareGrid w).rank (i, (bareGrid w).m)) (sLen D) (odd_sLen D)
    convert this using 2
    simp only [Grid.rank, bareGrid]; ring
  · have := even_mul_add_odd ((bareGrid w).rank ((bareGrid w).m, j)) D.R.t D.R.t_odd
    rw [mul_comm]
    convert this using 2
    simp only [Grid.rank, bareGrid]; ring

theorem rank_path_le (w : Pl D.host.E) {b : Edge} (hb : b ∈ oppositePath (bareGrid w).m) :
    (bareGrid w).rank b.src ≤ bigN D ∧ (bareGrid w).rank b.tgt ≤ bigN D := by
  have hr : D.R.r + 1 = D.R.k + D.R.m := by unfold Ranks.r; have := D.R.two_le_m; omega
  have key : ∀ i j, i ≤ D.R.m → j ≤ D.R.m → (bareGrid w).rank (i, j) ≤ bigN D := fun i j hi hj => by
    simp only [Grid.rank, bareGrid, bigN]
    have h1 := Nat.mul_le_mul_right D.R.t hj
    have h2 := Nat.mul_le_mul_right (sLen D) hi
    nlinarith
  rcases mem_oppositePath.1 hb with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · exact ⟨key _ _ hi.le le_rfl, key _ _ hi le_rfl⟩
  · exact ⟨key _ _ le_rfl hj, key _ _ le_rfl hj.le⟩

theorem path_apow_pow (w : Pl D.host.E) : ∃ n : ℤ, ((oppositePath D.R.m).map fun b =>
    apow (genAt w D.host.AAbar / genAt w D.host.AA)
      (((bareGrid w).rank b.src * (bareGrid w).rank b.tgt : ℕ) / 4)).prod =
      (resCard (Kw w) : ℂ) ^ ((n : ℂ) / 2) ∧
    |n| ≤ (D.R.m : ℤ) ^ 3 * (bigN D : ℤ) ^ 2 *
      (|FractionalIdeal.count D.host.E w D.host.AA| + |FractionalIdeal.count D.host.E w D.host.AAbar|) := by
  set a := FractionalIdeal.count D.host.E w D.host.AA
  set a' := FractionalIdeal.count D.host.E w D.host.AAbar
  set P : Edge → ℕ := fun b => (bareGrid w).rank b.src * (bareGrid w).rank b.tgt
  have hm : (bareGrid w).m = D.R.m := rfl
  have hev : Even ((oppositePath D.R.m).map P).sum := even_sum_of_even P _ fun b hb => even_rank_mul_path w (hm ▸ hb)
  obtain ⟨S, hS⟩ := hev
  have hsum : ((oppositePath D.R.m).map fun b => ((P b : ℕ) : ℂ) / 4).sum = ((((oppositePath D.R.m).map P).sum : ℕ) : ℂ) / 4 := by
    induction (oppositePath D.R.m) with
    | nil => simp
    | cons b l ih => simp only [List.map_cons, List.sum_cons, ih]; push_cast; ring
  refine ⟨(a - a') * S, ?_, ?_⟩
  · rw [prod_apow, hsum, genAt, genAt, div_eq_mul_inv, ← _root_.zpow_sub, apow_zpow, (isUnif_unifAt w).apow_eq, hS]
    congr 1; push_cast; ring
  · have hle : ((oppositePath D.R.m).map P).sum ≤ ((oppositePath D.R.m).map P).length • (bigN D ^ 2) := by
      refine List.sum_le_card_nsmul ((oppositePath D.R.m).map P) _ fun x hx => ?_
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
      obtain ⟨h1, h2⟩ := rank_path_le w (hm ▸ hb)
      simpa [P, sq] using Nat.mul_le_mul h1 h2
    have hlen : (oppositePath D.R.m).length = 2 * D.R.m := by simp [oppositePath]; ring
    rw [List.length_map, hlen, smul_eq_mul] at hle
    have hS' : (S : ℤ) ≤ D.R.m * bigN D ^ 2 := by
      have : S + S ≤ 2 * D.R.m * bigN D ^ 2 := hS ▸ hle
      have : S ≤ D.R.m * bigN D ^ 2 := by nlinarith
      exact_mod_cast this
    have hm1 : (1 : ℤ) ≤ D.R.m := by have := D.R.two_le_m; omega
    have hN : (0 : ℤ) ≤ bigN D := by positivity
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ S)]
    have h3 : |a - a'| ≤ |a| + |a'| := abs_sub _ _
    have h4 : (D.R.m : ℤ) * bigN D ^ 2 ≤ D.R.m ^ 3 * bigN D ^ 2 := by
      have : (D.R.m : ℤ) ≤ D.R.m ^ 3 := by nlinarith [mul_le_mul hm1 hm1 zero_le_one (by linarith)]
      exact mul_le_mul_of_nonneg_right this (by positivity)
    calc |a - a'| * (S : ℤ) ≤ (|a| + |a'|) * (D.R.m * bigN D ^ 2) :=
          mul_le_mul h3 hS' (by positivity) (by positivity)
      _ ≤ (|a| + |a'|) * (D.R.m ^ 3 * bigN D ^ 2) := mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = _ := by ring

theorem isLocallyConstant_aaVac (w : Pl D.host.E) : IsLocallyConstant (aaVac w) := by
  classical
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  set c : Kw w := (((genAt w D.host.AA)⁻¹ : (Kw w)ˣ) : Kw w)
  have h : ∀ᶠ y in nhds x, ∀ b ∈ (oppositePath (bareGrid w).m).toFinset, ∀ i j, c * (y b i j - x b i j) ∈ 𝒪[Kw w] := by
    refine (Filter.eventually_all_finset _).2 fun b _ => Filter.eventually_all.2 fun i =>
      Filter.eventually_all.2 fun j => ?_
    have hc : Continuous fun y : (bareGrid w).Args => c * (y b i j - x b i j) :=
      continuous_const.mul (((continuous_apply b).matrix_elem i j).sub continuous_const)
    exact (Model.isOpen_int.preimage hc).mem_nhds (by simp)
  filter_upwards [h] with y hy
  have key : ∀ b ∈ oppositePath (bareGrid w).m, ∀ i j, (c * y b i j ∈ 𝒪[Kw w] ↔ c * x b i j ∈ 𝒪[Kw w]) :=
    fun b hb i j => by
      have hd := hy b (List.mem_toFinset.2 hb) i j
      have e : c * y b i j = c * x b i j + c * (y b i j - x b i j) := by ring
      rw [e]
      exact ⟨fun h1 => by simpa using sub_mem h1 hd, fun h1 => add_mem h1 hd⟩
  have hs : (y ∈ {z : (bareGrid w).Args | ∀ b ∈ oppositePath (bareGrid w).m, ∀ i j, c * z b i j ∈ 𝒪[Kw w]}) ↔
      (x ∈ {z : (bareGrid w).Args | ∀ b ∈ oppositePath (bareGrid w).m, ∀ i j, c * z b i j ∈ 𝒪[Kw w]}) := by
    exact forall₂_congr fun b hb => forall₂_congr fun i j => key b hb i j
  unfold aaVac
  by_cases hx : x ∈ {z : (bareGrid w).Args | ∀ b ∈ oppositePath (bareGrid w).m, ∀ i j, c * z b i j ∈ 𝒪[Kw w]}
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hs.2 hx)]; rfl
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt hs.1 hx)]

theorem hasCompactSupport_aaVac (w : Pl D.host.E) (ψ : AddChar (Kw w) Circle) (keep : Bool) (g : (bareGrid w).VertexGroup)
    (x : ColArgs (bareGrid w)) (y : RowArgs (bareGrid w)) :
    HasCompactSupport (flatIntegrand one_le_sLen ψ (moved (bareGrid w) keep g (aaVac w)) x y) := by
  classical
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := Kw w)
  choose a b c h using exists_fill_entry (G := bareGrid w) one_le_sLen x y
  set u : (Kw w)ˣ := (genAt w D.host.AA)⁻¹
  choose K hK hK' using fun j : Fin ((bareGrid w).m - 1) => exists_isCompact_of_mul_mem
    (SplitFlip.diagGL (fun _ => u) * (Assignment.one.read (g (Edge.theta (bareGrid w).m j).tgt))⁻¹)
    (Assignment.one.read (g (Edge.theta (bareGrid w).m j).src))
  refine HasCompactSupport.intro (K := Set.univ.pi fun j => Set.univ.pi fun rs =>
    (fun M => M (a j rs) (b j rs) - c j rs) '' K j) (isCompact_univ_pi fun j => isCompact_univ_pi fun rs =>
      (hK j).image ((continuous_id.matrix_elem _ _).sub continuous_const)) fun v hv => ?_
  have h0 : aaVac w ((bareGrid w).moveArgs .one g (fill one_le_sLen x y v)) = 0 := by
    by_contra hne
    have hmem := Set.mem_of_indicator_ne_zero hne
    refine hv fun j _ rs _ => ⟨_, hK' j _ ?_, (h j rs v).symm⟩
    refine mem_matLat_stdLat.2 fun r s => ?_
    have hb : Edge.theta (bareGrid w).m j ∈ oppositePath (bareGrid w).m := by
      have := j.2; simp [oppositePath]; omega
    have := hmem _ hb r s
    simp only [Grid.moveArgs] at this
    simpa [Units.val_mul, diagGL_val, Matrix.mul_assoc, Matrix.diagonal_mul, u] using this
  simp [flatIntegrand, moved, Grid.pathAct, h0]

theorem flatIntegrable_aaVac (w : Pl D.host.E) {ψ : AddChar (Kw w) Circle} (hψ : Continuous ψ) :
    FlatIntegrable (G := bareGrid w) one_le_sLen ψ (unitVol w) (aaVac w) := by
  classical
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := Kw w)
  have := (isUnitVol_unitVol w).1
  intro g x y
  unfold varsVol
  have hm : Continuous ((bareGrid w).moveArgs .one g) := continuous_pi fun b =>
    (continuous_const.matrix_mul (continuous_apply b)).matrix_mul continuous_const
  have hc : Continuous (flatIntegrand one_le_sLen ψ (moved (bareGrid w) true g (aaVac w)) x y) :=
    (continuous_const.mul (continuous_const.mul
      ((isLocallyConstant_aaVac w).continuous.comp (hm.comp (continuous_fill one_le_sLen x y))))).mul
      (continuous_subtype_val.comp (hψ.comp (continuous_phase x).neg))
  exact hc.integrable_of_hasCompactSupport (hasCompactSupport_aaVac w ψ true g x y)

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)

theorem aaScalar_eq_pow (w : Pl D.host.E) (hψ : HasConductor (psiAt W w) (genAt w D.host.AA * genAt w D.host.AAbar)) :
    ∃ n : ℤ, aaScalar W w = (resCard (Kw w) : ℂ) ^ ((n : ℂ) / 2) ∧
    |n| ≤ 16 * ((D.R.m : ℤ) ^ 3 * (bigN D : ℤ) ^ 2 *
      (|FractionalIdeal.count D.host.E w D.host.AA| + |FractionalIdeal.count D.host.E w D.host.AAbar|)) := by
  obtain ⟨n1, h1, b1⟩ := _root_.GlobalTheory.FunObj.AaCoef.aaTerm_coef_eq_zpow W w
  obtain ⟨n2, h2, b2⟩ := _root_.GlobalTheory.OriginBox.aaTerm_datum_origin W w fun a ha => hψ.eq_one ha
  obtain ⟨n3, h3, b3⟩ := path_apow_pow w
  have hq : (resCard (Kw w) : ℂ) ≠ 0 := by
    have : 1 < resCard (Kw w) := Finite.one_lt_card; exact_mod_cast (show resCard (Kw w) ≠ 0 by omega)
  refine ⟨2 * n1 + n2 + n3, ?_, ?_⟩
  · have e1 : (((resCard (Kw w) : ℚ) ^ n1 : ℚ) : ℂ) = (resCard (Kw w) : ℂ) ^ (((2 * n1 : ℤ) : ℂ) / 2) := by
      rw [Rat.cast_zpow, Rat.cast_natCast, ← Complex.cpow_intCast]; congr 1; push_cast; ring
    rw [aaScalar, h1, h2, h3, e1, ← Complex.cpow_add _ _ hq, ← Complex.cpow_add _ _ hq]
    congr 1; push_cast; ring
  · have hB : 0 ≤ (D.R.m : ℤ) ^ 3 * (bigN D : ℤ) ^ 2 *
        (|FractionalIdeal.count D.host.E w D.host.AA| + |FractionalIdeal.count D.host.E w D.host.AAbar|) := by positivity
    calc |2 * n1 + n2 + n3| ≤ 2 * |n1| + |n2| + |n3| := by
          have := abs_add_le (2 * n1 + n2) n3; have := abs_add_le (2 * n1) n2
          rw [abs_mul, abs_two] at *; linarith
      _ ≤ _ := by linarith

theorem sAA_facts {U : Set T} (S : GridChoice W U)
    (hψ : ∀ w ∈ S.PA, HasConductor (psiAt W w) (genAt w D.host.AA * genAt w D.host.AAbar)) :
    S.sAA ≠ 0 ∧ (∃ r : ℝ, 0 < r ∧ S.sAA = r) ∧ ∃ Q : ℚ, S.sAA ^ 2 = Q := by
  classical
  have hw : ∀ w ∈ S.PA, ∃ n : ℤ, aaScalar W w = (resCard (Kw w) : ℂ) ^ ((n : ℂ) / 2) :=
    fun w hw => (aaScalar_eq_pow W w (hψ w hw)).imp fun _ h => h.1
  choose! n hn using hw
  have e : ∀ w ∈ S.PA, aaScalar W w = (((resCard (Kw w) : ℝ) ^ ((n w : ℝ) / 2) : ℝ) : ℂ) := fun w hw => by
    rw [hn w hw, Complex.ofReal_cpow (Nat.cast_nonneg _)]; push_cast; rfl
  have hr : S.sAA = ((∏ w ∈ S.PA, (resCard (Kw w) : ℝ) ^ ((n w : ℝ) / 2) : ℝ) : ℂ) := by
    rw [GridChoice.sAA, Complex.ofReal_prod]; exact Finset.prod_congr rfl e
  have hpos : 0 < ∏ w ∈ S.PA, (resCard (Kw w) : ℝ) ^ ((n w : ℝ) / 2) :=
    Finset.prod_pos fun w _ => Real.rpow_pos_of_pos (by have : 1 < resCard (Kw w) := Finite.one_lt_card; positivity) _
  have hsq : (∏ w ∈ S.PA, (resCard (Kw w) : ℝ) ^ ((n w : ℝ) / 2)) ^ 2 =
      ((∏ w ∈ S.PA, (resCard (Kw w) : ℚ) ^ n w : ℚ) : ℝ) := by
    rw [← Finset.prod_pow, Rat.cast_prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), Rat.cast_zpow, Rat.cast_natCast, ← Real.rpow_intCast]
    congr 1; push_cast; ring
  refine ⟨by rw [hr]; exact_mod_cast hpos.ne', ⟨_, hpos, hr⟩, ∏ w ∈ S.PA, (resCard (Kw w) : ℚ) ^ n w, ?_⟩
  rw [hr, ← Complex.ofReal_pow, hsq, Complex.ofReal_ratCast]

theorem flatIntegrable_aaVac_of_conductor (w : Pl D.host.E)
    (hψ : HasConductor (psiAt W w) (genAt w D.host.AA * genAt w D.host.AAbar)) :
    FlatIntegrable (G := bareGrid w) one_le_sLen (psiAt W w) (unitVol w) (aaVac w) :=
  flatIntegrable_aaVac w hψ.continuous

end GlobalTheory.FunObj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedDictionaryBound
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LevGeo.MassLev

theorem mass_components_le : GlobalTheory.UCls.MassBound → GlobalTheory.UCls.TorusBound → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (x0 : ∀ k, Frame ((U σ).X k).Ψ D.R.r) (FF : ∀ k, Set (ReciprocityTheory.L2DbarEstimates.V (nd ((U σ).X k)))), (∀ k, IsOrth ((U σ).X k) (x0 k) ∧ IsFundSet ((U σ).X k) (x0 k) (FF k)) → ∑ k, muF ((U σ).X k) (x0 k) (FF k) ≤ ENNReal.ofReal (massLev D.host.E D.R.r l.M) := by
  intro hMB hTB D j H Dw l Xo c U dict hL σ hσ x0 FF hF
  obtain ⟨G, Λ, g, Λk, u, hSD, hk, hdist⟩ := _root_.GlobalTheory.LevGeo.Reps.components_double_cosets D j H Dw l Xo c U dict hL σ hσ
  have hX' := fun k => _root_.GlobalTheory.PrincData.exists_princ_data D.host.E D.R.r l.M ((U σ).X k) (Λk k) l.three_le (hk k).2.2.2.1 (hk k).2.2.2.2.1
  choose X' hX'Gm hX'Ψ hX'p0 hX'Λ hX'Γ using hX'
  have hfm : ∀ k, ∃ y, IsOrth (X' k) y ∧ ∃ FF', IsFundSet (X' k) y FF' ∧ muF (X' k) y FF' < ⊤ :=
    fun k => GlobalTheory.finMu_all_data D.host.E D.R.r (X' k)
  choose y hy FF' hFF' _ using hfm
  have hμ : ∀ k, muF ((U σ).X k) (x0 k) (FF k) = muF (X' k) (y k) (FF' k) := by
    intro k
    obtain ⟨hGm, -, -, -, -, hgram, hfw, hbw⟩ := hk k
    refine _root_.GlobalTheory.CovolConj.muF_eq_of_conj D.host.E D.R.r ((U σ).X k) (X' k) (hX'Ψ k) (u k) (x0 k) (y k) (FF k) (FF' k)
      (hX'Gm k) (hX'p0 k) (by rw [hGm]; exact hgram) ?_ ?_ (hF k).1 (hy k) (hF k).2 (hFF' k)
    · intro γ hγ
      obtain ⟨γ', hγ', hc⟩ := hfw γ hγ
      exact ⟨γ', (hX'Γ k γ').2 (by rw [hGm]; exact hγ'), hc⟩
    · intro γ' hγ'
      have := (hX'Γ k γ').1 hγ'
      rw [hGm] at this
      exact hbw γ' this
  have hunf := hL.unf σ hσ
  set Ψ : Finset (D.host.E →+* ℂ) := Finset.univ.filter (fun τ => τ (H.rt : D.host.E) = H.rt0) with hΨdef
  have hΨ : ∀ k, (X' k).Ψ = Ψ := by
    intro k
    rw [hX'Ψ k]
    ext τ
    rw [(hunf.2.1 k).2 τ, hΨdef, Finset.mem_filter]
    simp
  rw [Finset.sum_congr rfl (fun k _ => hμ k)]
  set e := Fintype.equivFin (U σ).Comp
  rw [← e.symm.sum_comp]
  have hr : 2 ≤ D.R.r := Formalism.L2.Geo.two_le_r D
  have hTor := hTB D.host.E D.R.r l.M G Λ (by omega) (by have := l.three_le; omega) H.unram hSD
  exact hMB D.host.E D.R.r l.M _ _ G Λ Ψ (fun i => X' (e.symm i)) (fun i => g (e.symm i)) (fun i => y (e.symm i))
    (fun i => FF' (e.symm i)) hr l.three_le H.unram hSD hTor (fun i => (hk (e.symm i)).2.1)
    (fun i i' h => e.symm.injective (hdist _ _ h))
    (fun i => ⟨(hX'Gm _).trans (hk _).1, hΨ _, by rw [hX'Λ]; exact (hk _).2.2.1, fun γ => by rw [hX'Λ, hX'Γ, (hk _).1],
      hy _, hFF' _⟩)

end GlobalTheory.LevGeo.MassLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDeterminantSmulStandardBasisInverseFrames
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

theorem GlobalTheory.DefPt.det_gramPl_smul_single : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (eqv : ι ≃ Fin n) (Y : (K →+* ℂ) → Matrix ι ι ℂ), (∀ σ, (Y σ).det ≠ 0) → ∀ (t : K) (v : InfinitePlace K), (Formalism.HN.gramPl (Pi.basisFun K ι) (fun v => (Y v.embedding)⁻¹) v (fun k => t • (Pi.single (eqv.symm k) 1 : ι → K))).det.re = ‖v.embedding t‖ ^ (2 * n) * ‖(Y v.embedding).det‖ ^ 2 := by
  intro K _ _ _ ι _ _ n eqv Y hY t v
  have hinv : ((Y v.embedding)⁻¹)⁻¹ = Y v.embedding :=
    Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.2 (hY _))
  have hf : ∀ a : ι, Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K ι) (fun v => (Y v.embedding)⁻¹) v
      (t • (Pi.single a 1 : ι → K)) = fun i => v.embedding t * Y v.embedding i a := by
    intro a
    funext i
    simp only [Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt, hinv, Matrix.mulVec, dotProduct, Pi.basisFun_repr,
      Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single a]
    · simp [mul_comm]
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  have hg : Formalism.HN.gramPl (Pi.basisFun K ι) (fun v => (Y v.embedding)⁻¹) v
      (fun k => t • (Pi.single (eqv.symm k) 1 : ι → K)) =
      ((‖v.embedding t‖ ^ 2 : ℝ) : ℂ) • Matrix.reindex eqv eqv ((Y v.embedding)ᴴ * Y v.embedding) := by
    ext a b
    simp only [Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, hf, Matrix.of_apply, Matrix.smul_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Pi.star_apply,
      smul_eq_mul, Finset.mul_sum, star_mul']
    refine Finset.sum_congr rfl fun i _ => ?_
    have := Complex.conj_mul' (v.embedding t)
    push_cast
    rw [← this]
    simp only [RCLike.star_def]
    ring
  rw [hg, Matrix.det_smul, Matrix.det_reindex_self, Matrix.det_mul, Matrix.det_conjTranspose, Fintype.card_fin,
    RCLike.star_def, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.ofReal_re, ← pow_mul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HBdNonneg
section
noncomputable section

open Formalism.BasicNotions

namespace GlobalTheory.ClassCount

def hBd (D : D7) (n : ℕ) : ℝ := (12 * (D.R.f : ℝ) ^ 2 * (n : ℝ) ^ 4 * D.host.rdE ^ 2) ^ (6 * D.R.f * n ^ 2)

theorem hBd_mono {D : D7} {n N : ℕ} (hn : n ≤ N) (h1 : 1 ≤ 12 * (D.R.f : ℝ) ^ 2 * (N : ℝ) ^ 4 * D.host.rdE ^ 2)
    (hrd : 0 ≤ D.host.rdE) : hBd D n ≤ hBd D N := by
  unfold hBd
  have hb : 12 * (D.R.f : ℝ) ^ 2 * (n : ℝ) ^ 4 * D.host.rdE ^ 2 ≤ 12 * (D.R.f : ℝ) ^ 2 * (N : ℝ) ^ 4 * D.host.rdE ^ 2 := by
    have : (n : ℝ) ^ 4 ≤ (N : ℝ) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hn) 4
    gcongr
  calc _ ≤ (12 * (D.R.f : ℝ) ^ 2 * (N : ℝ) ^ 4 * D.host.rdE ^ 2) ^ (6 * D.R.f * n ^ 2) :=
        pow_le_pow_left₀ (by positivity) hb _
    _ ≤ _ := pow_le_pow_right₀ h1 (by gcongr)

end GlobalTheory.ClassCount

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarFundamentalDomainRightTranslateUnitary
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.Grid Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Mult MeasureTheory

theorem GlobalTheory.RightTranslateFundDomain.haar_and_fundDomain : ∀ {D : D7} {V : HSp D} (m : MeasureTheory.Measure (GA D V)) (fd : Set (GA D V)) (g : GA D V), m.IsHaarMeasure → MeasureTheory.IsFundamentalDomain (GQ V) fd m → (m.map (fun x => x * g⁻¹)).IsHaarMeasure ∧ MeasureTheory.IsFundamentalDomain (GQ V) ((fun x => x * g) ⁻¹' fd) (m.map (fun x => x * g⁻¹)) := by
  intro D V m fd g hm hfd
  have hmeas : Measurable (fun x : GA D V => x * g⁻¹) := measurable_mul_const g⁻¹
  refine ⟨?_, ?_⟩
  · have h := Measure.isHaarMeasure_map_mul_right m g⁻¹
    exact h
  · refine hfd.preimage_of_equiv (e := id) ?_ Function.bijective_id ?_
    · refine ⟨(measurable_mul_const g).aemeasurable, ?_⟩
      rw [Measure.map_map (measurable_mul_const g) hmeas]
      have : ((fun x : GA D V => x * g) ∘ fun x => x * g⁻¹) = id := by
        funext x; simp
      rw [this, Measure.map_id]
    · intro h x
      show (h • x) * g = h • (x * g)
      simp [Submonoid.smul_def, Subgroup.smul_def, mul_assoc]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeVacuumFnHasCompactSupportStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergLatticeVacuumFn_hasCompactSupport : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {κ : Type} [Fintype κ]
    (ψ₀ : AddChar (Fv F v) ℂ) (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v)))
    (χ : (κ → Fv F v) × (κ → Fv F v) → ℂ) (x₀ : κ → Fv F v),
    IsCompact (Λ : Set ((κ → Fv F v) × (κ → Fv F v))) → HasCompactSupport (GlobalTheory.HeisLatVac.vacFn ψ₀ Λ χ x₀) := by
  first | exact @GlobalTheory.HeisLatVac.vacFn_hasCompactSupport_of_isCompact | exact GlobalTheory.HeisLatVac.vacFn_hasCompactSupport_of_isCompact | (intros; apply GlobalTheory.HeisLatVac.vacFn_hasCompactSupport_of_isCompact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularFrameChangeBasechangeIntegralAtCompletStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triangular_frameChange_basechange_integral_at_completion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∃ (ρV : 𝓞 K →+* T.V) (_ : (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K)) (G : GlobalTheory.CM.PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (n : SABMap G.t B.t (spMap ρV)) (n' : SABMap t' t₀ (spMap iK)) (m1' : SABMap t' Xo.univ.t yT.x) (m2' : SABMap t' G.t (spMap (algebraMap T.V T.Fr))) (_ : m1'.φ = n'.φ ≫ m1.φ) (_ : m2'.φ ≫ n.φ = n'.φ ≫ m2.φ) (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr) (td : Ix Dw → T.Frˣ) (y' : FrPt Xo c T.Fr), (∀ σ i j, i < j → C σ i j = 0) ∧ (∀ σ i, C σ i i = (td (some ⟨σ, i⟩) : T.Fr)) ∧ FrChg C (td none : T.Fr) yT y' ∧ GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F K)) m1' m2' y'.u ∧ Integral T (iK.comp (algebraMap c.F K)) y' := by
  first | exact @GlobalTheory.PtDegInt.intPt | exact GlobalTheory.PtDegInt.intPt | (intros; apply GlobalTheory.PtDegInt.intPt <;> assumption)
end

