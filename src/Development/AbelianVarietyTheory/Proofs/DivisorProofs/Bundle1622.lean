module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1597
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0264
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeUnitNormSqNonneg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1596
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1495
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateInclusionRaynaudExtensionAlgebraicPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1598

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerExtensionStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_intertwiner_extension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ)
    (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁)
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))))
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e →
      ∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0 := by
  first | exact @GlobalTheory.ThK.EvNeZero.exists_ne_zero | exact GlobalTheory.ThK.EvNeZero.exists_ne_zero | (intros; apply GlobalTheory.ThK.EvNeZero.exists_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingsCurveFieldAboveFiniteNonempty
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.KerConjMean

theorem fld_finiteDimensional (D : D7) (hI : GlobalTheory.NormSum.Inp D) (δ t0 : ℂ) (hc : Crv D D.host.ccK δ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lat D δ) t0) : FiniteDimensional ℚ (fld D δ t0) := by
  obtain ⟨hdata, htor⟩ := (_root_.GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hI.g1).2 D.host.ccK δ hc
  have hwp : wpF (lat D δ) t0 ∈ Qbar := by
    refine (htor t0 ⟨2, two_pos, by exact_mod_cast ht.1⟩ fun h0 => ?_).1
    obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
    have h1 := GlobalTheory.ArchNorm.mul_mem_lamOf D D.host.ccK δ a h0
    rw [ha, mul_comm] at h1
    exact ht.2.1 h1
  let b := Module.finBasis ℚ D.what₂.LL
  obtain ⟨M, hM1, -, hM⟩ := GlobalTheory.ArchNorm.exists_galois
    (Set.range (fun i => D.what₂.embLL (b i)) ∪ {g2 (lat D δ), g3 (lat D δ), wpF (lat D δ) t0})
    ((Set.finite_range _).union (Set.toFinite _)) (by
      rintro y (⟨i, rfl⟩ | rfl | rfl | rfl)
      · exact mem_algebraicClosure_iff.2
          ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b i)).algHom D.what₂.embLL.toRatAlgHom)
      · exact hdata.2.1
      · exact hdata.2.2
      · exact hwp)
  have hσ : ∀ y, D.what₂.embLL y ∈ M := fun y => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr y, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_rat_smul]
    exact M.smul_mem (hM _ (Or.inl ⟨i, rfl⟩))
  have hle : fld D δ t0 ≤ M := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro y (⟨x, rfl⟩ | rfl | rfl | rfl)
    · exact hσ x
    · exact hM _ (Or.inr (by simp))
    · exact hM _ (Or.inr (by simp))
    · exact hM _ (Or.inr (by simp))
  exact Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion hle).injective

theorem ext_finite_nonempty : ∀ D : D7, GlobalTheory.NormSum.Inp D → ∀ δ t0 : ℂ, Crv D D.host.ccK δ → GL3Theta.IsTwoTorsionPointUnkilled D (lat D δ) t0 →
    ∀ σ : D.what₂.LL →+* ℂ, (ext D δ t0 σ).Finite ∧ (ext D δ t0 σ).Nonempty := by
  intro D hI δ t0 hc ht σ
  have := fld_finiteDimensional D hI δ t0 hc ht
  refine ⟨Set.toFinite _, ?_⟩
  let τ : D.what₂.LL →+* fld D δ t0 :=
    { toFun := fun x => ⟨D.what₂.embLL x, embLL_mem D δ t0 x⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ x y)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x y) }
  letI : Algebra D.what₂.LL (fld D δ t0) := τ.toAlgebra
  letI : Algebra D.what₂.LL ℂ := σ.toAlgebra
  have : IsScalarTower ℚ D.what₂.LL (fld D δ t0) := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : IsScalarTower ℚ D.what₂.LL ℂ := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : Algebra.IsAlgebraic ℚ (fld D δ t0) := Algebra.IsAlgebraic.of_finite ℚ _
  have : Algebra.IsAlgebraic D.what₂.LL (fld D δ t0) := Algebra.IsAlgebraic.tower_top (K := ℚ) D.what₂.LL
  let φ : fld D δ t0 →ₐ[D.what₂.LL] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨φ.restrictScalars ℚ, fun x => ?_⟩
  show φ (algebraMap D.what₂.LL (fld D δ t0) x) = σ x
  rw [φ.commutes]
  rfl

end GlobalTheory.KerConjMean
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyParameterSizesTestChoices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
open GlobalTheory.SignedHC

namespace GlobalTheory.KerConjMean.TopSizes

theorem natW_wtOf_le (n : ℕ) (E : Finset ℚ) (lo hi : ℝ) (hM : lo ≤ hi) (hE : ∀ x ∈ E, lo ≤ (x : ℝ) ∧ (x : ℝ) ≤ hi) (a : Fin n) :
    (((wtOf n E).natW a : ℕ) : ℝ) ≤ hi - lo + 1 := by
  have hn : 0 < n := a.pos
  have key : (wtOf n E).natW a = ((wtOf n E).w a - (wtOf n E).w ⟨n - 1, by omega⟩).toNat := by
    simp only [DomWeight.natW, DomWeight.detShift, dif_pos hn]
  have hd : (((wtOf n E).w a - (wtOf n E).w ⟨n - 1, by omega⟩ : ℤ) : ℝ) ≤ hi - lo + 1 := by
    unfold wtOf
    split_ifs with h
    · have e0 := hE _ (descEnum_mem E h.1 a)
      have e1 := hE _ (descEnum_mem E h.1 ⟨n - 1, by omega⟩)
      have f0 : ((⌊highestWeight E h.1 a⌋ : ℤ) : ℝ) ≤ ((highestWeight E h.1 a : ℚ) : ℝ) := by
        exact_mod_cast Int.floor_le _
      have f1 : ((highestWeight E h.1 ⟨n - 1, by omega⟩ : ℚ) : ℝ) - 1 <
          ((⌊highestWeight E h.1 ⟨n - 1, by omega⟩⌋ : ℤ) : ℝ) := by
        exact_mod_cast Int.sub_one_lt_floor _
      have hr : ((a : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast a.2
      have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; simp
      have g0 : ((highestWeight E h.1 a : ℚ) : ℝ) ≤ hi + ((n : ℝ) - 1) / 2 := by
        simp only [highestWeight]; push_cast; linarith [e0.2]
      have g1 : lo + ((n : ℝ) - 1) / 2 ≤ ((highestWeight E h.1 ⟨n - 1, by omega⟩ : ℚ) : ℝ) := by
        simp only [highestWeight, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat, hc]
        linarith [e1.1]
      push_cast
      linarith
    · simp; linarith
  rw [key]
  have c : ∀ z : ℤ, (z.toNat : ℝ) = (((z.toNat : ℕ) : ℤ) : ℝ) := fun z => (Int.cast_natCast _).symm
  rw [c, Int.toNat_eq_max]
  push_cast
  exact max_le (by push_cast at hd; exact hd) (by linarith)

theorem extend_bounds {n : ℕ} (d : ℕ) (f : Fin n → ℚ) (h : ℝ) (hh : 0 ≤ h)
    (hf : ∀ i, 0 ≤ ((f i : ℚ) : ℝ) ∧ ((f i : ℚ) : ℝ) ≤ h) (j : ℕ) :
    0 ≤ ((GridData.extend d f j : ℤ) : ℝ) ∧ ((GridData.extend d f j : ℤ) : ℝ) ≤ h := by
  unfold GridData.extend
  split_ifs with hj
  · obtain ⟨h1, h2⟩ := hf ⟨j - d, hj⟩
    have a1 : (0 : ℚ) ≤ f ⟨j - d, hj⟩ := by exact_mod_cast h1
    refine ⟨by exact_mod_cast Int.floor_nonneg.2 a1, le_trans ?_ h2⟩
    exact_mod_cast Int.floor_le _
  · simp [hh]

theorem entry_bounds {D : D7} (large₂ : SizeData₂ D) (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (j : ℕ) (τ : D.what₂.Tau) :
    ∀ x ∈ (num D 1 τ).weightX j, -(5 * large₂.sc.b) ≤ (x : ℝ) ∧ (x : ℝ) ≤ 2 * large₂.sc.b := by
  obtain ⟨hN, -, -, -, hm2, -, -, hb12⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hs
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hgap, hbe, -⟩ := hs
  have hSc := large₂.Sc_pos
  have hg0 : (0 : ℝ) ≤ (gap D 1 : ℝ) := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have hScb : large₂.Sc ≤ large₂.sc.b := by nlinarith
  have hts : D.R.t + sLen D + 1 ≤ bigN D := by
    have : D.R.t + sLen D + 1 ≤ D.R.m * (D.R.t + sLen D + 1) := Nat.le_mul_of_pos_left _ (by omega)
    unfold bigN; omega
  have hts' : (D.R.t : ℝ) + (sLen D : ℝ) + 1 ≤ large₂.sc.b := le_trans (by exact_mod_cast hts) hN
  have ht0 : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  have hs0 : (0 : ℝ) ≤ (sLen D : ℝ) := Nat.cast_nonneg _
  have hv : ∀ j, 0 ≤ ((GridData.extend 2 (D.hc τ).v j : ℤ) : ℝ) ∧ ((GridData.extend 2 (D.hc τ).v j : ℤ) : ℝ) ≤ large₂.Sc :=
    extend_bounds 2 _ _ hSc.le fun l => large₂.cloud_v τ l
  have hel : ∀ l : Fin D.R.m, 0 ≤ (((D.hc τ).e l : ℚ) : ℝ) ∧ (((D.hc τ).e l : ℚ) : ℝ) ≤ 4 * large₂.sc.b := fun l => by
    obtain ⟨h1, h2⟩ := hbe τ l
    have h3 := (D.hc τ).gap_be l
    have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
    have h4 : 0 ≤ (D.hc τ).e l := by linarith
    exact ⟨by exact_mod_cast h4, h2⟩
  have he := extend_bounds 1 _ _ (by linarith) hel
  have hcen : ∀ j, 1 ≤ j → j ≤ D.R.m → 0 ≤ ((cen D 1 τ j : ℤ) : ℝ) ∧ ((cen D 1 τ j : ℤ) : ℝ) ≤ large₂.sc.b := by
    intro j hj1 hj2
    have e := GridData.mid_eq (GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0) hj1
    have hv2 := hv 2
    have hj1' : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
    have hj2' : (j : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast hj2
    have hmid : 0 ≤ (((GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0).mid j : ℚ) : ℝ) ∧
        (((GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0).mid j : ℚ) : ℝ) ≤ large₂.sc.b := by
      rw [e]
      simp only [GridData.a, GridData.ofHCParam]
      push_cast
      constructor <;> nlinarith
    unfold cen
    refine ⟨by exact_mod_cast Int.floor_nonneg.2 (by exact_mod_cast hmid.1), le_trans ?_ hmid.2⟩
    exact_mod_cast Int.floor_le _
  intro x hx
  rcases GridData.mem_weightX.1 hx with h | h | ⟨i, hi1, hi2, h⟩ | ⟨l, -, -, h⟩
  · obtain ⟨i, hi, rfl⟩ := GridData.mem_tops.1 h
    have hi' : (i : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast (show i ≤ D.R.m from hi)
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg _
    have hv2 := hv 2
    simp only [GridData.a, num, GridData.ofHCParam]
    push_cast
    constructor <;> nlinarith
  · obtain ⟨i, -, -, rfl⟩ := GridData.mem_cloudHalf.1 h
    have h : 0 ≤ (((num D 1 τ).v i : ℤ) : ℝ) ∧ (((num D 1 τ).v i : ℤ) : ℝ) ≤ large₂.Sc := hv i
    simp only [GridData.vHalf]
    push_cast
    constructor <;> linarith
  · obtain ⟨a, ha, rfl⟩ := GlobalTheory.SignedHC.mem_block.1 h
    have h : 0 ≤ (((num D 1 τ).cen i : ℤ) : ℝ) ∧ (((num D 1 τ).cen i : ℤ) : ℝ) ≤ large₂.sc.b := hcen i hi1 hi2
    have h1 : (((num D 1 τ).s - 1 : ℕ) : ℝ) ≤ (sLen D : ℝ) := by
      exact_mod_cast (show sLen D - 1 ≤ sLen D from Nat.sub_le _ _)
    have ha' : (a : ℝ) + 1 ≤ (((num D 1 τ).s - 1 : ℕ) : ℝ) := by exact_mod_cast ha
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
    simp only [Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_natCast, Rat.cast_intCast, Rat.cast_one, Rat.cast_ofNat]
    constructor <;> linarith
  · obtain ⟨a, ha, rfl⟩ := GlobalTheory.SignedHC.mem_block.1 h
    have h : 0 ≤ (((num D 1 τ).e l : ℤ) : ℝ) ∧ (((num D 1 τ).e l : ℤ) : ℝ) ≤ 4 * large₂.sc.b := he l
    have h1 : ((num D 1 τ).t : ℝ) = (D.R.t : ℝ) := rfl
    have ha' : (a : ℝ) ≤ ((num D 1 τ).t : ℝ) := by exact_mod_cast Nat.lt_succ_iff.1 ha
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
    push_cast
    constructor <;> linarith

theorem sizesK : BigC fun {D} _ _ _ _ _ A _ _ _ _ _ _ ch _ b => 3 ≤ b ∧ 1 ≤ bigN D ∧ (bigN D : ℝ) ≤ b ∧ 1 ≤ D.R.f ∧ (D.R.f : ℝ) ≤ b ∧
  Fintype.card D.what₂.Tau ≤ D.R.f ∧ 0 ≤ D.host.rdE ∧ D.host.rdE ≤ b ∧ ∀ j : ℕ, j ≤ D.R.m →
    (ch.G.V (.top j)).rank ≤ bigN D ∧ ∀ τ i, ((wt ch.G (.top j) τ).natW i : ℝ) ≤ 8 * b := by
  refine ⟨0, fun CF _ => ⟨0, fun ε C _ => ⟨0, ?_⟩⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ hch _
  obtain ⟨hN, hf, hN1, hf1, -, hrd1, hrd, hb12⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hS.size
  have hlb : 0 ≤ Real.log large₂.sc.b := Real.log_nonneg (by linarith)
  have hc : ch.sc.cGap = 1 := by
    have h : ch.sc = { cGap := 1, cDep := CF, b := large₂.sc.b } := hch
    rw [h]
  refine ⟨by linarith, hN1, hN, hf1, hf, (Lnk.card_Tau D).le, by linarith, ?_, fun j hj => ⟨?_, fun τ i => ?_⟩⟩
  · exact (Real.log_le_log_iff (by linarith) (by linarith)).1 (by linarith)
  · exact GlobalTheory.DefRank.rank_le_bigN ch.G (.top j) hj
  · have key : ∀ x ∈ entries (Node.par D ch.sc.cGap (.top j) τ), -(5 * large₂.sc.b) ≤ (x : ℝ) ∧ (x : ℝ) ≤ 2 * large₂.sc.b := by
      rw [hc]
      intro x hx
      have e : entries (Node.par D 1 (.top j) τ) = (num D 1 τ).weightX j := entries_plus _
      exact entry_bounds large₂ hS.size j τ x (e ▸ hx)
    have hw := natW_wtOf_le _ _ _ _ (by linarith) key i
    calc (((wt ch.G (.top j) τ).natW i : ℕ) : ℝ)
        = (((wtOf _ (entries (Node.par D ch.sc.cGap (.top j) τ))).natW i : ℕ) : ℝ) := rfl
      _ ≤ _ := hw
      _ ≤ 8 * large₂.sc.b := by linarith

end GlobalTheory.KerConjMean.TopSizes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExOfFlatWtSome
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G GlobalTheory.Frames GlobalTheory.HTLat
open scoped NNReal

namespace GlobalTheory.FlatFrameLaw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}


open Classical in
theorem exOf_flatWt_some (τ : Psi H) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    exOf Dw (flatWt Dw τ) 0 (some ⟨σ, i⟩) =
      if σ = τ.1 then -1 else if σ = conjEmb τ.1 then 1 else 0 := by
  by_cases h1 : σ = τ.1
  · subst h1
    have hi : (i : ℕ) < Dw.p := by
      have := i.2; simp only [Datum.mult, if_pos τ.2] at this; exact this
    rw [if_pos rfl]
    show (wtOf Dw (flatWt Dw τ) 0).1 (τ.1, i) = -1
    rw [wtOf_big _ _ τ i hi]; simp [flatWt, parWt]
  · rw [if_neg h1]
    by_cases h2 : σ = conjEmb τ.1
    · subst h2
      have hi : (i : ℕ) < Dw.q := by
        have := i.2; simp only [Datum.mult, if_neg (conj_not_mem τ)] at this; exact this
      rw [if_pos rfl]
      show (wtOf Dw (flatWt Dw τ) 0).1 (conjEmb τ.1, i) = 1
      rw [wtOf_small _ _ τ i hi]; simp [flatWt, parWt]
    · rw [if_neg h2]
      show (wtOf Dw (flatWt Dw τ) 0).1 (σ, i) = 0
      simp only [wtOf]
      split_ifs with h h' h''
      · have hne : (⟨σ, h⟩ : Psi H) ≠ τ := fun e => h1 (congrArg Subtype.val e)
        simp [flatWt, parWt, hne]
      · rfl
      · have hne : (⟨conjEmb σ, h''⟩ : Psi H) ≠ τ := fun e => h2 (by
          rw [← congrArg Subtype.val e, GlobalTheory.AllWt.conjEmb_conjEmb])
        simp [flatWt, parWt, hne]
      · rfl
      · rfl

theorem exOf_flatWt_none (τ : Psi H) : exOf Dw (flatWt Dw τ) 0 none = 0 := by
  simp [exOf, exZ, wtOf]

theorem ne_conjEmb (τ : Psi H) : τ.1 ≠ conjEmb τ.1 := fun e => conj_not_mem τ (e ▸ τ.2)

end GlobalTheory.FlatFrameLaw

namespace GlobalTheory.FlatFrameLaw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem evR_flat_frChg {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (τ : Psi H) {f : Rul Xo c}
    (hf : f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0)) {C : Type} [Field C] [Algebra c.F C]
    (g : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) C) (a : C)
    (z y : FrPt Xo c C) (hch : FrChg g a z y) (hg : ∀ σ i j, i < j → g σ i j = 0)
    (hdet : ∀ σ, IsUnit (g σ).det) (ha : a ≠ 0) :
    evR Xo c f y = ((g τ.1).det)⁻¹ * (g (conjEmb τ.1)).det * evR Xo c f z := by
  classical
  have hdiag : ∀ σ, (g σ).det = ∏ i, g σ i i := fun σ =>
    Matrix.det_of_lowerTriangular _ fun i j hij => hg σ i j hij
  have hd : ∀ σ i, g σ i i ≠ 0 := fun σ i => by
    have hu := (hdet σ).ne_zero
    rw [hdiag σ] at hu
    exact Finset.prod_ne_zero_iff.1 hu i (Finset.mem_univ i)
  obtain ⟨h1, h2, pm, h3, h4, h5⟩ := hch
  let t : Ix Dw → Cˣ := fun i => Option.rec (Units.mk0 a ha) (fun s => Units.mk0 _ (hd s.1 s.2)) i
  have hb : FrBor t z y := by
    refine ⟨h1, fun σ i => ⟨g σ i, rfl, hg σ i, h2 σ i⟩, pm, h3, ?_, h5⟩
    rw [h4, show spMap (RingHom.id C) = 𝟙 _ from Spec.map_id _]
    exact Category.comp_id _
  rw [GlobalTheory.FlagTan.evR_frBor hf hb]
  congr 1
  rw [Units.coe_prod, Fintype.prod_option, Fintype.prod_sigma]
  have hF : ∀ σ, ∏ i : Fin (Dw.mult σ), ((t (some ⟨σ, i⟩) ^ exOf Dw (flatWt Dw τ) 0 (some ⟨σ, i⟩) : Cˣ) : C) =
      if σ = τ.1 then ((g σ).det)⁻¹ else if σ = conjEmb τ.1 then (g σ).det else 1 := fun σ => by
    simp only [exOf_flatWt_some, t, Units.val_zpow_eq_zpow_val, Units.val_mk0]
    by_cases e1 : σ = τ.1
    · simp only [if_pos e1, zpow_neg_one, Finset.prod_inv_distrib, hdiag]
    · by_cases e2 : σ = conjEmb τ.1
      · simp only [if_neg e1, if_pos e2, zpow_one, hdiag]
      · simp only [if_neg e1, if_neg e2, zpow_zero, Finset.prod_const_one]
  simp only [hF, exOf_flatWt_none, zpow_zero, Units.val_one, one_mul]
  rw [Fintype.prod_eq_mul τ.1 (conjEmb τ.1) (ne_conjEmb τ) fun σ hσ => by rw [if_neg hσ.1, if_neg hσ.2],
    if_pos rfl, if_neg (ne_conjEmb τ).symm, if_pos rfl]

end GlobalTheory.FlatFrameLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleFormConvergentThetaIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open Filter Topology
open scoped ENNReal

noncomputable section

namespace GlobalTheory.ThetaIntAdm

theorem exists_clm_integral {S Ω : Type} [AddCommGroup S] [Module ℂ S] [TopologicalSpace S] [IsTopologicalAddGroup S]
    [FirstCountableTopology S] [BarrelledSpace ℂ S] [MeasurableSpace Ω] (μ : Measure Ω) (T : Ω → S →L[ℂ] ℂ)
    (hint : ∀ f, Integrable (fun x => T x f) μ) : ∃ L : S →L[ℂ] ℂ, ∀ f, L f = ∫ x, T x f ∂μ := by
  let q : Seminorm ℂ S := Seminorm.of (fun f => ∫ x, ‖T x f‖ ∂μ)
    (fun f g => by
      have hf := (hint f).norm
      have hg := (hint g).norm
      have hfg := (hint (f + g)).norm
      rw [← integral_add hf hg]
      exact integral_mono hfg (hf.add hg) fun x => by simp only [map_add (f := _)]; exact norm_add_le _ _)
    (fun c f => by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun x => by simp [map_smul, norm_mul]))
  have hq : ∀ f, q f = ∫ x, ‖T x f‖ ∂μ := fun f => rfl
  have hlsc : LowerSemicontinuous q := by
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro c
    apply IsSeqClosed.isClosed
    intro y y₀ hy hlim
    have hc : 0 ≤ c := le_trans (apply_nonneg _ _) (hy 0)
    show q y₀ ≤ c
    rw [hq, integral_norm_eq_lintegral_enorm (hint y₀).aestronglyMeasurable]
    apply ENNReal.toReal_le_of_le_ofReal hc
    have hpt : ∀ x, Tendsto (fun n => ‖T x (y n)‖ₑ) atTop (𝓝 ‖T x y₀‖ₑ) := fun x =>
      ((T x).continuous.enorm.continuousAt.tendsto).comp hlim
    calc ∫⁻ x, ‖T x y₀‖ₑ ∂μ = ∫⁻ x, liminf (fun n => ‖T x (y n)‖ₑ) atTop ∂μ := by
          congr 1; funext x; exact (hpt x).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ x, ‖T x (y n)‖ₑ ∂μ) atTop :=
          lintegral_liminf_le' fun n => (hint (y n)).aestronglyMeasurable.enorm
      _ ≤ liminf (fun _ : ℕ => ENNReal.ofReal c) atTop := by
          refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
          show ∫⁻ x, ‖T x (y n)‖ₑ ∂μ ≤ ENNReal.ofReal c
          rw [← ofReal_integral_norm_eq_lintegral_enorm (hint (y n))]
          exact ENNReal.ofReal_le_ofReal (hy n)
      _ = ENNReal.ofReal c := liminf_const _
  have hqc : Continuous q := Seminorm.continuous_of_lowerSemicontinuous _ hlsc
  let L : S →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ x, T x f ∂μ
      map_add' := fun f g => by simp only [map_add (f := _)]; exact integral_add (hint f) (hint g)
      map_smul' := fun c f => by simp only [map_smul, smul_eq_mul, RingHom.id_apply]; exact integral_const_mul c _ }
  have hL0 : ContinuousAt L 0 := by
    rw [ContinuousAt, map_zero]
    refine squeeze_zero_norm (a := fun f => q f) (fun f => ?_) ?_
    · exact norm_integral_le_integral_norm _
    · have := hqc.tendsto 0
      rwa [map_zero] at this
  exact ⟨⟨L, continuous_of_continuousAt_zero L.toAddMonoidHom hL0⟩, fun f => rfl⟩

end GlobalTheory.ThetaIntAdm

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (theta)
open scoped Classical

theorem GlobalTheory.ThetaIntAdm.exists_admissible_form_convergent_thetaIntegral : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {Y : Spc F E d} (M : Model σ X Y)
    (ψ : AddChar (AF F) ℂ) (χX χY : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : Rep σ X Y), M.IsWeil ψ χX χY om →
    (∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), M.Conv om Φ) →
    ∃ l ∈ (GlobalTheory.WeilM.adeleClass F).adm (Fin n × Fin d), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), l Φ = M.I om Φ 1 := by
  intro F E _ _ _ _ _ σ n d X Y M ψ χX χY om hW hC
  obtain ⟨l₀, hl₀, hl₀e⟩ := _root_.GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin n × Fin d)
  have hS := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hW
  have pres : ∀ p, ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), om p Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) :=
    hS.pres
  have adm : ∀ p, ∀ l ∈ (GlobalTheory.WeilM.adeleClass F).adm (Fin n × Fin d),
      l ∘ₗ om p ∈ (GlobalTheory.WeilM.adeleClass F).adm (Fin n × Fin d) := hS.adm
  have th : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), ∀ g, theta om Φ g 1 = l₀ (om (g, 1) Φ) :=
    fun Φ hΦ g => (hl₀e _ (pres _ Φ hΦ)).symm
  let fI : GlobalTheory.WeilM.schA F (Fin n × Fin d) →ₗ[ℂ] ℂ :=
    { toFun := fun Φ => M.I om Φ.1 1
      map_add' := fun Φ Ψ => by
        have e : (fun g => theta om (Φ + Ψ).1 g 1) = fun g => theta om Φ.1 g 1 + theta om Ψ.1 g 1 := by
          funext g
          rw [th _ (Φ + Ψ).2, th _ Φ.2, th _ Ψ.2, Submodule.coe_add, map_add (f := _), map_add (f := _)]
        show ∫ g in M.dom, theta om (Φ + Ψ).1 g 1 ∂M.μ = ∫ g in M.dom, theta om Φ.1 g 1 ∂M.μ + ∫ g in M.dom, theta om Ψ.1 g 1 ∂M.μ
        rw [e]
        exact integral_add (hC _ Φ.2 1) (hC _ Ψ.2 1)
      map_smul' := fun c Φ => by
        have e : (fun g => theta om (c • Φ).1 g 1) = fun g => c * theta om Φ.1 g 1 := by
          funext g
          rw [th _ (c • Φ).2, th _ Φ.2, Submodule.coe_smul, map_smul, map_smul, smul_eq_mul]
        show ∫ g in M.dom, theta om (c • Φ).1 g 1 ∂M.μ = c • ∫ g in M.dom, theta om Φ.1 g 1 ∂M.μ
        rw [e, smul_eq_mul]
        exact integral_const_mul c _ }
  obtain ⟨l, hl⟩ := LinearMap.exists_extend fI
  have hlΦ : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), l Φ = M.I om Φ 1 :=
    fun Φ hΦ => LinearMap.congr_fun hl ⟨Φ, hΦ⟩
  refine ⟨l, ?_, hlΦ⟩
  intro g₀ hg₀
  have mem : ∀ f : SchwartzMap (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ, GlobalTheory.WeilM.pureA F f g₀ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) :=
    fun f => Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩
  choose T hT using fun x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J => adm (x, 1) l₀ hl₀ g₀ hg₀
  have eT : ∀ f : SchwartzMap (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ, (fun x => T x f) = fun x => theta om (GlobalTheory.WeilM.pureA F f g₀) x 1 := fun f => by
    funext x
    rw [← hT x f, th _ (mem f)]
    rfl
  haveI := _root_.GlobalTheory.schwartzMap_barrelledSpace (Fin n × Fin d → mixedEmbedding.mixedSpace F)
  obtain ⟨L, hL⟩ := GlobalTheory.ThetaIntAdm.exists_clm_integral (M.μ.restrict M.dom) T
    (fun f => by rw [eT f]; exact hC _ (mem f) 1)
  refine ⟨L, fun f => ?_⟩
  rw [hlΦ _ (mem f), hL, eT f]
  rfl
end
end

