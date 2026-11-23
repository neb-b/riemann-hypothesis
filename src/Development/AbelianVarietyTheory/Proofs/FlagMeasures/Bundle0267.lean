module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0264
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHFinOrd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle0005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle0007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle0004
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0178
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0147
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSelfDualLatticeIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeStabiliserIsCompactIsOpen
section
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory

theorem adelicStab_isCompact_isOpen :
    ∀ (I : AutInst), IsCompact I.Kset ∧ IsOpen I.Kset ∧ LocallyCompactSpace I.Gf ∧ T2Space I.Gf := by
  intro I
  obtain ⟨h1, h2, -, h4, h5, -⟩ := GlobalTheory.CongTop.adelic_topology I
  exact ⟨h4, h5, h2, h1⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockProjectionBesselStatement
section
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_projection_bessel : Hyps → AmpKF → CellConv → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (L : LocBessel k r) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (h : ℝ) (μG : Measure (Mt k r)) (om om' : ι → ℂ) (l : R.H → L.Wp) (l' : R.H → L.Wq) (lI : ∀ I, (RI I).H → L.Wp) (lI' : ∀ I, (RI I).H → L.Wq) (w : R.H) (wI : ∀ I, (RI I).H) (κ₀ κ₁ : κ → ℂ), haveI := FiniteDimensional.complete ℂ L.Wp; haveI := FiniteDimensional.complete ℂ L.Wq; R.IsDS L.ε mu → GapAtLeast L.ε mu h → (∀ I, (RI I).IsDS L.ε (muI I) ∧ GapAtLeast L.ε (muI I) h) → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GapCell k r h → L.c ≠ 0 → L.κN ≠ ⊤ → IsHaarOn (UH (Hpk k r)) μG → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → (∀ g ∈ Sset k r L.z, ρ g *ᵥ om = om) → (∀ g ∈ Sset k r L.z', ρ g *ᵥ om' = om') → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π R.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' R.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x)) → (∀ I, (∀ x ∈ (RI I).sm, ∀ v ∈ (RI I).TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π (RI I).σ L.μW L.μN x v = (innerSL ℂ (lI I v)).smulRight (lI I x)) ∧ (∀ x ∈ (RI I).sm, ∀ v ∈ (RI I).TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' (RI I).σ L.μW' L.μN x v = (innerSL ℂ (lI' I v)).smulRight (lI' I x))) → (∃ v, R.KFin v ∧ l v ≠ 0) → (∃ v, R.KFin v ∧ l' v ≠ 0) → PI.UpqRep.IsLowUnitH k r L.ε mu R.σ w → (∀ I, PI.UpqRep.IsLowUnitH k r L.ε (muI I) (RI I).σ (wI I)) → (∀ I, ∀ v ∈ R.sm, lI I (∑ c, pr I c (tm R om v c)) = κ₀ I • l v ∧ lI' I (∑ c, pr I c (tm R om' v c)) = κ₁ I • l' v) → ∀ (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r)) (ν : Measure (PairSp k r)), CellData L μG γ μR νR ν → (herm Γ (ρ γ *ᵥ om') om * (PI.BesselPeriodGGP.fdegH μG R.σ w : ℂ)) • amp R l l' w νR γ = ∑ I, ((ep I : ℂ) * κ₁ I * star (κ₀ I) * (PI.BesselPeriodGGP.fdegH μG (RI I).σ (wI I) : ℂ)) • amp (RI I) (lI I) (lI' I) (wI I) νR γ := by
  first | exact @GlobalTheory.CellPieri.amp_pieri | exact GlobalTheory.CellPieri.amp_pieri | (intros; apply GlobalTheory.CellPieri.amp_pieri <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnLevelStabTriv
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2

namespace GlobalTheory

theorem columnLevel_stabTriv :
    ∀ (D : D7) (X : HidaSetting D) (hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
      Formalism.L2.SG.ColsDim.StabTriv (iotaF X u) (Ku X u hK) := by
  intro D X hK u h γ hγ

  have hfin : IsOfFinOrder γ :=
    Formalism.L2.SG.PoincareInHH.Cut.gamFinKu_of X u hK
      (Formalism.L2.SG.PoincareInHH.Cut.latOfLattice_holds X u) h γ hγ
  exact Formalism.L2.SG.PoincareInHH.Cut.gamUnipKu_holds X u hK h γ hγ hfin

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CongruenceNormalFiniteIndex
section
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.CongTop

theorem congruence_normal_finite_index : ∀ (I : AutInst), (∃ K : Subgroup I.Gf, (K : Set I.Gf) = I.Kset) ∧ ∀ g : ℕ, 1 ≤ g → (∃ K : Subgroup I.Gf, (K : Set I.Gf) = I.Kg g) ∧ IsOpen (I.Kg g) ∧ (∀ x ∈ I.Kset, ∀ y ∈ I.Kg g, x * y * x⁻¹ ∈ I.Kg g) ∧ ∃ s : Finset I.Gf, ∀ x ∈ I.Kset, ∃ t ∈ s, t⁻¹ * x ∈ I.Kg g := by
  intro I
  obtain ⟨-, -, -, hKc, -, hK, hg⟩ := GlobalTheory.CongTop.adelic_topology I
  refine ⟨hK, fun g hg1 => ?_⟩
  obtain ⟨hKgo, ⟨H, hH⟩, hnorm⟩ := hg g hg1
  refine ⟨⟨H, hH⟩, hKgo, hnorm, ?_⟩

  have hopen : ∀ t ∈ I.Kset, IsOpen {x : I.Gf | t⁻¹ * x ∈ I.Kg g} := fun t _ =>
    hKgo.preimage (continuous_const_mul t⁻¹)
  have hsub : I.Kset ⊆ ⋃ t ∈ I.Kset, {x : I.Gf | t⁻¹ * x ∈ I.Kg g} := by
    intro x hx
    refine Set.mem_biUnion hx ?_
    show x⁻¹ * x ∈ I.Kg g
    rw [inv_mul_cancel, ← hH]
    exact H.one_mem
  obtain ⟨b, -, hb, hcov⟩ := hKc.elim_finite_subcover_image hopen hsub
  refine ⟨hb.toFinset, fun x hx => ?_⟩
  obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp (hcov hx)
  exact ⟨t, hb.mem_toFinset.mpr ht, hxt⟩

end GlobalTheory.CongTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousAutomorphicKernelDiscreteSeriesTest
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

theorem decE_dOp_le_exp_floor {n : ℕ} (ε : Fin n → Bool) (h : ℝ) (hn : 1 ≤ n)
    (hh : 32 * (n : ℝ) ^ 2 * Real.sqrt (rkR ε) ≤ h) (g : Formalism.REAL.UJ ε) :
    decE (rkR ε) h (dOp (uMat g)) ≤ Real.exp (-(4 * (n : ℝ) ^ 2 * (⌊dOp (uMat g)⌋₊ : ℝ))) := by
  obtain ⟨-, hHS, -, -, -⟩ := GlobalTheory.Count.Cartan.cartan_distances n ε
  obtain ⟨hd0, -, -, hle, hge⟩ := hHS g g hn
  set d := dOp (uMat g) with hd
  rcases Nat.eq_zero_or_pos (rkR ε) with h0 | hq
  ·
    have hz : d = 0 := by
      have h1 : dHS (uMat g) ≤ 0 := by simpa [h0] using hge
      have h2 : Real.sqrt 2 * d ≤ 0 := hle.trans h1
      have h3 : d ≤ 0 := by
        by_contra hc
        have : 0 < Real.sqrt 2 * d := mul_pos (by positivity) (lt_of_not_ge hc)
        linarith
      exact le_antisymm h3 hd0
    simp [decE, hz, h0]
  · obtain ⟨hanti, hint, -, -⟩ := shell_sum_majorant n (rkR ε) h hn hq hh
    have hfl : ((⌊d⌋₊ : ℕ) : ℝ) ≤ d := Nat.floor_le hd0
    calc decE (rkR ε) h d ≤ decE (rkR ε) h (⌊d⌋₊ : ℕ) :=
          hanti (Set.mem_Ici.mpr (Nat.cast_nonneg _)) (Set.mem_Ici.mpr hd0) hfl
      _ ≤ _ := hint _

theorem continuous_kern_phe : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.I.n →
    LocDec B h → HBig B 32 h → Continuous (fun p : B.I.GA × B.I.GA => kern B.I (phe B d) p.1 p.2) := by
  intro B d h hd hn hl hb
  classical
  obtain ⟨-, he1, he, hec⟩ := GlobalTheory.rowsAut_idem_elementary B
  obtain ⟨hphc, hphm, -⟩ := _root_.GlobalTheory.Dec.PhMajProof.phMaj B d h hd hl
  obtain ⟨-, -, -, -, hsupp, -, -⟩ := B.e_adm
  have hC := fun v => GlobalTheory.Count.Cartan.cartan_distances B.I.n (B.I.ε v)

  have hKmul : ∀ a w b : B.I.Gf, a ∈ B.I.Kset → w ∈ B.I.Kset → b ∈ B.I.Kset →
      a * w * b⁻¹ ∈ B.I.Kset := by
    intro a w b ha hw hbm
    simp only [AutInst.Kset, Set.mem_ofPred_eq] at ha hw hbm ⊢
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using mul_mem (mul_mem ha hw) (inv_mem hbm)

  obtain ⟨K1, hK1o, hK1one, hK1K⟩ : ∃ K1 : Set B.I.Gf, IsOpen K1 ∧ (1 : B.I.Gf) ∈ K1 ∧ K1 ⊆ B.I.Kset := by
    refine ⟨_, B.I.topf_open 1 le_rfl, ?_, ?_⟩
    · refine ⟨one_mem _, fun y _ => ⟨0, zero_mem _, ?_⟩⟩
      simp
    · intro x hx
      exact hx.1
  obtain ⟨Mv, hMv⟩ : ∃ Mv : InfinitePlace B.I.F → ℝ,
      ∀ v, Mv v = dOp (uMat (1 : Formalism.REAL.UJ (B.I.ε v))) + 1 := ⟨_, fun v => rfl⟩
  rw [continuous_iff_continuousAt]
  rintro ⟨x0, y0⟩

  have c1 : Continuous fun p : B.I.GA × B.I.GA => x0⁻¹ * p.1 := continuous_const.mul continuous_fst
  have c2 : Continuous fun p : B.I.GA × B.I.GA => y0⁻¹ * p.2 := continuous_const.mul continuous_snd
  have hNn : {p : B.I.GA × B.I.GA | (∀ v, dOp (uMat ((x0⁻¹ * p.1).1 v)) < Mv v) ∧ (x0⁻¹ * p.1).2 ∈ K1 ∧
      (∀ v, dOp (uMat ((y0⁻¹ * p.2).1 v)) < Mv v) ∧ (y0⁻¹ * p.2).2 ∈ K1} ∈ nhds (x0, y0) := by
    have e1 : ∀ᶠ p in nhds (x0, y0), ∀ v, dOp (uMat (((x0⁻¹ * p.1) : B.I.GA).1 v)) < Mv v := by
      rw [Filter.eventually_all]
      intro v
      have hc : Continuous fun p : B.I.GA × B.I.GA => dOp (uMat ((x0⁻¹ * p.1).1 v)) :=
        (hC v).2.2.2.2.comp ((continuous_apply v).comp (continuous_fst.comp c1))
      have h0 : dOp (uMat ((x0⁻¹ * (x0, y0).1).1 v)) < Mv v := by simp [hMv]
      exact (hc.tendsto (x0, y0)).eventually (eventually_lt_nhds h0)
    have e2 : ∀ᶠ p in nhds (x0, y0), (x0⁻¹ * p.1).2 ∈ K1 :=
      ((continuous_snd.comp c1).tendsto (x0, y0)).eventually (hK1o.mem_nhds (by simpa using hK1one))
    have e3 : ∀ᶠ p in nhds (x0, y0), ∀ v, dOp (uMat (((y0⁻¹ * p.2) : B.I.GA).1 v)) < Mv v := by
      rw [Filter.eventually_all]
      intro v
      have hc : Continuous fun p : B.I.GA × B.I.GA => dOp (uMat ((y0⁻¹ * p.2).1 v)) :=
        (hC v).2.2.2.2.comp ((continuous_apply v).comp (continuous_fst.comp c2))
      have h0 : dOp (uMat ((y0⁻¹ * (x0, y0).2).1 v)) < Mv v := by simp [hMv]
      exact (hc.tendsto (x0, y0)).eventually (eventually_lt_nhds h0)
    have e4 : ∀ᶠ p in nhds (x0, y0), (y0⁻¹ * p.2).2 ∈ K1 :=
      ((continuous_snd.comp c2).tendsto (x0, y0)).eventually (hK1o.mem_nhds (by simpa using hK1one))
    filter_upwards [e1, e2, e3, e4] with p h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩

  set n := B.I.n with hnn
  set C' : ℝ := |∏ v, d v| * (B.e 1).re * ∏ v, Real.exp (4 * (n : ℝ) ^ 2 * (1 + 2 * Mv v)) with hC'
  have hC'0 : 0 ≤ C' :=
    mul_nonneg (mul_nonneg (abs_nonneg _) he1) (Finset.prod_nonneg fun v _ => (Real.exp_pos _).le)
  set D : B.I.GFset → InfinitePlace B.I.F → ℝ := fun γ v => dOp (uMat ((x0⁻¹ * γ.1 * y0).1 v)) with hD
  set t : B.I.GFset → ℝ := fun γ => if (x0⁻¹ * γ.1 * y0).2 ∈ B.I.Kset then
      C' * ∏ v, Real.exp (-(2 * (2 * (n : ℝ) ^ 2) * (⌊D γ v⌋₊ : ℝ))) else 0 with ht
  have ht0 : ∀ γ, 0 ≤ t γ ∧ t γ ≤ C' * ∏ v, Real.exp (-(2 * (2 * (n : ℝ) ^ 2) * (⌊D γ v⌋₊ : ℝ))) := by
    intro γ
    have hp : 0 ≤ C' * ∏ v, Real.exp (-(2 * (2 * (n : ℝ) ^ 2) * (⌊D γ v⌋₊ : ℝ))) :=
      mul_nonneg hC'0 (Finset.prod_nonneg fun v _ => (Real.exp_pos _).le)
    by_cases hK : (x0⁻¹ * γ.1 * y0).2 ∈ B.I.Kset
    · simp only [ht, if_pos hK]
      exact ⟨hp, le_rfl⟩
    · simp only [ht, if_neg hK]
      exact ⟨le_rfl, hp⟩
  have hDnn : ∀ γ v, 0 ≤ D γ v := fun γ v => ((hC v).2.1 ((x0⁻¹ * γ.1 * y0).1 v) 1 hn).1
  have ha : Real.exp (-(2 * (n : ℝ) ^ 2)) ≤ 1 / 2 := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : Real.exp (-(2 * (n : ℝ) ^ 2)) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by nlinarith)
    have h2 : (1 + 1 : ℝ) ≤ Real.exp 1 := Real.add_one_le_exp 1
    have h3 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
    have h4 := Real.exp_pos (-1)
    nlinarith
  have hA : 0 ≤ (3 * Real.sqrt n / (tau1 B.I x0 * tau1 B.I y0)) ^ (2 * n ^ 2 * B.I.f) :=
    Even.pow_nonneg ⟨n ^ 2 * B.I.f, by ring⟩ _
  have hcount : ∀ r : InfinitePlace B.I.F → ℝ, (∀ v, 0 ≤ r v) →
      {γ | t γ ≠ 0 ∧ ∀ v, D γ v ≤ r v}.Finite ∧
      (({γ | t γ ≠ 0 ∧ ∀ v, D γ v ≤ r v}.ncard : ℕ) : ℝ) ≤
        (3 * Real.sqrt n / (tau1 B.I x0 * tau1 B.I y0)) ^ (2 * n ^ 2 * B.I.f) *
          Real.exp (2 * (n : ℝ) ^ 2 * ∑ v, r v) := by
    intro r hr
    obtain ⟨hfin, hcard⟩ := _root_.GlobalTheory.Dec.BoundedDistance.countRat B.I x0 y0 r hn hr
    have hsub : {γ | t γ ≠ 0 ∧ ∀ v, D γ v ≤ r v} ⊆ Subtype.val ⁻¹'
        {γ ∈ B.I.GFset | (x0⁻¹ * γ * y0).2 ∈ B.I.Kset ∧ ∀ v, dOp (uMat ((x0⁻¹ * γ * y0).1 v)) ≤ r v} := by
      rintro γ ⟨htγ, hrγ⟩
      refine ⟨γ.2, ?_, hrγ⟩
      by_contra hK
      exact htγ (by simp only [ht, if_neg hK])
    have hpre := Set.Finite.preimage (f := (Subtype.val : B.I.GFset → B.I.GA)) Subtype.val_injective.injOn hfin
    refine ⟨hpre.subset hsub, ?_⟩
    calc (({γ | t γ ≠ 0 ∧ ∀ v, D γ v ≤ r v}.ncard : ℕ) : ℝ)
        ≤ ((Subtype.val ⁻¹' {γ ∈ B.I.GFset | (x0⁻¹ * γ * y0).2 ∈ B.I.Kset ∧
            ∀ v, dOp (uMat ((x0⁻¹ * γ * y0).1 v)) ≤ r v}).ncard : ℝ) :=
          Nat.cast_le.mpr (Set.ncard_le_ncard hsub hpre)
      _ = (({γ ∈ B.I.GFset | (x0⁻¹ * γ * y0).2 ∈ B.I.Kset ∧
            ∀ v, dOp (uMat ((x0⁻¹ * γ * y0).1 v)) ≤ r v}.ncard : ℕ) : ℝ) := by
          apply congrArg (fun k : ℕ => (k : ℝ))
          apply Set.ncard_preimage_of_injective_subset_range Subtype.val_injective
          intro γ hγ
          exact ⟨⟨γ, hγ.1⟩, rfl⟩
      _ ≤ _ := hcard
  obtain ⟨hsum, -⟩ := GlobalTheory.summable_and_tsum_le_of_box_count (InfinitePlace B.I.F) B.I.GFset D t
    (2 * (n : ℝ) ^ 2) _ C' hA hC'0 ha hDnn ht0 hcount

  have hcγ : ∀ γ : B.I.GFset, Continuous fun p : B.I.GA × B.I.GA => phe B d (p.1⁻¹ * γ.1 * p.2) := by
    intro γ
    have hm : Continuous fun p : B.I.GA × B.I.GA => p.1⁻¹ * γ.1 * p.2 :=
      (continuous_fst.inv.mul continuous_const).mul continuous_snd
    exact (hphc.comp (continuous_fst.comp hm)).mul (hec.comp (continuous_snd.comp hm))

  have hbound : ∀ γ : B.I.GFset, ∀ p ∈ {p : B.I.GA × B.I.GA | (∀ v, dOp (uMat ((x0⁻¹ * p.1).1 v)) < Mv v) ∧
      (x0⁻¹ * p.1).2 ∈ K1 ∧ (∀ v, dOp (uMat ((y0⁻¹ * p.2).1 v)) < Mv v) ∧ (y0⁻¹ * p.2).2 ∈ K1},
      ‖phe B d (p.1⁻¹ * γ.1 * p.2)‖ ≤ t γ := by
    rintro γ ⟨x, y⟩ ⟨hax, hKx, hby, hKy⟩
    simp only at hax hKx hby hKy ⊢
    set a := x0⁻¹ * x with ha'
    set b := y0⁻¹ * y with hb'
    set w := x⁻¹ * γ.1 * y with hw
    have hz : x0⁻¹ * γ.1 * y0 = a * w * b⁻¹ := by rw [ha', hb', hw]; group
    have hphe : ‖phe B d w‖ = ‖ph B d w.1‖ * ‖B.e w.2‖ := norm_mul _ _
    rw [hphe]
    by_cases hew : B.e w.2 = 0
    · rw [hew, norm_zero, mul_zero]
      exact (ht0 γ).1
    have hzK : (x0⁻¹ * γ.1 * y0).2 ∈ B.I.Kset := by
      rw [hz]
      exact hKmul a.2 w.2 b.2 (hK1K hKx) (hsupp _ hew) (hK1K hKy)
    simp only [ht, if_pos hzK]

    have hmaj : ‖ph B d w.1‖ ≤ |∏ v, d v| *
        ∏ v, Real.exp (-(4 * (n : ℝ) ^ 2 * (⌊dOp (uMat (w.1 v))⌋₊ : ℝ))) := by
      refine (hphm w.1).trans ?_
      simp only [majPh]
      refine mul_le_mul (le_abs_self _) ?_ (Finset.prod_nonneg fun v _ => (Real.exp_pos _).le)
        (abs_nonneg _)
      refine Finset.prod_le_prod₀ (fun v _ => (Real.exp_pos _).le) fun v _ => ?_
      exact decE_dOp_le_exp_floor (B.I.ε v) h hn (hb v) (w.1 v)
    have hshift : ∀ v, Real.exp (-(4 * (n : ℝ) ^ 2 * (⌊dOp (uMat (w.1 v))⌋₊ : ℝ))) ≤
        Real.exp (4 * (n : ℝ) ^ 2 * (1 + 2 * Mv v)) *
          Real.exp (-(2 * (2 * (n : ℝ) ^ 2) * (⌊D γ v⌋₊ : ℝ))) := by
      intro v
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      obtain ⟨hnn0, hinv, -⟩ := (hC v).2.1 (b.1 v) (b.1 v) hn
      have htri1 := ((hC v).2.1 (a.1 v * w.1 v) (b.1 v)⁻¹ hn).2.2.1
      have htri2 := ((hC v).2.1 (a.1 v) (w.1 v) hn).2.2.1
      have hzv : (x0⁻¹ * γ.1 * y0).1 v = a.1 v * w.1 v * (b.1 v)⁻¹ := by rw [hz]; rfl
      have hDz : D γ v ≤ dOp (uMat (a.1 v)) + dOp (uMat (w.1 v)) + dOp (uMat (b.1 v)) := by
        simp only [hD, hzv]
        linarith
      have hwnn : 0 ≤ dOp (uMat (w.1 v)) := ((hC v).2.1 (w.1 v) (w.1 v) hn).1
      have hfz : ((⌊D γ v⌋₊ : ℕ) : ℝ) ≤ D γ v := Nat.floor_le (hDnn γ v)
      have hfw : dOp (uMat (w.1 v)) < (⌊dOp (uMat (w.1 v))⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      have hav := hax v
      have hbv := hby v
      have hkey : ((⌊D γ v⌋₊ : ℕ) : ℝ) ≤ (⌊dOp (uMat (w.1 v))⌋₊ : ℝ) + 1 + 2 * Mv v := by linarith
      have hn2 : (0 : ℝ) ≤ 4 * (n : ℝ) ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hkey hn2]
    have hprod : ∏ v, Real.exp (-(4 * (n : ℝ) ^ 2 * (⌊dOp (uMat (w.1 v))⌋₊ : ℝ))) ≤
        (∏ v, Real.exp (4 * (n : ℝ) ^ 2 * (1 + 2 * Mv v))) *
          ∏ v, Real.exp (-(2 * (2 * (n : ℝ) ^ 2) * (⌊D γ v⌋₊ : ℝ))) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod₀ (fun v _ => (Real.exp_pos _).le) fun v _ => hshift v
    calc ‖ph B d w.1‖ * ‖B.e w.2‖
        ≤ (|∏ v, d v| * ((∏ v, Real.exp (4 * (n : ℝ) ^ 2 * (1 + 2 * Mv v))) *
            ∏ v, Real.exp (-(2 * (2 * (n : ℝ) ^ 2) * (⌊D γ v⌋₊ : ℝ))))) * (B.e 1).re := by
          refine mul_le_mul ?_ (he _) (norm_nonneg _) ?_
          · exact hmaj.trans (mul_le_mul_of_nonneg_left hprod (abs_nonneg _))
          · exact mul_nonneg (abs_nonneg _) (mul_nonneg
              (Finset.prod_nonneg fun v _ => (Real.exp_pos _).le)
              (Finset.prod_nonneg fun v _ => (Real.exp_pos _).le))
      _ = C' * ∏ v, Real.exp (-(2 * (2 * (n : ℝ) ^ 2) * (⌊D γ v⌋₊ : ℝ))) := by
          rw [hC']; ring
  have key := continuousOn_tsum (fun γ => (hcγ γ).continuousOn) hsum hbound
  exact key.continuousAt hNn

end GlobalTheory.Dec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousHasCompactSupportInfFinProductTestFunc
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory.ProdCont

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) {M n : ℕ}

noncomputable def glueTup (Y : (Fin n → Fin M → Ainf F ⊗[F] E) × (Fin n → Fin M → Af F ⊗[F] E)) :
    Fin n → Fin M → AF F ⊗[F] E :=
  fun a i => (Algebra.TensorProduct.basis (AF F) b).equivFun.symm fun k =>
    pairA F ((Algebra.TensorProduct.basis (Ainf F) b).repr (Y.1 a i) k)
      ((Algebra.TensorProduct.basis (Af F) b).repr (Y.2 a i) k)

theorem continuous_glueTup : Continuous (glueTup (F := F) (E := E) b (M := M) (n := n)) := by
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  haveI : ContinuousSMul (AF F) (AF F ⊗[F] E) := IsModuleTopology.toContinuousSMul (AF F) _
  have hs : Continuous (Algebra.TensorProduct.basis (AF F) b).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis (AF F) b).equivFun.symm.toLinearMap
  have hi : Continuous (Algebra.TensorProduct.basis (Ainf F) b).equivFun :=
    IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis (Ainf F) b).equivFun.toLinearMap
  have hf : Continuous (Algebra.TensorProduct.basis (Af F) b).equivFun :=
    IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis (Af F) b).equivFun.toLinearMap
  refine continuous_pi fun a => continuous_pi fun i => hs.comp (continuous_pi fun k => ?_)
  have h1 : Continuous fun Y : (Fin n → Fin M → Ainf F ⊗[F] E) × (Fin n → Fin M → Af F ⊗[F] E) =>
      (Algebra.TensorProduct.basis (Ainf F) b).equivFun (Y.1 a i) k :=
    (continuous_apply k).comp (hi.comp ((continuous_apply i).comp ((continuous_apply a).comp continuous_fst)))
  have h2 : Continuous fun Y : (Fin n → Fin M → Ainf F ⊗[F] E) × (Fin n → Fin M → Af F ⊗[F] E) =>
      (Algebra.TensorProduct.basis (Af F) b).equivFun (Y.2 a i) k :=
    (continuous_apply k).comp (hf.comp ((continuous_apply i).comp ((continuous_apply a).comp continuous_snd)))
  exact (h1.prodMk h2 :)

theorem glueTup_proj (X : Fin n → Fin M → AF F ⊗[F] E) :
    glueTup b (projInf X, projFin X) = X := by
  funext a i
  refine GlobalTheory.GaugeGlue.tens_ext b fun k => ?_
  simp only [glueTup]
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  simp only [projInf, projFin, Module.Basis.equivFun_apply, GlobalTheory.GaugeGlue.repr_map]
  rfl

end GlobalTheory.ProdCont


open GlobalTheory.ProdCont in
theorem GlobalTheory.prod_continuous_hasCompactSupport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (M n : ℕ) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ), Continuous Φi → HasCompactSupport Φi → Continuous Φf → HasCompactSupport Φf → IsProdInfFin Φ Φi Φf → Continuous Φ ∧ HasCompactSupport Φ := by
  intro F E _ _ _ _ _ M n Φ Φi Φf hci hki hcf hkf hΦ
  haveI : FiniteDimensional F E := inferInstance
  let b := Module.finBasis F E
  have hpf : Continuous (projFin (F := F) (E := E) (M := M) (n := n)) :=
    continuous_pi fun a => continuous_pi fun i =>
      (GlobalTheory.GaugeGlue.continuous_map b (sndA F) GlobalTheory.GaugeGlue.continuous_sndA).comp
        ((continuous_apply i).comp (continuous_apply a))
  have hpi := GlobalTheory.GaugeGlue.continuous_projInf (F := F) (E := E) (M := M) (n := n) b
  have hEq : Φ = fun X => Φi (projInf X) * Φf (projFin X) := funext hΦ
  refine ⟨hEq ▸ (hci.comp hpi).mul (hcf.comp hpf), ?_⟩
  have hg : Continuous fun X : Fin n → Fin M → AF F ⊗[F] E => (projInf X, projFin X) :=
    hpi.prodMk hpf
  have hK : IsCompact (tsupport Φi ×ˢ tsupport Φf) := hki.isCompact.prod hkf.isCompact
  have hsub : tsupport Φ ⊆ (fun X => (projInf X, projFin X)) ⁻¹' (tsupport Φi ×ˢ tsupport Φf) := by
    refine closure_minimal (fun X hX => ?_)
      ((isClosed_tsupport Φi).prod (isClosed_tsupport Φf) |>.preimage hg)
    have h0 : Φi (projInf X) * Φf (projFin X) ≠ 0 := by rw [← hΦ]; exact hX
    exact ⟨subset_tsupport _ (left_ne_zero_of_mul h0), subset_tsupport _ (right_ne_zero_of_mul h0)⟩
  have hsub2 : tsupport Φ ⊆ glueTup b '' (tsupport Φi ×ˢ tsupport Φf) := fun X hX =>
    ⟨_, hsub hX, glueTup_proj b X⟩
  exact (hK.image (continuous_glueTup b)).of_isClosed_subset (isClosed_tsupport Φ) hsub2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DenseCompactlySupportedL2
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.CompactDense

theorem dense_of_sigmaCompact {X : Type} [TopologicalSpace X] [T2Space X] [SigmaCompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) :
    Dense {y : Lp ℂ 2 μ | ∃ C : Set X, IsCompact C ∧ ∀ᵐ z ∂μ, z ∉ C → (y : X → ℂ) z = 0} := by
  intro y
  have hm : ∀ n, MeasurableSet (compactCovering X n) := fun n => (isCompact_compactCovering X n).isClosed.measurableSet
  have hy : MemLp (y : X → ℂ) 2 μ := Lp.memLp y
  let u : ℕ → Lp ℂ 2 μ := fun n => (hy.indicator (hm n).nullMeasurableSet).toLp _
  have hu : ∀ n, (u n : X → ℂ) =ᵐ[μ] (compactCovering X n).indicator y := fun n => MemLp.coeFn_toLp _
  refine mem_closure_of_tendsto (f := u) (b := Filter.atTop) ?_ (Filter.Eventually.of_forall fun n => ?_)
  · have hi : Integrable (fun z => ‖(y : X → ℂ) z‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm hy.aestronglyMeasurable).1 hy
    have e : ∀ n, ‖u n - y‖ ^ 2 = ∫ z, (compactCovering X n)ᶜ.indicator (fun z => ‖(y : X → ℂ) z‖ ^ 2) z ∂μ := by
      intro n
      rw [← @inner_self_eq_norm_sq ℂ, L2.inner_def, ← integral_re (L2.integrable_inner _ _)]
      refine integral_congr_ae ?_
      filter_upwards [hu n, Lp.coeFn_sub (u n) y] with z h1 h2
      rw [inner_self_eq_norm_sq, h2, Pi.sub_apply, h1]
      by_cases hz : z ∈ compactCovering X n <;> simp [hz]
    have h0 : Filter.Tendsto (fun n => ‖u n - y‖ ^ 2) Filter.atTop (nhds (∫ _z, (0 : ℝ) ∂μ)) := by
      simp only [e]
      refine tendsto_integral_of_dominated_convergence _ (fun n => hi.1.indicator (hm n).compl) hi
        (fun n => Filter.Eventually.of_forall fun z => ?_) (Filter.Eventually.of_forall fun z => ?_)
      · refine (norm_indicator_le_norm_self _ _).trans (le_of_eq ?_)
        simp
      · obtain ⟨N, hN⟩ := exists_mem_compactCovering z
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Filter.eventually_ge_atTop N] with n hn
        have : z ∈ compactCovering X n := compactCovering_subset X hn hN
        simp [this]
    rw [integral_zero] at h0
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h1 := h0.sqrt
    simpa using h1
  · refine ⟨_, isCompact_compactCovering X n, ?_⟩
    filter_upwards [hu n] with z h hz
    simp [h, hz]

theorem dense_compact_support : ∀ B : RowsAut, Dense {y : B.I.L2 B.μf B.fund | ∃ C : Set B.I.GA, IsCompact C ∧ ∀ᵐ z ∂((B.I.muA B.μf).restrict B.fund), z ∉ C → (y : B.I.GA → ℂ) z = 0} := by
  intro B
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  exact dense_of_sigmaCompact _

end GlobalTheory.CompactDense
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFibreMeasuresLocalHermitianForm
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct ENNReal

namespace GlobalTheory.HermFibreLocal

theorem exists_isFibreFamily : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (ν : Measure (Fv F v)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∃ fib : Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E), IsFibreFamily μ (fun X => qR (Fv F v) σ J (X 0)) id Set.univ ν {c | c ≠ 0} fib := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM v μ ν hμ hν
  exact (GlobalTheory.LocalDensityCompare.null_and_exists v σ J hσ hM hJ μ hμ ν hν).2

end GlobalTheory.HermFibreLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SecondCountableFiniteAdelicUnitaryPoints
section
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.CongTop

theorem secondCountable_finiteAdelicPoints : ∀ (I : AutInst), SecondCountableTopology I.Gf :=
  fun I => (adelic_topology I).2.2.1

end GlobalTheory.CongTop
end

