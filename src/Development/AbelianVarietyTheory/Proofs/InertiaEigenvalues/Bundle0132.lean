module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MapCSmulMulVec
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0113
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0123
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0122

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMatrixGamma
section
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB GlobalTheory.CycFr GlobalTheory.WachTie

noncomputable section

namespace GlobalTheory.WachTie

theorem exists_matrix_gamma : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {l : ℕ} (R : Fr l O) (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (jE : (ZMod n → R.EE) →ₐ[O] W.EE) (T : LocLat G Qp LL O) {r : ℕ} (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T)), FrTie W R j → EETie W R j jE → (∀ k, (b k : W.DD T) ∈ W.NΔ T) → ∃ Gm : ZMod n → Matrix (Fin r) (Fin r) O⟦X⟧, (∀ i, ∃ B : Matrix (Fin r) (Fin r) O⟦X⟧, Gm i = 1 + (X : O⟦X⟧) • B) ∧ (∀ k, W.γD T W.gam (b k : W.DD T) = ∑ m, (fun i => j (Gm i m k) : LetA O n) • (b m : W.DD T)) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W l R j jE T r b
    hF _ hb
  classical
  obtain ⟨-, hinv, -, -, -, hs, hX, -⟩ := hF
  have hsm : ∀ (g : W.Gam) (a : LetA O n) (x : W.DD T),
      W.γD T g (a • x) = letγ (W.γ₀ g) a • W.γD T g x := fun g a x => by
    have := W.γD_smul T g (algebraMap (LetA O n) W.EE a) x
    rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
    exact this
  have hXj : (X : O⟦X⟧) ∣ j X := by
    have h1 : (1 : W.Gam) ∈ W.DelF := (W.DelF_def 1).2 ⟨1, one_pos, one_pow _⟩
    have h2 : R.s ≠ 0 := by rw [hs]; exact (Finset.card_pos.2 ⟨1, h1⟩).ne'
    exact (dvd_pow_self _ h2).trans hX.symm.dvd
  let z : Fin r → ↥(W.N T) := fun k => ⟨W.γD T W.gam (b k : W.DD T), W.N_Γ T _ _ (b k).2⟩
  have hexp : ∀ y : ↥(W.N T), (y : W.DD T) = ∑ m, b.repr y m • (b m : W.DD T) := fun y => by
    conv_lhs => rw [← b.sum_repr y]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
  have hc : ∀ k m i, ∃ c, j c = b.repr (z k) m i := by
    intro k m i
    refine (hinv _).2 fun δ hδ => ?_
    have h1 : W.γD T δ (z k : W.DD T) = z k := by
      change W.γD T δ (W.γD T W.gam (b k : W.DD T)) = W.γD T W.gam (b k : W.DD T)
      rw [← W.γD_mul, mul_comm, W.γD_mul, (hb k).2 δ hδ]
    have h2 : z k = ∑ m, letγ (W.γ₀ δ) (b.repr (z k) m) • b m := by
      apply Subtype.ext
      rw [← h1]
      conv_lhs => rw [hexp (z k)]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, hsm, Submodule.coe_sum, Submodule.coe_smul]
      exact Finset.sum_congr rfl fun m _ => by rw [(hb m).2 δ hδ]
    have h3 : b.repr (z k) m = letγ (W.γ₀ δ) (b.repr (z k) m) := by
      conv_lhs => rw [h2]
      rw [b.repr_sum_self]
    exact (congrFun h3 i).symm
  choose c hc using hc
  refine ⟨fun i => Matrix.of fun m k => c k m i, fun i => ?_, fun k => ?_⟩
  · have hd : ∀ m k, (X : O⟦X⟧) ∣ c k m i - (1 : Matrix (Fin r) (Fin r) O⟦X⟧) m k := by
      intro m k
      obtain ⟨y, hy, hy'⟩ := W.N_π T W.gam _ (b k).2
      have h1 : z k - b k = (letπ : LetA O n) • (⟨y, hy⟩ : ↥(W.N T)) := Subtype.ext hy'
      have h2 := congrArg (fun w => b.repr w m i) h1
      simp only [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, Pi.sub_apply,
        smul_eq_mul, Pi.mul_apply, b.repr_self, letπ] at h2
      rw [X_dvd_iff, ← constantCoeff_algHom j hXj, ← X_dvd_iff, map_sub, hc]
      have h3 : j ((1 : Matrix (Fin r) (Fin r) O⟦X⟧) m k) =
          (Finsupp.single k (1 : LetA O n) : Fin r →₀ LetA O n) m i := by
        by_cases h : m = k
        · subst h; simp
        · rw [Matrix.one_apply_ne h, Finsupp.single_eq_of_ne h]; simp
      rw [h3, h2]
      exact dvd_mul_right _ _
    choose d hd using hd
    refine ⟨Matrix.of d, ?_⟩
    ext1 m k
    simp only [Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← hd]; ring
  · simp only [Matrix.of_apply, hc]
    exact hexp (z k)

end GlobalTheory.WachTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenCompactAnnihilatorScaledIntegersK
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.DualScaledIntegers

theorem exists_open_compact_annihilator : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ c : F, c ≠ 0 → ∃ D : AddSubgroup A.K, (D : Set A.K) = {b : A.K | ∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1} ∧ IsOpen (D : Set A.K) ∧ IsCompact (D : Set A.K) := by
  intro F E _ _ _ _ U A ψ hψ c hc
  have := U.ultraF
  have := U.lcF
  obtain ⟨-, -, hnd, -, -, -, -, -, -, hop, hcp, R, hR⟩ := _root_.GlobalTheory.JR.EtFacts.main F E A
  haveI : ContinuousSMul F A.K := IsModuleTopology.toContinuousSMul F A.K
  let D : AddSubgroup A.K :=
    { carrier := {b : A.K | ∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1}
      zero_mem' := by
        intro z _
        simp [Et.psiK]
      add_mem' := by
        intro a b ha hb z hz
        have h1 := ha z hz
        have h2 := hb z hz
        simp only [Et.psiK] at h1 h2 ⊢
        rw [mul_add, map_add (f := _), AddChar.map_add_eq_mul, h1, h2, one_mul]
      neg_mem' := by
        intro a ha z hz
        have h1 := ha z hz
        simp only [Et.psiK] at h1 ⊢
        rw [mul_neg, map_neg, AddChar.map_neg_eq_inv, h1, inv_one] }
  have hcs : Continuous fun z : A.K => c • z := continuous_const_smul c
  have hM : IsCompact {z : A.K | c • z ∈ A.OK} := by
    have : {z : A.K | c • z ∈ A.OK} = (fun z : A.K => c⁻¹ • z) '' A.OK := by
      ext z
      constructor
      · intro hz
        exact ⟨c • z, hz, inv_smul_smul₀ hc z⟩
      · rintro ⟨w, hw, rfl⟩
        show c • c⁻¹ • w ∈ A.OK
        rwa [smul_inv_smul₀ hc]
    rw [this]
    exact hcp.image (continuous_const_smul _)
  have htr : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap _
  have hDo : IsOpen (D : Set A.K) := by
    refine AddSubgroup.isOpen_of_mem_nhds D (g := 0) ?_
    have h := hM.eventually_forall_of_forall_eventually (x₀ := (0 : A.K))
      (P := fun b z => A.psiK ψ (z * b) = 1) (fun y _ => by
        have hc2 : Continuous fun p : A.K × A.K => Algebra.trace F A.K (p.2 * p.1) :=
          htr.comp (continuous_snd.mul continuous_fst)
        have h0 : Metric.closedBall (0 : F) 1 ∈ 𝓝 (Algebra.trace F A.K (((0 : A.K), y).2 * ((0 : A.K), y).1)) := by
          simpa using Metric.closedBall_mem_nhds (0 : F) one_pos
        filter_upwards [hc2.continuousAt.preimage_mem_nhds h0] with p hp
        exact hψ.1 _ (by simpa using hp))
    exact h
  refine ⟨D, rfl, hDo, ?_⟩
  have hU : {z : A.K | c • z ∈ A.OK} ∈ 𝓝 (0 : A.K) := by
    refine (hop.preimage hcs).mem_nhds ?_
    show c • (0 : A.K) ∈ A.OK
    rw [smul_zero, ← hR]
    exact R.zero_mem
  obtain ⟨M, N, hMU, -, -, -, hN, hMN, -⟩ :=
    (exists_small_dual_lattices F ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm F) hnd).2 _ hU
  refine hN.of_isClosed_subset (D.isClosed_of_isOpen hDo) fun b hb => ?_
  exact (hMN b).2 fun x hx => hb x (hMU hx)

end GlobalTheory.JR.DualScaledIntegers
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStableQuadraticGaussIntegral
section
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad.GaussStable

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem NL_add [Unram F E] (A : Et F E) (y m : A.L) :
    A.NL (y + m) = A.NL y + Algebra.trace A.K A.L (star m * y) + A.NL m := by
  obtain ⟨-, hinj, hN, htr, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  apply hinj
  rw [map_add (f := _), map_add (f := _), hN, hN, hN, htr, star_add, star_mul, star_star]
  ring

theorem NL_zero [Unram F E] (A : Et F E) : A.NL 0 = 0 := by
  obtain ⟨-, hinj, hN, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  apply hinj
  rw [hN, zero_mul, map_zero]

theorem formL_symm_nondeg [U : Unram F E] (A : Et F E) (v : A.Kˣ) :
    (EtMeas.formL A v).IsSymm ∧ (EtMeas.formL A v).Nondegenerate := by
  have := U.charZero
  have := EtMeas.finite_L A
  obtain ⟨-, hinj, -, htr, hnd⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  have hs : (EtMeas.formL A v).IsSymm := ⟨fun y y' => by
    rw [EtMeas.formL_apply, EtMeas.formL_apply]
    congr 2
    apply hinj
    rw [htr, htr]; simp [add_comm, mul_comm]⟩
  have hl : ∀ y', (∀ y, EtMeas.formL A v y' y = 0) → y' = 0 := fun y' h => hnd y' fun y => by
    have h1 : (v : A.K) * Algebra.trace A.K A.L (star y' * y) = 0 := EtMeas.eq_zero_of_trace F A.K _ fun k => by
      have := h (k • y)
      rw [EtMeas.formL_apply, mul_smul_comm, map_smul, smul_eq_mul] at this
      rw [← this]; congr 1; ring
    simpa using h1
  exact ⟨hs, ⟨hl, fun y h => hl y fun y' => by rw [hs.eq]; exact h y'⟩⟩


open scoped Classical in
open Classical in
theorem integral_indicator_char {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (M : AddSubgroup V)
    (hMo : IsOpen (M : Set V)) (χ : V → ℂ) (hχ : ∀ a b, χ (a + b) = χ a * χ b) :
    ∫ m, (M : Set V).indicator χ m ∂μ = if ∀ m ∈ M, χ m = 1 then (μ.real (M : Set V) : ℂ) else 0 := by
  classical
  split_ifs with h
  · rw [show (M : Set V).indicator χ = (M : Set V).indicator (fun _ => (1 : ℂ)) from
      Set.indicator_congr (fun m hm => h m hm), integral_indicator_const _ hMo.measurableSet]
    simp
  · push Not at h
    obtain ⟨m0, hm0, h1⟩ := h
    refine AbsInv.integral_eq_zero_of_translate μ _ m0 (χ m0) h1 fun m => ?_
    by_cases hm : m ∈ M
    · rw [Set.indicator_of_mem (by exact M.add_mem hm hm0), Set.indicator_of_mem (by exact hm), hχ, mul_comm]
    · have h2 : m + m0 ∉ M := fun h' => hm (by simpa using M.sub_mem h' hm0)
      rw [Set.indicator_of_notMem (by exact h2), Set.indicator_of_notMem (by exact hm), mul_zero]

end GlobalTheory.JR.WeilQuad.GaussStable


open GlobalTheory.JR.WeilQuad.GaussStable in
theorem GlobalTheory.JR.WeilQuad.exists_stableGauss : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L)
    (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ u : A.Kˣ, ∃ G, IsStableGauss A ψ x μ u G := by
  intro F E _ _ _ _ hU A ψ x μ ω h u
  classical
  obtain ⟨-, -, hψ, hsd, -⟩ := h
  haveI := hsd.1
  haveI : IsUltrametricDist F := hU.ultraF
  haveI : LocallyCompactSpace F := hU.lcF
  haveI := EtMeas.finite_L A
  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  set β := EtMeas.formL A ((u * x : A.Kˣ) : A.K) with hβ
  set f : A.L → ℂ := fun y => A.psiK ψ ((u : A.K) * x * A.NL y) with hf
  have htr : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap _
  have hin : Continuous fun y : A.L => Algebra.trace F A.K ((u : A.K) * x * A.NL y) :=
    htr.comp (continuous_const.mul (GlobalTheory.JR.EtMeas.continuous_NL A))
  have hflc : IsLocallyConstant f := (isLocallyConstant_of_stdChar hψ).comp_continuous hin
  have hfc : Continuous f := hflc.continuous
  have hkey : ∀ y m, f (y + m) = f y * ψ (β m y) * f m := by
    intro y m
    simp only [hf, hβ, EtMeas.formL_apply, Units.val_mul, NL_add A, Et.psiK, mul_add, map_add (f := _),
      AddChar.map_add_eq_mul]
  have hf0 : f 0 = 1 := by simp [hf, NL_zero A, Et.psiK]
  obtain ⟨-, hsmall⟩ := GlobalTheory.JR.exists_small_dual_lattices F ψ hψ A.L β
    (formL_symm_nondeg A (u * x)).1 (formL_symm_nondeg A (u * x)).2
  obtain ⟨M, N, hMU, hMo, hMc, hNo, hNc, hN, -⟩ :=
    hsmall {y | f y = 1} ((hflc.isOpen_fiber 1).mem_nhds hf0)
  have hfM : ∀ m ∈ M, f m = 1 := fun m hm => hMU hm
  have hMpos : μ.real (M : Set A.L) ≠ 0 :=
    (ENNReal.toReal_pos (hMo.measure_pos μ ⟨0, M.zero_mem⟩).ne' hMc.measure_lt_top.ne).ne'
  refine ⟨∫ y in (N : Set A.L), f y ∂μ, M ⊔ N, AddSubgroup.isOpen_mono le_sup_left hMo, ?_, ?_⟩
  · refine (hMc.add hNc).of_isClosed_subset
      (AddSubgroup.isClosed_of_isOpen _ (AddSubgroup.isOpen_mono le_sup_left hMo)) ?_
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.1 hz
    exact Set.add_mem_add ha hb
  intro Λ hΛo hΛc hle
  have hMΛ : M ≤ Λ := le_sup_left.trans hle
  have hNΛ : N ≤ Λ := le_sup_right.trans hle
  set iM : A.L → ℂ := (M : Set A.L).indicator (fun _ => 1) with hiM
  set iΛ : A.L → ℂ := (Λ : Set A.L).indicator (fun _ => 1) with hiΛ
  have hiMc : Continuous iM :=
    IsClopen.continuous_indicator ⟨AddSubgroup.isClosed_of_isOpen _ hMo, hMo⟩ continuous_const
  have hiΛc : Continuous iΛ :=
    IsClopen.continuous_indicator ⟨AddSubgroup.isClosed_of_isOpen _ hΛo, hΛo⟩ continuous_const
  let g : A.L → A.L → ℂ := fun m y => iM m * (iΛ y * f (y + m))
  have hgc : Continuous (Function.uncurry g) :=
    (hiMc.comp continuous_fst).mul ((hiΛc.comp continuous_snd).mul (hfc.comp (continuous_snd.add continuous_fst)))
  have hgs : HasCompactSupport (Function.uncurry g) := by
    refine HasCompactSupport.intro (hMc.prod hΛc) ?_
    rintro ⟨m, y⟩ hp
    simp only [Set.mem_prod, not_and_or] at hp
    rcases hp with hp | hp
    · have : iM m = 0 := by rw [hiM, Set.indicator_of_notMem hp]
      simp [Function.uncurry, g, this]
    · have : iΛ y = 0 := by rw [hiΛ, Set.indicator_of_notMem hp]
      simp [Function.uncurry, g, this]
  have hswap := integral_integral_swap_of_hasCompactSupport hgc hgs (μ := μ) (ν := μ)
  have hA : ∀ m, ∫ y, g m y ∂μ = iM m * ∫ y in (Λ : Set A.L), f y ∂μ := by
    intro m
    by_cases hm : m ∈ M
    · have e : ∀ y, iΛ y * f (y + m) = (Λ : Set A.L).indicator f (y + m) := by
        intro y
        by_cases hy : y ∈ Λ
        · rw [hiΛ, Set.indicator_of_mem (by exact hy), Set.indicator_of_mem (by exact Λ.add_mem hy (hMΛ hm)), one_mul]
        · have h2 : y + m ∉ Λ := fun h' => hy (by simpa using Λ.sub_mem h' (hMΛ hm))
          rw [hiΛ, Set.indicator_of_notMem (by exact hy), Set.indicator_of_notMem (by exact h2), zero_mul]
      simp only [g]
      rw [integral_const_mul]
      congr 1
      simp_rw [e]
      rw [integral_add_right_eq_self (μ := μ) ((Λ : Set A.L).indicator f) m,
        integral_indicator hΛo.measurableSet]
    · have h1 : iM m = 0 := by rw [hiM, Set.indicator_of_notMem (by exact hm)]
      simp [g, h1]
  have hB : ∀ y, ∫ m, g m y ∂μ = (N : Set A.L).indicator (fun y => (μ.real (M : Set A.L) : ℂ) * f y) y := by
    intro y
    have e : ∀ m, g m y = iΛ y * f y * (M : Set A.L).indicator (fun m => ψ (β m y)) m := by
      intro m
      by_cases hm : m ∈ M
      · have h1 : iM m = 1 := by rw [hiM, Set.indicator_of_mem (by exact hm)]
        have h2 : (M : Set A.L).indicator (fun m => ψ (β m y)) m = ψ (β m y) :=
          Set.indicator_of_mem (by exact hm) _
        simp only [g]
        rw [h1, h2, hkey, hfM m hm]; ring
      · have h1 : iM m = 0 := by rw [hiM, Set.indicator_of_notMem (by exact hm)]
        have h2 : (M : Set A.L).indicator (fun m => ψ (β m y)) m = 0 :=
          Set.indicator_of_notMem (by exact hm) _
        simp only [g]
        rw [h1, h2]; ring
    simp_rw [e]
    rw [integral_const_mul, integral_indicator_char μ M hMo (fun m => ψ (β m y))
      (fun a b => by simp [map_add (f := _), AddChar.map_add_eq_mul])]
    by_cases hy : y ∈ N
    · rw [if_pos ((hN y).1 hy), Set.indicator_of_mem (by exact hy), hiΛ, Set.indicator_of_mem (by exact hNΛ hy)]
      ring
    · rw [if_neg (fun h' => hy ((hN y).2 h')), Set.indicator_of_notMem (by exact hy), mul_zero]
  have h1 : ∫ m, ∫ y, g m y ∂μ ∂μ = (μ.real (M : Set A.L) : ℂ) * ∫ y in (Λ : Set A.L), f y ∂μ := by
    simp_rw [hA]
    rw [integral_mul_const, hiM, integral_indicator_const _ hMo.measurableSet]
    simp
  have h2 : ∫ y, ∫ m, g m y ∂μ ∂μ = (μ.real (M : Set A.L) : ℂ) * ∫ y in (N : Set A.L), f y ∂μ := by
    simp_rw [hB]
    rw [integral_indicator hNo.measurableSet, integral_const_mul]
  have hmain := h1.symm.trans (hswap.trans h2)
  unfold gaussInt
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hMpos) hmain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIntegralClosureOfSeparableInvolutionAlgebr
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma.IntegralFinite

open Matrix

theorem isIntegral_matrix_trace {R F : Type} [CommRing R] [Field F] [Algebra R F] {n : Type}
    [Fintype n] [DecidableEq n] (M : Matrix n n F) (hM : IsIntegral R M) : IsIntegral R M.trace := by
  first
  | exact @_root_.GlobalTheory.TargetStatementAlt.target
  | exact _root_.GlobalTheory.TargetStatementAlt.target
  | (apply _root_.GlobalTheory.TargetStatementAlt.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.TargetStatementAlt.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TargetStatementAlt.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TargetStatementAlt.target ..)

variable {K : UQ} (B : InvAlg K)

theorem isIntegral_trace {x : B.A} (hx : IsIntegral K.O x) :
    IsIntegral K.O (Algebra.trace K.E B.A x) := by
  let bs := Module.finBasis K.E B.A
  rw [Algebra.trace_eq_matrix_trace bs]
  exact isIntegral_matrix_trace _ (hx.map ((Algebra.leftMulMatrix bs).restrictScalars K.O))

theorem trace_mem_range {x : B.A} (hx : IsIntegral K.O x) :
    ∃ c : K.O, algebraMap K.O K.E c = Algebra.trace K.E B.A x :=
  IsIntegrallyClosed.isIntegral_iff.mp (isIntegral_trace B hx)

theorem finite_integralClosure :
    ∀ (K : UQ) (B : InvAlg K), B.P.Separable → Module.Finite K.O (integralClosure K.O B.A) := by
  intro K B hsep
  classical
  let bs := Module.finBasis K.E B.A
  haveI : Algebra.IsAlgebraic K.O K.E := IsLocalization.isAlgebraic K.E (nonZeroDivisors K.O)
  haveI : Algebra.IsAlgebraic K.O B.A := Algebra.IsAlgebraic.trans K.O K.E B.A
  obtain ⟨y, hy, hint⟩ := Algebra.IsAlgebraic.exists_integral_multiples K.O (Finset.univ.image bs)
  have hy' : algebraMap K.O K.E y ≠ 0 := by
    intro h
    exact hy (IsFractionRing.injective K.O K.E (by rw [h, map_zero]))
  let b := bs.isUnitSMul (w := fun _ => algebraMap K.O K.E y) (fun _ => (Ne.isUnit hy'))
  have hbint : ∀ i, IsIntegral K.O (b i) := by
    intro i
    have h := hint (bs i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    simpa [b, Module.Basis.isUnitSMul_apply, algebraMap_smul] using h
  have hnd : (Algebra.traceForm K.E B.A).Nondegenerate := by
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · exact Centraliser.eq_zero_of_trace_mul B hsep a (fun z => by simpa [Algebra.traceForm_apply] using ha z)
    · exact Centraliser.eq_zero_of_trace_mul B hsep a
        (fun z => by simpa [Algebra.traceForm_apply, mul_comm] using ha z)
  let d := (Algebra.traceForm K.E B.A).dualBasis hnd b
  have hle : Subalgebra.toSubmodule (integralClosure K.O B.A) ≤ Submodule.span K.O (Set.range d) := by
    intro x hx
    have hx' : IsIntegral K.O x := hx
    rw [← d.sum_repr x]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c, hc⟩ := trace_mem_range B (hx'.mul (hbint i))
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, ← hc, algebraMap_smul]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨i, rfl⟩)
  haveI : IsNoetherian K.O (Submodule.span K.O (Set.range d)) :=
    isNoetherian_span_of_finite K.O (Set.finite_range d)
  haveI : IsNoetherian K.O (Subalgebra.toSubmodule (integralClosure K.O B.A)) := isNoetherian_of_le hle
  exact Module.IsNoetherian.finite K.O (Subalgebra.toSubmodule (integralClosure K.O B.A))

end GlobalTheory.UnitLemma.IntegralFinite
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FisSelfReNonneg
section
noncomputable section

open MvPolynomial

namespace GlobalTheory.FockIsotypic

variable {σ : Type} [Fintype σ]

def flat (σ : Type) [Fintype σ] : σ ≃ Fin (Fintype.card σ) × Unit :=
  (Fintype.equivFin σ).trans (Equiv.prodPUnit _).symm

def fis (P Q : MvPolynomial σ ℂ) : ℂ :=
  ReciprocityTheory.PGsh.fischer (rename (flat σ) P) (rename (flat σ) Q)

theorem fis_conj (P Q : MvPolynomial σ ℂ) : starRingEnd ℂ (fis P Q) = fis Q P := by
  classical
  unfold fis
  set P' := rename (flat σ) P
  set Q' := rename (flat σ) Q
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ReciprocityTheory.PGsh.fischer_eq_sum P' Q' (P'.support ∪ Q'.support) Finset.subset_union_left,
    ReciprocityTheory.PGsh.fischer_eq_sum Q' P' (P'.support ∪ Q'.support) Finset.subset_union_right, map_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  simp only [ReciprocityTheory.PGsh.fw, map_mul, Complex.conj_conj, map_natCast]
  ring

theorem fis_self_re_nonneg (P : MvPolynomial σ ℂ) : 0 ≤ (fis P P).re := by
  classical
  unfold fis
  set P' := rename (flat σ) P
  rw [ReciprocityTheory.PGsh.fischer_eq_sum P' P' P'.support subset_rfl, Complex.re_sum]
  refine Finset.sum_nonneg fun A _ => ?_
  rw [Complex.mul_conj, ReciprocityTheory.PGsh.fw, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

theorem fis_self_ne_zero {P : MvPolynomial σ ℂ} (hP : P ≠ 0) : fis P P ≠ 0 :=
  ReciprocityTheory.PGsh.fischer_self_ne_zero _ fun h =>
    hP (rename_injective _ (flat σ).injective (h.trans (map_zero _).symm))

theorem fis_add_right (P Q Q' : MvPolynomial σ ℂ) : fis P (Q + Q') = fis P Q + fis P Q' := by
  unfold fis
  rw [map_add (f := _), ReciprocityTheory.PGsh.fischer_add_right]

theorem fis_smul_right (c : ℂ) (P Q : MvPolynomial σ ℂ) : fis P (c • Q) = starRingEnd ℂ c * fis P Q := by
  unfold fis
  rw [map_smul, ReciprocityTheory.PGsh.fischer_smul_right]

theorem fis_smul_left (c : ℂ) (P Q : MvPolynomial σ ℂ) : fis (c • P) Q = c * fis P Q := by
  unfold fis
  rw [map_smul, ReciprocityTheory.PGsh.fischer_smul_left]

@[reducible] def fisCore (S : Submodule ℂ (MvPolynomial σ ℂ)) : InnerProductSpace.Core ℂ S where
  inner x y := fis y.1 x.1
  conj_inner_symm x y := fis_conj _ _
  re_inner_nonneg x := fis_self_re_nonneg _
  add_left x y z := fis_add_right _ _ _
  smul_left x y r := fis_smul_right _ _ _
  definite x hx := by
    by_contra h
    exact fis_self_ne_zero (fun h' => h (Subtype.ext h')) hx

end GlobalTheory.FockIsotypic

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeCountAndGramDetSignNormClassStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeCount_and_gramDetSign_norm_class : ∀ (K : UQ) (B : InvAlg K) (x : B.A) (u : B.Aˣ), B.N (x * (u * B.σ (u : B.A))) = B.N x ∧ K.eta (B.gramDet (x * (u * B.σ (u : B.A)))) = K.eta (B.gramDet x) := by
  first | exact @GlobalTheory.UnitLemma.NormClass.N_norm_class | exact GlobalTheory.UnitLemma.NormClass.N_norm_class | (intros; apply GlobalTheory.UnitLemma.NormClass.N_norm_class <;> assumption)
end

