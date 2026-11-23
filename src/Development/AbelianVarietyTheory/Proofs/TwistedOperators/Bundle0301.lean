module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLines
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1216
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0288
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarAtOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1032
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0290
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralMulRightOfCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0280

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetAdelicUnitaryPreservesLatticeAlmostA
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertSph Matrix Filter
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LatAlmostAll

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem eventually_integral (a : AF F) : ∀ᶠ v : Pl F in cofinite, evFin F v a ∈ v.adicCompletionIntegers F :=
  a.2.2

theorem smul_mem_latAt (X : Spc F E n) (w : Pl (F := F)) {b : AF F} (hb : evFin F w b ∈ w.adicCompletionIntegers F)
    {z : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (hz : z ∈ latAt X w) : b • z ∈ latAt X w := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hv, y, hy, rfl⟩ := hz
    rw [smul_smul]
    refine AddSubgroup.subset_closure ⟨b * a, ?_, ?_, y, hy, rfl⟩
    · intro u hu
      rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]
    · rw [map_mul]
      exact mul_mem hb hv
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem exists_int_smul_mem (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsFullLattice E) (v : Fin n → E) :
    ∃ c : ℤ, c ≠ 0 ∧ c • v ∈ L := by
  exact _root_.GlobalTheory.IntSmulMemLatticeTwistedOperators.exists_nonzero_int_smul_mem_of_isLattice L hL v

theorem exists_int_mulVec_mem (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsFullLattice E) (N : Matrix (Fin n) (Fin n) E) :
    ∃ c : ℤ, c ≠ 0 ∧ ∀ y ∈ L, c • (N *ᵥ y) ∈ L := by
  have key : ∀ L' : Submodule (𝓞 E) (Fin n → E), L'.FG → ∃ c : ℤ, c ≠ 0 ∧ ∀ y ∈ L', c • (N *ᵥ y) ∈ L := by
    intro L' hL'
    induction L', hL' using Submodule.fg_induction with
    | singleton x =>
      obtain ⟨c, hc, hx⟩ := exists_int_smul_mem L hL (N *ᵥ x)
      refine ⟨c, hc, fun y hy => ?_⟩
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [Matrix.mulVec_smul, smul_comm]
      exact L.smul_mem r hx
    | sup A B _ _ hA hB =>
      obtain ⟨c, hc, hA⟩ := hA
      obtain ⟨d, hd, hB⟩ := hB
      refine ⟨c * d, mul_ne_zero hc hd, fun y hy => ?_⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
      rw [Matrix.mulVec_add, smul_add]
      refine add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact zsmul_mem (hA a ha) d
      · rw [mul_smul]; exact zsmul_mem (hB b hb) c
  exact key L hL.fg

theorem eventually_incM (X : Spc F E n) (hL : X.L.IsFullLattice E) (N : Matrix (Fin n) (Fin n) E) :
    ∀ᶠ w : Pl F in cofinite, ∀ z ∈ latAt X w, incM F N *ᵥ z ∈ latAt X w := by
  obtain ⟨c, hc, hN⟩ := exists_int_mulVec_mem X.L hL N
  filter_upwards [eventually_integral (algebraMap F (AF F) (c : F)⁻¹)] with w hw z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hv, y, hy, rfl⟩ := hz
    have h1 : (a • fun i => inclR (F := F) (AF F) ((c • (N *ᵥ y)) i)) ∈ latAt X w :=
      AddSubgroup.subset_closure ⟨a, ha, hv, _, hN y hy, rfl⟩
    have h2 := smul_mem_latAt X w hw h1
    convert h2 using 1
    rw [Matrix.mulVec_smul, smul_comm]
    congr 1
    ext i
    have hc' : (c : F) ≠ 0 := Int.cast_ne_zero.2 hc
    have h3 : (incM F N *ᵥ fun i => inclR (F := F) (AF F) (y i)) i = inclR (F := F) (AF F) ((N *ᵥ y) i) :=
      (RingHom.map_mulVec (inclR (F := F) (AF F)) N y i).symm
    rw [h3, Pi.smul_apply, Pi.smul_apply, map_zsmul, algebraMap_smul, ← Int.cast_smul_eq_zsmul F, smul_smul,
      inv_mul_cancel₀ hc', one_smul]
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mulVec_neg]; exact neg_mem hx

theorem eventually_single (X : Spc F E n) (hL : X.L.IsFullLattice E) (i j : Fin n) (t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    ∀ᶠ w : Pl F in cofinite, ∀ z ∈ latAt X w, Matrix.single i j t *ᵥ z ∈ latAt X w := by
  induction t using TensorProduct.induction_on with
  | zero => exact Eventually.of_forall fun w z _ => by simp [zero_mem]
  | tmul a e =>
    have h : Matrix.single i j (a ⊗ₜ[F] e : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = a • incM F (Matrix.single i j e) := by
      ext k l
      simp only [incM, Matrix.smul_apply, Matrix.map_apply, Matrix.single_apply]
      split_ifs
      · simp [inclR, TensorProduct.smul_tmul']
      · simp
    filter_upwards [eventually_integral a, eventually_incM X hL (Matrix.single i j e)] with w hw h2 z hz
    rw [h, Matrix.smul_mulVec]
    exact smul_mem_latAt X w hw (h2 z hz)
  | add s t hs ht =>
    filter_upwards [hs, ht] with w h1 h2 z hz
    rw [Matrix.single_add, Matrix.add_mulVec]
    exact add_mem (h1 z hz) (h2 z hz)

theorem eventually_mulVec_mem (X : Spc F E n) (hL : X.L.IsFullLattice E) (M : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    ∀ᶠ w : Pl F in cofinite, ∀ z ∈ latAt X w, M *ᵥ z ∈ latAt X w := by
  have h : ∀ᶠ w : Pl F in cofinite, ∀ i j, ∀ z ∈ latAt X w, Matrix.single i j (M i j) *ᵥ z ∈ latAt X w :=
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_single X hL i j (M i j)
  filter_upwards [h] with w hw z hz
  rw [Matrix.matrix_eq_sum_single M, Matrix.sum_mulVec]
  refine sum_mem fun i _ => ?_
  rw [Matrix.sum_mulVec]
  exact sum_mem fun j _ => hw i j z hz

theorem exists_finset_keeps : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n), X.L.IsFullLattice E → ∀ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J,
    ∃ S₁ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ w ∉ S₁, ∀ z ∈ GlobalTheory.InertSph.latAt X w,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g *ᵥ z ∈ GlobalTheory.InertSph.latAt X w ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt X w := by
  intro F E _ _ _ _ _ σ n X hL g
  have h := (eventually_mulVec_mem X hL (mat g)).and (eventually_mulVec_mem X hL (mat g⁻¹))
  refine ⟨(eventually_cofinite.1 h).toFinset, fun w hw z hz => ?_⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hw
  exact ⟨hw.1 z hz, hw.2 z hz⟩

end GlobalTheory.LatAlmostAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKernelApprox
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory

namespace GlobalTheory.KernelApprox

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem thetaKO_sub (g : GA D S) (h : GA D T) (f f' : WO S T → ℂ) :
    thetaKO om g h f - thetaKO om g h f' = thetaKO om g h (f - f') := by
  simp only [thetaKO, map_sub, Pi.sub_apply]

theorem exists_kernel_approx (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ S T χS χT om) (P : (WO S T → ℂ) → Prop)
    {Φ : WO S T → ℂ} (hΦ : IsThetaFunO ψ S T Φ)
    (hden : ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → Φ ∈ GlobalTheory.Size.thetaLevel ψ S T U →
      ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (d : ℕ) (ε : ℝ), 0 < ε →
        ∃ X, P X ∧ X ∈ GlobalTheory.Size.thetaLevel ψ S T U ∧ GlobalTheory.Size.sobO ψ θ μ 𝓕 d (X - Φ) < ENNReal.ofReal ε) :
    ∃ a : ℕ, ∀ ε : ℝ, 0 < ε → ∃ X, P X ∧ ∀ g h,
      ‖thetaKO om g h X - thetaKO om g h Φ‖ ≤ ε * GlobalTheory.Grow.quotHeight S g ^ a * GlobalTheory.Grow.quotHeight T h ^ a := by
  obtain ⟨a, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D S.rank T.rank
  obtain ⟨U, hU, hΦU⟩ := GlobalTheory.Size.isTheta_iff_level.1 hΦ
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.Size.exists_isCovolOne S T
  obtain ⟨C, hC0, hC⟩ := (H _ _ rfl rfl).real ψ hθ hU
  refine ⟨a, fun ε hε => ?_⟩
  have hK : 0 < (C + 1) * 4 ^ a := by positivity
  obtain ⟨X, hPX, hXU, hsob⟩ := hden U hU hΦU μ 𝓕 hμ d (ε / ((C + 1) * 4 ^ a)) (div_pos hε hK)
  refine ⟨X, hPX, fun g h => ?_⟩
  have hΨ : X - Φ ∈ GlobalTheory.Size.thetaLevel ψ S T U := Submodule.sub_mem _ hXU hΦU
  rw [thetaKO_sub]
  obtain ⟨-, hb⟩ := hC _ _ _ hω μ 𝓕 hμ (X - Φ) hΨ
  have hsr : (GlobalTheory.Size.sobO ψ θ μ 𝓕 d (X - Φ)).toReal ≤ ε / ((C + 1) * 4 ^ a) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsob.le
    rwa [ENNReal.toReal_ofReal (div_pos hε hK).le] at this
  obtain ⟨γ, hγ, h1⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight S g
  obtain ⟨γ', hγ', h2⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight T h
  rw [← GlobalTheory.ChainOnto.ThetaSwap.thetaKO_left_fst hω hΨ.1 γ hγ g h,
    ← GlobalTheory.Chain.LiftConv.thetaKO_left hω hΨ.1 (γ * g) γ' hγ' h]
  have hq1 := GlobalTheory.Grow.quotHeight_pos S g
  have hq2 := GlobalTheory.Grow.quotHeight_pos T h
  have hh1 := GlobalTheory.Grow.height_pos S (γ * g)
  have hh2 := GlobalTheory.Grow.height_pos T (γ' * h)
  have hs0 : 0 ≤ (GlobalTheory.Size.sobO ψ θ μ 𝓕 d (X - Φ)).toReal := ENNReal.toReal_nonneg
  have hpow : (GlobalTheory.Grow.height S (γ * g) * GlobalTheory.Grow.height T (γ' * h)) ^ a ≤
      4 ^ a * (GlobalTheory.Grow.quotHeight S g ^ a * GlobalTheory.Grow.quotHeight T h ^ a) := by
    rw [← mul_pow, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) a
  have hne : (C + 1) * 4 ^ a ≠ 0 := hK.ne'
  calc ‖thetaKO om (γ * g) (γ' * h) (X - Φ)‖
      ≤ C * (GlobalTheory.Size.sobO ψ θ μ 𝓕 d (X - Φ)).toReal *
          (GlobalTheory.Grow.height S (γ * g) * GlobalTheory.Grow.height T (γ' * h)) ^ a := hb _ _
    _ ≤ (C + 1) * (ε / ((C + 1) * 4 ^ a)) * (4 ^ a * (GlobalTheory.Grow.quotHeight S g ^ a * GlobalTheory.Grow.quotHeight T h ^ a)) :=
        mul_le_mul (mul_le_mul (by linarith) hsr hs0 (by linarith)) hpow (pow_nonneg (mul_pos hh1 hh2).le a)
          (mul_nonneg (by linarith) (div_pos hε hK).le)
    _ = ((C + 1) * 4 ^ a) * (ε / ((C + 1) * 4 ^ a)) * (GlobalTheory.Grow.quotHeight S g ^ a * GlobalTheory.Grow.quotHeight T h ^ a) := by
        ring
    _ = ε * GlobalTheory.Grow.quotHeight S g ^ a * GlobalTheory.Grow.quotHeight T h ^ a := by
        rw [mul_div_cancel₀ _ hne]; ring

end GlobalTheory.KernelApprox

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParamSubgroupTransposeGramLieAt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.KapXLine

variable {D : D7}

theorem kapX_mul (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (g h : GA D X) :
    kapX X e hJ (g * h) = kapX X e hJ g * kapX X e hJ h := by
  apply Subtype.ext
  show Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e).toMonoidHom (matHom X (g * h)) =
    Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e).toMonoidHom (matHom X g) *
      Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e).toMonoidHom (matHom X h)
  rw [map_mul, map_mul]

theorem kapX_one (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) : kapX X e hJ 1 = 1 := by
  apply Subtype.ext
  show Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e).toMonoidHom (matHom X 1) = 1
  rw [map_one, map_one]

theorem continuous_kapX (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) : Continuous (kapX X e hJ) := by
  have h1 : Continuous (matHom X) := continuous_subtype_val
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact (Units.continuous_val.comp h1).matrix_reindex e e
  · exact (Units.continuous_coe_inv.comp h1).matrix_reindex e e

theorem smul_eq_zero_of_finTens {u : AF D.host.F} (hu : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F u = 0) {z : AE D}
    (hz : GlobalTheory.LFun.finTens D.host.F D.host.E z = 0) : u • z = 0 := by
  have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).injective (hu.trans (map_zero _).symm)
  refine GlobalTheory.LFun.tens_ext ?_ ?_
  · rw [Algebra.smul_def, map_mul, map_zero]
    change (u.1 ⊗ₜ[D.host.F] (1 : D.host.E)) * _ = 0
    rw [hu1, TensorProduct.zero_tmul, zero_mul]
  · rw [Algebra.smul_def, map_mul, map_zero, hz, mul_zero]

theorem kapX_mem_UAt (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) (Wd : Spc D.host.F D.host.E d)
    (hJ : Wd.J = D.host.xi0 • reindex e e X.gramᵀ) {g : GA D X} (hg : g ∈ GinfC X) :
    kapX X e hJ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Wd (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) := by
  intro u hu
  have hf : finHom X g = 1 := hg
  have hent : ∀ a b, GlobalTheory.LFun.finTens D.host.F D.host.E (Formalism.L2.Theta.mt X g a b) =
      (1 : Matrix (Fin X.rank) (Fin X.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) a b := by
    intro a b
    have := congrArg (fun k : GL (Fin X.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) => k.1 a b) hf
    exact this
  ext i j
  rw [mat_kapX]
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply, reindex_apply, submatrix_apply]
  apply smul_eq_zero_of_finTens hu
  rw [map_sub, hent, Matrix.one_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · have h' : e.symm i ≠ e.symm j := fun k => h (e.symm.injective k)
    simp [h, h']

end GlobalTheory.KapXLine

open GlobalTheory.KapXLine in
theorem GlobalTheory.KapXLine.exists_line : ∀ (D : D7) (θ : InfFam D) (X : HSp D) (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ),
    IsInfFam θ → Y ∈ lieAt X τ → ∀ {d : ℕ} (e : Fin X.rank ≃ Fin d) (Wd : Spc D.host.F D.host.E d)
    (hJ : Wd.J = D.host.xi0 • reindex e e X.gramᵀ),
    ∃ γ ∈ Lines D.sp.cm.sig Wd, ∀ t : ℝ, γ (Multiplicative.ofAdd t) = kapX X e hJ (oneP θ X τ Y t) := by
  intro D θ X τ Y hθ hY d e Wd hJ
  let γ : Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Wd.J :=
    { toFun := fun t => kapX X e hJ (oneP θ X τ Y (Multiplicative.toAdd t))
      map_one' := by
        show kapX X e hJ (oneP θ X τ Y 0) = 1
        rw [GlobalTheory.Mem.Lift.oneP_zero hθ, kapX_one]
      map_mul' := fun s t => by
        show kapX X e hJ (oneP θ X τ Y (Multiplicative.toAdd s + Multiplicative.toAdd t)) = _
        rw [GlobalTheory.Mem.Lift.oneP_add hθ hY, kapX_mul] }
  refine ⟨γ, ⟨?_, fun t => ?_⟩, fun t => rfl⟩
  · exact (continuous_kapX X e hJ).comp ((GlobalTheory.Mem.Lift.continuous_oneP hθ hY).comp continuous_toAdd)
  · exact kapX_mem_UAt X e Wd hJ (GlobalTheory.Mem.Lift.isAtTau_oneP hθ hY _).1

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParameterInUnitaryArchimedeanMaxCompact
section
noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.CompactLine

theorem incM_map_piInf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m : ℕ}
    (J : Matrix (Fin m) (Fin m) E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, inclR, compInf, infEmb_tmul]

theorem commute_of_gen {β : Type} [Fintype β] [DecidableEq β] {R S : ℕ} (C : Matrix β (Ix R S) ℂ)
    (A' : Matrix (Ix R S) β ℂ) (hCA : C * A' = 1) (g θ : Matrix β β ℂ) (Y : Mat R S) (hY : IsKC Y) (t : ℝ)
    (hθ : θ * C = C * Jm R S) (hg : g * C = C * NormedSpace.exp (t • Y)) : Commute g θ := by
  have h1 : Commute Y (Jm R S) := (GlobalTheory.CartanInt.UnitLog.isKC_iff_commute Y).1 hY
  have h2 : Commute (NormedSpace.exp (t • Y)) (Jm R S) := (h1.smul_left t).exp_left
  have h3 : g * θ * C = θ * g * C := by
    rw [Matrix.mul_assoc, hθ, ← Matrix.mul_assoc, hg, Matrix.mul_assoc θ, hg, ← Matrix.mul_assoc θ, hθ,
      Matrix.mul_assoc, Matrix.mul_assoc, h2.eq]
  calc g * θ = g * θ * C * A' := by rw [Matrix.mul_assoc _ C, hCA, Matrix.mul_one]
    _ = θ * g := by rw [h3, Matrix.mul_assoc _ C, hCA, Matrix.mul_one]

theorem exists_line_in_kInf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ X B.emb, ∃ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, γ (Multiplicative.ofAdd (1 : ℝ)) = k ∧
      ∀ t, γ t ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ X B.emb := by
  intro F E _ _ _ _ _ σ B n X r s hb hX k hk
  choose A hA hAθ using fun w => GlobalTheory.RealLift.frameEx_holds n r s _ (X.θ w) (hX.sig w) (hX.cartan w)
  have hA1 : ∀ w, GlobalTheory.RealLift.IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf, one_smul]; exact hA w
  obtain ⟨γ, hγ, Y, hgen, hKC, hγ1⟩ := GlobalTheory.RealLift.kLine_of_lineEx GlobalTheory.RealLift.exists_line_of_upq F E σ (Fin n) r s
    B.emb (incM F X.J) 1 A X.θ hb.cm hA1 hAθ k hk.1 hk.2
  refine ⟨γ, hγ, hγ1, fun t => ⟨hγ.2 t, fun w => ?_⟩⟩
  obtain ⟨A', hAA⟩ := (hA w).2
  exact commute_of_gen (A w) A' hAA _ _ (Y w) (hKC w) t.toAdd (hAθ w) (hgen t.toAdd w)

end GlobalTheory.CompactLine

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TripleAssembly

section Darboux

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def darbAlg {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z)
    (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (E := E) w) : Submodule ℂ ((Fin n × Fin d → AF F) → ℂ) :=
  Submodule.span ℂ {Φ | ∃ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
      f ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.Pol M ψ τ ∧ (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) ∧
      (∀ᶠ v in Filter.cofinite, φ v = M.vac v) ∧ Φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ}


open Classical in
def liftPure {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z)
    {P : Type} [AddCommGroup P] [Module ℂ P] (pr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] P)
    {N : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) → Type} [∀ v, AddCommGroup (N v)] [∀ v, Module ℂ (N v)]
    (pv : ∀ v, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] N v) (s : ∀ v, N v) :
    ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] P ⊗[ℂ] GlobalTheory.SmallThetaModules.RTens s :=
  if H : ∃ q : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] P ⊗[ℂ] GlobalTheory.SmallThetaModules.RTens s,
      ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        q (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = pr f ⊗ₜ GlobalTheory.SmallThetaModules.pureT s (fun v => pv v (φ v))
  then H.choose else 0

end Darboux

theorem exists_rtensOp {ι : Type} {N : ι → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)] (s : ∀ i, N i)
    (a : ∀ i, Module.End ℂ (N i)) :
    ∃ T : Module.End ℂ (GlobalTheory.SmallThetaModules.RTens s), ∀ ξ, Formalism.MainNotions.KudlaSiegelWeil.Restr s ξ →
      T (GlobalTheory.SmallThetaModules.pureT s ξ) = GlobalTheory.SmallThetaModules.pureT s (fun i => a i (ξ i)) :=
  GlobalTheory.SmallThetaModules.exists_lift s (GlobalTheory.SmallThetaModules.pureT s)
    (fun l hl => GlobalTheory.SmallThetaModules.pureT_sep s l hl) s a

variable {D : D7}

def vacIm {a a' : ℕ} (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F a a') :
    ∀ v, Rf.Pi v := fun v => Rf.p v (Γ.M.vac v)

abbrev PiT {a a' : ℕ} (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F a a') (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F a a') : Type :=
  R.Pi ⊗[ℂ] GlobalTheory.SmallThetaModules.RTens (vacIm Γ Rf)


open Classical in
def thetaLift {m k d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E m} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k}
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z) (ψ : AddChar (AF D.host.F) ℂ) (G : Matrix (Fin m) (Fin m) D.host.E)
    (e : Fin k ≃ Fin d) (S : Submodule ℂ ((Fin m × Fin k → AF D.host.F) → ℂ)) {P : Type} [AddCommGroup P] [Module ℂ P]
    (pD : ((Fin m × Fin k → AF D.host.F) → ℂ) →ₗ[ℂ] P) : (Matrix (Fin d) (Fin m) (AE D) → ℂ) →ₗ[ℂ] P :=
  if H : ∃ q : (Matrix (Fin d) (Fin m) (AE D) → ℂ) →ₗ[ℂ] P, ∀ Ψ ∈ S, q (GlobalTheory.TripleRead.thO Mo ψ G e Ψ) = pD Ψ
  then H.choose else 0

def mapA (ψ : AddChar (AF D.host.F) ℂ) {W W₁ X : HSp D} (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F W.rank W₁.rank) (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F W.rank W₁.rank) :
    (WO W X → ℂ) →ₗ[ℂ] PiT R Γ Rf :=
  thetaLift Γ.M ψ (sgn true W).gram e (darbAlg Γ.M Bs.ψ Bs.emb) (liftPure Γ.M R.p Rf.p (vacIm Γ Rf))

def mapB (ψ : AddChar (AF D.host.F) ℂ) {W W₁ X : HSp D} (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F W.rank W₁.rank) (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F W.rank W₁.rank) :
    (WO W₁ X → ℂ) →ₗ[ℂ] PiT R Γ Rf :=
  thetaLift Γ.M' ψ (sgn false W₁).gram e (darbAlg Γ.M' Bs.ψ Bs.emb) (liftPure Γ.M' R.p' Rf.p' (vacIm Γ Rf))


open Classical in
def opFin {M X : HSp D} (ω : WRep M X) (S : Submodule ℂ (WO M X → ℂ)) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : (WO M X → ℂ) →ₗ[ℂ] P) (h : GA D X) : Module.End ℂ P :=
  if H : ∃ T : Module.End ℂ P, ∀ Φ ∈ S, p (ω (1, h) Φ) = T (p Φ) then H.choose else 1


open Classical in
def opLie (θ : InfFam D) {M X : HSp D} (ω : WRep M X) (S : Submodule ℂ (WO M X → ℂ)) {P : Type} [AddCommGroup P]
    [Module ℂ P] (p : (WO M X → ℂ) →ₗ[ℂ] P) (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ) : Module.End ℂ P :=
  if H : ∃ T : Module.End ℂ P, ∀ Φ ∈ S, ∀ Φ' ∈ S, IsDer θ X (fun h => ω (1, h)) τ Y Φ Φ' → p Φ' = T (p Φ)
  then H.choose else 0

end GlobalTheory.TripleAssembly

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExtendRestrictionFinitePointsEqStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extend_restriction_finitePoints_eq : ∀ {D : D7} {V : HSp D} (c : CoefA V), c.Is → ∀ (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (Ψ : GA D V → c.W), (∀ γ ∈ GQ V, ∀ k, Lev.finE V k ∈ lev D.sp.cm V.gram β L → ∀ h, Ψ (γ * h * k) = Lev.levChi V β L k • c.ρ k⁻¹ (Ψ h)) → ∀ h : GA D V, c.ext (fun u => Ψ (GlobalTheory.AdelicScalar.finLift V u)) h = Ψ h := by
  first | exact @GlobalTheory.AdelicRestrict.ext_restrict | exact GlobalTheory.AdelicRestrict.ext_restrict | (intros; apply GlobalTheory.AdelicRestrict.ext_restrict <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GroupConvolutionNormalizedIndicatorSelfStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupConvolution_normalizedIndicator_self : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (H : Subgroup G), IsOpen (H : Set G) → IsCompact (H : Set G) → conv μ (normInd μ (H : Set G)) (normInd μ (H : Set G)) = normInd μ (H : Set G) := by
  first | exact @GlobalTheory.TrIdem.conv_normInd_self | exact GlobalTheory.TrIdem.conv_normInd_self | (intros; apply GlobalTheory.TrIdem.conv_normInd_self <;> assumption)
end

