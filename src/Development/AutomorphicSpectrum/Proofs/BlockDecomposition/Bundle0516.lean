module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1114
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0466
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0491
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0461
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0476
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0492

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteReindexing
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.SecReindex

open PositivityTheory.Rg.BcB.G8.Fin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_under (v : PlF E) : ∃ w : Pl E, w.under (𝓞 (maximalRealSubfield E)) = v := by
  have hinj : Function.Injective (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) := by
    first
    | exact FaithfulSMul.algebraMap_injective _ _
    | exact NoZeroSMulDivisors.algebraMap_injective _ _
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral v.asIdeal
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  refine ⟨⟨Q, hQmax.isPrime, ?_⟩, ?_⟩
  · rintro rfl
    apply v.ne_bot
    rw [← hQ]
    exact Ideal.comap_bot_of_injective _ hinj
  · ext1
    exact hQ

def secEquiv {S : Set (Pl E)} (hS : IsSection S) : S ≃ PlF E :=
  Equiv.ofBijective (fun w => w.1.under (𝓞 (maximalRealSubfield E))) (by
    constructor
    · rintro ⟨u, hu⟩ ⟨u', hu'⟩ h
      exact Subtype.ext ((hS u).unique ⟨hu, rfl⟩ ⟨hu', h.symm⟩)
    · intro v
      obtain ⟨w, rfl⟩ := exists_under v
      obtain ⟨u, ⟨hu, huw⟩, -⟩ := hS w
      exact ⟨⟨u, hu⟩, huw⟩)

theorem secPl_eq {S : Set (Pl E)} (hS : IsSection S) (u : S) :
    secPl S (secEquiv hS u) = some u.1 := by
  have hv : secEquiv hS u = u.1.under (𝓞 (maximalRealSubfield E)) := rfl
  have h : ∃ w ∈ S, w.under (𝓞 (maximalRealSubfield E)) = secEquiv hS u := ⟨u.1, u.2, hv.symm⟩
  rw [secPl, dite_eq_left h]
  obtain ⟨h1, h2⟩ := h.choose_spec
  exact congrArg some ((hS u.1).unique ⟨h1, h2.trans hv⟩ ⟨u.2, rfl⟩)

theorem reindex : Reindex := by
  intro E _ _ _ S hS g
  rw [show (∏ᶠ (w : Pl E) (_ : w ∈ S), g w) = ∏ᶠ u : S, g u from
    (finprod_set_coe_eq_finprod_mem S).symm]
  exact finprod_eq_of_bijective (secEquiv hS) (secEquiv hS).bijective
    (fun u => by rw [secPl_eq hS u] <;> rfl)

end GlobalTheory.CompanionTheory.SecReindex

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteRestrictionVanishing
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.EulerV

open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem finite_above (v : PlF E) : Finite (Above v) := by
  by_cases h : Nonempty (Above v)
  · obtain ⟨u⟩ := h
    refine Finite.of_injective (β := (GlobalTheory.EulerTw.orb E u.1 : Finset (Pl E)))
      (fun w => ⟨w.1, (GlobalTheory.EulerTwRestr.mem_orb_iff u.1 w.1).2 (w.2.trans u.2.symm)⟩) ?_
    intro x y hxy
    exact Subtype.ext (congrArg (fun z => z.1) hxy)
  · haveI := not_nonempty_iff.1 h
    infer_instance

def pn (n : ℕ) (v : PlF E) : GL (Fin n) (Af E) →* GL (Fin n) (Av v) := GeneralLinearGroup.map (projv v)

def ev {v : PlF E} (w : Above v) : GL (Fin n) (Av v) →* GLw n w.1 :=
  GeneralLinearGroup.map (Pi.evalRingHom (fun w : Above v => w.1.adicCompletion E) w)

def Kn (n : ℕ) (v : PlF E) : Subgroup (GL (Fin n) (Av v)) :=
  ⨅ w : Above v, (GlobalTheory.LFun.KGL w.1 (n := n)).comap (ev w)

theorem mem_Kn {v : PlF E} {y : GL (Fin n) (Av v)} : y ∈ Kn n v ↔ ∀ w : Above v, ev w y ∈ GlobalTheory.LFun.KGL w.1 (n := n) := by
  simp only [Kn, Subgroup.mem_iInf, Subgroup.mem_comap]

theorem ev_pn {v : PlF E} (w : Above v) (g : GL (Fin n) (Af E)) :
    ev w (pn n v g) = GeneralLinearGroup.map (pLoc E w.1) g := rfl

theorem mem_Kv {a b : ℕ} {v : PlF E} {y : Yv a b v} : y ∈ Kv a b v ↔ y.1 ∈ Kn a v ∧ y.2 ∈ Kn b v := by
  simp only [Kv, Subgroup.mem_iInf, Subgroup.mem_comap, mem_Kn, Subgroup.mem_prod, forall_and]
  rfl

theorem mem_Kf_iff {g : GL (Fin n) (Af E)} : g ∈ Kf E n ↔ ∀ v : PlF E, pn n v g ∈ Kn n v := by
  have h : g ∈ Kf E n ↔ ∀ w : Pl E, GeneralLinearGroup.map (pLoc E w) g ∈ GlobalTheory.LFun.KGL w (n := n) := by
    simp only [Kf, Subgroup.mem_iInf, Subgroup.mem_comap]
  rw [h]
  refine ⟨fun H v => mem_Kn.2 fun w => H w.1, fun H w => ?_⟩
  exact mem_Kn.1 (H (w.under (𝓞 (maximalRealSubfield E)))) ⟨w, rfl⟩

theorem continuous_projv (v : PlF E) : Continuous (projv v) :=
  continuous_pi fun w => RestrictedProduct.continuous_eval w.1

theorem continuous_pn (v : PlF E) : Continuous (pn n v) :=
  Continuous.units_map _ (Continuous.matrix_map continuous_id (continuous_projv v))

theorem continuous_ev {v : PlF E} (w : Above v) : Continuous (ev (n := n) w) :=
  Continuous.units_map _ (Continuous.matrix_map continuous_id (continuous_apply w))

theorem isOpen_Kn (v : PlF E) : IsOpen (Kn n v : Set (GL (Fin n) (Av v))) := by
  haveI := finite_above v
  rw [Kn, Subgroup.coe_iInf]
  exact isOpen_iInter_of_finite fun w =>
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w.1 n).1.preimage (continuous_ev w)

theorem pn_ext {g h : GL (Fin n) (Af E)} (H : ∀ v : PlF E, pn n v g = pn n v h) : g = h :=
  GlobalTheory.EulerTwRestr.gl_ext fun w => by
    exact congrArg (ev ⟨w, rfl⟩) (H (w.under (𝓞 (maximalRealSubfield E))))

theorem eventually_mem_Kn (g : GL (Fin n) (Af E)) : ∀ᶠ v : PlF E in cofinite, pn n v g ∈ Kn n v := by
  have h1 : ∀ᶠ w : Pl E in cofinite, ∀ i j, pLoc E w (g.1 i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => (g.1 i j).2
  have h2 : ∀ᶠ w : Pl E in cofinite, ∀ i j, pLoc E w ((g⁻¹).1 i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => ((g⁻¹).1 i j).2
  have hx : ∀ᶠ w : Pl E in cofinite, GeneralLinearGroup.map (pLoc E w) g ∈ GlobalTheory.LFun.KGL w (n := n) := by
    filter_upwards [h1, h2] with w h1 h2
    exact GlobalTheory.EulerTwRestr.mem_KGL_iff.2 ⟨fun i j => by rw [GlobalTheory.EulerTwRestr.loc_val]; exact h1 i j,
      fun i j => by rw [GlobalTheory.EulerTwRestr.loc_inv_val]; exact h2 i j⟩
  refine eventually_cofinite.2 (((eventually_cofinite.1 hx).image
    fun w : Pl E => w.under (𝓞 (maximalRealSubfield E))).subset ?_)
  intro v hv
  simp only [Set.mem_setOf_eq, mem_Kn, not_forall, ev_pn] at hv
  obtain ⟨w, hw⟩ := hv
  exact ⟨w.1, hw, w.2⟩

theorem exists_lift (y : ∀ v : PlF E, GL (Fin n) (Av v)) (hy : ∀ᶠ v : PlF E in cofinite, y v ∈ Kn n v) :
    ∃ x : GL (Fin n) (Af E), ∀ v, pn n v x = y v := by
  let un : Pl E → PlF E := fun w => w.under (𝓞 (maximalRealSubfield E))
  let Y : ∀ w : Pl E, GLw n w := fun w => ev (⟨w, rfl⟩ : Above (un w)) (y (un w))
  have hc : ∀ᶠ w : Pl E in cofinite, Y w ∈ GlobalTheory.LFun.KGL w (n := n) := by
    have hB := eventually_cofinite.1 hy
    refine eventually_cofinite.2 ((hB.biUnion fun v _ => (Set.finite_coe_iff (s := {w : Pl E | un w = v})).1 (finite_above v)).subset ?_)
    intro w hw
    refine Set.mem_iUnion₂.2 ⟨un w, fun h => hw (mem_Kn.1 h ⟨w, rfl⟩), rfl⟩
  let M : Matrix (Fin n) (Fin n) (Af E) := Matrix.of fun i j =>
    ⟨fun w => (Y w).1 i j, hc.mono fun w h => (GlobalTheory.EulerTwRestr.mem_KGL_iff.1 h).1 i j⟩
  let M' : Matrix (Fin n) (Fin n) (Af E) := Matrix.of fun i j =>
    ⟨fun w => ((Y w)⁻¹).1 i j, hc.mono fun w h => (GlobalTheory.EulerTwRestr.mem_KGL_iff.1 h).2 i j⟩
  have hloc : ∀ P Q : Matrix (Fin n) (Fin n) (Af E), (∀ w : Pl E, P.map (pLoc E w) = Q.map (pLoc E w)) → P = Q :=
    fun P Q h => Matrix.ext fun i j => Subtype.ext (funext fun w => congrFun (congrFun (h w) i) j)
  have hMM' : M * M' = 1 := hloc _ _ fun w => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact (Y w).mul_inv
  have hM'M : M' * M = 1 := hloc _ _ fun w => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact (Y w).inv_mul
  refine ⟨⟨M, M', hMM', hM'M⟩, fun v => Units.ext (Matrix.ext fun i j => funext ?_)⟩
  rintro ⟨w, rfl⟩
  rfl

theorem exists_Kf_lift {v : PlF E} {k : GL (Fin n) (Av v)} (hk : k ∈ Kn n v) :
    ∃ x ∈ Kf E n, pn n v x = k := by
  have hm : ∀ u : PlF E, (Function.update (fun u : PlF E => (1 : GL (Fin n) (Av u))) v k) u ∈ Kn n u := by
    intro u
    by_cases h : u = v
    · subst h
      simpa using hk
    · simp [Function.update_of_ne h, one_mem]
  obtain ⟨x, hx⟩ := exists_lift _ (Eventually.of_forall hm)
  exact ⟨x, mem_Kf_iff.2 fun u => by rw [hx]; exact hm u, by rw [hx]; simp⟩

theorem isCompact_Kn (v : PlF E) : IsCompact (Kn n v : Set (GL (Fin n) (Av v))) := by
  have e : (Kn n v : Set (GL (Fin n) (Av v))) = pn n v '' (Kf E n : Set (GL (Fin n) (Af E))) := by
    ext k
    refine ⟨fun hk => ?_, ?_⟩
    · obtain ⟨x, hx, rfl⟩ := exists_Kf_lift hk
      exact ⟨x, hx, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact mem_Kf_iff.1 hg v
  rw [e]
  exact (GlobalTheory.EulerTwRestr.isCompact_Kglob (E := E) (n := n)).image (continuous_pn v)

theorem coe_Kv (a b : ℕ) (v : PlF E) : (Kv a b v : Set (Yv a b v)) =
    (Kn a v : Set (GL (Fin a) (Av v))) ×ˢ (Kn b v : Set (GL (Fin b) (Av v))) :=
  Set.ext fun _ => mem_Kv

theorem mem_prod_iff (a b : ℕ) (x : Gf E a b) :
    x ∈ (Kf E a).prod (Kf E b) ↔ ∀ v, pv a b v x ∈ Kv a b v := by
  rw [Subgroup.mem_prod, mem_Kf_iff, mem_Kf_iff]
  simp only [mem_Kv, forall_and]
  rfl

theorem isOpen_Kf : IsOpen (Kf E n : Set (GL (Fin n) (Af E))) := GlobalTheory.EulerTwRestr.isOpen_Kglob

theorem isCompact_Kf : IsCompact (Kf E n : Set (GL (Fin n) (Af E))) := GlobalTheory.EulerTwRestr.isCompact_Kglob

theorem coe_level (a b : ℕ) : {x : Gf E a b | ∀ v, pv a b v x ∈ Kv a b v} =
    (Kf E a : Set (GL (Fin a) (Af E))) ×ˢ (Kf E b : Set (GL (Fin b) (Af E))) :=
  Set.ext fun x => (mem_prod_iff a b x).symm

theorem isRestrGroup (a b : ℕ) :
    GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch (Gf E a b)) (pv (E := E) a b) (Kv a b) := by
  refine ⟨fun w => w.elim, fun v => ?_, fun v => ?_, fun v => ?_, fun x y _ H => ?_, fun x => ?_, fun c y hy => ?_, ?_, fun C _ => ?_⟩
  · exact ((continuous_pn v).comp continuous_fst).prodMk ((continuous_pn v).comp continuous_snd)
  · rw [coe_Kv]
    exact (isOpen_Kn v).prod (isOpen_Kn v)
  · rw [coe_Kv]
    exact (isCompact_Kn v).prod (isCompact_Kn v)
  · exact Prod.ext (pn_ext fun v => congrArg Prod.fst (H v)) (pn_ext fun v => congrArg Prod.snd (H v))
  · filter_upwards [eventually_mem_Kn x.1, eventually_mem_Kn x.2] with v h1 h2
    exact mem_Kv.2 ⟨h1, h2⟩
  · obtain ⟨x₁, h₁⟩ := exists_lift (fun v => (y v).1) (hy.mono fun v h => (mem_Kv.1 h).1)
    obtain ⟨x₂, h₂⟩ := exists_lift (fun v => (y v).2) (hy.mono fun v h => (mem_Kv.1 h).2)
    exact ⟨(x₁, x₂), fun w => w.elim, fun v => Prod.ext (h₁ v) (h₂ v)⟩
  · rw [coe_level]
    exact isOpen_Kf.prod isOpen_Kf
  · have e : {x : Gf E a b | (∀ w, GlobalTheory.RestrMeas.noArch (Gf E a b) w x ∈ C w) ∧ ∀ v, pv a b v x ∈ Kv a b v} =
        (Kf E a : Set (GL (Fin a) (Af E))) ×ˢ (Kf E b : Set (GL (Fin b) (Af E))) := by
      rw [← coe_level]
      exact Set.ext fun x => ⟨fun h => h.2, fun h => ⟨fun w => w.elim, h⟩⟩
    rw [e]
    exact isCompact_Kf.prod isCompact_Kf

theorem cjv_spec (hC : CjEx) (v : PlF E) (x : Af E) :
    projv v (conjFin (IsCMField.complexConj E).toRingEquiv x) = cjv v (projv v x) := by
  have h := hC E v
  rw [cjv, dite_eq_left h]
  exact h.choose_spec.2 x

theorem pn_thF (hC : CjEx) (n : ℕ) (v : PlF E) (x : GL (Fin n) (Af E)) :
    pn n v (thF E n x) = thetaGL n (cjv v) (pn n v x) :=
  GlobalTheory.ThetaPull.map_thetaGL _ _ _ (cjv_spec hC v) x

theorem pv_thP (hC : CjEx) (a b : ℕ) (v : PlF E) (x : Gf E a b) :
    pv a b v (thP E a b x) = thv a b v (pv a b v x) :=
  Prod.ext (pn_thF hC a v x.1) (pn_thF hC b v x.2)

theorem theta_mem_Kn (hC : CjEx) {v : PlF E} {k : GL (Fin n) (Av v)} (hk : k ∈ Kn n v) :
    thetaGL n (cjv v) k ∈ Kn n v := by
  obtain ⟨x, hx, rfl⟩ := exists_Kf_lift hk
  rw [← pn_thF hC]
  exact mem_Kf_iff.1 (GlobalTheory.EulerTwKU.thF_mem_Kglob x hx) v

theorem main : RestrV := fun hC E _ _ _ a b =>
  ⟨isRestrGroup a b, fun v x => pv_thP hC a b v x,
    fun v k hk => mem_Kv.2 ⟨theta_mem_Kn hC (mem_Kv.1 hk).1, theta_mem_Kn hC (mem_Kv.1 hk).2⟩,
    mem_prod_iff a b⟩

end GlobalTheory.CompanionTheory.EulerV

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot

variable {D : D7} {ρ r s p : ℕ}

def rowT (y : Mx D (r + s) p) : Mx D r p := fun i j => y (Fin.castAdd s i) j

def rowB (y : Mx D (r + s) p) : Mx D s p := fun i j => y (Fin.natAdd r i) j

def rowJ (x : Mx D r p) (z : Mx D s p) : Mx D (r + s) p :=
  fun i j => Fin.addCases (motive := fun _ => AE D) (fun a => x a j) (fun b => z b j) i

def IsBlockSL2Embedding (b : HermE D (r + s)) (b₁ : HermE D r) (b₂ : HermE D s) : Prop :=
  (∀ i j, b.1 (Fin.castAdd s i) (Fin.castAdd s j) = b₁.1 i j) ∧
  (∀ i j, b.1 (Fin.natAdd r i) (Fin.natAdd r j) = b₂.1 i j) ∧
  (∀ i j, b.1 (Fin.castAdd s i) (Fin.natAdd r j) = 0) ∧ ∀ i j, b.1 (Fin.natAdd r j) (Fin.castAdd s i) = 0

def Total (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D) (b₀ : HermE D ρ) (μ : Measure (Mx D ρ p)) : Prop :=
  ∀ u : Mx D ρ p → ℂ, Continuous u → (∃ B : ℝ, ∀ y, ‖u y‖ ≤ B) →
    (∀ Ω, IsTh ψ χ θ b₀ μ Ω → ∫ y, u y * conj (Ω 1 y) ∂μ = 0) → u = 0

abbrev V1 (D : D7) : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral 1

def WeilCont : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ : (AE D)ˣ →* Circle,
    IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 →
    ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω → ∀ Φ : schwartzA θ V.rank n,
      Continuous fun u : G D n × Mx D V.rank n => (ω u.1 Φ).1 u.2

def WeilKFin : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ : (AE D)ˣ →* Circle,
    IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 →
    ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω →
    ∀ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l → ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ,
      (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∀ Φ : schwartzA θ V.rank n, Φ.1 ∈ fockA θ V n l s →
      ∃ W : Submodule ℂ (Mx D V.rank n → ℂ), FiniteDimensional ℂ W ∧ W ≤ fockA θ V n l s ∧ ∀ k ∈ K D n, (ω k Φ).1 ∈ W

def OrbitMaj : Prop :=
  ∀ (D : D7) (n : ℕ) (θ : InfFam D), IsInfFam θ → ∀ l : D.what₂.Tau → ℝ, (∀ τ, l τ ≠ 0) →
    ∀ f ∈ fockA θ (V1 D) n l (fun _ => 1), ∀ A₁ A₂ : Set (Mx D n n), IsCompact A₁ → IsCompact A₂ →
      ∃ M ∈ schwartzA θ (V1 D).rank n, (∀ y, 0 ≤ (M y).re ∧ (M y).im = 0) ∧
        ∀ a : GL (Fin n) (AE D), a.1 ∈ A₁ → (a⁻¹).1 ∈ A₂ → ∀ y : Mx D (V1 D).rank n,
          ‖f (HMul.hMul y a.1 : Mx D (V1 D).rank n)‖ ≤ ‖M y‖

def IwaCpt : Prop :=
  ∀ (D : D7) (n : ℕ) (C : Set (G D n)), IsCompact C → ∃ (A₁ A₂ : Set (Mx D n n)) (R : ℝ), IsCompact A₁ ∧ IsCompact A₂ ∧
    ∀ h ∈ C, ∃ (m t k : G D n) (a : GL (Fin n) (AE D)) (b : Mx D n n), k ∈ K D n ∧ h = m * t * k ∧
      mat m = blk4 a.1 0 0 (adj (a⁻¹).1) ∧ mat t = blk4 1 b 0 1 ∧ a.1 ∈ A₁ ∧ (a⁻¹).1 ∈ A₂ ∧
      (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ≤ R

def FockTranslateSchwartzMajorant : Prop :=
  ∀ (D : D7) (n : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ : (AE D)ˣ →* Circle,
    IsHeckeChar D χ → ResEta D χ 1 → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (μ : Measure (Mx D (V1 D).rank n)) (𝓕 : Set (Mx D (V1 D).rank n)), IsCovolOne (ratMx D (V1 D).rank n) μ 𝓕 →
    ∀ ω : G D n →* Module.End ℂ (schwartzA θ (V1 D).rank n), IsWeilSch ψ χ θ (V1 D) μ ω →
    ∀ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l → (∀ τ, l τ ≠ 0) → ∀ Φ : schwartzA θ (V1 D).rank n,
      Φ.1 ∈ fockA θ (V1 D) n l (fun _ => 1) → ∀ C : Set (G D n), IsCompact C →
      ∃ M ∈ schwartzA θ (V1 D).rank n, ∀ h ∈ C, ∀ y, ‖(ω h Φ).1 y‖ ≤ ‖M y‖

def SchwTensor : Prop :=
  ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ r s p : ℕ, ∀ φ ∈ schwartzA θ r p, ∀ φ' ∈ schwartzA θ s p,
    (fun y : Mx D (r + s) p => φ (rowT y) * φ' (rowB y)) ∈ schwartzA θ (r + s) p

def ProdTh : Prop :=
  ∀ (D : D7) (r s p : ℕ) (μr : Measure (Mx D r p)) (𝓕r : Set (Mx D r p)) (μs : Measure (Mx D s p)) (𝓕s : Set (Mx D s p)),
    IsCovolOne (ratMx D r p) μr 𝓕r → IsCovolOne (ratMx D s p) μs 𝓕s → ∀ ψ, IsCharAF D.host.F ψ →
    ∀ (χr χs : (AE D)ˣ →* Circle) (θ : InfFam D), IsInfFam θ → ∀ (br : HermE D r) (bs : HermE D s) (b : HermE D (r + s)),
    IsBlockSL2Embedding b br bs → ∀ Ωr Ωs, IsTh ψ χr θ br μr Ωr → IsTh ψ χs θ bs μs Ωs →
      IsTh ψ (χr * χs) θ b ((μr.prod μs).map fun z => rowJ z.1 z.2) fun h y => Ωr h (rowT y) * Ωs h (rowB y)

def ProdMeas : Prop :=
  ∀ (D : D7) (r s p : ℕ) (μr : Measure (Mx D r p)) (𝓕r : Set (Mx D r p)) (μs : Measure (Mx D s p)) (𝓕s : Set (Mx D s p))
    (μ : Measure (Mx D (r + s) p)) (𝓕 : Set (Mx D (r + s) p)),
    IsCovolOne (ratMx D r p) μr 𝓕r → IsCovolOne (ratMx D s p) μs 𝓕s → IsCovolOne (ratMx D (r + s) p) μ 𝓕 →
    μ = (μr.prod μs).map fun z => rowJ z.1 z.2

def EucTotal : Prop :=
  ∀ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [MeasurableSpace Z] [BorelSpace Z]
    (lam : Measure Z) [lam.IsAddHaarMeasure] (ι : Type) [Fintype ι] (c : ι → Z →L[ℝ] ℂ), (∀ z, (∀ k, c k z = 0) → z = 0) →
    ∀ A : Subalgebra ℂ (Z → ℂ), (∀ k, (fun z => c k z) ∈ A) → (∀ k, (fun z => conj (c k z)) ∈ A) →
    ∀ (g : Z → ℝ), Continuous g → (∀ z, 0 < g z) → ∀ C a : ℝ, 0 < a → (∀ z, g z ≤ C * Real.exp (-a * ‖z‖ ^ 2)) →
    ∀ w : Z → ℂ, Continuous w → (∃ B : ℝ, ∀ z, ‖w z‖ ≤ B) → (∀ P ∈ A, ∫ z, w z * P z * (g z : ℂ) ∂lam = 0) → w = 0

def FockTotal : Prop :=
  ∀ (D : D7) (p : ℕ) (θ : InfFam D), IsInfFam θ → ∀ l : D.what₂.Tau → ℝ, (∀ τ, l τ ≠ 0) →
    ∀ (μ : Measure (Mx D (V1 D).rank p)) (𝓕 : Set (Mx D (V1 D).rank p)), IsCovolOne (ratMx D (V1 D).rank p) μ 𝓕 →
    ∀ u : Mx D (V1 D).rank p → ℂ, Continuous u → (∃ B : ℝ, ∀ y, ‖u y‖ ≤ B) →
      (∀ φ ∈ fockA θ (V1 D) p l (fun _ => 1), ∫ y, u y * conj (φ y) ∂μ = 0) → u = 0

def OneTotal : Prop :=
  ∀ (D : D7) (p : ℕ) (μ : Measure (Mx D 1 p)) (𝓕 : Set (Mx D 1 p)), IsCovolOne (ratMx D 1 p) μ 𝓕 →
    ∀ ψ, IsCharAF D.host.F ψ → ∀ b₀ : HermE D 1, b₀.1.det ≠ 0 → ∀ χ, IsHeckeChar D χ → ResEta D χ 1 →
    ∀ θ, IsInfFam θ → Total ψ χ θ b₀ μ

def ZeroTotal : Prop :=
  ∀ (D : D7) (p : ℕ) (μ : Measure (Mx D 0 p)) (𝓕 : Set (Mx D 0 p)), IsCovolOne (ratMx D 0 p) μ 𝓕 →
    ∀ ψ, IsCharAF D.host.F ψ → ∀ b₀ : HermE D 0, ∀ θ, IsInfFam θ → Total ψ 1 θ b₀ μ

def StepTotal : Prop :=
  ∀ (D : D7) (r s p : ℕ) (μr : Measure (Mx D r p)) (𝓕r : Set (Mx D r p)) (μs : Measure (Mx D s p)) (𝓕s : Set (Mx D s p))
    (μ : Measure (Mx D (r + s) p)) (𝓕 : Set (Mx D (r + s) p)),
    IsCovolOne (ratMx D r p) μr 𝓕r → IsCovolOne (ratMx D s p) μs 𝓕s → IsCovolOne (ratMx D (r + s) p) μ 𝓕 →
    ∀ ψ, IsCharAF D.host.F ψ → ∀ (χr χs : (AE D)ˣ →* Circle) (θ : InfFam D), IsInfFam θ →
    ∀ (br : HermE D r) (bs : HermE D s) (b : HermE D (r + s)), IsBlockSL2Embedding b br bs →
      Total ψ χr θ br μr → Total ψ χs θ bs μs → Total ψ (χr * χs) θ b μ

end GlobalTheory.CompanionTheory.ThTot

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramMapContinuousHermitian
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Gram

theorem inner_facts : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (r : ℕ) (ρ : D.what₂.Tau), Continuous (fun y : Mx D V.rank r => (inner V y y : Mx D r r)) ∧ ∀ y : Mx D V.rank r, (inner V y y : Mx D r r) ∈ hermA D r ∧ compAt θ ρ (inner V y y : Mx D r r) = (compAt θ ρ y).conjTranspose * gramAt D V ρ * compAt θ ρ y := by
  intro D θ hθ V r ρ
  haveI := (Formalism.IndefR.Eqv.ae_facts D).1
  refine ⟨?_, fun y => ⟨?_, ?_⟩⟩
  · change Continuous (fun y : Mx D V.rank r => GlobalTheory.MixModel.adj y * (GlobalTheory.MixModel.gA V * y))
    exact GlobalTheory.MixModel.continuous_adj.matrix_mul (continuous_const.matrix_mul continuous_id)
  · change GlobalTheory.MixModel.adj (GlobalTheory.MixModel.adj y * (GlobalTheory.MixModel.gA V * y)) = GlobalTheory.MixModel.adj y * (GlobalTheory.MixModel.gA V * y)
    rw [GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_adj, GlobalTheory.MixModel.adj_gA, Matrix.mul_assoc]
  · change compAt θ ρ (GlobalTheory.MixModel.adj y * (GlobalTheory.MixModel.rat (Formalism.BasicNotions.HSpace.gram V) * y)) = _
    rw [GlobalTheory.CompanionTheory.WSum.compAt_mul', GlobalTheory.CompanionTheory.WSum.compAt_mul', GlobalTheory.CompanionTheory.WSum.compAt_adj hθ, GlobalTheory.CompanionTheory.WSum.compAt_rat hθ, Matrix.mul_assoc]
    rfl

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Gram
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralSplitCentreInvariant
section
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.CompanionTheory.CuspTransfer

noncomputable section
namespace GlobalTheory.CompanionTheory.CuspTransfer

theorem lintegral_image_prod_Ico_of_invariant {X Z : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (e : X × ℝ ≃ₜ Z) (ν : Measure X) [SFinite ν] {h : Z → ENNReal} (hh : Measurable h)
    {k : X → ENNReal} (hk : ∀ x t, h (e (x, t)) = k x) (D : Set X) :
    ∫⁻ g in e '' (D ×ˢ Set.Ico (0 : ℝ) 1), h g ∂(Measure.map e (ν.prod volume)) =
      ∫⁻ x in D, k x ∂ν := by
  have hemb : MeasurableEmbedding e := e.toMeasurableEquiv.measurableEmbedding
  rw [hemb.restrict_map, e.injective.preimage_image, hemb.lintegral_map, ← Measure.prod_restrict,
    lintegral_prod (fun p => h (e p)) (hh.comp e.measurable).aemeasurable]
  refine lintegral_congr fun x => ?_
  simp [hk]

theorem lintegral_productDomain_norm_sq : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (ν : Measure (normOneGL (K := E) (n := a))) [ν.IsHaarMeasure] (c : ENNReal), Measure.map (fun p : normOneGL (K := E) (n := a) × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) (ν.prod volume) = c • μ → ∀ φ : GA E a → ℂ, Continuous φ → (∀ t g, φ (splitCentre E a t * g) = φ g) → ∫⁻ g in ((fun p : normOneGL (K := E) (n := a) × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) '' (RightCosetSpace.fundamentalDomain (rationalGLOne (K := E) (n := a)) ×ˢ Set.Ico (0 : ℝ) 1)), ‖φ g‖ₑ ^ 2 ∂(c • μ) = ∫⁻ x in RightCosetSpace.fundamentalDomain (rationalGLOne (K := E) (n := a)), ‖φ (x : GA E a)‖ₑ ^ 2 ∂ν := by
  intro E _ _ _ a ha μ _ ν _ c hmap φ hc hinv
  obtain ⟨e, he⟩ := GlobalTheory.T.adelic_GL_norm_one_split E a ha
  have hF : (fun p : normOneGL (K := E) (n := a) × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) = ⇑e :=
    funext fun p => (he p.1 p.2).symm
  rw [hF] at hmap
  rw [hF, ← hmap]
  set_option synthInstance.maxHeartbeats 200000 in
    refine lintegral_image_prod_Ico_of_invariant e ν
      (h := fun g => ‖φ g‖ₑ ^ 2) (k := fun x => ‖φ (x : GA E a)‖ₑ ^ 2)
      (hc.enorm.measurable.pow_const 2) (fun x t => ?_) _
  simp only [he, hinv]

end GlobalTheory.CompanionTheory.CuspTransfer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonOf
section
namespace GlobalTheory.CompanionTheory.LocCompareHalves

open PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.UnitaryBC GlobalTheory.BCT

theorem locCompareOf : PositivityTheory.Rg.BcB.G8.Fin.LocCompareOf := by
  intro hI hS hC E _ _ _ hU a b S hSec φ₁ φ₂ h₁ h₂ δ₁ δ₂ e₁ e₂ w hw
  by_cases hs : IsSplitAt w
  · exact hS hC E hU a b S hSec φ₁ φ₂ h₁ h₂ δ₁ δ₂ e₁ e₂ w hw hs
  · exact hI hC E hU a b S hSec φ₁ φ₂ h₁ h₂ δ₁ δ₂ e₁ e₂ w hw hs

end GlobalTheory.CompanionTheory.LocCompareHalves
end

