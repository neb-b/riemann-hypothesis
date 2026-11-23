module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0013
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0083
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementB
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle0003
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionRelation
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0088
public import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.NonemptyAlgebra
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0067
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMatrixOfIsLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitLatBasis

theorem exists_matrix_of_isLattice {R K : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] {n : ℕ} (M : Submodule R (Fin n → K)) [Submodule.IsFullLattice K M] :
    ∃ B : GL (Fin n) K, ∀ x : Fin n → K, x ∈ M ↔
      ∀ i, ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec x i ∈ (algebraMap R K).range := by
  have := Submodule.IsLattice.finite K M
  have := Submodule.IsLattice.free K M
  have hr : Module.finrank R M = n := by
    rw [((Submodule.IsFullLattice.finrank_eq K M).trans (Module.finrank_fintype_fun_eq_card K)), Fintype.card_fin]
  let b : Module.Basis (Fin n) R M := Module.finBasisOfFinrankEq R M hr
  let c : Module.Basis (Fin n) K (Fin n → K) := b.extendOfIsFullLattice K
  let p := Pi.basisFun K (Fin n)
  let B : GL (Fin n) K := ⟨p.toMatrix c, c.toMatrix p, by simp, by simp⟩
  have hB : ∀ x i, ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec x i = c.repr x i := by
    intro x i
    have := congrFun (Module.Basis.toMatrix_mulVec_repr p c x) i
    exact this
  refine ⟨B, fun x => ?_⟩
  simp only [hB]
  constructor
  · intro hx i
    refine ⟨b.repr ⟨x, hx⟩ i, ?_⟩
    have h1 : x = ∑ j, algebraMap R K (b.repr ⟨x, hx⟩ j) • c j := by
      have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
      rw [Submodule.coe_sum] at this
      simp only [c, Module.Basis.extendOfIsFullLattice_apply, algebraMap_smul]
      exact this.symm
    have h2 := congrFun (c.repr_sum_self fun j => algebraMap R K (b.repr ⟨x, hx⟩ j)) i
    rw [← h1] at h2
    exact h2.symm
  · intro h
    choose r hr using h
    rw [← c.sum_repr x]
    refine sum_mem fun j _ => ?_
    rw [← hr, algebraMap_smul]
    refine M.smul_mem _ ?_
    simp [c]

theorem mul_mem_intAE (D : D7) {x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D)
    (hy : y ∈ intAE D) : x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem section_mem {A K ι κ : Type} [CommRing A] [Field K] (O : ValuationSubring K) (π : A →+* K) (σ : K → A) (ε : A)
    (I : Set A) (L : AddSubgroup (ι → A)) (h1 : ∀ a, π (σ a) = a) (h2 : ∀ x, σ (π x) = ε * x)
    (h3 : ∀ x, π x ∈ O → ε * x ∈ I) (h4 : ∀ a ∈ I, ∀ y ∈ L, (fun i => a * y i) ∈ L)
    (g : κ → ι → A) (hg : ∀ j, g j ∈ L) (w : ι → K)
    (hw : w ∈ Submodule.span O (Set.range fun j i => π (g j i))) : (fun i => σ (w i)) ∈ L := by
  have hε : ε ∈ I := by simpa using h3 1 (by simpa using one_mem O)
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    simp only [h2]
    exact h4 _ hε _ (hg j)
  | zero =>
    have : σ 0 = 0 := by simpa using h2 0
    simp only [Pi.zero_apply, this]
    exact zero_mem L
  | add x y _ _ hx hy =>
    have : ∀ a b, σ (a + b) = ε * (σ a + σ b) := fun a b => by rw [← h2, map_add (f := _), h1, h1]
    simp only [Pi.add_apply, this]
    exact h4 _ hε _ (add_mem hx hy)
  | smul c x _ hx =>
    have : ∀ i, σ ((c • x) i) = (ε * σ c) * σ (x i) := fun i => by
      rw [mul_assoc, ← h2, map_mul, h1, h1]; rfl
    simp only [this]
    exact h4 _ (h3 _ (by rw [h1]; exact c.2)) _ hx


set_option maxHeartbeats 1000000 in
theorem exists_basis : ∀ {D : D7} (V : HSp D) (e : Formalism.L2.Theta.AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E →+* Fv D.host.F v) (s : Fv D.host.F v → Formalism.L2.Theta.AE D), e * e = e → (∀ a, π (finPart D (s a)) = a) → (∀ x, finPart D (s (π x)) = finPart D e * x) → (∀ x, finPart D e * x ∈ intAE D ↔ π x ∈ Formalism.UG.Ov D.host.F v) → (∀ a ∈ intAE D, ∀ y ∈ LamHat V, (fun i => a * y i) ∈ LamHat V) → ∃ B : GL (Fin V.rank) (Fv D.host.F v), ∀ y : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E, (fun i => finPart D e * y i) ∈ LamHat V ↔ ∀ i, ((B⁻¹ : GL (Fin V.rank) (Fv D.host.F v)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v)).mulVec (fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v := by
  intro D V e v π s _ h1 h2 h3 h4
  obtain ⟨k, x, hxL, hx⟩ := GlobalTheory.LatticeLocalGlobal.exists_generators V
  let φ : D.host.E →+* Fv D.host.F v := π.comp (Algebra.TensorProduct.includeRight
    (R := D.host.F) (A := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (B := D.host.E)).toRingHom
  have hφ : ∀ a, φ a = π (1 ⊗ₜ[D.host.F] a) := fun _ => rfl
  let M : Submodule (v.adicCompletionIntegers D.host.F) (Fin V.rank → Fv D.host.F v) :=
    Submodule.span _ (Set.range fun j i => φ (V.frame.repr (x j) i))
  have hL : ∀ w ∈ V.L0, (fun i => φ (V.frame.repr w i)) ∈ M := by
    intro w hw
    obtain ⟨n, rfl⟩ := hx w hw
    have : (fun i => φ (V.frame.repr (∑ j, n j • x j) i)) = ∑ j, n j • fun i => φ (V.frame.repr (x j) i) := by
      funext i
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_zsmul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply]
    rw [this]
    exact sum_mem fun j _ => zsmul_mem (Submodule.subset_span (Set.mem_range_self j)) _
  have hfull : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
    let W := Submodule.span D.host.E (V.L0 : Set V.V)
    change W = ⊤
    by_contra h
    let e' : V.V ≃ₗ⋆[D.host.E] V.V :=
      V.frame.equivFun.trans ((starLinearEquiv D.host.E).trans V.frame.equivFun.symm)
    let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
      (LinearMap.domRestrict' W).comp (V.hT.comp e'.toLinearMap)
    have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E V.V := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt h
    obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    have hsmul (a : D.host.E) : a • e' z ∈ V.L0 := by
      rw [← V.baseLattice_isUnimodular]
      simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual,
        Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
      intro y hy
      have hzy : V.hT (e' z) y = 0 :=
        congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩)
          (LinearMap.mem_ker.mp hz)
      have hyz : V.hT y (e' z) = 0 := by
        have hh := V.herm.eq y (e' z)
        simp only [starRingEnd_apply, hzy, star_eq_zero] at hh
        exact hh
      simp [hyz]
    let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
      ((LinearMap.toSpanSingleton D.host.E _ (e' z)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
    let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
    let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective D.host.E (fun hz' => hz0 (e'.map_eq_zero_iff.mp hz')) (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField D.host.E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
  have hsp : ∀ w : V.V, (fun i => φ (V.frame.repr w i)) ∈
      Submodule.span (Fv D.host.F v) (M : Set (Fin V.rank → Fv D.host.F v)) := by
    intro w
    have hw : w ∈ Submodule.span D.host.E (V.L0 : Set V.V) := by
      rw [hfull]; trivial
    induction hw using Submodule.span_induction with
    | mem w hw => exact Submodule.subset_span (hL w hw)
    | zero =>
      simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
      exact zero_mem _
    | add a b _ _ ha hb =>
      simp only [map_add (f := _), Finsupp.coe_add, Pi.add_apply]
      exact add_mem ha hb
    | smul c a _ ha =>
      simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul]
      exact Submodule.smul_mem _ (φ c) ha
  have : Submodule.IsFullLattice (Fv D.host.F v) M := by
    haveI : Submodule.IsLattice (Fv D.host.F v) M :=
      Submodule.IsLattice.of_fg _ (Submodule.fg_span (Set.finite_range _))
    refine ⟨?_⟩
    rw [eq_top_iff, ← (Pi.basisFun (Fv D.host.F v) (Fin V.rank)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have : Pi.basisFun (Fv D.host.F v) (Fin V.rank) i = fun j => φ (V.frame.repr (V.frame i) j) := by
      funext j
      simp only [Pi.basisFun_apply, Module.Basis.repr_self, Pi.single_apply, Finsupp.single_apply, eq_comm (a := i)]
      split_ifs <;> simp
    rw [this]
    exact hsp _
  obtain ⟨B, hB⟩ := exists_matrix_of_isLattice M
  have hε : finPart D e ∈ intAE D := by simpa using (h3 1).2 (by rw [RingHom.map_one]; exact one_mem _)
  have hπε : π (finPart D e) = 1 := by
    have := h1 (π 1)
    rwa [h2, mul_one, RingHom.map_one] at this
  have hto : ∀ z ∈ LamHat V, (fun i => π (z i)) ∈ M := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, u, hu, rfl⟩ := hy
      have ha' : π (a ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ Formalism.UG.Ov D.host.F v :=
        (h3 _).1 (mul_mem_intAE D hε (AddSubgroup.subset_closure ⟨a, ha, 1, rfl⟩))
      have hu' := M.smul_mem ⟨_, ha'⟩ (hL _ hu)
      convert hu' using 1
      funext i
      rw [V.frame.repr_sum_self]
      show _ = π _ * π _
      rw [← RingHom.map_mul]
      congr 1
      show _ = (a ⊗ₜ[D.host.F] (1 : D.host.E)) * (1 ⊗ₜ[D.host.F] u i)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | zero =>
      simp only [Pi.zero_apply, RingHom.map_zero]
      exact zero_mem _
    | add y z _ _ hy hz =>
      simp only [Pi.add_apply, RingHom.map_add (f := _)]
      exact add_mem hy hz
    | neg y _ hy =>
      simp only [Pi.neg_apply, RingHom.map_neg]
      exact neg_mem hy
  refine ⟨B, fun y => ?_⟩
  have hR : ∀ t : Fv D.host.F v, t ∈ (algebraMap (v.adicCompletionIntegers D.host.F) (Fv D.host.F v)).range ↔
      t ∈ Formalism.UG.Ov D.host.F v := fun t => ⟨fun ⟨r, hr⟩ => hr ▸ r.2, fun h => ⟨⟨t, h⟩, rfl⟩⟩
  have hB' := hB fun j => π (y j)
  simp only [hR] at hB'
  rw [← hB']
  constructor
  · intro h
    have := hto _ h
    simpa only [RingHom.map_mul, hπε, one_mul] using this
  · intro h
    have hg : ∀ j, (fun i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] V.frame.repr (x j) i) ∈ LamHat V :=
      fun j => AddSubgroup.subset_closure
        ⟨1, fun w => by rw [map_one]; exact one_mem _, fun i => V.frame.repr (x j) i, by
          show ∑ i, V.frame.repr (x j) i • V.frame i ∈ V.L0
          rw [V.frame.sum_repr]
          exact hxL j, rfl⟩
    have := section_mem (v.adicCompletionIntegers D.host.F) π (fun a => finPart D (s a)) (finPart D e)
      (intAE D) (LamHat V) h1 h2 (fun x hx => (h3 x).2 hx) h4 _ hg (fun j => π (y j)) h
    simpa only [h2] using this

end GlobalTheory.SplitLatBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExponentShapeOfIntegralClassOneLetter
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

noncomputable section

namespace GlobalTheory.KerStd.OneLetter

open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq)
open Formalism.DworkPowerSeriesWeights (Integral mvExp)

theorem localLogarithm_eq_single_variable_oneLetter (D : D7) (p : ℕ) [Fact p.Prime] (h1 : nP D p = 1) {β : Type} (v : OrbitPlaces.Pl D × β) :
    OrbitPlaces.logPl D p v = at1 v (lgF ℂ_[p] p) := by
  rw [Formalism.L2.Th1.D.SingleLetterLog.at_variable_artin_hasse_eq_one_log]
  ext m
  have hb : ∀ e : ℕ, OrbitPlaces.backPl D p v.1 e = v.1 := fun e => by
    simp [OrbitPlaces.backPl, h1, posPl_zero]
  show (∑ e ∈ Finset.range (JetTdeg m + 1), _) = ∑ e ∈ Finset.range (m.degree + 1), _
  have hd : JetTdeg m = m.degree := rfl
  rw [hd]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [hb]

theorem owOK_one {K : Type} [NormedField K] (σ : K →+* K) :
    OwOK 2 σ (fun _ : Fin (2 / 2) => (1 : K)) (fun _ => 1) :=
  ⟨fun _ => ⟨by simp, by simp⟩, fun _ => ⟨Formalism.L2.Th1.D.SingleLetterLog.iter_one σ 2, Formalism.L2.Th1.D.SingleLetterLog.iter_one σ 2⟩⟩

theorem trDual_one {K : Type} [NormedField K] (σ : K →+* K) :
    TrDual 2 σ (fun _ : Fin (2 / 2) => (1 : K)) (fun _ => 1) := by
  refine ⟨by simp, fun r r' => ?_⟩
  have hr : r = r' := Fin.ext (by have := r.isLt; have := r'.isLt; omega)
  rw [Formalism.L2.Th1.D.SingleLetterLog.univ_two, Finset.sum_pair (by decide)]
  have h1 : (1 : ZMod 2).val = 1 := rfl
  simp [h1, hr]

theorem beMean_fin_unit {K : Type} [Field K] (l : ℕ) (σ : K →+* K) (be0 : MvPowerSeries (Fin 2) K) (ζ : K) :
    Formalism.L2.Th1.D.beMean (d := 2) l σ be0 (fun _ : Fin (2 / 2) => (1 : K)) (fun _ => 1) ζ =
      Formalism.L2.Th1.D.beMean (d := 2) l σ be0 (fun _ : Unit => (1 : K)) (fun _ => 1) ζ := by
  have h : Formalism.L2.Th1.D.beTil (d := 2) l σ be0 (fun _ : Fin (2 / 2) => (1 : K)) (fun _ => 1) =
      Formalism.L2.Th1.D.beTil (d := 2) l σ be0 (fun _ : Unit => (1 : K)) (fun _ => 1) := by
    unfold Formalism.L2.Th1.D.beTil
    rw [Finset.sum_const, Finset.sum_const]
    simp
  unfold Formalism.L2.Th1.D.beMean
  rw [h]

end GlobalTheory.KerStd.OneLetter

namespace GlobalTheory.KerStd

open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq)
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open OneLetter

theorem expShape_of_integralClass : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)), CurveData p g2 g3 s2 ε σ F → nP D p = 1 → ∀ (N N' : ℕ) (ep : ℂ_[p]) (Th : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]), ‖ep‖ = 1 → HostLog p g2 g3 s2 ε (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Th : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) → OrbitPlaces.ThetaExpansionRealPlaces D p Th := by
  intro D p _ g2 g3 s2 ε σ F hC h1 N N' ep Th hep hH
  obtain ⟨h5, hg2, hg3, hε, hth, hσ, hF, hN⟩ := hC
  have hl : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨f1, f2, hph⟩ := Formalism.L2.Th1.D.FAux.ffs p Formalism.L2.Th1.D.first_level_on_curve g2 g3 ε hg2 hg3 hε hth σ hσ F hF s2 hN
  obtain ⟨ζ, hζ⟩ := Formalism.L2.Th1.D.FAux.exists_root2 p
  set B : MvPowerSeries (ZMod 2) (MaximalUnramifiedExtension p) :=
    Formalism.L2.Th1.D.beMean (d := 2) p σ (cob F (phFF p g2 g3 s2 ε)) (fun _ : Unit => (1 : MaximalUnramifiedExtension p)) (fun _ => 1) ζ with hBdef
  set Bc : MvPowerSeries (ZMod 2) ℂ_[p] := MvPowerSeries.map (MaximalUnramifiedExtension p).subtype B with hBc
  have hstd : BeStd p 2 Bc := ⟨σ, F, cob F (phFF p g2 g3 s2 ε), fun _ => 1, fun _ => 1, ζ,
    ⟨hσ, hF, f1, f2, owOK_one σ, trDual_one σ, hζ⟩, by rw [beOf, beMean_fin_unit]⟩
  have hB14 := _root_.GlobalTheory.KerStd.bHyps_of_beStd p 2 Bc h5 le_rfl even_two hstd

  have hO := Formalism.L2.Th1.D.oneLetterHalf (MaximalUnramifiedExtension p) p σ hσ F hF _ f1 f2 ζ hζ _ hph
  have h2 := (Formalism.InvariantFactorPaths.G7.Top.mapSimeq (MaximalUnramifiedExtension p) ℂ_[p] Unit (MaximalUnramifiedExtension p).subtype (Formalism.L2.Th1.D.FAux.norm_coe p)).1 _ _ hO
  have hsL0 : MvPowerSeries.HasSubst (fun _ : ZMod 2 => (lgF (MaximalUnramifiedExtension p) p : MvPowerSeries Unit (MaximalUnramifiedExtension p))) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => Formalism.L2.Th1.D.Pair.cc_lgF hl)
  have hsL : MvPowerSeries.HasSubst (fun _ : ZMod 2 => (lgF ℂ_[p] p : MvPowerSeries Unit ℂ_[p])) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => Formalism.L2.Th1.D.Pair.cc_lgF hl)
  have e2 : MvPowerSeries.map (MaximalUnramifiedExtension p).subtype (MvPowerSeries.C ((2 : MaximalUnramifiedExtension p)⁻¹) *
      MvPowerSeries.subst (fun _ : ZMod 2 => (lgF (MaximalUnramifiedExtension p) p : MvPowerSeries Unit (MaximalUnramifiedExtension p))) B) =
      MvPowerSeries.C ((2 : ℂ_[p])⁻¹) *
        MvPowerSeries.subst (fun _ : ZMod 2 => (lgF ℂ_[p] p : MvPowerSeries Unit ℂ_[p])) Bc := by
    rw [map_mul, MvPowerSeries.map_C, MvPowerSeries.map_subst hsL0, map_inv₀, map_ofNat]
    have e3 : MvPowerSeries.map (MaximalUnramifiedExtension p).subtype (lgF (MaximalUnramifiedExtension p) p : MvPowerSeries Unit (MaximalUnramifiedExtension p)) = lgF ℂ_[p] p :=
      Formalism.InvariantFactorPaths.G7.FormalGroupLaws.map_lgF (MaximalUnramifiedExtension p).subtype p
    simp only [e3, hBc]
  rw [e2] at h2
  obtain ⟨-, hsymm, -, -, -⟩ := Formalism.InvariantFactorPaths.G7.Top.simeqRules ℂ_[p] (OrbitPlaces.Pl D × Fin N × Fin N')
  have hsub := (Formalism.InvariantFactorPaths.G7.Top.simeqRules ℂ_[p] Unit).2.2.2.2 (OrbitPlaces.Pl D × Fin N × Fin N')
  have h3 : ∀ x : OrbitPlaces.Pl D × Fin N × Fin N', Simeq (at1 x (PowerSeries.map (MaximalUnramifiedExtension p).subtype (phFF p g2 g3 s2 ε)))
      (MvPowerSeries.C ((2 : ℂ_[p])⁻¹) *
        MvPowerSeries.subst (fun _ : ZMod 2 => at1 x (lgF ℂ_[p] p)) Bc) := by
    intro x
    have hsx : MvPowerSeries.HasSubst
        (fun _ : Unit => (MvPowerSeries.X x : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
    have h4 := hsub _ _ (fun _ : Unit => (MvPowerSeries.X x : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]))
      (fun _ => by simp) (fun _ => Formalism.InvariantFactorPaths.G7.TwoS.integral_X x) h2
    rw [MvPowerSeries.subst_mul hsx, MvPowerSeries.subst_C,
      MvPowerSeries.subst_comp_subst_apply hsL hsx] at h4
    exact h4
  have h5s := Formalism.L2.Th1.D.B4.simeq_sum Finset.univ _ _ fun x _ => h3 x
  obtain ⟨h50, h5I⟩ := hsymm _ _ h5s
  set f : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p] :=
    ∑ x : OrbitPlaces.Pl D × Fin N × Fin N', at1 x (PowerSeries.map (MaximalUnramifiedExtension p).subtype (phFF p g2 g3 s2 ε)) with hf
  set g : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p] :=
    ∑ x : OrbitPlaces.Pl D × Fin N × Fin N', MvPowerSeries.C ((2 : ℂ_[p])⁻¹) *
        MvPowerSeries.subst (fun _ : ZMod 2 => at1 x (lgF ℂ_[p] p)) Bc with hg
  have hm0 : PowerSeries.constantCoeff (PowerSeries.map (MaximalUnramifiedExtension p).subtype (phFF p g2 g3 s2 ε)) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, Formalism.L2.Th1.D.FAux.cc_phFF hl, map_zero]
  have hf0 : MvPowerSeries.constantCoeff f = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hf, map_sum]
    exact Finset.sum_eq_zero fun x _ => Formalism.L2.Th1.D.Pair.constantCoeff_inVar_eq_zero x hm0
  have hg0 : MvPowerSeries.constantCoeff g = 0 := by
    have h := h50
    rw [map_sub, hf0, sub_zero] at h
    exact h
  have hng0 : MvPowerSeries.constantCoeff (-g) = 0 := by rw [map_neg, hg0, neg_zero]
  have hnf0 : MvPowerSeries.constantCoeff (-f) = 0 := by rw [map_neg, hf0, neg_zero]

  have hsA : MvPowerSeries.HasSubst (fun i : OrbitPlaces.Pl D × Fin N × Fin N' => at1 i (lgF ℂ_[p] p)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => Formalism.L2.Th1.D.Pair.constantCoeff_inVar_eq_zero i (Formalism.L2.Th1.D.Pair.cc_lgF hl)
  have hsE : MvPowerSeries.HasSubst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' =>
      (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun v => by simp
  have hlogfun : (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => MvPowerSeries.C ep * OrbitPlaces.logPl D p v) =
      fun v => MvPowerSeries.C ep * at1 v (lgF ℂ_[p] p) := funext fun v => by rw [localLogarithm_eq_single_variable_oneLetter D p h1]
  have hlog2 : (OrbitPlaces.logPl D p (β := Fin N × Fin N')) = fun v => at1 v (lgF ℂ_[p] p) :=
    funext fun v => localLogarithm_eq_single_variable_oneLetter D p h1 v
  have hS : MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => MvPowerSeries.C ep * OrbitPlaces.logPl D p v) Th =
      MvPowerSeries.subst (fun i : OrbitPlaces.Pl D × Fin N × Fin N' => at1 i (lgF ℂ_[p] p))
        (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' =>
          (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Th) := by
    rw [hlogfun, MvPowerSeries.subst_comp_subst_apply hsE hsA]
    congr 1
    funext v
    rw [MvPowerSeries.subst_mul hsA, MvPowerSeries.subst_C, MvPowerSeries.subst_X hsA]

  have hE : ∀ z : OrbitPlaces.Pl D, ∀ a : Fin N, ∀ b : Fin N',
      MvPowerSeries.subst (fun s : ZMod 2 => if s = 0 then
          (MvPowerSeries.X (z, a, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])
        else MvPowerSeries.C (1 : ℂ_[p]) * MvPowerSeries.X (z, a, b)) Bc =
      MvPowerSeries.subst (fun _ : ZMod 2 =>
        (MvPowerSeries.X (z, a, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Bc := by
    intro z a b
    simp only [map_one, one_mul, ite_self]
  have hsX : ∀ x : OrbitPlaces.Pl D × Fin N × Fin N', MvPowerSeries.HasSubst
      (fun _ : ZMod 2 => (MvPowerSeries.X x : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) :=
    fun x => MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => by simp
  set E' : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p] :=
    ((-1 : ℂ_[p]) / 2) • ∑ x : OrbitPlaces.Pl D × Fin N × Fin N',
      MvPowerSeries.subst (fun _ : ZMod 2 =>
        (MvPowerSeries.X x : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Bc with hE'
  have hsubE : MvPowerSeries.subst (fun i : OrbitPlaces.Pl D × Fin N × Fin N' => at1 i (lgF ℂ_[p] p)) E' = -g := by
    rw [hE', ← MvPowerSeries.coe_substAlgHom hsA, map_smul, MvPowerSeries.coe_substAlgHom hsA,
      Formalism.L2.Th1.D.Pair.subst_sum hsA, hg, MvPowerSeries.smul_eq_C_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [MvPowerSeries.subst_comp_subst_apply (hsX x) hsA]
    simp only [MvPowerSeries.subst_X hsA]
    rw [← neg_mul, ← map_neg]
    congr 2
    ring
  have hE0 : MvPowerSeries.constantCoeff E' = 0 := by
    rw [← HostLog.constantCoeff_subst (fun i => Formalism.L2.Th1.D.Pair.constantCoeff_inVar_eq_zero i (Formalism.L2.Th1.D.Pair.cc_lgF hl)) E',
      hsubE, hng0]
  have hsum : (∑ z : OrbitPlaces.Pl D, ((-1 : ℂ_[p]) / 2) • ∑ a : Fin N, ∑ b : Fin N',
      MvPowerSeries.subst (fun s : ZMod 2 => if s = 0 then
          (MvPowerSeries.X (z, a, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])
        else MvPowerSeries.C (1 : ℂ_[p]) * MvPowerSeries.X (z, a, b)) Bc) = E' := by
    simp only [hE, hE', Fintype.sum_prod_type, Finset.smul_sum]
  have e5 : mvExp (g - f) * mvExp (-g) = mvExp (-f) := by
    rw [← Formalism.InvariantFactorPaths.G7.mvExp_add h50 hng0]
    congr 1
    ring
  have e6 : mvExp (-f) * mvExp f = 1 := by
    rw [← Formalism.InvariantFactorPaths.G7.mvExp_add hnf0 hf0, neg_add_cancel, Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.mvExp_zero']
  refine ⟨ep, hep, fun _ => Bc, fun _ => hB14, fun _ => 1, fun _ => norm_one, fun _ => -1, fun _ => Or.inr rfl,
    mvExp (g - f) * (mvExp f * MvPowerSeries.subst (fun i : OrbitPlaces.Pl D × Fin N × Fin N' => at1 i (lgF ℂ_[p] p))
        (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' =>
          (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Th)),
    Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' h5I hH, ?_⟩
  show _ = _ * MvPowerSeries.subst (OrbitPlaces.logPl D p (β := Fin N × Fin N')) (product_zeroth_first_parts.expS ℂ_[p]
    (∑ z : OrbitPlaces.Pl D, ((-1 : ℂ_[p]) / 2) • ∑ a : Fin N, ∑ b : Fin N',
      MvPowerSeries.subst (fun s : ZMod 2 => if s = 0 then
          (MvPowerSeries.X (z, a, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])
        else MvPowerSeries.C (1 : ℂ_[p]) * MvPowerSeries.X (z, a, b)) Bc))
  rw [hS, hsum, hlog2]
  show _ = _ * MvPowerSeries.subst _ (mvExp E')
  rw [Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_mvExp' hsA hE0, hsubE]
  calc _ = (mvExp (-f) * mvExp f) * MvPowerSeries.subst (fun i : OrbitPlaces.Pl D × Fin N × Fin N' => at1 i (lgF ℂ_[p] p))
        (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' =>
          (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Th) := by
        rw [e6, one_mul]
    _ = _ := by rw [← e5]; ring

end GlobalTheory.KerStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerPEqSpanBeta
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLat

theorem ker_localizedTheta_eq_span_beta : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), ϖ.untilt = ((l : ℕ) : Per.OC l) →
    Per.kerP l = Ideal.span {beta ϖ} := by
  intro l _ ϖ hϖ
  obtain ⟨_, _, -, -, hK, -⟩ := GlobalTheory.AinfChecks.padicComplex l
  have hk : RingHom.ker (Per.θ l) = Ideal.span {((l : ℕ) : Per.Ainf l) - Per.tm ϖ} := (hK ϖ hϖ).1
  obtain ⟨-, hker, hA, -⟩ := thetaP_facts l
  have hu := GlobalTheory.RingBasics.isUnit_l l
  have hmem : ∀ a : Per.Ainf l, Per.θ l a = 0 →
      algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l := by
    intro a ha
    rw [← hker, RingHom.mem_ker, hA, ha]
    rfl
  have h0 : Per.θ l (((l : ℕ) : Per.Ainf l) - Per.tm ϖ) = 0 := by
    have : ((l : ℕ) : Per.Ainf l) - Per.tm ϖ ∈ RingHom.ker (Per.θ l) := by
      rw [hk]; exact Ideal.mem_span_singleton_self _
    exact this
  have hlb : ((l : ℕ) : Per.AinfP l) * beta ϖ =
      -algebraMap (Per.Ainf l) (Per.AinfP l) (((l : ℕ) : Per.Ainf l) - Per.tm ϖ) := by
    rw [l_mul_beta, map_sub, map_natCast]; ring
  refine le_antisymm (fun y hy => ?_) ?_
  · rw [← hker, RingHom.mem_ker] at hy
    obtain ⟨n, a, h⟩ := IsLocalization.Away.surj ((l : ℕ) : Per.Ainf l) y
    rw [map_natCast] at h
    have ha : Per.θ l a = 0 := by
      apply Subtype.ext
      rw [← hA, ← h, map_mul, hy, zero_mul]
      rfl
    have h2 : a ∈ Ideal.span {((l : ℕ) : Per.Ainf l) - Per.tm ϖ} := hk ▸ ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 h2
    rw [← Ideal.mul_unit_mem_iff_mem _ (hu.pow n), h, map_mul]
    have : algebraMap (Per.Ainf l) (Per.AinfP l) (((l : ℕ) : Per.Ainf l) - Per.tm ϖ) =
        -(((l : ℕ) : Per.AinfP l) * beta ϖ) := by rw [hlb, neg_neg]
    rw [this]
    exact Ideal.mul_mem_left _ _ (neg_mem (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
  · rw [Ideal.span_singleton_le_iff_mem]
    have h3 : ((l : ℕ) : Per.AinfP l) * beta ϖ ∈ Per.kerP l := by
      rw [hlb]; exact neg_mem (hmem _ h0)
    have h4 : linv l * (((l : ℕ) : Per.AinfP l) * beta ϖ) = beta ϖ := by
      rw [← mul_assoc, mul_comm (linv l), mul_linv, one_mul]
    rw [← h4]
    exact Ideal.mul_mem_left _ _ h3

end GlobalTheory.Pst.StLat
end

