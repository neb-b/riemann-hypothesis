module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.KernelDictionary
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticIntegralTraceFormPerfect
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0090
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticWeilFOpNOpFOpGauss
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0143
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysLatOfTrivial
section
noncomputable section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB

namespace GlobalTheory.TrivCrys

open Module TensorProduct

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]

open PowerSeries in
open Module TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] in
private theorem lid_rTensor_map_id_eq {V : Type} [AddCommGroup V] [Module Qp V] [Module LL V]
    [IsScalarTower Qp LL V] (f : V →ₗ[Qp] Qp) (σ : B →ₗ[Qp] B) (x : V ⊗[Qp] B) :
    TensorProduct.lid Qp B (LinearMap.rTensor B f
      (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) σ x)) =
      σ (TensorProduct.lid Qp B (LinearMap.rTensor B f x)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => simp [AlgebraTensorModule.map_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

open PowerSeries in
open Module TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] in
private theorem eq_sum_basis_tmul_coord {V : Type} [AddCommGroup V] [Module Qp V] {ι : Type}
    [Fintype ι] (b : Basis ι Qp V) (x : V ⊗[Qp] B) :
    x = ∑ i, b i ⊗ₜ[Qp] TensorProduct.lid Qp B (LinearMap.rTensor B (b.coord i) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n =>
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Basis.coord_apply]
    simp_rw [← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul, b.sum_repr]
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    simp only [map_add (f := _), TensorProduct.tmul_add, Finset.sum_add_distrib]


open PowerSeries in
open Module TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] in
theorem _root_.GlobalTheory.TrivCrys.dcris_of_trivial {V : Type} [AddCommGroup V] [Module Qp V]
    [Module LL V] [IsScalarTower Qp LL V] [FiniteDimensional Qp V] (ρ : Representation LL G V)
    (hρ : ∀ g x, ρ g x = x) :
    _root_.Formalism.WeaklyAdmissibleFiltrations.Dcris PD ρ =
      LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
        (IsScalarTower.toAlgHom Qp K₀ B).toLinearMap) := by
  have hid : ∀ g, ρ g = LinearMap.id := fun g => LinearMap.ext (hρ g)
  ext x
  rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.mem_Dcris, LinearMap.mem_range]
  constructor
  · intro hx
    let b := Module.finBasis Qp V
    have hc : ∀ i, ∃ k : K₀, algebraMap K₀ B k =
        TensorProduct.lid Qp B (LinearMap.rTensor B (b.coord i) x) := by
      intro i
      refine (_root_.GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.invariantsEq PD _).mp fun g => ?_
      have h := hx g
      unfold _root_.Formalism.WeaklyAdmissibleFiltrations.actVB at h
      rw [hid g] at h
      conv_rhs => rw [← h]
      rw [lid_rTensor_map_id_eq]
      rfl
    choose k hk using hc
    refine ⟨∑ i, b i ⊗ₜ[Qp] k i, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, eq_sum_basis_tmul_coord b x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [AlgebraTensorModule.map_tmul, ← hk i]
    rfl
  · rintro ⟨y, rfl⟩ g
    unfold _root_.Formalism.WeaklyAdmissibleFiltrations.actVB
    rw [hid g]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul m k => simp [AlgebraTensorModule.map_tmul]
    | add y z hy hz => simp only [map_add (f := _), hy, hz]


open PowerSeries in
open Module TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] in
theorem _root_.GlobalTheory.TrivCrys.isCrys_of_trivial {V : Type} [AddCommGroup V] [Module Qp V] [Module LL V]
    [IsScalarTower Qp LL V] [FiniteDimensional Qp V] (ρ : Representation LL G V)
    (hρ : ∀ g x, ρ g x = x) : _root_.Formalism.WeaklyAdmissibleFiltrations.IsCrys PD ρ := by
  haveI : Nontrivial B := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply PD.not_mem_filtration_two
    rw [Subsingleton.elim PD.t 0, map_zero]
    exact zero_mem _
  have key : ⇑(AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
      (IsScalarTower.toAlgHom Qp K₀ B).toLinearMap) =
      ⇑(LinearMap.lTensor V (IsScalarTower.toAlgHom Qp K₀ B).toLinearMap) := by
    funext w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul m k => simp [AlgebraTensorModule.map_tmul]
    | add u w hu hw => simp only [map_add (f := _), hu, hw]
  have hinj : Function.Injective (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
      (IsScalarTower.toAlgHom Qp K₀ B).toLinearMap) := by
    rw [key]
    exact Module.Flat.lTensor_preserves_injective_linearMap _
      (fun a c h => (algebraMap K₀ B).injective h)
  unfold _root_.Formalism.WeaklyAdmissibleFiltrations.IsCrys
  rw [_root_.GlobalTheory.TrivCrys.dcris_of_trivial PD ρ hρ, LinearMap.finrank_range_of_inj hinj,
    Module.finrank_tensorProduct, mul_comm]


open PowerSeries in
open Module TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] in
theorem _root_.GlobalTheory.TrivCrys.isCrys_lat_of_trivial : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] [FiniteDimensional Qp LL] (U : _root_.Formalism.BasicNotions.LocLat G Qp LL O), (∀ g x, U.ρ g x = x) → _root_.Formalism.WeaklyAdmissibleFiltrations.IsCrys PD U.ρ := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ _ U hU
  haveI := U.fdim
  haveI : FiniteDimensional Qp U.V := Module.Finite.trans LL U.V
  exact _root_.GlobalTheory.TrivCrys.isCrys_of_trivial PD U.ρ hU

end GlobalTheory.TrivCrys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSelfDualPiHaarTraceStarDotProductUnramified
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.PiSelfDual

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E]

theorem finite : Module.Finite F E :=
  Module.finite_of_finrank_pos (by rw [Unram.finrank_eq (F := F) (E := E)]; norm_num)

theorem isModuleTopology : IsModuleTopology F E := by
  haveI : LocallyCompactSpace F := Unram.lcF E
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : Module.Finite F E := finite
  exact IsModuleTopology.iso (R := F) (A := Fin 2 → F)
    (ContinuousLinearEquiv.ofFinrankEq (by simp [Unram.finrank_eq (F := F) (E := E)]))

theorem star_smul_F {r : ℕ} (a : F) (c : Fin r → E) : star (a • c) = a • star c := by
  funext i
  show star (a • c i) = a • star (c i)
  rw [Algebra.smul_def, Algebra.smul_def, star_mul, Unram.star_fix (E := E) a, mul_comm]

theorem trace_star (z : E) : Algebra.trace F E (star z) = Algebra.trace F E z := by
  apply (algebraMap F E).injective
  rw [(_root_.GlobalTheory.NTr.traceForm_perfect F E).1, (_root_.GlobalTheory.NTr.traceForm_perfect F E).1, star_star, add_comm]

def trForm (r : ℕ) : LinearMap.BilinForm F (Fin r → E) :=
  LinearMap.mk₂ F (fun c b => Algebra.trace F E (star c ⬝ᵥ b))
    (fun c c' b => by simp [star_add, add_dotProduct])
    (fun a c b => by rw [star_smul_F, smul_dotProduct, LinearMap.map_smul])
    (fun c b b' => by simp [dotProduct_add])
    (fun a c b => by rw [dotProduct_smul, LinearMap.map_smul])

theorem trForm_apply (r : ℕ) (c b : Fin r → E) :
    trForm (F := F) r c b = Algebra.trace F E (star c ⬝ᵥ b) := rfl

theorem trForm_isSymm (r : ℕ) : (trForm (F := F) (E := E) r).IsSymm := by
  refine ⟨fun x y => ?_⟩
  rw [trForm_apply, trForm_apply, star_dotProduct, trace_star]

theorem trForm_separatingLeft (r : ℕ) (c : Fin r → E) (hc : ∀ b, trForm (F := F) r c b = 0) : c = 0 := by
  classical
  funext i
  obtain ⟨e, -, he⟩ := (_root_.GlobalTheory.NTr.traceForm_perfect F E).2.1
  have h0 := hc (Pi.single i (c i * e))
  rw [trForm_apply, dotProduct_single, Pi.star_apply] at h0
  have h1 : algebraMap F E (Algebra.trace F E (star (c i) * (c i * e))) = star (c i) * c i * (e + star e) := by
    rw [(_root_.GlobalTheory.NTr.traceForm_perfect F E).1]
    simp only [star_mul, star_star]
    ring
  rw [h0, map_zero, he, mul_one] at h1
  rcases mul_eq_zero.1 h1.symm with h | h
  · simpa using h
  · simpa using h

theorem trForm_nondegenerate (r : ℕ) : (trForm (F := F) (E := E) r).Nondegenerate :=
  ⟨fun c hc => trForm_separatingLeft r c hc, fun b hb => trForm_separatingLeft r b (fun c => by
    rw [(trForm_isSymm (F := F) r).eq]; exact hb c)⟩

def intLat (r : ℕ) : AddSubgroup (Fin r → E) :=
  haveI : IsUltrametricDist E := Unram.ultraE F
  { carrier := {b | ∀ i, ‖b i‖ ≤ 1}
    add_mem' := fun {a b} ha hb i => by
      simp only [Set.mem_setOf_eq, Pi.add_apply] at *
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (hb i))
    zero_mem' := fun i => by simp
    neg_mem' := fun {a} ha i => by simpa using ha i }

theorem intLat_eq (r : ℕ) :
    ((intLat (F := F) (E := E) r : AddSubgroup (Fin r → E)) : Set (Fin r → E)) =
      Set.univ.pi (fun _ => Metric.closedBall (0 : E) 1) := by
  ext b
  simp [intLat, Metric.mem_closedBall, dist_zero_right]

theorem dual_intLat (r : ℕ) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) :
    {y : Fin r → E | ∀ x ∈ intLat (F := F) (E := E) r, ψ (trForm (F := F) r x y) = 1} =
      ((intLat (F := F) (E := E) r : AddSubgroup (Fin r → E)) : Set (Fin r → E)) := by
  classical
  haveI : IsUltrametricDist E := Unram.ultraE F
  have key := ((_root_.GlobalTheory.StdChar.psi_conductor F E).2 ψ hψ).2.2.2
  ext y
  constructor
  · intro hy i
    refine (key (y i)).1 (fun e he => ?_)
    have hx : Pi.single i (star e) ∈ intLat (F := F) (E := E) r := by
      intro j
      by_cases hj : j = i
      · subst hj; simp [Unram.norm_star (F := F), he]
      · simp [Pi.single_apply, hj]
    have := hy _ hx
    rwa [trForm_apply, Pi.star_single, star_star, single_dotProduct] at this
  · intro hy x hx
    have hn : ‖star x ⬝ᵥ y‖ ≤ 1 := by
      unfold dotProduct
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun i _ => ?_)
      rw [norm_mul, Pi.star_apply, Unram.norm_star (F := F)]
      exact mul_le_one₀ (hx i) (norm_nonneg _) (hy i)
    have := (key 1).2 (by simp) (star x ⬝ᵥ y) hn
    rwa [mul_one] at this

end GlobalTheory.JR.PiSelfDual


open GlobalTheory.JR.PiSelfDual in
theorem GlobalTheory.JR.selfDual_pi_trace : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → @SelfDual (Fin r → E) _ _ (@MeasurableSpace.pi (Fin r) (fun _ => E) (fun _ => M.mE)) (@Measure.pi (Fin r) (fun _ => E) _ (fun _ => M.mE) (fun _ => M.μE)) (fun c b => ψ (Algebra.trace F E (star c ⬝ᵥ b))) := by
  intro F E _ _ _ _ _ r M ψ hψ
  letI := M.mE
  haveI := M.bE
  haveI := M.haarE
  haveI : LocallyCompactSpace E := Unram.lcE F
  haveI : IsUltrametricDist E := Unram.ultraE F
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : Module.Finite F E := finite
  haveI : IsModuleTopology F E := isModuleTopology
  haveI : BorelSpace (Fin r → E) := Pi.borelSpace
  haveI : (Measure.pi fun _ : Fin r => M.μE).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hvol : (Measure.pi fun _ : Fin r => M.μE) ((intLat (F := F) (E := E) r : AddSubgroup (Fin r → E)) : Set (Fin r → E)) = 1 := by
    rw [intLat_eq, Measure.pi_pi]
    simp [M.volE]
  have hopen : IsOpen ((intLat (F := F) (E := E) r : AddSubgroup (Fin r → E)) : Set (Fin r → E)) := by
    rw [intLat_eq]
    exact isOpen_set_pi Set.finite_univ (fun _ _ => IsUltrametricDist.isOpen_closedBall _ one_ne_zero)
  have hcpt : IsCompact ((intLat (F := F) (E := E) r : AddSubgroup (Fin r → E)) : Set (Fin r → E)) := by
    rw [intLat_eq]
    exact isCompact_univ_pi (fun _ => isCompact_closedBall _ _)
  have h := (_root_.GlobalTheory.JR.selfDual_iff_lattice_volume_and_plancherel F E ψ hψ (Fin r → E) (trForm r) (trForm_isSymm r) (trForm_nondegenerate r)
    (Measure.pi fun _ => M.μE) inferInstance).1 (intLat r) hopen hcpt |>.1
  refine h.2 ?_
  rw [dual_intLat r ψ hψ, hvol, one_mul]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MixedModelPartialFourierColumnTwiceNegColumn
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.PartialInv

def intLat (F : Type) [NormedField F] [IsUltrametricDist F] (r : ℕ) : AddSubgroup (Fin r → F) where
  carrier := Set.univ.pi fun _ => Metric.closedBall (0 : F) 1
  zero_mem' := by intro i _; simp
  add_mem' := by
    intro a b ha hb i _
    have h1 := ha i trivial
    have h2 := hb i trivial
    simp only [mem_closedBall_zero_iff] at h1 h2 ⊢
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)
  neg_mem' := by
    intro a ha i _
    have h1 := ha i trivial
    simpa using h1

theorem mem_intLat {F : Type} [NormedField F] [IsUltrametricDist F] {r : ℕ} (x : Fin r → F) :
    x ∈ intLat F r ↔ ∀ i, ‖x i‖ ≤ 1 := by
  change x ∈ Set.univ.pi (fun _ => Metric.closedBall (0 : F) 1) ↔ _
  simp [Set.mem_pi]

theorem isTest_slice {F : Type} [NormedField F] {r : ℕ} {f : Gl r F → ℂ} (hf : IsTest f)
    (A : Matrix (Fin r) (Fin r) F) (c : Fin r → F) (l : F) : IsTest fun v : Fin r → F => f (A, v, c, l) := by
  have hc : Continuous fun v : Fin r → F => ((A, v, c, l) : Gl r F) := by fun_prop
  refine ⟨hf.1.comp_continuous hc, ?_⟩
  have he : IsClosedEmbedding fun v : Fin r → F => ((A, v, c, l) : Gl r F) := by
    refine Function.LeftInverse.isClosedEmbedding (f := fun Y : Gl r F => Y.2.1) (fun _ => rfl) (by fun_prop) hc
  exact hf.2.comp_isClosedEmbedding he

theorem selfDual_pi (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) :
    letI := M.mF
    SelfDual (Measure.pi fun _ : Fin r => M.μF) (fun x y : Fin r → F => ψ (x ⬝ᵥ y)) := by
  letI := M.mF
  haveI := M.bF
  haveI := M.haarF
  haveI : IsUltrametricDist F := Unram.ultraF E
  haveI : LocallyCompactSpace F := Unram.lcF E
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  have hcond := ((_root_.GlobalTheory.StdChar.psi_conductor F E).2 ψ hψ).2.2.1
  have hsymm : LinearMap.BilinForm.IsSymm (dotProductBilin F F : LinearMap.BilinForm F (Fin r → F)) :=
    ⟨fun x y => by simp [dotProduct_comm]⟩
  have hnd : LinearMap.BilinForm.Nondegenerate (dotProductBilin F F : LinearMap.BilinForm F (Fin r → F)) := by
    constructor
    · intro x hx
      ext i
      simpa using hx (Pi.single i 1)
    · intro x hx
      ext i
      simpa using hx (Pi.single i 1)
  have hopen : IsOpen (intLat F r : Set (Fin r → F)) :=
    isOpen_set_pi Set.finite_univ fun _ _ => IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hcpt : IsCompact (intLat F r : Set (Fin r → F)) :=
    isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hvol : (Measure.pi fun _ : Fin r => M.μF) (intLat F r : Set (Fin r → F)) = 1 := by
    change (Measure.pi fun _ : Fin r => M.μF) (Set.univ.pi fun _ => Metric.closedBall (0 : F) 1) = 1
    rw [Measure.pi_pi]
    simp [M.volF]
  have hdual : {y : Fin r → F | ∀ x ∈ intLat F r,
      ψ ((dotProductBilin F F : LinearMap.BilinForm F (Fin r → F)) x y) = 1} = (intLat F r : Set (Fin r → F)) := by
    ext y
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, mem_intLat, dotProductBilin_apply_apply]
    constructor
    · intro h i
      refine (hcond (y i)).1 fun e he => ?_
      have := h (Pi.single i e) (fun j => by
        by_cases hj : j = i
        · subst hj; simpa using he
        · simp [hj])
      simpa using this
    · intro h x hx
      refine hψ.1 _ ?_
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
      rw [norm_mul]
      exact mul_le_one₀ (hx i) (norm_nonneg _) (h i)
  have key := ((_root_.GlobalTheory.JR.selfDual_iff_lattice_volume_and_plancherel F E ψ hψ (Fin r → F) (dotProductBilin F F) hsymm hnd
    (Measure.pi fun _ : Fin r => M.μF) inferInstance).1 (intLat F r) hopen hcpt).1
  rw [hdual, hvol] at key
  exact key.2 (mul_one 1)

theorem ptrB_ptrB (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ)
    (f : Gl r F → ℂ) (hf : IsTest f) : WeilMix.ptrB M ψ (WeilMix.ptrB M ψ f) = WeilMix.negB f := by
  funext Y
  exact (selfDual_pi F E r M ψ hψ).2 _ (isTest_slice hf Y.1 Y.2.2.1 Y.2.2.2) Y.2.1

end GlobalTheory.JR.PartialInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormTotallyPositiveOfTotallyPositiveNeZero
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem norm_pos_of_totallyPositive (E E' : Type) [Field E] [NumberField E] [Field E']
    [NumberField E'] [Algebra E E'] (a : E') (ha : a ≠ 0) (hpos : ∀ φ : E' →+* ℝ, 0 < φ a)
    (φ : E →+* ℝ) : 0 < φ (Algebra.norm E a) := by
  letI : Algebra E ℂ := (Complex.ofRealHom.comp φ).toAlgebra
  have hmap : ∀ x, algebraMap E ℂ x = ((φ x : ℝ) : ℂ) := fun x => rfl
  have key := Algebra.norm_eq_prod_embeddings E ℂ a
  let g : (E' →ₐ[E] ℂ) → (E' →ₐ[E] ℂ) := fun σ =>
    { (starRingEnd ℂ).comp σ.toRingHom with
      commutes' := fun x => by
        show (starRingEnd ℂ) (σ (algebraMap E E' x)) = algebraMap E ℂ x
        rw [σ.commutes, hmap, Complex.conj_ofReal] }
  have hg : ∀ σ x, g σ x = (starRingEnd ℂ) (σ x) := fun σ x => rfl
  have hne : ∀ σ : E' →ₐ[E] ℂ, σ a ≠ 0 := fun σ => (map_ne_zero σ).2 ha
  have hnorm : ∀ σ : E' →ₐ[E] ℂ, ((‖σ a‖ : ℝ) : ℂ) ≠ 0 := fun σ => by
    exact_mod_cast (norm_ne_zero_iff.2 (hne σ))
  have h1 : ∏ σ : E' →ₐ[E] ℂ, σ a / ((‖σ a‖ : ℝ) : ℂ) = 1 := by
    refine Finset.prod_involution (fun σ _ => g σ) ?_ ?_ (fun _ _ => Finset.mem_univ _) ?_
    · intro σ _
      rw [hg, Complex.norm_conj, div_mul_div_comm, Complex.mul_conj, div_eq_one_iff_eq
        (mul_ne_zero (hnorm σ) (hnorm σ)), Complex.normSq_eq_norm_sq]
      push_cast; ring
    · intro σ _ hf hgs
      apply hf
      have hreal : ComplexEmbedding.IsReal σ.toRingHom := by
        rw [ComplexEmbedding.isReal_iff]
        ext x
        rw [ComplexEmbedding.conjugate_coe_eq]
        exact congrArg (fun τ : E' →ₐ[E] ℂ => τ x) hgs
      have hc : σ a = ((hreal.embedding a : ℝ) : ℂ) := (hreal.coe_embedding_apply a).symm
      have hp := hpos hreal.embedding
      rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
      exact div_self (by exact_mod_cast hp.ne')
    · intro σ _
      ext x
      simp [hg]
  rw [Finset.prod_div_distrib, div_eq_one_iff_eq (Finset.prod_ne_zero_iff.2 fun σ _ => hnorm σ)]
    at h1
  rw [h1, hmap] at key
  have hr : φ (Algebra.norm E a) = ∏ σ : E' →ₐ[E] ℂ, ‖σ a‖ := by
    apply Complex.ofReal_injective
    rw [key]; push_cast; rfl
  rw [hr]
  exact Finset.prod_pos fun σ _ => norm_pos_iff.2 (hne σ)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticWeilFOpNOpFOpGaussStatement
section
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadraticWeil_fOp_nOp_fOp_gauss : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ (u : A.Kˣ) (G : ℂ), IsStableGauss A ψ x μ u G → ∀ φ : A.L → ℂ, IsTest φ → ∀ z, fOp A ψ x μ (nOp A ψ x u (fOp A ψ x μ φ)) z = G * A.psiK ψ (-((u⁻¹ : A.Kˣ) : A.K) * x * A.NL z) * fOp A ψ x μ (nOp A ψ x (-((u⁻¹ : A.Kˣ) : A.K)) φ) ((-((u⁻¹ : A.Kˣ) : A.K)) • z) := by
  first | exact @GlobalTheory.JR.WeilQuad.fOp_nOp_fOp | exact GlobalTheory.JR.WeilQuad.fOp_nOp_fOp | (intros; apply GlobalTheory.JR.WeilQuad.fOp_nOp_fOp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaSelfAdjointLieOfCountLimitDescentStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitLemmaSelfAdjointLie_of_count_limit_descent : CountIdentity → UnitaryLimit → LinearDescent → UnitLemmaLie := by
  first | exact @GlobalTheory.UnitLemma.LieEnd.unitLemmaLie_of | exact GlobalTheory.UnitLemma.LieEnd.unitLemmaLie_of | (intros; apply GlobalTheory.UnitLemma.LieEnd.unitLemmaLie_of <;> assumption)
end

