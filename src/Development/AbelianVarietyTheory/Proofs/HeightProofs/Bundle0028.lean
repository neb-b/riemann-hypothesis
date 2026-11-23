module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.GeneratorPullback.PullAlong
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.EqOrConjOfPlaceOf
section
noncomputable section

namespace GlobalTheory.AutFunCompare

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups

section Points

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)
variable {R R' R'' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] [CommRing R''] [Algebra F R'']

theorem HA_ext {g h : HA R σ J} (e : ∀ r s, (HA.mat R σ J g).1 r s = (HA.mat R σ J h).1 r s) : g = h :=
  Subtype.ext (Units.ext (Matrix.ext e))

theorem map_tensNU_zero (φ : R' →ₐ[F] R'') (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b)
    (h : ∀ a, φ (j a) = 0) (z : R ⊗[F] E) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) (tensNU j hj z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]

theorem map_tensNU_self (φ : R' →ₐ[F] R) (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b)
    (h : ∀ a, φ (j a) = a) (z : R ⊗[F] E) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) (tensNU j hj z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem mat_mapH (φ : R →ₐ[F] R') (g : HA R σ J) (r s : Fin M) :
    (HA.mat R' σ J (mapH σ J φ g)).1 r s =
      Algebra.TensorProduct.map φ (AlgHom.id F E) ((HA.mat R σ J g).1 r s) := rfl

theorem mat_extH (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) (g : HA R σ J) (r s : Fin M) :
    (HA.mat R' σ J (extH σ J j hj g)).1 r s =
      (1 - tensNU (E := E) j hj 1) * (1 : Matrix (Fin M) (Fin M) (R' ⊗[F] E)) r s +
        tensNU j hj ((HA.mat R σ J g).1 r s) := rfl

theorem mapH_extH_zero (φ : R' →ₐ[F] R'') (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b)
    (h : ∀ a, φ (j a) = 0) (g : HA R σ J) : mapH σ J φ (extH σ J j hj g) = 1 := by
  refine HA_ext σ J fun r s => ?_
  rw [mat_mapH, mat_extH, map_add (f := _), map_mul, map_sub, map_tensNU_zero φ j hj h, map_tensNU_zero φ j hj h]
  show _ = (1 : Matrix (Fin M) (Fin M) (R'' ⊗[F] E)) r s
  by_cases e : r = s <;> simp [Matrix.one_apply, e]

theorem mapH_extH_self (φ : R' →ₐ[F] R) (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b)
    (h : ∀ a, φ (j a) = a) (g : HA R σ J) : mapH σ J φ (extH σ J j hj g) = g := by
  refine HA_ext σ J fun r s => ?_
  rw [mat_mapH, mat_extH, map_add (f := _), map_mul, map_sub, map_tensNU_self φ j hj h, map_tensNU_self φ j hj h]
  simp

variable [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace R'] [IsTopologicalRing R']

theorem continuous_tensNU (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) (hc : Continuous j)
    [FiniteDimensional F E] : Continuous (tensNU (E := E) j hj) := by
  have : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have : IsModuleTopology R' (R' ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  have : IsTopologicalRing (R' ⊗[F] E) := IsModuleTopology.isTopologicalRing R' _
  let b := Module.finBasis F E
  let e := (Algebra.TensorProduct.basis R b).equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : (tensNU (E := E) j hj : _ → _) = fun z => ∑ i, j (e z i) • ((1 : R') ⊗ₜ[F] b i) := by
    funext z
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_equivFun z, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [e, TensorProduct.smul_tmul']
  rw [h2]
  refine continuous_finsetSum _ fun i _ => ?_
  have h3 : Continuous fun z => j (e z i) := hc.comp ((continuous_apply i).comp h1)
  exact Continuous.fun_smul h3 continuous_const

theorem continuous_mapH [FiniteDimensional F E] (φ : R →ₐ[F] R') (hc : Continuous φ) :
    Continuous (mapH σ J φ) := by
  have h : Continuous (Algebra.TensorProduct.map φ (AlgHom.id F E)) :=
    continuous_tensNU (E := E) φ.toLinearMap (map_mul φ) hc
  refine Continuous.subtype_mk (Continuous.comp (g := bc _) ?_ continuous_subtype_val) _
  exact Continuous.units_map _ (continuous_id.matrix_map h)

theorem continuous_extH [FiniteDimensional F E] (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b)
    (hc : Continuous j) : Continuous (extH σ J j hj) := by
  have : IsModuleTopology R' (R' ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (R' ⊗[F] E) := IsModuleTopology.isTopologicalRing R' _
  have h := continuous_tensNU (E := E) j hj hc
  refine Continuous.subtype_mk (Continuous.comp (g := Units.map _) ?_ continuous_subtype_val) _
  exact Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map h))

end Points

section Groups

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) (V : HSpace E)

theorem projFin_ofFin (y : GFin hc V) : IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projFin hc V (ofFin hc V y) = y :=
  mapH_extH_self _ _ _ _ _ (fun _ => rfl) y
theorem projInf_ofFin (y : GFin hc V) : IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projInf hc V (ofFin hc V y) = 1 :=
  mapH_extH_zero _ _ _ _ _ (fun _ => rfl) y
theorem projInf_ofInf (y : GInf hc V) : IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projInf hc V (ofInf hc V y) = y :=
  mapH_extH_self _ _ _ _ _ (fun _ => rfl) y
theorem projFin_ofInf (y : GInf hc V) : IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projFin hc V (ofInf hc V y) = 1 :=
  mapH_extH_zero _ _ _ _ _ (fun _ => rfl) y

theorem eq_of_proj {g h : GA hc V} (h1 : IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projInf hc V g = IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projInf hc V h)
    (h2 : IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projFin hc V g = IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projFin hc V h) : g = h := by
  rw [← mul_inv_eq_one]
  have a : IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projInf hc V (g * h⁻¹) = 1 := by rw [map_mul, map_inv, h1, mul_inv_cancel]
  have b : IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projFin hc V (g * h⁻¹) = 1 := by rw [map_mul, map_inv, h2, mul_inv_cancel]
  exact Subtype.ext (Units.ext (GlobalTheory.AutFunCounterexample.tens_inj (F := F) (E := E) (A := Ainf F) (B := Af F) _
    (congrArg (fun x => (HA.mat _ _ _ x).1) a) (congrArg (fun x => (HA.mat _ _ _ x).1) b)))

theorem ofFin_projFin {g : GA hc V} (h : g ∈ finPts hc V) : ofFin hc V (IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projFin hc V g) = g :=
  eq_of_proj hc V ((projInf_ofFin hc V _).trans (Eq.symm h)) (projFin_ofFin hc V _)

theorem ofInf_projInf {g : GA hc V} (h : g ∈ realPts hc V) : ofInf hc V (IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projInf hc V g) = g :=
  eq_of_proj hc V (projInf_ofInf hc V _) ((projFin_ofInf hc V _).trans (Eq.symm h))

theorem continuous_ofFin : Continuous (ofFin hc V) :=
  continuous_extH _ _ _ _ (continuous_const.prodMk continuous_id)

theorem continuous_projFin : Continuous (IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projFin hc V) :=
  continuous_mapH _ _ _ continuous_snd

def infEmb (τ : E →+* ℂ) : Ainf F ⊗[F] E →+* ℂ :=
  (locMap hc τ).comp (Algebra.TensorProduct.map
    (Pi.evalAlgHom F (fun w : InfinitePlace F => w.Completion) (placeOf F τ) :
      Ainf F →ₐ[F] (placeOf F τ).Completion) (AlgHom.id F E)).toRingHom

theorem isInfEmb_infEmb (τ : E →+* ℂ) : Formalism.MainNotions.StandardLattice.IsInfEmb τ (infEmb hc τ) := by
  refine ⟨fun x => ?_, ?_⟩
  · show locMap hc τ ((1 : (placeOf F τ).Completion) ⊗ₜ[F] x) = _
    change InfinitePlace.Completion.extensionEmbedding (placeOf F τ) 1 * τ x = τ x
    rw [map_one, one_mul]
  · have : (fun a : Ainf F => infEmb hc τ (a ⊗ₜ[F] (1 : E))) =
        fun a => InfinitePlace.Completion.extensionEmbedding (placeOf F τ) (a (placeOf F τ)) := by
      funext a
      show locMap hc τ (a (placeOf F τ) ⊗ₜ[F] (1 : E)) = _
      change InfinitePlace.Completion.extensionEmbedding (placeOf F τ) (a (placeOf F τ)) * τ 1 = _
      rw [map_one, mul_one]
    rw [this]
    exact (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous.comp (continuous_apply _)

theorem isInfEmb_unique (τ : E →+* ℂ) (θ θ' : Ainf F ⊗[F] E →+* ℂ) (h : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ)
    (h' : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ') : θ = θ' := by
  have key : (fun a : Ainf F => θ (a ⊗ₜ[F] (1 : E))) = fun a : Ainf F => θ' (a ⊗ₜ[F] (1 : E)) := by
    refine (InfiniteAdeleRing.denseRange_algebraMap F).equalizer h.2 h'.2 ?_
    funext x
    have e : (algebraMap F (Ainf F) x) ⊗ₜ[F] (1 : E) = (1 : Ainf F) ⊗ₜ[F] (algebraMap F E x) := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    show θ (algebraMap F (Ainf F) x ⊗ₜ[F] (1 : E)) = θ' (algebraMap F (Ainf F) x ⊗ₜ[F] (1 : E))
    rw [e, h.1, h'.1]
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    have e : a ⊗ₜ[F] x = (a ⊗ₜ[F] (1 : E)) * ((1 : Ainf F) ⊗ₜ[F] x) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, map_mul, map_mul, h.1, h'.1, congrFun key a]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

def evW (w : InfinitePlace F) : Ainf F →ₐ[F] w.Completion :=
  Pi.evalAlgHom F (fun w : InfinitePlace F => w.Completion) w


open Classical in
def sgW (w : InfinitePlace F) : w.Completion →ₗ[F] Ainf F :=
  LinearMap.single F (fun w : InfinitePlace F => w.Completion) w

omit [NumberField F] in
theorem sgW_mul (w : InfinitePlace F) (a b : w.Completion) : sgW w (a * b) = sgW w a * sgW w b := by
  classical
  exact Pi.single_mul w a b

omit [NumberField E] [StarRing E] in
theorem infTens_ext {z z' : Ainf F ⊗[F] E} (h : ∀ w : InfinitePlace F,
    Algebra.TensorProduct.map (evW w) (AlgHom.id F E) z =
    Algebra.TensorProduct.map (evW w) (AlgHom.id F E) z') : z = z' := by
  classical
  have key : ∀ z : Ainf F ⊗[F] E, z = ∑ w : InfinitePlace F,
      LinearMap.rTensor E (sgW w) (Algebra.TensorProduct.map (evW w) (AlgHom.id F E) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      have : a = ∑ w, sgW w (evW w a) := (Finset.univ_sum_single a).symm
      conv_lhs => rw [this]
      exact TensorProduct.sum_tmul _ _ _
    | add x y hx hy =>
      simp only [map_add (f := _), Finset.sum_add_distrib]
      rw [← hx, ← hy]
  rw [key z, key z']
  exact Finset.sum_congr rfl fun w _ => by rw [h w]



end Groups

end GlobalTheory.AutFunCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
section
open NumberField IsDedekindDomain MeasureTheory

namespace GlobalTheory.AdeleCocompact

variable (F : Type) [Field F] [NumberField F]

theorem exists_bound_sub_integer :
    ∃ C : InfinitePlace F → ℝ, ∀ x : F, ∃ y : 𝓞 F, ∀ v : InfinitePlace F, v (x - y) ≤ C v := by
  classical
  refine ⟨fun v => ∑ i, v (integralBasis F i), fun x => ?_⟩
  refine ⟨∑ i, ⌊(integralBasis F).repr x i⌋ • RingOfIntegers.basis F i, fun v => ?_⟩
  have h : x - ((∑ i, ⌊(integralBasis F).repr x i⌋ • RingOfIntegers.basis F i : 𝓞 F) : F)
      = ∑ i, ((Int.fract ((integralBasis F).repr x i) : ℚ) : F) * integralBasis F i := by
    conv_lhs => enter [1]; rw [← (integralBasis F).sum_repr x]
    change _ - algebraMap (𝓞 F) F _ = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, ← integralBasis_apply, Int.fract, Rat.smul_def, zsmul_eq_mul]
    push_cast
    ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, ← InfinitePlace.norm_embedding_eq, map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [map_mul, norm_mul, InfinitePlace.norm_embedding_eq v (integralBasis F i), map_ratCast,
    Complex.norm_ratCast]
  refine mul_le_of_le_one_left (apply_nonneg _ _) ?_
  rw [abs_of_nonneg (by exact_mod_cast Int.fract_nonneg _)]
  exact_mod_cast (Int.fract_lt_one _).le

omit [NumberField F] in
theorem properSpace_completion (v : InfinitePlace F) : ProperSpace v.Completion := by
  refine ⟨fun x r => ?_⟩
  have h := InfinitePlace.Completion.isometry_extensionEmbedding v
  rw [← h.preimage_closedBall]
  exact h.isClosedEmbedding.isCompact_preimage (isCompact_closedBall _ _)

theorem exists_compact_infinite :
    ∃ K : Set (InfiniteAdeleRing F), IsCompact K ∧
      ∀ a : InfiniteAdeleRing F, ∃ y : 𝓞 F, a - algebraMap F (InfiniteAdeleRing F) y ∈ K := by
  obtain ⟨C, hC⟩ := exists_bound_sub_integer F
  haveI := properSpace_completion F
  refine ⟨Set.pi Set.univ fun v : InfinitePlace F => Metric.closedBall (0 : v.Completion) (1 + C v),
    isCompact_univ_pi fun v => isCompact_closedBall _ _, fun a => ?_⟩
  have hU : IsOpen (X := InfiniteAdeleRing F)
      (Set.pi Set.univ fun v : InfinitePlace F => Metric.ball (a v) 1) :=
    isOpen_set_pi Set.finite_univ fun v _ => Metric.isOpen_ball
  obtain ⟨x, hx⟩ := (InfiniteAdeleRing.denseRange_algebraMap F).exists_mem_open hU
    ⟨a, fun v _ => Metric.mem_ball_self one_pos⟩
  obtain ⟨y, hy⟩ := hC x
  refine ⟨y, fun v _ => ?_⟩
  have h1 : ‖a v - algebraMap F (InfiniteAdeleRing F) x v‖ < 1 := by
    rw [← dist_eq_norm, dist_comm]; exact hx v trivial
  have h2 : ‖algebraMap F (InfiniteAdeleRing F) (x - y) v‖ ≤ C v := by
    rw [InfiniteAdeleRing.algebraMap_apply, InfinitePlace.Completion.norm_coe]
    exact hy v
  have h3 : (a - algebraMap F (InfiniteAdeleRing F) y) =
      (a - algebraMap F (InfiniteAdeleRing F) x) + algebraMap F (InfiniteAdeleRing F) (x - y) := by
    rw [map_sub]; ring
  rw [mem_closedBall_zero_iff, h3]
  exact (norm_add_le (a v - algebraMap F (InfiniteAdeleRing F) x v) _).trans (add_le_add h1.le h2)

theorem isCompact_integral :
    IsCompact {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} := by
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F
  have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (𝓕 := Filter.cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

theorem exists_compact_adele : ∀ (F : Type) [Field F] [NumberField F], ∃ K : Set (AdeleRing (𝓞 F) F), IsCompact K ∧ ∀ a : AdeleRing (𝓞 F) F, ∃ x : F, a - algebraMap F (AdeleRing (𝓞 F) F) x ∈ K := by
  intro F _ _
  obtain ⟨K, hK, hK'⟩ := exists_compact_infinite F
  refine ⟨K ×ˢ {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F},
    hK.prod (isCompact_integral F), fun a => ?_⟩
  obtain ⟨x, b, hb, hab⟩ := GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul F 1 one_pos a.2
  obtain ⟨y, hy⟩ := hK' (a.1 - algebraMap F (InfiniteAdeleRing F) x)
  refine ⟨x + y, ?_, ?_⟩
  · change a.1 - algebraMap F (InfiniteAdeleRing F) (x + y) ∈ K
    rw [map_add (f := _), ← sub_sub]; exact hy
  · change ∀ v, (a.2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) (x + y)) v ∈ v.adicCompletionIntegers F
    have h : a.2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) (x + y) =
        b - algebraMap F (FiniteAdeleRing (𝓞 F) F) y := by
      rw [hab, map_add (f := _), one_smul]; ring
    rw [h]
    intro v
    exact sub_mem (hb v) (HeightOneSpectrum.coe_mem_adicCompletionIntegers v y)

end GlobalTheory.AdeleCocompact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.IsRigTransport
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionTauCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj Matrix

section Data

variable {R : Type} [CommRing R] [IsDomain R]

end Data

section Transport

variable {A : Over (Sp ℂ)} [GrpObj A] {L M : LB A.left} {g : ℕ}

theorem valAt'_resU {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)ˣ)
    (hV : ⊤ ≤ x ⁻¹ᵁ V) : valAt' x V (res h a).val = valAt' x U a.val :=
  valAt'_res x h _ hV

theorem iso_fr {w : LB.Iso L M} (hw : w.IsGen) (u : HolUnif A L g) (z : Fin g → ℂ) {j j' : M.ι} {i i' : L.ι}
    (hj : ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U j) (hj' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U j')
    (hi : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i) (hi' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i') :
    valAt' (u.ex z).left (M.U j ⊓ L.U i) (w.s (j, i)).val * u.fr i z =
      valAt' (u.ex z).left (M.U j ⊓ M.U j') (M.g j j').val *
        (valAt' (u.ex z).left (M.U j' ⊓ L.U i') (w.s (j', i')).val * u.fr i' z) := by
  have hO : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (M.U j ⊓ L.U i ⊓ (M.U j' ⊓ L.U i')) := fun p hp =>
    ⟨⟨hj hp, hi hp⟩, hj' hp, hi' hp⟩
  have hii : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.U i ⊓ L.U i') := fun p hp => ⟨hi hp, hi' hp⟩
  have e := congrArg (fun a : Γ(A.left, M.U j ⊓ L.U i ⊓ (M.U j' ⊓ L.U i'))ˣ => valAt' (u.ex z).left _ a.val)
    (hw (j, i) (j', i'))
  have e' : valAt' (u.ex z).left (M.U j ⊓ L.U i) (w.s (j, i)).val =
      valAt' (u.ex z).left (M.U j ⊓ M.U j') (M.g j j').val *
        (valAt' (u.ex z).left (L.U i ⊓ L.U i') (L.g i i').val)⁻¹ *
        valAt' (u.ex z).left (M.U j' ⊓ L.U i') (w.s (j', i')).val := by
    refine (valAt'_resU _ _ _ hO).symm.trans (e.trans ((valAt'_mul _ _ _ _).trans (congrArg₂ (· * ·)
      ((valAt'_mul _ _ _ _).trans (congrArg₂ (· * ·) (valAt'_resU _ _ _ hO)
        ((valAt'_units_inv _ hO _).trans (congrArg (·⁻¹) (valAt'_resU _ _ _ hO))))) (valAt'_resU _ _ _ hO))))
  have hne := valAt'_unit_ne_zero _ hii (L.g i i')
  rw [e', u.fr_compat i i' z hii]
  field_simp

theorem valAt'_g_self {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) (x : Sp ℂ ⟶ X) {j : M.ι} (hj : ⊤ ≤ x ⁻¹ᵁ M.U j) :
    valAt' x (M.U j ⊓ M.U j) (M.g j j).val = 1 := by
  rw [← valAt'_resU x (le_inf le_rfl le_rfl : M.U j ≤ M.U j ⊓ M.U j) _ hj, hM.g_self, Units.val_one,
    valAt'_one x hj]

theorem exists_chart_ex (hL : L.IsLB) (u : HolUnif A L g) (z : Fin g → ℂ) :
    ∃ i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i := by
  obtain ⟨i, hi⟩ := exists_chart hL ((u.ex z).left (default : PrimeSpectrum ℂ))
  exact ⟨i, (top_le_preimage_iff_mem _ _).2 hi⟩

def frT (hL : L.IsLB) (w : LB.Iso L M) (u : HolUnif A L g) (j : M.ι) (z : Fin g → ℂ) : ℂ :=
  valAt' (u.ex z).left (M.U j ⊓ L.U (exists_chart_ex hL u z).choose) (w.s (j, (exists_chart_ex hL u z).choose)).val *
    u.fr (exists_chart_ex hL u z).choose z

theorem frT_eq (hL : L.IsLB) (hM : M.IsLB) {w : LB.Iso L M} (hw : w.IsGen) (u : HolUnif A L g) {j : M.ι} {i : L.ι}
    {z : Fin g → ℂ} (hj : ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U j) (hi : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i) :
    frT hL w u j z = valAt' (u.ex z).left (M.U j ⊓ L.U i) (w.s (j, i)).val * u.fr i z := by
  rw [frT, iso_fr hw u z hj hj (exists_chart_ex hL u z).choose_spec hi, valAt'_g_self hM _ hj, _root_.one_mul]

def transport (hL : L.IsLB) (hM : M.IsLB) {w : LB.Iso L M} (hw : w.IsGen) (u : HolUnif A L g) : HolUnif A M g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr := frT hL w u
  fr_hol j z₀ hz₀ := by
    obtain ⟨i, hi⟩ := exists_chart_ex hL u z₀
    have h₁ := u.hol (M.U j ⊓ L.U i) (w.s (j, i)).val
    have hm : {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (M.U j ⊓ L.U i)} ∈ nhds z₀ :=
      h₁.1.mem_nhds ((top_le_preimage_inf _ _ _).2 ⟨hz₀, hi⟩)
    have hd := (h₁.2.mul ((u.fr_hol i).mono fun z hz => ((top_le_preimage_inf _ _ _).1 hz).2)).differentiableAt hm
    refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hm] with z hz
    exact frT_eq hL hM hw u ((top_le_preimage_inf _ _ _).1 hz).1 ((top_le_preimage_inf _ _ _).1 hz).2
  fr_ne j z hz := by
    have hi := (exists_chart_ex hL u z).choose_spec
    exact mul_ne_zero (valAt'_unit_ne_zero _ ((top_le_preimage_inf _ _ _).2 ⟨hz, hi⟩) _) (u.fr_ne _ _ hi)
  fr_compat j j' z hz :=
    have hi := (exists_chart_ex hL u z).choose_spec
    iso_fr hw u z ((top_le_preimage_inf _ _ _).1 hz).1 ((top_le_preimage_inf _ _ _).1 hz).2 hi hi

theorem isAH_transport (hL : L.IsLB) (hM : M.IsLB) {w : LB.Iso L M} (hw : w.IsGen) (u : HolUnif A L g)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (h : u.IsAH Hm χ) : (transport hL hM hw u).IsAH Hm χ := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun l j z hj => ?_⟩
  obtain ⟨i, hi⟩ := exists_chart_ex hL u z
  have hl : u.ex (z + l) = u.ex z := by rw [u.ex_add, (u.ker _).2 l.2, _root_.mul_one]
  have a := frT_eq hL hM hw u (z := z) hj hi
  have b := frT_eq hL hM hw u (j := j) (i := i) (z := z + l) (by rw [hl]; exact hj) (by rw [hl]; exact hi)
  rw [hl] at b
  refine a.trans (Eq.trans ?_ (congrArg _ b.symm))
  rw [h.2.2.2 l i z hi]
  ring

end Transport

theorem isGen_refl {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) :
    LB.Gen.IsGen (⟨fun p => L.g p.1 p.2⟩ : LB.Iso L L) := by
  refine fun p q => unit_ext fun y hy => ?_
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

def polOfPullback {S S' : Scheme.{0}} (P : Out.PolAV S) {f : S' ⟶ S} (A : Over S') [GrpObj A] [IsCommMonObj A]
    {φ : A.left ⟶ P.A.left} (h : IsGrpPullback A P.A f φ) : Out.PolAV S' where
  A := A
  isAb :=
    { comm := inferInstance
      smooth := MorphismProperty.of_isPullback (P := @Smooth) h.1 P.isAb.smooth
      proper := MorphismProperty.of_isPullback (P := @IsProper) h.1 P.isAb.proper
      geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 P.isAb.geomConnected }
  g := P.g
  smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
  L := P.L.pull φ
  isLB := pull_isLB P.isLB _
  rigid := PolBaseChange.rigidified_pull h P.rigid
  sym := PolBaseChange.sym_pull h P.sym
  ample :=
    haveI := P.isAb.proper
    AmpleBaseChange.relAmple_of_isPullback P.isLB P.ample h.1
  ktriv := kTriv_pull h P.isLB (pull_isLB P.isLB _) ((isGen_iff _).1 (isGen_refl (pull_isLB P.isLB φ))) P.ktriv

end GlobalTheory.TorsionTauCompare
end
end

