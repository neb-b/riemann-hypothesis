module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.UnipotentRadicalActionFormula
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0004

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.ContinuousFirstOrbitMap
section
noncomputable section

namespace PI.LevelKSplit.W.MVA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

theorem cancel_prod {X Y : Type} [TopologicalSpace X] [AddGroup X] [IsTopologicalAddGroup X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y]
    (ν : Measure X) [ν.IsAddHaarMeasure] [SFinite ν] (a b : Measure Y) [SFinite a] [SFinite b]
    (h : ν.prod a = ν.prod b) : a = b := by
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (0 : X)
  have h0 : ν K ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hKn).ne'
  have hinf : ν K ≠ ⊤ := hK.measure_lt_top.ne
  ext s hs
  have h1 := congrArg (fun m => m (K ×ˢ s)) h
  simp only [Measure.prod_prod] at h1
  exact (ENNReal.mul_right_inj h0 hinf).1 h1

section Top

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

theorem continuous_crd (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] : Continuous (crd (F := F) (E := E) R) := by
  first
  | exact continuous_induced_dom
  | exact IsModuleTopology.continuous_of_linearMap (crd (F := F) (E := E) R).toLinearMap
  | fun_prop
  | (delta crd; exact LinearMap.continuous_of_finiteDimensional _)

theorem continuous_crd_symm (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] : Continuous (crd (F := F) (E := E) R).symm := by
  first
  | exact continuous_induced_rng.2 (by simpa [Function.comp_def] using continuous_id)
  | exact IsModuleTopology.continuous_of_linearMap (crd (F := F) (E := E) R).symm.toLinearMap
  | fun_prop

variable (R1 R2 : Type) [CommRing R1] [Algebra F R1] [CommRing R2] [Algebra F R2]
  [TopologicalSpace R1] [IsTopologicalRing R1] [TopologicalSpace R2] [IsTopologicalRing R2]

theorem continuous_first_orbit_map : Continuous (p1 (F := F) (E := E) R1 R2) := by
  have key : ∀ x, p1 (F := F) (E := E) R1 R2 x =
      (crd (F := F) (E := E) R1).symm (fun i => (crd (F := F) (E := E) (R1 × R2) x i).1) := by
    intro x
    apply (crd (F := F) (E := E) R1).injective
    rw [LinearEquiv.apply_symm_apply]
    funext i
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
      simp [crd, p1, Algebra.TensorProduct.basis_repr_tmul]
    | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, Prod.fst_add, hx, hy]
  rw [show p1 (F := F) (E := E) R1 R2 = fun x =>
      (crd (F := F) (E := E) R1).symm (fun i => (crd (F := F) (E := E) (R1 × R2) x i).1) from funext key]
  exact (continuous_crd_symm R1).comp
    (continuous_pi fun i => continuous_fst.comp ((continuous_apply i).comp (continuous_crd (R1 × R2))))

theorem continuous_p2 : Continuous (p2 (F := F) (E := E) R1 R2) := by
  have key : ∀ x, p2 (F := F) (E := E) R1 R2 x =
      (crd (F := F) (E := E) R2).symm (fun i => (crd (F := F) (E := E) (R1 × R2) x i).2) := by
    intro x
    apply (crd (F := F) (E := E) R2).injective
    rw [LinearEquiv.apply_symm_apply]
    funext i
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
      simp [crd, p2, Algebra.TensorProduct.basis_repr_tmul]
    | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, Prod.snd_add, hx, hy]
  rw [show p2 (F := F) (E := E) R1 R2 = fun x =>
      (crd (F := F) (E := E) R2).symm (fun i => (crd (F := F) (E := E) (R1 × R2) x i).2) from funext key]
  exact (continuous_crd_symm R2).comp
    (continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp (continuous_crd (R1 × R2))))

theorem continuous_qq :
    Continuous (fun y : (R1 ⊗[F] E) × (R2 ⊗[F] E) => qq R1 R2 y.1 y.2) := by
  delta qq
  exact (continuous_crd_symm (R1 × R2)).comp (continuous_pi fun k =>
    (((continuous_apply k).comp (continuous_crd R1)).comp continuous_fst).prodMk
      (((continuous_apply k).comp (continuous_crd R2)).comp continuous_snd))

variable {M : ℕ}

theorem continuous_psiE : Continuous (psiE (F := F) (E := E) (M := M) R1 R2) := by
  show Continuous (fun x : Fin M → (R1 × R2) ⊗[F] E =>
    (fun i => p1 (F := F) (E := E) R1 R2 (x i), fun i => p2 (F := F) (E := E) R1 R2 (x i)))
  exact (continuous_pi fun i => (continuous_first_orbit_map R1 R2).comp (continuous_apply i)).prodMk
    (continuous_pi fun i => (continuous_p2 R1 R2).comp (continuous_apply i))


set_option maxHeartbeats 800000 in
theorem continuous_qqv :
    Continuous (fun y : (Fin M → R1 ⊗[F] E) × (Fin M → R2 ⊗[F] E) => fun i => qq R1 R2 (y.1 i) (y.2 i)) := by
  refine continuous_pi fun i => ?_
  have h1 : Continuous (fun y : (Fin M → R1 ⊗[F] E) × (Fin M → R2 ⊗[F] E) => (y.1 i, y.2 i)) :=
    ((continuous_apply i).comp continuous_fst).prodMk ((continuous_apply i).comp continuous_snd)
  have h2 := (continuous_qq R1 R2).comp h1
  simpa only [Function.comp_def] using h2

set_option maxHeartbeats 1000000 in
theorem continuous_psiE_symm : Continuous (psiE (F := F) (E := E) (M := M) R1 R2).symm := by
  show Continuous (fun y : (Fin M → R1 ⊗[F] E) × (Fin M → R2 ⊗[F] E) =>
    fun i => qq R1 R2 (y.1 i) (y.2 i))
  exact continuous_qqv R1 R2

theorem continuous_lin (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (g : HA R σ J) :
    Continuous (lin R σ J g) := by
  first
  | exact IsModuleTopology.continuous_of_linearMap ((lin R σ J g).restrictScalars R)
  | exact Continuous.matrix_mulVec continuous_const continuous_id
  | (delta lin; fun_prop)

end Top

section Meas

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R1 R2 : Type) [CommRing R1] [Algebra F R1] [CommRing R2] [Algebra F R2]
  [TopologicalSpace R1] [IsTopologicalRing R1] [LocallyCompactSpace R1] [T2Space R1]
  [SecondCountableTopology R1]
  [TopologicalSpace R2] [IsTopologicalRing R2] [LocallyCompactSpace R2] [T2Space R2]
  [SecondCountableTopology R2]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem pres_snd
    (hV : ∀ (g : HA (R1 × R2) σ J) (ν : Measure (Fin M → (R1 × R2) ⊗[F] E)),
      ν.IsAddHaarMeasure → ν.map (lin (R1 × R2) σ J g) = ν)
    (g : HA R2 σ J) (μ : Measure (Fin M → R2 ⊗[F] E)) (hμ : μ.IsAddHaarMeasure) :
    μ.map (lin R2 σ J g) = μ := by
  let ν1 : Measure (Fin M → R1 ⊗[F] E) := Measure.addHaar
  let e := psiE (F := F) (E := E) (M := M) R1 R2
  have hc : Continuous e := continuous_psiE R1 R2
  have hcs : Continuous e.symm := continuous_psiE_symm R1 R2
  let P0 : Measure ((Fin M → R1 ⊗[F] E) × (Fin M → R2 ⊗[F] E)) := ν1.prod μ
  have : P0.IsAddHaarMeasure := inferInstance
  let P : Measure (Fin M → (R1 × R2) ⊗[F] E) := P0.map e.symm
  have : P.IsAddHaarMeasure := e.symm.isAddHaarMeasure_map P0 hcs hc
  have hP := hV (lift R1 R2 σ J g) P inferInstance
  have hl1 := continuous_lin (R1 × R2) σ J (lift R1 R2 σ J g)
  have hl2 := continuous_lin R2 σ J g
  have hPe : P.map e = P0 := by
    rw [Measure.map_map hc.measurable hcs.measurable]
    have : (e ∘ e.symm) = id := funext e.apply_symm_apply
    rw [this, Measure.map_id]
  have key : P0.map (Prod.map id (lin R2 σ J g)) = P0 := by
    have h1 : (Prod.map id (lin R2 σ J g)) ∘ e = e ∘ (lin (R1 × R2) σ J (lift R1 R2 σ J g)) := by
      funext x
      exact (psi_lin R1 R2 σ J g x).symm
    calc P0.map (Prod.map id (lin R2 σ J g))
        = (P.map e).map (Prod.map id (lin R2 σ J g)) := by rw [hPe]
      _ = P.map ((Prod.map id (lin R2 σ J g)) ∘ e) :=
          Measure.map_map (measurable_id.prodMap hl2.measurable) hc.measurable
      _ = P.map (e ∘ (lin (R1 × R2) σ J (lift R1 R2 σ J g))) := by rw [h1]
      _ = (P.map (lin (R1 × R2) σ J (lift R1 R2 σ J g))).map e :=
          (Measure.map_map hc.measurable hl1.measurable).symm
      _ = P0 := by rw [hP, hPe]
  rw [← Measure.map_prod_map ν1 μ measurable_id hl2.measurable, Measure.map_id] at key
  exact (cancel_prod ν1 _ _ key).symm ▸ rfl

end Meas

end PI.LevelKSplit.W.MVA
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.NCHeisC
section
noncomputable section

namespace PI.LevelKSplit.W.NCH

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct

section Cont

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsTopologicalRing (R ⊗[F] E)]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} (P : Frame E M r) (T : F)

theorem continuous_pWpR : Continuous (PI.LevelKSplit.W.NC.pWp R σ J P) := by
  show Continuous fun x => PI.LevelKSplit.W.NC.pWp R σ J P x
  unfold PI.LevelKSplit.W.NC.pWp
  refine (continuous_id.sub ?_).sub ?_ <;>
  refine continuous_finsetSum _ fun a _ => ?_ <;>
  exact (PI.VolSemiDirect.W.Md.continuous_hR _ σ J (hu := continuous_const) (hv := continuous_id)).smul continuous_const

theorem continuous_yH : Continuous (PI.LevelKSplit.W.NC.yH R σ J P) := by
  refine continuous_pi fun a => ?_
  exact (continuous_pWpR P).comp (PI.VolSemiDirect.W.Md.continuous_linear_action _ σ J (hg := continuous_id) (hv := continuous_const))

theorem continuous_sL_apply (half : R ⊗[F] E) {X : Type} [TopologicalSpace X]
    {y : X → Fin r → Fin M → R ⊗[F] E} (hy : Continuous y) (v : Fin M → R ⊗[F] E) :
    Continuous fun x => sL (PI.VolSemiDirect.W.datR R σ J P T) half (y x) v := by
  have hh : ∀ {u w : X → Fin M → R ⊗[F] E}, Continuous u → Continuous w →
      Continuous fun x => (PI.VolSemiDirect.W.datR R σ J P T).h (u x) (w x) :=
    fun hu hw => PI.VolSemiDirect.W.Md.continuous_hR _ σ J (hu := hu) (hv := hw)
  simp only [sL, uv, cf, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.sum_apply, Finset.sum_apply, LinearMap.smulRight_apply, PI.VolSemiDirect.W.PG.Dat.hL,
    LinearMap.coe_mk, AddHom.coe_mk]
  refine (continuous_const.add (continuous_finsetSum _ fun a _ => ?_)).sub
    (continuous_finsetSum _ fun b _ => ?_)
  · exact (hh continuous_const continuous_const).smul (((continuous_apply a).comp hy).add
      (continuous_finsetSum _ fun b _ => ((continuous_const.mul
        (hh ((continuous_apply b).comp hy) ((continuous_apply a).comp hy))).neg).smul continuous_const))
  · exact (hh ((continuous_apply b).comp hy) continuous_const).smul continuous_const

theorem continuous_sLmat (half : R ⊗[F] E) {X : Type} [TopologicalSpace X]
    {y : X → Fin r → Fin M → R ⊗[F] E} (hy : Continuous y) :
    Continuous fun x => LinearMap.toMatrix' (sL (PI.VolSemiDirect.W.datR R σ J P T) half (y x)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [LinearMap.toMatrix'_apply]
  exact (continuous_apply i).comp (continuous_sL_apply P T half hy _)

end Cont

end PI.LevelKSplit.W.NCH
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.NCIface
section
noncomputable section

namespace PI.LevelKSplit.W.NC

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open scoped TensorProduct

section Ext

variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

def HeisP : Prop :=
  IsHermND σ J → (∀ x, σ (σ x) = x) → ∀ (r : ℕ) (P : Frame E M r) (T : F), P.IsStd σ J T →
  ∃ sH : (Fin r → Wp (Af F) σ J P) → HA (Af F) σ J,
    Continuous sH ∧ Continuous (yH (Af F) σ J P) ∧
    (∀ y, sH y ∈ LevelUnipotentSubgroup (Af F) σ J P) ∧
    (∀ n ∈ LevelUnipotentSubgroup (Af F) σ J P, ∃ y : Fin r → Wp (Af F) σ J P,
      (∀ a, (y a : Fin M → Af F ⊗[F] E) = yH (Af F) σ J P n a) ∧ (sH y)⁻¹ * n ∈ Zsub (Af F) σ J P) ∧
    (∀ y, ∀ z ∈ Zsub (Af F) σ J P, ∀ a, yH (Af F) σ J P (sH y * z) a = y a) ∧
    Zsub (Af F) σ J P ≤ LevelUnipotentSubgroup (Af F) σ J P ∧
    (∀ z ∈ Zsub (Af F) σ J P, ∀ n ∈ LevelUnipotentSubgroup (Af F) σ J P, z * n = n * z) ∧
    (∀ y y', sH y * sH y' * (sH (y + y'))⁻¹ ∈ Zsub (Af F) σ J P) ∧
    (∀ n ∈ Nsub (Af F) σ J P, ∀ z ∈ Zsub (Af F) σ J P, n * z * n⁻¹ ∈ Zsub (Af F) σ J P) ∧
    (∀ h ∈ Hsub (Af F) σ J P, ∀ y, ∃ y' : Fin r → Wp (Af F) σ J P,
      (∀ a, (y' a : Fin M → Af F ⊗[F] E) = lin (Af F) σ J h (y a)) ∧ h * sH y * h⁻¹ = sH y') ∧
    (∀ h ∈ Hsub (Af F) σ J P, ∀ z ∈ Zsub (Af F) σ J P, h * z * h⁻¹ = z)

def LevP : Prop :=
  IsHermND σ J → (∀ x, σ (σ x) = x) → ∀ (r : ℕ) (P : Frame E M r) (T : F), P.IsStd σ J T →
  ∃ (A : Subgroup (HA (Af F) σ J)) (Lev : HA (Af F) σ J → HA (Af F) σ J),
    A ≤ Nsub (Af F) σ J P ∧ IsClosed (A : Set (HA (Af F) σ J)) ∧ Continuous Lev ∧
    (∀ n ∈ Nsub (Af F) σ J P, Lev n ∈ A ∧ (Lev n)⁻¹ * n ∈ LevelUnipotentSubgroup (Af F) σ J P) ∧
    (∀ u ∈ A, u ∈ LevelUnipotentSubgroup (Af F) σ J P → u = 1) ∧
    (∀ n ∈ Nsub (Af F) σ J P, ∀ m ∈ LevelUnipotentSubgroup (Af F) σ J P, n * m * n⁻¹ ∈ LevelUnipotentSubgroup (Af F) σ J P) ∧
    (∀ h ∈ Hsub (Af F) σ J P, ∀ u ∈ A, h * u = u * h)

end Ext

def HeisPAll : Prop := ForAllCM fun F E _ _ _ _ σ M J => HeisP F E σ M J
def LevPAll : Prop := ForAllCM fun F E _ _ _ _ σ M J => LevP F E σ M J

end PI.LevelKSplit.W.NC
end
end

