module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0150
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0031
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.FormalDegreeBessel.StatementG
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ActOMemLatOOfStab
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.LatStabAct

open GlobalTheory.AdelicLatMove

variable {D : D7}

def latCoord (V : HSp D) : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) where
  carrier := L0c D V
  add_mem' := by
    intro a b ha hb
    show ∑ i, (a i + b i) • V.frame i ∈ V.L0
    simp only [add_smul, Finset.sum_add_distrib]
    exact V.L0.add_mem ha hb
  zero_mem' := by
    show ∑ i, (0 : D.host.E) • V.frame i ∈ V.L0
    simp
  smul_mem' := by
    intro c a ha
    show ∑ i, (c • a i) • V.frame i ∈ V.L0
    simp only [smul_assoc, ← Finset.smul_sum]
    exact V.L0.smul_mem c ha

def swapF (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →+* EAf D :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toAlgHom.toRingHom

theorem swap_mem_hatL {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (y : Fin n → Af D.host.F ⊗[D.host.F] D.host.E)
    (hy : y ∈ latHat D.host.F D.host.E (Λ : Set (Fin n → D.host.E))) :
    (fun i => swapF D (y i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    exact pure_mem_hatL Λ a ha x hx
  | zero => simp only [Pi.zero_apply, map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => simp only [Pi.add_apply, map_add (f := _)]; exact Submodule.add_mem _ ha hb
  | neg a _ ha => simp only [Pi.neg_apply, map_neg]; exact Submodule.neg_mem _ ha

theorem mulVec_pure_mem (V : HSp D) (g : GA D V) (hg : g ∈ KsphC V ∅) (x : Fin V.rank → D.host.E)
    (hx : x ∈ L0c D V) :
    (mt V g).map (toEAf D) *ᵥ (fun i => x i ⊗ₜ[D.host.F] (1 : Af D.host.F)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) (latCoord V) := by
  have h1 : (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) ∈ latHat D.host.F D.host.E (L0c D V) :=
    AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, x, hx, rfl⟩
  have h2 := swap_mem_hatL (latCoord V) _ ((hg.2.1 _).1 h1)
  convert h2 using 1
  funext i
  rw [RingHom.map_mulVec]
  congr 1

variable {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}

theorem fin_smul_gen (β α : Af D.host.F) (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β) •
      (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] M i j : WO S T) =
      Matrix.of fun i j => (pairA D.host.F 0 (β * α)) ⊗ₜ[D.host.F] M i j := by
  ext i j
  change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (_ ⊗ₜ _) = _ ⊗ₜ _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  congr 1
  exact Prod.ext (mul_zero _) rfl

theorem fin_smul_mem {P : HeightOneSpectrum (𝓞 D.host.F) → Prop} {β : Af D.host.F} (hβ : β ∈ intAf D.host.F)
    (h0 : ∀ v, ¬ P v → evalV D.host.F v β = 0) {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β) • u ∈ latO S T LS LT P := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨β * α, fun w => ?_, fun w hw => ?_, a, ha, s, hs, t, ht,
      fin_smul_gen β α (fun i j => a * t i * ∑ k, star (s k) * S.gram k j)⟩
    · rw [map_mul]; exact mul_mem (hβ w) (hα w)
    · rw [map_mul, h0 w hw, zero_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x x' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg x _ h => rw [smul_neg]; exact neg_mem h

theorem actO_mem_latO_of_stab : ∀ (D : D7) (S T : HSp D), ∀ g ∈ KsphC S ∅, ∀ h ∈ KsphC T ∅, ∀ (P : HeightOneSpectrum (𝓞 D.host.F) → Prop), ∀ u ∈ latO S T (L0c D S) (L0c D T) P, actO S T g h u ∈ latO S T (L0c D S) (L0c D T) P := by
  intro D S T g hg h hh P u hu
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨α, hα, h0, a, ha, s, hs, t, ht, rfl⟩ := hu
    have e := rankOne_pure S T a s t 1 1
    have e2 := fin_smul_gen (S := S) (T := T) α (1 * 1) (fun i j => a * t i * ∑ k, star (s k) * S.gram k j)
    rw [← e, mul_one, mul_one] at e2
    have e3 : ∀ (c : AE D) (x : WO S T), actO S T g h (c • x) = c • actO S T g h x := fun c x => by
      simp only [actO, Matrix.mul_smul, Matrix.smul_mul]
    rw [← e2, e3, actO_rankOne]
    exact fin_smul_mem hα h0 (rankOne_mem_latO S T (latCoord S) (latCoord T) a ha _
      (mulVec_pure_mem S g hg s hs) _ (mulVec_pure_mem T h hh t ht))
  | zero => simp only [actO, Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => simp only [actO, Matrix.mul_add, Matrix.add_mul] at hy hz ⊢; exact add_mem hy hz
  | neg y _ hy => simp only [actO, Matrix.mul_neg, Matrix.neg_mul] at hy ⊢; exact neg_mem hy

end GlobalTheory.LatStabAct

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.AdelicGroupTop

theorem isTopologicalGroup_HA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : IsTopologicalGroup (HA (AF F) σ J) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := F) (E := E)
  exact inferInstanceAs (IsTopologicalGroup (HR (AF F) σ J))

theorem adelic_unitary_topology : ∀ (D : D7) (V : HSp D), LocallyCompactSpace (GA D V) ∧ SecondCountableTopology (GA D V) ∧ T2Space (GA D V) ∧ BorelSpace (GA D V) ∧ IsTopologicalGroup (GA D V) ∧ DiscreteTopology (GQ V) ∧ Countable (GQ V) := by
  intro D V
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  have hd : DiscreteTopology (GQ V) := GlobalTheory.RationalDiscrete.discreteTopology_GQ D V
  have h2' : SecondCountableTopology (GA D V) := h2
  exact ⟨h1, h2, h3, ⟨rfl⟩, isTopologicalGroup_HA D.sp.cm.sig V.gram, hd,
    TopologicalSpace.separableSpace_iff_countable.1 inferInstance⟩

end GlobalTheory.Mem.AdelicGroupTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoordSymm
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.OrientedCoord

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem mul_gramInv (V : HSp D) : V.gram.map (incA D) * (V.gram⁻¹).map (incA D) = 1 :=
  mul_eq_one_comm.1 (GlobalTheory.OrientedSmall.gramInv_mul V)

def coord (S T : HSp D) : WO S T ≃+ WA S T where
  toFun := toTWsmall S T
  invFun y := HMul.hMul (y : Matrix (Fin S.rank) (Fin T.rank) (AE D))ᵀ (S.gram.map (incA D))
  left_inv x := by
    simp only [toTWsmall, Matrix.transpose_transpose]
    rw [Matrix.mul_assoc, GlobalTheory.OrientedSmall.gramInv_mul, Matrix.mul_one]
  right_inv y := by
    simp only [toTWsmall]
    rw [Matrix.mul_assoc, mul_gramInv, Matrix.mul_one, Matrix.transpose_transpose]
  map_add' x y := by
    simp only [toTWsmall]
    rw [Matrix.add_mul, Matrix.transpose_add]

theorem coord_apply (S T : HSp D) (x : WO S T) :
    coord S T x = (HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) ((S.gram⁻¹).map (incA D)))ᵀ := rfl

theorem coord_symm_apply (S T : HSp D) (y : WA S T) :
    (coord S T).symm y = HMul.hMul (y : Matrix (Fin S.rank) (Fin T.rank) (AE D))ᵀ (S.gram.map (incA D)) := rfl

theorem continuous_coord (S T : HSp D) : Continuous (coord S T) :=
  (continuous_id.matrix_mul continuous_const).matrix_transpose

theorem continuous_coord_symm (S T : HSp D) : Continuous (coord S T).symm :=
  continuous_id.matrix_transpose.matrix_mul continuous_const

theorem coord_ratW (S T : HSp D) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    coord S T (ratW T S γ) = ratW S T (γ * S.gram⁻¹)ᵀ := by
  rw [coord_apply]
  unfold ratW
  rw [← Matrix.map_mul, Matrix.transpose_map]

theorem coord_symm_ratW (S T : HSp D) (γ : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    (coord S T).symm (ratW S T γ) = ratW T S (γᵀ * S.gram) := by
  rw [coord_symm_apply]
  unfold ratW
  rw [Matrix.map_mul, Matrix.transpose_map]

theorem coord_map_zero (S T : HSp D) {R : Type} [CommRing R] (φ : AE D →+* R) (x : WO S T) (h : x.map φ = 0) :
    (coord S T x).map φ = 0 := by
  rw [coord_apply, Matrix.transpose_map, Matrix.map_mul, h, Matrix.zero_mul, Matrix.transpose_zero]

theorem coord_symm_map_zero (S T : HSp D) {R : Type} [CommRing R] (φ : AE D →+* R) (y : WA S T) (h : y.map φ = 0) :
    ((coord S T).symm y).map φ = 0 := by
  rw [coord_symm_apply, Matrix.map_mul, Matrix.transpose_map, h, Matrix.transpose_zero, Matrix.zero_mul]

theorem symplOH_eq (S T : HSp D) (hr : S.rank ≤ T.rank) (x y : WO S T) :
    symplOH S T x y = symplH S T (coord S T x) (coord S T y) := by
  unfold symplOH symplH
  rw [(GlobalTheory.OrientedSmall.bridgeSmall D S T hr).1 x y]
  rfl

theorem heisO_coord (S T : HSp D) (hr : S.rank ≤ T.rank) (ψ : AddChar (AF D.host.F) ℂ) (w : WO S T) (f : WA S T → ℂ) :
    heisO ψ S T w (fun x => f (coord S T x)) = fun x => Heisenberg₂ ψ S T (coord S T w) f (coord S T x) := by
  funext x
  simp only [heisO, Formalism.L2.Theta.Heisenberg₂, map_add (f := _), symplOH_eq S T hr]

theorem isThetaFunO_coord (S T : HSp D) (hr : S.rank ≤ T.rank) (ψ : AddChar (AF D.host.F) ℂ) (f : WA S T → ℂ) :
    IsThetaFunO ψ S T (fun x => f (coord S T x)) ↔ IsThetaFun ψ S T f := by
  have c1 := continuous_coord S T
  have c2 := continuous_coord_symm S T
  refine ⟨fun hf => ⟨fun γ w => ?_, ?_, ?_, fun k L hL h0 w => ?_⟩,
    fun hf => ⟨fun γ w => ?_, ?_, hf.cont.comp c1, fun k L hL h0 w => ?_⟩⟩
  · have := hf.quasi (γᵀ * S.gram) ((coord S T).symm w)
    rw [← coord_symm_ratW, symplOH_eq S T hr] at this
    simpa only [map_add (f := _), AddEquiv.apply_symm_apply] using this
  · obtain ⟨U, hU, hfix⟩ := hf.level
    refine ⟨U.comap (coord S T).symm.toAddMonoidHom, hU.preimage c2, fun u hu h0 => ?_⟩
    have := hfix ((coord S T).symm u) hu (coord_symm_map_zero S T _ u h0)
    rw [heisO_coord S T hr] at this
    funext y
    simpa only [AddEquiv.apply_symm_apply] using congrFun this ((coord S T).symm y)
  · simpa only [Function.comp_def, AddEquiv.apply_symm_apply] using hf.cont.comp c2
  · have := hf.smooth k ((coord S T).symm.toAddMonoidHom.comp L) (c2.comp hL)
      (fun t => coord_symm_map_zero S T _ _ (h0 t)) ((coord S T).symm w)
    simpa only [map_add (f := _), AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_coe, AddEquiv.apply_symm_apply] using this
  · have := hf.quasi (γ * S.gram⁻¹)ᵀ (coord S T w)
    rw [← coord_ratW, ← symplOH_eq S T hr] at this
    simpa only [map_add (f := _)] using this
  · obtain ⟨U, hU, hfix⟩ := hf.level
    refine ⟨U.comap (coord S T).toAddMonoidHom, hU.preimage c1, fun u hu h0 => ?_⟩
    rw [heisO_coord S T hr, hfix (coord S T u) hu (coord_map_zero S T _ u h0)]
  · have := hf.smooth k ((coord S T).toAddMonoidHom.comp L) (c1.comp hL)
      (fun t => coord_map_zero S T _ _ (h0 t)) (coord S T w)
    simpa only [map_add (f := _), AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_coe] using this

theorem coord_gen (S T : HSp D) (β : AF D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    coord S T (Matrix.of fun i j => β ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) =
      Matrix.of fun i j => β ⊗ₜ[D.host.F] (a * star (s i) * t j) := by
  rw [← AddEquiv.eq_symm_apply, coord_symm_apply]
  ext i j
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum,
    TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : incA D (S.gram k j) = (1 : AF D.host.F) ⊗ₜ[D.host.F] S.gram k j := rfl
  rw [this, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  congr 1
  ring

theorem coord_mem_latVWS (S T : HSp D) (hr : S.rank ≤ T.rank) (Z : Finset (HeightOneSpectrum (𝓞 D.host.F))) (u : WO S T)
    (hu : u ∈ latO S T (L0c D S) (L0c D T) (fun v => v ∉ Z)) : coord S T u ∈ latVWS S T Z := by
  have : latO S T (L0c D S) (L0c D T) (fun v => v ∉ Z) ≤ (latVWS S T Z).comap (coord S T).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro w ⟨α, hα, h0, a, ha, s, hs, t, ht, rfl⟩
    refine AddSubgroup.subset_closure ⟨α, hα, fun v hv => h0 v (not_not.2 hv), a, ha, s, hs, t, ht, ?_⟩
    simp only [if_pos hr]
    exact coord_gen S T _ a s t
  exact this hu

theorem exists_coord : ∀ (D : D7) (S T : HSp D), S.rank ≤ T.rank → ∃ e : WO S T ≃+ WA S T, Continuous e ∧ Continuous e.symm ∧ (∀ x, e x = toTWsmall S T x) ∧ (∀ x, e x ∈ ratL S T ↔ x ∈ ratL T S) ∧ (∀ (a : AE D) (x : WO S T), e (a • x) = a • e x) ∧ (∀ (ψ : AddChar (AF D.host.F) ℂ) (w : WO S T) (f : WA S T → ℂ), heisO ψ S T w (fun x => f (e x)) = fun x => Heisenberg₂ ψ S T (e w) f (e x)) ∧ (∀ (ψ : AddChar (AF D.host.F) ℂ) (f : WA S T → ℂ), IsThetaFunO ψ S T (fun x => f (e x)) ↔ IsThetaFun ψ S T f) ∧ ∀ (Z : Finset (HeightOneSpectrum (𝓞 D.host.F))) (u : WO S T), u ∈ latO S T (L0c D S) (L0c D T) (fun v => v ∉ Z) → e u ∈ latVWS S T Z := by
  intro D S T hr
  refine ⟨coord S T, continuous_coord S T, continuous_coord_symm S T, fun _ => rfl, fun x => ⟨?_, ?_⟩, fun a x => ?_,
    heisO_coord S T hr, isThetaFunO_coord S T hr, coord_mem_latVWS S T hr⟩
  · rintro ⟨γ, hγ⟩
    have hγ' : ratW S T γ = coord S T x := hγ
    refine ⟨γᵀ * S.gram, ?_⟩
    change ratW T S _ = x
    rw [← coord_symm_ratW, hγ', AddEquiv.symm_apply_apply]
  · rintro ⟨γ, rfl⟩
    exact ⟨(γ * S.gram⁻¹)ᵀ, (coord_ratW S T γ).symm⟩
  · rw [coord_apply, coord_apply, Matrix.smul_mul, Matrix.transpose_smul]

end GlobalTheory.OrientedCoord

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOscillatorGaussianKernelRightStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_oscillatorGaussianKernel_right : ∀ (P Q : ℕ) (T : Type) [TopologicalSpace T] (Y : Matrix (Ix P Q) (Fin Q) ℂ) (v φ : Ix P Q → ℂ) (Y' : T → Matrix (Ix P Q) (Fin Q) ℂ) (v' φ' : T → Ix P Q → ℂ), Continuous Y' → Continuous v' → Continuous φ' → (∀ t, IsUnit (Yᴴ * Jm P Q * Y' t).det) → Continuous fun t => ker Y v φ (Y' t) (v' t) (φ' t) := by
  first | exact @GlobalTheory.OscGauss.continuous_ker_right | exact GlobalTheory.OscGauss.continuous_ker_right | (intros; apply GlobalTheory.OscGauss.continuous_ker_right <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteHermitianEqPmGramUnitaryCompact
section
open Matrix

namespace GlobalTheory.DefiniteFrame

theorem exists_frame {n p q : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature J p q) :
    ∃ (e : Fin n ≃ Fin p ⊕ Fin q) (B : Matrix (Fin n) (Fin n) ℂ), IsUnit B.det ∧
      J = Bᴴ * (Formalism.UG.Jpq p q).submatrix e e * B := by
  obtain ⟨e, P, hP⟩ := h
  have hP' : P.valᴴ * (reindex e e J) * P.val = Formalism.UG.Jpq p q := hP
  refine ⟨e, (P⁻¹).val.submatrix e e, ?_, ?_⟩
  · rw [det_submatrix_equiv_self]
    exact (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)
  · have h1 := Units.mul_inv P
    have h2 : (P⁻¹).valᴴ * P.valᴴ = 1 := by
      rw [← conjTranspose_mul, h1, conjTranspose_one]
    rw [conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, ← hP']
    have h3 : (P⁻¹).valᴴ *
        (P.valᴴ * (reindex e e J) * P.val) *
        (P⁻¹).val = reindex e e J := by
      calc _ = ((P⁻¹).valᴴ * P.valᴴ) * (reindex e e J) *
          (P.val * (P⁻¹).val) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
    rw [h3]
    ext i j
    simp

theorem isCompact_UH_gram {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (hB : IsUnit B.det) :
    IsCompact (Formalism.QuantumDeterminants.UH (Bᴴ * B)) := by
  have hc : Continuous fun u : Matrix (Fin n) (Fin n) ℂ => B⁻¹ * u * B :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have h1 : B * B⁻¹ = 1 := mul_nonsing_inv B hB
  have h1' : B⁻¹ * B = 1 := nonsing_inv_mul B hB
  have h2 : (B⁻¹)ᴴ * Bᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  have h2' : Bᴴ * (B⁻¹)ᴴ = 1 := by rw [← conjTranspose_mul, h1', conjTranspose_one]
  convert (GlobalTheory.isCompact_unitaryGroup (Fin n) ℂ).image hc using 1
  ext g
  simp only [Formalism.QuantumDeterminants.UH, Set.mem_ofPred_eq, Set.mem_image, SetLike.mem_coe,
    Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose]
  constructor
  · intro hg
    refine ⟨B * g * B⁻¹, ?_, ?_⟩
    · calc (B * g * B⁻¹)ᴴ * (B * g * B⁻¹) = (B⁻¹)ᴴ * (gᴴ * (Bᴴ * B) * g) * B⁻¹ := by
            simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = ((B⁻¹)ᴴ * Bᴴ) * (B * B⁻¹) := by rw [hg]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h1, h2, Matrix.one_mul]
    · calc B⁻¹ * (B * g * B⁻¹) * B = (B⁻¹ * B) * g * (B⁻¹ * B) := by
            simp only [Matrix.mul_assoc]
        _ = g := by rw [h1', Matrix.one_mul, Matrix.mul_one]
  · rintro ⟨u, hu, rfl⟩
    calc (B⁻¹ * u * B)ᴴ * (Bᴴ * B) * (B⁻¹ * u * B)
        = Bᴴ * (uᴴ * ((B⁻¹)ᴴ * Bᴴ) * (B * B⁻¹) * u) * B := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Bᴴ * B := by rw [h1, h2, Matrix.mul_one, Matrix.mul_one, hu, Matrix.mul_one]

theorem UH_neg {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) : Formalism.QuantumDeterminants.UH (-H) = Formalism.QuantumDeterminants.UH H := by
  ext g
  simp [Formalism.QuantumDeterminants.UH]

theorem definite_frame (n p q : ℕ) (J : Matrix (Fin n) (Fin n) ℂ)
    (h : Formalism.UG.HasSignature J p q) (hpq : p = 0 ∨ q = 0) :
    (∃ B : Matrix (Fin n) (Fin n) ℂ, IsUnit B.det ∧ (J = Bᴴ * B ∨ J = -(Bᴴ * B))) ∧
      IsCompact (Formalism.QuantumDeterminants.UH J) := by
  obtain ⟨e, B, hB, hJ⟩ := exists_frame h
  rcases hpq with rfl | rfl
  · have h1 : Formalism.UG.Jpq 0 q = -1 := by
      ext i j
      rcases i with i | i
      · exact i.elim0
      rcases j with j | j
      · exact j.elim0
      simp [Formalism.UG.Jpq, Matrix.one_apply]
    have h2 : J = -(Bᴴ * B) := by
      rw [hJ, h1, submatrix_neg]
      simp
    refine ⟨⟨B, hB, Or.inr h2⟩, ?_⟩
    rw [h2, UH_neg]
    exact isCompact_UH_gram B hB
  · have h1 : Formalism.UG.Jpq p 0 = 1 := by
      ext i j
      rcases i with i | i
      swap
      · exact i.elim0
      rcases j with j | j
      swap
      · exact j.elim0
      simp [Formalism.UG.Jpq, Matrix.one_apply]
    have h2 : J = Bᴴ * B := by
      rw [hJ, h1]
      simp
    refine ⟨⟨B, hB, Or.inl h2⟩, ?_⟩
    rw [h2]
    exact isCompact_UH_gram B hB

end GlobalTheory.DefiniteFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DimKKapAtWcPos
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.WeylDimPos

theorem weylDimU_pos {p : ℕ} (lam : Fin p → ℤ) (h : ∀ i j : Fin p, i ≤ j → lam j ≤ lam i) : 0 < weylDimU lam := by
  unfold weylDimU
  refine Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => ?_
  have hij : i < j := (Finset.mem_filter.1 hj).2
  have h1 : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ) := by exact_mod_cast hij
  have h2 : (0 : ℚ) ≤ ((lam i - lam j : ℤ) : ℚ) := by exact_mod_cast sub_nonneg.2 (h i j hij.le)
  exact div_pos (by linarith) (by linarith)

theorem dimK_kapW_pos {R : Ranks} (h : HCParam R) (p q : ℕ) (hpq : p + q = R.r) :
    0 < dimK p q (Formalism.L2.NTheta.kapW h p q) := by
  obtain ⟨h1, h2, -⟩ := Formalism.L2.NTheta.holOK_kapW h p q hpq
  exact mul_pos (weylDimU_pos _ fun i j hij => h1 i j hij) (weylDimU_pos _ fun i j hij => h2 i j hij)

theorem dimK_kapAt_pos {D : D7} (W : HSp D) (hW : W.SigOK) (hr : W.rank = D.R.r) (σ : D.what₂.LL →+* ℂ)
    (ρ : D.what₂.Tau) : 0 < dimK _ _ (kapAt W σ ρ) :=
  dimK_kapW_pos _ _ _ (by rw [← hr]; obtain ⟨e, -⟩ := hW (tauE D ρ); simpa using (Fintype.card_congr e).symm)

theorem dimK_kapAt_Wc_pos (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) :
    0 < dimK _ _ (kapAt (Wc D i) σ ρ) :=
  dimK_kapAt_pos _ (D.sp.W_sig _) (D.sp.W_rank _ (by omega) (by have := i.2; omega)) σ ρ

end GlobalTheory.Mem.WeylDimPos
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfAffineHyperplaneLineSumsStatement
section
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_affineHyperplane_line_sums : ∀ (k W M : Type) [Field k] [Fintype k] [DecidableEq k] [AddCommGroup W] [Module k W] [Finite W] [AddCommGroup M] [Module ℂ M] (ψ : W → M), ψ 0 = 0 → (∀ g : Module.Dual k W, g ≠ 0 → ∑ᶠ x ∈ {x | g x = 1}, ψ x = 0) → (∀ x, ∑ a : kˣ, ψ ((a : k) • x) = 0) → ∀ x, ψ x = 0 := by
  first | exact @GlobalTheory.FiniteRadon.eq_zero_of_hyperplane_sums | exact GlobalTheory.FiniteRadon.eq_zero_of_hyperplane_sums | (intros; apply GlobalTheory.FiniteRadon.eq_zero_of_hyperplane_sums <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeStabiliserSubgroupOutsidePlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Ksph

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_subgroup_ksph : ∀ (D : D7) (V : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))),
    ∃ K : Subgroup (GA D V), (K : Set (GA D V)) = KsphC V S ∧ ∀ S', S ⊆ S' → KsphC V S' ⊆ KsphC V S :=
  fun _ V S => ⟨_, (GlobalTheory.AutFunCompare.KsphC_eq V S).symm,
    fun _ hS _ hg => ⟨hg.1, hg.2.1, fun v hv => hg.2.2 v (hS hv)⟩⟩

end GlobalTheory.Mem.Ksph
end

