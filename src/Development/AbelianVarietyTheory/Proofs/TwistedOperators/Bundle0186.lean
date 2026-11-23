module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsVolumeTransportOfLatticeIsometry
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0885

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceInverseGramConjSmulEq
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan

variable {D : D7}

theorem frameMatrix_mul_frameMatrixInv (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : frP S b * frPinv S b = 1 :=
  Module.Basis.toMatrix_mul_toMatrix_flip _ _

theorem frPinv_mul_frP (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : frPinv S b * frP S b = 1 :=
  Module.Basis.toMatrix_mul_toMatrix_flip _ _

theorem isoPair_re (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) :
    GlobalTheory.VolTransport.IsoPair (D.sp.cm.sig : D.host.E →+* D.host.E) (reS S b).gram S.gram (frP S b) (frPinv S b) := by
  refine ⟨frameMatrix_mul_frameMatrixInv S b, frPinv_mul_frP S b, ?_, ?_⟩
  · have := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.embMat_isom D.sp.cm (reS S b) S LinearMap.id (fun x y => rfl)
    have e : (LinearMap.toMatrix (reS S b).frame S.frame) LinearMap.id = frP S b :=
      LinearMap.toMatrix_id_eq_basis_toMatrix b S.frame
    rw [← e]; exact this
  · have := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.embMat_isom D.sp.cm S (reS S b) LinearMap.id (fun x y => rfl)
    have e : (LinearMap.toMatrix S.frame (reS S b).frame) LinearMap.id = frPinv S b :=
      LinearMap.toMatrix_id_eq_basis_toMatrix S.frame b
    rw [← e]; exact this

def reGrp (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : GA D (reS S b) ≃* GA D S :=
  GlobalTheory.VolTransport.conjA (isoPair_re S b)

theorem mt_reGrp (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (h : GA D (reS S b)) :
    mt S (reGrp S b h) = HMul.hMul (α := Matrix (Fin S.rank) (Fin S.rank) (AE D))
      (β := Matrix (Fin S.rank) (Fin S.rank) (AE D)) (γ := Matrix (Fin S.rank) (Fin S.rank) (AE D))
      (HMul.hMul (α := Matrix (Fin S.rank) (Fin S.rank) (AE D)) (β := Matrix (Fin S.rank) (Fin S.rank) (AE D))
        (γ := Matrix (Fin S.rank) (Fin S.rank) (AE D)) ((frP S b).map (incA D)) (mt (reS S b) h))
      ((frPinv S b).map (incA D)) :=
  GlobalTheory.VolTransport.conjA_mat (isoPair_re S b) h

theorem finHom_eq (V : HSp D) (g : GA D V) :
    ((finHom V g : GL _ _) : Matrix (Fin V.rank) (Fin V.rank) _) = finMat D.sp.cm.sig V.gram g := rfl

theorem reW_continuous (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : Continuous (reW S T b) := by
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  unfold reW
  exact continuous_id.matrix_mul continuous_const

set_option synthInstance.maxHeartbeats 200000 in
theorem mul_mul_cancel {m n : ℕ} (x : Matrix (Fin m) (Fin n) (AE D)) (A B : Matrix (Fin n) (Fin n) (AE D))
    (h : A * B = 1) : x * A * B = x := by
  rw [Matrix.mul_assoc, h, Matrix.mul_one]

variable (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)

def reWinv (x : WO S T) : WO (reS S b) T :=
  HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) x ((frP S b).map (incA D))

theorem frPinv_frP_A : HMul.hMul (α := Matrix (Fin S.rank) (Fin S.rank) (AE D)) ((frPinv S b).map (incA D))
    ((frP S b).map (incA D)) = 1 := by
  rw [← Matrix.map_mul, frPinv_mul_frP, Matrix.map_one _ (map_zero _) (map_one _)]

theorem map_frameMatrix_mul_map_frameMatrixInv : HMul.hMul (α := Matrix (Fin S.rank) (Fin S.rank) (AE D)) ((frP S b).map (incA D))
    ((frPinv S b).map (incA D)) = 1 := by
  rw [← Matrix.map_mul, frameMatrix_mul_frameMatrixInv, Matrix.map_one _ (map_zero _) (map_one _)]

theorem reW_reWinv (x : WO S T) : reW S T b (reWinv S T b x) = x :=
  mul_mul_cancel x _ _ (map_frameMatrix_mul_map_frameMatrixInv S b)

theorem reWinv_reW (x : WO (reS S b) T) : reWinv S T b (reW S T b x) = x :=
  mul_mul_cancel x _ _ (frPinv_frP_A S b)

theorem reW_add (x y : WO (reS S b) T) : reW S T b (x + y) = reW S T b x + reW S T b y :=
  Matrix.add_mul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) y _

theorem reW_zero : reW S T b 0 = 0 :=
  Matrix.zero_mul (α := AE D) (l := Fin T.rank) ((frPinv S b).map (incA D))

theorem reWinv_add (x y : WO S T) : reWinv S T b (x + y) = reWinv S T b x + reWinv S T b y :=
  Matrix.add_mul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) y _

theorem reWinv_continuous : Continuous (reWinv S T b) := by
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  unfold reWinv
  exact continuous_id.matrix_mul continuous_const

def reWAdd : WO (reS S b) T →+ WO S T where
  toFun := reW S T b
  map_zero' := reW_zero S T b
  map_add' := reW_add S T b

def reWHomeo : WO (reS S b) T ≃ₜ WO S T where
  toFun := reW S T b
  invFun := reWinv S T b
  left_inv := reWinv_reW S T b
  right_inv := reW_reWinv S T b
  continuous_toFun := reW_continuous S T b
  continuous_invFun := reWinv_continuous S T b

def reFEquiv : (WO S T → ℂ) ≃ₗ[ℂ] (WO (reS S b) T → ℂ) :=
  { reF S T b with
    invFun := fun f x => f (reWinv S T b x)
    left_inv := fun f => funext fun x => by
      show f (reW S T b (reWinv S T b x)) = f x
      rw [reW_reWinv]
    right_inv := fun f => funext fun x => by
      show f (reWinv S T b (reW S T b x)) = f x
      rw [reWinv_reW] }

theorem hO_eq_trace (V : HSp D) (x y : WO V T) :
    hO V T x y = Matrix.trace (((V.gram⁻¹).map (incA D) * (y.map (cA D))ᵀ * T.gram.map (incA D)) * x) := by
  simp only [hO, Matrix.trace, Matrix.mul_apply, Matrix.diag, Matrix.map_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine (Finset.sum_congr rfl fun b _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  exact Finset.sum_congr rfl fun d _ => Finset.sum_comm

theorem inv_gram_re : ((reS S b).gram⁻¹ : Matrix (Fin S.rank) (Fin S.rank) D.host.E) =
    frPinv S b * S.gram⁻¹ * Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frPinv S b) := by
  have h := (isoPair_re S b).2.2.1
  have e1 : (frP S b)⁻¹ = frPinv S b := Matrix.inv_eq_left_inv (frPinv_mul_frP S b)
  have e2 : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frP S b))⁻¹ =
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frPinv S b) := by
    refine Matrix.inv_eq_left_inv ?_
    rw [← Formalism.UG.cT_mul, frameMatrix_mul_frameMatrixInv, Formalism.UG.cT_one]
  have h' : ((reS S b).gram : Matrix (Fin S.rank) (Fin S.rank) D.host.E) =
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frP S b) * S.gram * frP S b := h.symm
  rw [h', Matrix.mul_inv_rev, Matrix.mul_inv_rev, e1, e2, Matrix.mul_assoc]

theorem trace_inverseGram_conj_smul_eq {R : Type*} [CommRing R] (c : R →+* R) {m n : ℕ} (Gi Gi' P : Matrix (Fin n) (Fin n) R)
    (GT : Matrix (Fin m) (Fin m) R)
    (x y : Matrix (Fin m) (Fin n) R) (h : P * Gi * (P.map c)ᵀ = Gi') :
    Matrix.trace (Gi * ((y * P).map c)ᵀ * GT * (x * P)) = Matrix.trace (Gi' * (y.map c)ᵀ * GT * x) := by
  rw [Matrix.map_mul, Matrix.transpose_mul, ← h]
  rw [show Gi * ((P.map c)ᵀ * (y.map c)ᵀ) * GT * (x * P) =
    (Gi * (P.map c)ᵀ * ((y.map c)ᵀ * GT * x)) * P by simp only [Matrix.mul_assoc]]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem gram_key : HMul.hMul (α := Matrix (Fin S.rank) (Fin S.rank) (AE D))
    (HMul.hMul (α := Matrix (Fin S.rank) (Fin S.rank) (AE D)) ((frPinv S b).map (incA D)) ((S.gram⁻¹).map (incA D)))
      ((((frPinv S b).map (incA D)).map (cA D))ᵀ) =
    (((reS S b).gram⁻¹ : Matrix (Fin S.rank) (Fin S.rank) D.host.E)).map (incA D) := by
  rw [inv_gram_re]
  have e : (((frPinv S b).map (incA D)).map (cA D))ᵀ =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frPinv S b)).map (incA D) := by
    ext i j; rfl
  rw [e, Matrix.map_mul, Matrix.map_mul]

theorem hO_reW (x y : WO (reS S b) T) : hO S T (reW S T b x) (reW S T b y) = hO (reS S b) T x y := by
  rw [hO_eq_trace, hO_eq_trace]
  exact trace_inverseGram_conj_smul_eq (cA D) _ _ _ _ x y (gram_key S b)

theorem symplOH_reW (x y : WO (reS S b) T) :
    symplOH S T (reW S T b x) (reW S T b y) = symplOH (reS S b) T x y := by
  simp only [symplOH, symplO, hO_reW]

theorem heisO_reF (ψ : AddChar (AF D.host.F) ℂ) (w : WO (reS S b) T) (f : WO S T → ℂ) :
    heisO ψ (reS S b) T w (reF S T b f) = reF S T b (heisO ψ S T (reW S T b w) f) := by
  funext x
  simp only [heisO, reF_apply, reW_add, symplOH_reW]

theorem reW_ratW (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    reW S T b (ratW T (reS S b) γ) = ratW T S (γ * frPinv S b) :=
  (Matrix.map_mul (f := incA D) (L := γ) (M := frPinv S b)).symm

theorem reWinv_ratW (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    reWinv S T b (ratW T S γ) = ratW T (reS S b) (γ * frP S b) :=
  (Matrix.map_mul (f := incA D) (L := γ) (M := frP S b)).symm

theorem mem_ratL_reW (x : WO (reS S b) T) : reW S T b x ∈ ratL T S ↔ x ∈ ratL T (reS S b) := by
  constructor
  · rintro ⟨γ, hγ⟩
    refine ⟨γ * frP S b, ?_⟩
    have h1 : reWinv S T b (ratW T S γ) = x := by
      rw [← reWinv_reW S T b x]; exact congrArg (reWinv S T b) hγ
    rw [reWinv_ratW] at h1
    exact h1
  · rintro ⟨γ, hγ⟩
    refine ⟨HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) D.host.E) γ (frPinv S b), ?_⟩
    have h1 : reW S T b (ratW T (reS S b) γ) = reW S T b x := congrArg (reW S T b) hγ
    exact (reW_ratW S T b γ).symm.trans h1

theorem block_frame_conjugation_identity {R : Type*} [Ring R] {m n : ℕ} (A : Matrix (Fin m) (Fin m) R) (x : Matrix (Fin m) (Fin n) R)
    (M P Pi : Matrix (Fin n) (Fin n) R) (h : Pi * P = 1) : A * x * M * Pi = A * (x * Pi) * (P * M * Pi) := by
  rw [show A * (x * Pi) * (P * M * Pi) = A * x * (Pi * P) * M * Pi by simp only [Matrix.mul_assoc], h,
    Matrix.mul_one]

theorem reW_actO (h : GA D (reS S b)) (g : GA D T) (x : WO (reS S b) T) :
    reW S T b (actO (reS S b) T h g x) = actO S T (reGrp S b h) g (reW S T b x) := by
  unfold actO reW
  rw [← map_inv, mt_reGrp]
  exact block_frame_conjugation_identity _ _ _ _ _ (frPinv_frP_A S b)

theorem map_mul_one {R : Type*} [Semiring R] (f : D.host.E →+* R) {n : ℕ} (A B : Matrix (Fin n) (Fin n) D.host.E)
    (h : A * B = 1) : A.map f * B.map f = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]

theorem conj_eq_one_iff {R : Type*} [Ring R] {n : ℕ} (X P Pi : Matrix (Fin n) (Fin n) R) (h1 : P * Pi = 1)
    (h2 : Pi * P = 1) : P * X * Pi = 1 ↔ X = 1 := by
  constructor
  · intro h
    calc X = Pi * (P * X * Pi) * P := by simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]; rw [Matrix.mul_assoc, h2, Matrix.mul_one]
      _ = 1 := by rw [h, Matrix.mul_one, h2]
  · rintro rfl
    rw [Matrix.mul_one, h1]

theorem reGrp_mem_GinfC (h : GA D (reS S b)) : reGrp S b h ∈ GinfC S ↔ h ∈ GinfC (reS S b) := by
  have e := GlobalTheory.VolTransport.conjA_finMat (isoPair_re S b) h
  simp only [GinfC, MonoidHom.mem_ker, Units.ext_iff, finHom_eq, Units.val_one]
  refine Iff.trans (Eq.to_iff (congrArg (· = (1 : Matrix (Fin S.rank) (Fin S.rank) _)) e)) ?_
  exact conj_eq_one_iff _ _ _ (map_mul_one _ _ _ (frameMatrix_mul_frameMatrixInv S b)) (map_mul_one _ _ _ (frPinv_mul_frP S b))

theorem reGrp_mem_GQ (h : GA D (reS S b)) (hh : h ∈ GQ (reS S b)) : reGrp S b h ∈ GQ S :=
  GlobalTheory.VolTransport.conjA_rat (isoPair_re S b) h hh

set_option synthInstance.maxHeartbeats 200000 in
theorem map_mul_eq_zero_iff {R : Type*} [Ring R] {m n : ℕ} (φ : AE D →+* R) (x : Matrix (Fin m) (Fin n) (AE D))
    (P Pi : Matrix (Fin n) (Fin n) D.host.E) (h : Pi * P = 1) :
    (x * Pi.map (incA D)).map φ = 0 ↔ x.map φ = 0 := by
  rw [Matrix.map_mul]
  constructor
  · intro hx
    have hP : (Pi.map (incA D)).map φ * (P.map (incA D)).map φ = 1 := by
      rw [Matrix.map_map, Matrix.map_map]
      exact map_mul_one (φ.comp (incA D)) Pi P h
    have e : x.map φ * (Pi.map (incA D)).map φ * (P.map (incA D)).map φ = x.map φ := by
      rw [Matrix.mul_assoc, hP, Matrix.mul_one]
    rw [← e, hx, Matrix.zero_mul]
  · intro hx; rw [hx, Matrix.zero_mul]

theorem reW_map_eq_zero {R : Type*} [Ring R] (φ : AE D →+* R) (x : WO (reS S b) T) :
    (reW S T b x).map φ = 0 ↔ x.map φ = 0 :=
  map_mul_eq_zero_iff φ x (frP S b) (frPinv S b) (frPinv_mul_frP S b)

end GlobalTheory.AdSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeIdempotentConstantTermVanish
section
open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

noncomputable section

namespace GlobalTheory.TypeConstTerm

theorem isClosed_of_isParabRad : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r : ℕ}
    (P N : Subgroup (GL (Fin r) k)), IsParabRad P N → IsClosed (N : Set (GL (Fin r) k)) := by
  intro k _ _ _ _ r P N hPN
  obtain ⟨s, d, hd, g, -, rfl⟩ := hPN
  haveI : T2Space k := by
    letI := IsTopologicalAddGroup.rightUniformSpace k
    haveI := isUniformAddGroup_of_addCommGroup (G := k)
    infer_instance
  have hU : IsClosed (unipRad k (stdBlocks d hd) : Set (GL (Fin r) k)) := by
    have : (unipRad k (stdBlocks d hd) : Set (GL (Fin r) k)) =
        (⋂ i, ⋂ j, ⋂ (_ : blk (stdBlocks d hd) j < blk (stdBlocks d hd) i),
          {x : GL (Fin r) k | (x : Matrix (Fin r) (Fin r) k) i j = 0}) ∩
        ⋂ c, ⋂ i, ⋂ j, {x : GL (Fin r) k | (x : Matrix (Fin r) (Fin r) k) (stdBlocks d hd ⟨c, i⟩)
          (stdBlocks d hd ⟨c, j⟩) = (1 : Matrix (Fin (d c)) (Fin (d c)) k) i j} := by
      ext x
      simp only [SetLike.mem_coe, mem_unipRad, mem_parab, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    rw [this]
    refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq ?_ continuous_const) (isClosed_iInter fun c => isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq ?_ continuous_const)
    · exact Units.continuous_val.matrix_elem _ _
    · exact Units.continuous_val.matrix_elem _ _
  have : (conjBy g (unipRad k (stdBlocks d hd)) : Set (GL (Fin r) k)) =
      (fun x => g⁻¹ * x * g) ⁻¹' (unipRad k (stdBlocks d hd) : Set (GL (Fin r) k)) := by
    ext x; exact mem_conjBy
  rw [this]
  exact hU.preimage (by fun_prop)

theorem integral_swap_of_support : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (N : Subgroup G), IsClosed (N : Set G) →
    ∀ (ν : Measure N) [IsFiniteMeasureOnCompacts ν] (Φ : G → G → ℂ), Continuous (Function.uncurry Φ) →
    ∀ (C D : Set G), IsCompact C → IsCompact D → (∀ z u, Φ z u ≠ 0 → z ∈ C ∧ u ∈ D) →
    ∫ u : N, (∫ z, Φ z u ∂μ) ∂ν = ∫ z, (∫ u : N, Φ z u ∂ν) ∂μ := by
  intro G _ _ _ _ _ _ μ _ N hN ν _ Φ hΦ C D hC hD hsupp
  refine (integral_integral_swap_of_hasCompactSupport (f := fun (z : G) (u : N) => Φ z u) (μ := μ) (ν := ν)
    (hΦ.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) ?_).symm
  refine HasCompactSupport.intro (hC.prod (hN.isClosedEmbedding_subtypeVal.isCompact_preimage hD)) fun p hp => ?_
  by_contra hne
  obtain ⟨h1, h2⟩ := hsupp _ _ hne
  exact hp ⟨h1, h2⟩

theorem integrable_comp_of_SB : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (N : Subgroup G), IsClosed (N : Set G) → ∀ (ν : Measure N) [IsFiniteMeasureOnCompacts ν] (f : G → ℂ),
    f ∈ SB G → ∀ x y : G, Integrable (fun u : N => f (x * u * y)) ν := by
  intro G _ _ _ _ _ _ N hN ν _ f hf x y
  refine Continuous.integrable_of_hasCompactSupport (hf.1.continuous.comp (by fun_prop)) ?_
  refine HasCompactSupport.intro (hN.isClosedEmbedding_subtypeVal.isCompact_preimage
    (hf.2.isCompact.image (f := fun g => x⁻¹ * g * y⁻¹) (by fun_prop))) fun u hu => ?_
  by_contra hne
  exact hu ⟨x * u * y, subset_tsupport _ hne, by group⟩

theorem conj_stdMaxRad_le (F : Type) [Field F] {r a b : ℕ} (h : a + b = r) (P N : Subgroup (GL (Fin r) F))
    (hPN : IsParabRad P N) (g₀ : GL (Fin r) F) (hP : P ≤ conjBy g₀ (stdMaxParab F h)) :
    conjBy g₀ (stdMaxRad F h) ≤ N := by
  obtain ⟨s, d, hd, g, rfl, rfl⟩ := hPN
  have h1 : parab F (stdBlocks d hd) ≤ conjBy (g⁻¹ * g₀) (stdMaxParab F h) := by
    intro x hx
    have hx' : g * x * g⁻¹ ∈ conjBy g (parab F (stdBlocks d hd)) := mem_conjBy.2 (by simpa [mul_assoc] using hx)
    have := mem_conjBy.1 (hP hx')
    rw [mem_conjBy]
    simpa [mul_assoc] using this
  have hc := GlobalTheory.T.mem_stdMaxParabolic_of_blockParabolic_le_conj F h d hd _ h1
  have h2 : parab F (stdBlocks d hd) ≤ stdMaxParab F h := by
    intro x hx
    have := mem_conjBy.1 (h1 hx)
    have e : x = (g⁻¹ * g₀) * ((g⁻¹ * g₀)⁻¹ * x * (g⁻¹ * g₀)) * (g⁻¹ * g₀)⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hc this) (inv_mem hc)
  have h3 := _root_.GlobalTheory.RadRev.stdMaxRad_le_unipRad F h d hd h2
  intro y hy
  rw [mem_conjBy] at hy ⊢
  have hn : (g⁻¹ * g₀) * (g₀⁻¹ * y * g₀) * (g⁻¹ * g₀)⁻¹ ∈ stdMaxRad F h :=
    (Subgroup.mem_normalizer_iff.1 (parab_le_normalizer F _ hc) _).1 hy
  have e : g⁻¹ * y * g = (g⁻¹ * g₀) * (g₀⁻¹ * y * g₀) * (g⁻¹ * g₀)⁻¹ := by group
  rw [e]
  exact h3 hn

theorem typeConstTermVanish : TypeConstTermVanish := by
  intro k _ _ _ _ r a b h _ _ W _ _ _ τ _ hfix _ _ μ _ φ hφ f hf P N hPN hP ν _ x y
  obtain ⟨g₀, hP⟩ := hP
  haveI : T2Space k := by
    letI := IsTopologicalAddGroup.rightUniformSpace k
    haveI := isUniformAddGroup_of_addCommGroup (G := k)
    infer_instance
  have hNa := conj_stdMaxRad_le k h P N hPN g₀ hP
  have hNc := isClosed_of_isParabRad k P N hPN
  set e := idemGL k μ τ with he_def
  have key : ∀ x' w : GL (Fin r) k, ∫ u : N, e (x' * u * w) ∂ν = 0 := by
    intro x' w
    obtain ⟨c, hc⟩ := _root_.GlobalTheory.RadRedLift.red_lift k h (x' * g₀)
    refine GlobalTheory.T.integral_compactOpenTypeIdempotent_unipotent_eq_zero k τ μ N ν (conjBy c (stdMaxRad 𝓀[k] h)) ?_ x' ?_ w
    · intro v hv
      have h0 : τ c⁻¹ v = 0 := hfix _ fun u hu => by
        have := hv (c * u * c⁻¹) (mem_conjBy.2 (by simpa [mul_assoc] using hu))
        calc τ u (τ c⁻¹ v) = τ (u * c⁻¹) v := by rw [map_mul]; rfl
          _ = τ (c⁻¹ * (c * u * c⁻¹)) v := by rw [show u * c⁻¹ = c⁻¹ * (c * u * c⁻¹) by group]
          _ = τ c⁻¹ (τ (c * u * c⁻¹) v) := by rw [map_mul]; rfl
          _ = τ c⁻¹ v := by rw [this]
      have : v = τ c (τ c⁻¹ v) := by rw [← Module.End.mul_apply, ← map_mul]; simp
      rw [this, h0, map_zero]
    · intro v hv
      obtain ⟨u, hu, hu2, hred⟩ := hc _ (mem_conjBy.1 hv)
      refine ⟨x'⁻¹ * u * x', hNa (mem_conjBy.2 ?_), ?_, ?_⟩
      · have := mem_conjBy.1 hu2
        simpa [mul_assoc] using this
      · simpa [mul_assoc] using hu
      · have e1 : x' * (x'⁻¹ * u * x') * x'⁻¹ = u := by group
        have : (⟨x' * (x'⁻¹ * u * x') * x'⁻¹, by rw [e1]; exact hu⟩ : KO k (Fin r)) = ⟨u, hu⟩ := Subtype.ext e1
        rw [this, hred]
        group
  have heSB : e ∈ SB (GL (Fin r) k) :=
    GlobalTheory.Orb.typeIdem_mem_SB μ _ τ GlobalTheory.SplitFlip.isOpen_KO GlobalTheory.SplitFlip.isCompact_KO
      (by
        have : ((GlobalTheory.LocGL.redK k (Fin r)).ker : Set (KO k (Fin r))) = Subtype.val ⁻¹' (KOne k (Fin r) : Set _) := by
          ext g; exact GlobalTheory.LocGL.redK_eq_one_iff g
        rw [this]; exact GlobalTheory.StepData.isOpen_KOne.preimage continuous_subtype_val)
  have hfSB : f ∈ SB (GL (Fin r) k) := by
    rcases hf with rfl | rfl
    · exact GlobalTheory.Orb.conv_mem_SB heSB hφ
    · exact GlobalTheory.Orb.conv_mem_SB hφ heSB
  refine ⟨integrable_comp_of_SB _ N hNc ν f hfSB x y, ?_⟩
  have hec : Continuous e := heSB.1.continuous
  have hφc : Continuous φ := hφ.1.continuous
  rcases hf with rfl | rfl
  · have h1 : ∀ u : N, GlobalTheory.AutomorphicL2Unitary.conv μ e φ (x * u * y) = ∫ z, e (x * u * (y * z)) * φ z⁻¹ ∂μ := by
      intro u
      rw [GlobalTheory.AutomorphicL2Unitary.conv, ← integral_mul_left_eq_self _ (x * u * y)]
      simp [mul_assoc]
    simp_rw [h1]
    rw [integral_swap_of_support _ μ N hNc ν (fun z u => e (x * u * (y * z)) * φ z⁻¹) (by fun_prop) ((fun z : GL (Fin r) k => z⁻¹) '' tsupport φ)
      ((fun p : GL (Fin r) k × GL (Fin r) k => x⁻¹ * p.1 * p.2 * y⁻¹) '' ((KO k (Fin r) : Set _) ×ˢ tsupport φ))
      (hφ.2.isCompact.image (by fun_prop)) ((GlobalTheory.SplitFlip.isCompact_KO.prod hφ.2.isCompact).image (by fun_prop)) ?_]
    · simp_rw [integral_mul_const]
      simp [key]
    · intro z u hz
      have h1 := left_ne_zero_of_mul hz
      have h2 := subset_tsupport _ (right_ne_zero_of_mul hz)
      refine ⟨⟨z⁻¹, h2, by simp⟩, ⟨(x * u * (y * z), z⁻¹), ⟨?_, h2⟩, by group⟩⟩
      by_contra hK
      exact h1 (GlobalTheory.Orb.typeIdem_of_notMem μ _ τ hK)
  · have h1 : ∀ u : N, GlobalTheory.AutomorphicL2Unitary.conv μ φ e (x * u * y) = ∫ z, φ z * e (z⁻¹ * x * u * y) ∂μ := by
      intro u
      simp [GlobalTheory.AutomorphicL2Unitary.conv, mul_assoc]
    simp_rw [h1]
    rw [integral_swap_of_support _ μ N hNc ν (fun z u => φ z * e (z⁻¹ * x * u * y)) (by fun_prop) (tsupport φ)
      ((fun p : GL (Fin r) k × GL (Fin r) k => x⁻¹ * p.1 * p.2 * y⁻¹) '' (tsupport φ ×ˢ (KO k (Fin r) : Set _)))
      hφ.2.isCompact ((hφ.2.isCompact.prod GlobalTheory.SplitFlip.isCompact_KO).image (by fun_prop)) ?_]
    · simp_rw [integral_const_mul]
      simp [key]
    · intro z u hz
      have h1 := subset_tsupport _ (left_ne_zero_of_mul hz)
      have h2 := right_ne_zero_of_mul hz
      refine ⟨h1, ⟨(z, z⁻¹ * x * u * y), ⟨h1, ?_⟩, by group⟩⟩
      by_contra hK
      exact h2 (GlobalTheory.Orb.typeIdem_of_notMem μ _ τ hK)

end GlobalTheory.TypeConstTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedQuadraticCharSignSplitEqOneInertEqNeg
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QuadSignLocal

theorem primesOver_eq_image (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    Ideal.primesOver v.asIdeal (𝓞 D.host.E) =
      HeightOneSpectrum.asIdeal '' {u : HeightOneSpectrum (𝓞 D.host.E) | u.under (𝓞 D.host.F) = v} := by
  ext P
  constructor
  · rintro ⟨hP, hlo⟩
    refine ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, ?_, rfl⟩
    ext1
    simp only [HeightOneSpectrum.under_asIdeal]
    exact (Ideal.LiesOver.over (P := P) (p := v.asIdeal)).symm
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u.isPrime, ⟨?_⟩⟩
    have := congrArg HeightOneSpectrum.asIdeal hu
    simp only [HeightOneSpectrum.under_asIdeal] at this
    exact this.symm

theorem ncard_primesOver (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    (Ideal.primesOver v.asIdeal (𝓞 D.host.E)).ncard =
      {u : HeightOneSpectrum (𝓞 D.host.E) | u.under (𝓞 D.host.F) = v}.ncard := by
  rw [primesOver_eq_image]
  exact Set.ncard_image_of_injective _ (fun a b h => HeightOneSpectrum.ext h)

theorem quadSign_split_inert : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)), (∀ w w' : HeightOneSpectrum (𝓞 D.host.E), w ≠ w' → (∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) = v ↔ u = w ∨ u = w') → quadSign D v = 1) ∧ (∀ w : HeightOneSpectrum (𝓞 D.host.E), (∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) = v ↔ u = w) → quadSign D v = -1) := by
  intro D v
  constructor
  · intro w w' hne h
    have hs : {u : HeightOneSpectrum (𝓞 D.host.E) | u.under (𝓞 D.host.F) = v} = {w, w'} := by
      ext u; simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]; exact h u
    have h2 : (Ideal.primesOver v.asIdeal (𝓞 D.host.E)).ncard = 2 := by
      rw [ncard_primesOver, hs, Set.ncard_pair hne]
    unfold quadSign
    rw [if_pos h2]
  · intro w h
    have hs : {u : HeightOneSpectrum (𝓞 D.host.E) | u.under (𝓞 D.host.F) = v} = {w} := by
      ext u; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]; exact h u
    have h1 : (Ideal.primesOver v.asIdeal (𝓞 D.host.E)).ncard = 1 := by
      rw [ncard_primesOver, hs, Set.ncard_singleton]
    unfold quadSign
    rw [if_neg (by rw [h1]; decide)]

end GlobalTheory.QuadSignLocal
end

