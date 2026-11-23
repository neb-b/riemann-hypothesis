module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0007
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0009
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0005
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterConductorCondition
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LBumpEx
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

namespace PositivityTheory.Rg.Rsw.L.LBumpEx

variable {D : D7}

theorem theta_e (θ : InfFam D) (hθ : IsInfFam θ) {e : AE D} (he : ∀ w, compInf D.host.F D.host.E w e = 1)
    (τ : D.what₂.Tau) : θ τ (infPart D e) = 1 := by
  have h := ((GlobalTheory.StdUnn.RealComp.real_components D θ hθ).1 (e - 1)).1
    (fun w => by rw [map_sub, map_one, he w, sub_self])
  have h' := h τ
  rw [map_sub, map_sub, map_one, map_one, sub_eq_zero] at h'
  exact h'

end PositivityTheory.Rg.Rsw.L.LBumpEx

open PositivityTheory.Rg.Rsw.L.LBumpEx Classical in
theorem PositivityTheory.Rg.Rsw.L.bumpEx : IdemEx → BumpEx := by
  intro hI D θ hθ a b S e he C hC hCi
  obtain ⟨hee, -⟩ := (hI D S).2 e he
  have : IsModuleTopology (Af D.host.F) (AfE D) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AfE D) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
  have : T2Space (AF D.host.F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  obtain ⟨hom⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (AF D.host.F)
  have : T2Space (AE D) := hom.isEmbedding.t2Space
  set ef : AfE D := finPart D e with hef_def
  have hef : ef * ef = ef := by rw [hef_def, ← map_mul, hee]
  have hefI : ef ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D ef hef
  have hS : ∀ v : Pl D, PositivityTheory.Rg.Rsw.L.LBumpEx.cf v ef = if v ∈ S then 1 else 0 := fun v => by
    rw [← cv_eq]; exact he.2 v
  have hθe := theta_e θ hθ he.1
  obtain ⟨N, hN, hNC⟩ := exists_nat_mul_mem (D := D)
    (Q := ⋃ i, ⋃ j, (fun x : Mx D a b => ef * finPart D (x i j)) '' C)
    (isCompact_iUnion fun i => isCompact_iUnion fun j => hC.image
      (continuous_const.mul ((GlobalTheory.Member.continuous_finPart D).comp (continuous_id.matrix_elem i j))))
  let W := U S ef N 1 b
  have hWo : IsOpen (W : Set (Matrix (Fin 1) (Fin b) (AfE D))) := U_isOpen hefI N 1 b
  have hWc : IsCompact (W : Set (Matrix (Fin 1) (Fin b) (AfE D))) := U_isCompact hefI hS hN 1 b
  let g : Matrix (Fin 1) (Fin b) (AfE D) → ℂ := fun w =>
    if (QuotientAddGroup.mk w : _ ⧸ W) = 0 then 1 else 0
  have hg : g ∈ GlobalTheory.WeilM.SB (Fin 1 → Fin b → AfE D) := GlobalTheory.SchwartzBruhatTensor.coset_mem_SB W hWo hWc 0
  have hg1 : ∀ w, g w = if w ∈ W then 1 else 0 := fun w => by
    simp only [g, QuotientAddGroup.eq_zero_iff]
  let rc : Mx D 1 b → (D.what₂.Tau → Fin 1 → Fin b → ℂ) := fun y τ i j => compAt θ τ y i j
  have hrc : Continuous rc := continuous_pi fun τ => GlobalTheory.RealWeil.continuous_compAt hθ τ 1 b
  have hK : IsCompact (⋃ i, (fun x : Mx D a b => rc (x.submatrix (fun _ : Fin 1 => i) id)) '' C) :=
    isCompact_iUnion fun i => hC.image (hrc.comp (continuous_id.matrix_submatrix _ _))
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  let bump : ContDiffBump (0 : D.what₂.Tau → Fin 1 → Fin b → ℂ) :=
    ⟨max R 1, max R 1 + 1, lt_max_of_lt_right one_pos, by linarith⟩
  have hc : HasCompactSupport fun y => ((bump y : ℝ) : ℂ) :=
    bump.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  let f : SchwartzMap (D.what₂.Tau → Fin 1 → Fin b → ℂ) ℂ :=
    hc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp bump.contDiff)
  have hf : ∀ y, f y = ((bump y : ℝ) : ℂ) := fun y => rfl
  let η₀ : Mx D 1 b → ℂ := fun y => f (fun τ i j => compAt θ τ y i j) * g (fun i j => finPart D (y i j))
  have hη : ∀ y, η₀ y = ((bump (rc y) : ℝ) : ℂ) *
      (if (Matrix.of fun i j => finPart D (y i j)) ∈ W then 1 else 0) := fun y => by
    show f _ * g _ = _
    rw [hf]
    congr 1
    exact hg1 _
  refine ⟨fun _ => η₀, fun i => ⟨Submodule.subset_span ⟨f, g, hg, rfl⟩, ?_, ?_, ?_, ?_⟩⟩
  ·
    obtain ⟨Ka, hKa, hKaC⟩ := GlobalTheory.StabCompact.exists_compact_adele D θ hθ (max R 1 + 1)
      (⋃ i, ⋃ j, (fun w : Matrix (Fin 1) (Fin b) (AfE D) => w i j) '' (W : Set _))
      (isCompact_iUnion fun i => isCompact_iUnion fun j =>
        (hWc.image ((continuous_apply j).comp (continuous_apply i)) :
          IsCompact ((fun w : Matrix (Fin 1) (Fin b) (AfE D) => w i j) '' (W : Set _))))
    have hKc : IsCompact {y : Mx D 1 b | ∀ i j, y i j ∈ Ka} :=
      isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => hKa
    refine HasCompactSupport.intro' hKc hKc.isClosed fun y hy => ?_
    by_contra hne
    change ¬ η₀ y = 0 at hne
    apply hy
    intro i j
    rw [hη] at hne
    have h1 := left_ne_zero_of_mul hne
    have h2 := right_ne_zero_of_mul hne
    have hw : (Matrix.of fun i j => finPart D (y i j)) ∈ W := by
      by_contra h
      exact h2 (if_neg h)
    refine hKaC _ (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, _, hw, rfl⟩⟩) fun ρ => ?_
    have hb : bump (rc y) ≠ 0 := fun h => h1 (by rw [h, Complex.ofReal_zero])
    have hmem : rc y ∈ Metric.ball (0 : D.what₂.Tau → Fin 1 → Fin b → ℂ) (max R 1 + 1) := by
      rw [← bump.support_eq]; exact hb
    rw [mem_ball_zero_iff] at hmem
    have h3 : ‖rc y ρ i j‖ ≤ ‖rc y‖ :=
      ((norm_le_pi_norm (rc y ρ i) j).trans (norm_le_pi_norm (rc y ρ) i)).trans (norm_le_pi_norm (rc y) ρ)
    exact h3.trans hmem.le
  ·
    intro y
    show η₀ y = if IntOff S y then η₀ (e • y) else 0
    by_cases hy : IntOff S y
    · rw [if_pos hy, hη, hη]
      have hr : rc (e • y) = rc y := by
        funext τ i j
        show θ τ (infPart D ((e • y) i j)) = θ τ (infPart D (y i j))
        rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_mul, hθe τ, one_mul]
      have hw : (Matrix.of fun i j => finPart D ((e • y) i j)) = Matrix.of fun i j => ef * finPart D (y i j) := by
        funext i j
        rw [Matrix.of_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
      have hiff := mem_U_iff (N := N) hef hS (w := Matrix.of fun i j => finPart D (y i j))
        (fun v hv i j => by rw [Matrix.of_apply, ← cv_eq]; exact hy v hv i j)
      rw [hr, hw]
      simp only [Matrix.of_apply] at hiff
      by_cases hm : (Matrix.of fun i j => finPart D (y i j)) ∈ W
      · rw [if_pos hm, if_pos (hiff.1 hm)]
      · rw [if_neg hm, if_neg (fun h => hm (hiff.2 h))]
    · rw [if_neg hy, hη, if_neg, mul_zero]
      intro hm
      exact hy fun v hv i j => by rw [cv_eq]; exact hm.1 v hv i j
  ·
    intro y
    show 0 ≤ (η₀ y).re ∧ (η₀ y).re ≤ 1 ∧ (η₀ y).im = 0
    rw [hη]
    split_ifs
    · rw [mul_one, Complex.ofReal_re, Complex.ofReal_im]
      exact ⟨bump.nonneg, bump.le_one, rfl⟩
    · simp
  ·
    intro x hx
    show η₀ (x.submatrix (fun _ => i) id) = 1
    rw [hη, if_pos, bump.one_of_mem_closedBall]
    · simp
    · exact Metric.closedBall_subset_closedBall (le_max_left _ _)
        (hR (Set.mem_iUnion.2 ⟨i, x, hx, rfl⟩))
    · refine ⟨fun v hv i' j => ?_, fun i' j => ?_⟩
      · rw [Matrix.of_apply, ← cv_eq]; exact hCi x hx v hv i j
      · exact hNC _ (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, x, hx, rfl⟩⟩)

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixW_C
section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open scoped TensorProduct
open IsDedekindDomain NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU Filter

namespace PositivityTheory.Rg.Rsw.L.LFixW

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E]

theorem trace_map {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (φ : R →ₐ[F] R')
    (z : R ⊗[F] E) :
    Algebra.trace R' (R' ⊗[F] E) (Algebra.TensorProduct.map φ (AlgHom.id F E) z) =
      φ (Algebra.trace R (R ⊗[F] E) z) := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis R' (bE F E)),
    Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis R (bE F E)), Matrix.trace, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply]
  have e : Algebra.TensorProduct.map φ (AlgHom.id F E) (z * (1 ⊗ₜ[F] bE F E i)) =
      Algebra.TensorProduct.map φ (AlgHom.id F E) z * (1 ⊗ₜ[F] bE F E i) := by
    rw [map_mul]; simp
  rw [← e, LIdemEx.repr_map']

theorem sgl_self (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) : (singleV F v y) v = y :=
  GlobalTheory.CompanionTheory.PsiCondLoc.single_self v y

theorem sgl_ne (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) {w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) :
    (singleV F v y) w = 0 :=
  GlobalTheory.CompanionTheory.PsiCondLoc.single_ne v y h

theorem sgl_mul (u : Af F) (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) :
    u * singleV F v y = singleV F v (u v * y) :=
  GlobalTheory.CompanionTheory.PsiCondLoc.mul_single u v y

def iV (v : HeightOneSpectrum (𝓞 F)) : Fv F v →ₗ[F] AF F where
  toFun a := pairA F 0 (singleV F v a)
  map_add' a b := by
    refine Prod.ext (by show (0 : Ainf F) = 0 + 0; rw [add_zero]) (Subtype.ext (funext fun w => ?_))
    show (singleV F v (a + b)) w = (singleV F v a) w + (singleV F v b) w
    by_cases h : w = v
    · subst h; rw [sgl_self, sgl_self, sgl_self]
    · rw [sgl_ne v _ h, sgl_ne v _ h, sgl_ne v _ h,
        add_zero]
  map_smul' c a := by
    rw [Algebra.smul_def (A := AF F), RingHom.id_apply]
    refine Prod.ext (by show (0 : Ainf F) = _ * 0; rw [mul_zero]) ?_
    show singleV F v (c • a) = (algebraMap F (Af F) c) * singleV F v a
    rw [sgl_mul, Algebra.smul_def]
    rfl

theorem iV_fst (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) : (iV v a).1 = 0 := rfl

theorem iV_snd (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) : (iV v a).2 = singleV F v a := rfl


variable (E) in
def plc (v : HeightOneSpectrum (𝓞 F)) : Fv F v ⊗[F] E →ₗ[F] AF F ⊗[F] E := TensorProduct.map (iV v) LinearMap.id

theorem plc_tmul (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (e : E) : plc E v (a ⊗ₜ[F] e) = iV v a ⊗ₜ[F] e := rfl

theorem evFin_apply (v : HeightOneSpectrum (𝓞 F)) (y : AF F) : evFin F v y = y.2 v := rfl

theorem evInf_apply (w : InfinitePlace F) (y : AF F) : evInf F w y = y.1 w := rfl

theorem compFin_plc_self (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v ⊗[F] E) : compFin F E v (plc E v t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | tmul a e =>
    rw [plc_tmul]
    show evFin F v (iV v a) ⊗ₜ[F] e = _
    rw [evFin_apply, iV_snd, sgl_self]

theorem compFin_plc_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (t : Fv F v ⊗[F] E) :
    compFin F E w (plc E v t) = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]
  | tmul a e =>
    rw [plc_tmul]
    show evFin F w (iV v a) ⊗ₜ[F] e = 0
    rw [evFin_apply, iV_snd, sgl_ne v _ h, TensorProduct.zero_tmul]

theorem compInf_plc (w : InfinitePlace F) (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v ⊗[F] E) :
    compInf F E w (plc E v t) = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]
  | tmul a e =>
    rw [plc_tmul]
    show evInf F w (iV v a) ⊗ₜ[F] e = 0
    rw [evInf_apply, iV_fst]
    exact TensorProduct.zero_tmul _ _

theorem psi_kernel {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S → ∀ y : AF F, y.1 = 0 → (∀ v ∈ S, y.2 v = 0) →
      (∀ v ∉ S, y.2 v ∈ v.adicCompletionIntegers F) → ψ y = 1 := by
  obtain ⟨α, hα, hk⟩ := GlobalTheory.CompanionTheory.PsiCondLoc.exists_int_kernel hψ
  have hα0 : (α : F) ≠ 0 := by exact_mod_cast hα
  have h1 := Filter.eventually_cofinite.1 (eventually_int (F := F) ((α : F)⁻¹))
  refine ⟨h1.toFinset, fun S hS y hy1 hyS hyI => ?_⟩
  have hu : algebraMap F (Af F) ((α : F)⁻¹) * y.2 ∈ Formalism.UG.intAd F := by
    intro v
    show (algebraMap F (Af F) ((α : F)⁻¹)) v * y.2 v ∈ v.adicCompletionIntegers F
    by_cases hv : v ∈ S
    · rw [hyS v hv, mul_zero]; exact zero_mem _
    · have hv' : v ∉ h1.toFinset := fun h => hv (hS h)
      rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hv'
      exact mul_mem hv' (hyI v hv)
  have e : y = pairA F 0 (algebraMap F (Af F) (α : F) * (algebraMap F (Af F) ((α : F)⁻¹) * y.2)) := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hα0, map_one, one_mul]
    exact Prod.ext hy1 rfl
  rw [e]
  exact hk _ hu

end Gen

section D

open Formalism.BasicNotions Formalism.L2.Theta GlobalTheory.StdUnn

variable {D : D7}

theorem trA_fst (z : AE D) (w : InfinitePlace D.host.F) :
    (trA z).1 w = Algebra.trace w.Completion (w.Completion ⊗[D.host.F] D.host.E) (compInf D.host.F D.host.E w z) := by
  rw [← evInf_apply]
  exact (trace_map (evInf D.host.F w) z).symm

theorem trA_snd (z : AE D) (v : Pl D) :
    (trA z).2 v = Algebra.trace (Fv D.host.F v) (Fv D.host.F v ⊗[D.host.F] D.host.E) (cv D v z) := by
  rw [← evFin_apply]
  exact (trace_map (evFin D.host.F v) z).symm

theorem mul_plc (z : AE D) (v : Pl D) (t : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    z * plc D.host.E v t = plc D.host.E v (cv D v z * t) := by
  refine LIdemEx.ae_ext _ _ (fun w => ?_) (fun w => ?_)
  · rw [map_mul, compInf_plc, compInf_plc, mul_zero]
  · rw [map_mul]
    by_cases h : w = v
    · subst h; rw [compFin_plc_self, compFin_plc_self]
    · rw [compFin_plc_ne h, compFin_plc_ne h, mul_zero]

theorem trA_plc (v : Pl D) (t : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    trA (plc D.host.E v t) =
      pairA D.host.F 0 (singleV D.host.F v (Algebra.trace (Fv D.host.F v) (Fv D.host.F v ⊗[D.host.F] D.host.E) t)) := by
  refine Prod.ext (funext fun w => ?_) (Subtype.ext (funext fun w => ?_))
  · rw [trA_fst, compInf_plc, map_zero]; rfl
  · show (trA (plc D.host.E v t)).2 w = (singleV D.host.F v _) w
    rw [trA_snd]
    by_cases h : w = v
    · subst h; rw [compFin_plc_self, sgl_self]
    · rw [compFin_plc_ne h, map_zero, sgl_ne v _ h]

end D

end PositivityTheory.Rg.Rsw.L.LFixW

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGenKE
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LGenK

open Matrix

section GlobalTheory

variable {R : Type} [CommRing R] {n : ℕ}

theorem submatrix_fromBlocks_mul (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  unfold blk4
  rw [Matrix.submatrix_mul_equiv _ _ _ finSumFinEquiv.symm _, fromBlocks_multiply]

theorem block_matrix_one : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  unfold blk4; rw [fromBlocks_one, Matrix.submatrix_one_equiv]

theorem conj_block_matrix (s : R →+* R) (a b c d : Matrix (Fin n) (Fin n) R) :
    cj s (blk4 a b c d) = blk4 (cj s a) (cj s c) (cj s b) (cj s d) := by
  unfold blk4; rw [← cj_fromBlocks]; rfl

theorem block_matrix_map {S : Type} [CommRing S] (f : R →+* S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  unfold blk4; rw [← fromBlocks_map]; rfl

theorem blockMatrixTwoByTwoFin_injective {a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R} (h : blk4 a b c d = blk4 a' b' c' d') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have : fromBlocks a b c d = fromBlocks a' b' c' d' := by
    have := congrArg (fun M => M.submatrix finSumFinEquiv finSumFinEquiv) h
    simpa [blk4, Matrix.submatrix_submatrix] using this
  exact Matrix.fromBlocks_inj.1 this

def bA (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁
def bB (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂
def bC (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁
def bD (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂

theorem block_matrix_of_blocks (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : blk4 (bA M) (bB M) (bC M) (bD M) = M := by
  unfold blk4 bA bB bC bD
  rw [fromBlocks_toBlocks, Matrix.submatrix_submatrix]
  simp

theorem unit_fromBlocks (s : R →+* R) (a b c d : Matrix (Fin n) (Fin n) R)
    (h : cj s (blk4 a b c d) * blk4 0 1 (-1) 0 * blk4 a b c d = blk4 0 1 (-1) 0) :
    cj s (fromBlocks a b c d) * fromBlocks 0 1 (-1) 0 * fromBlocks a b c d = fromBlocks 0 1 (-1) 0 := by
  rw [conj_block_matrix, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul] at h
  obtain ⟨h1, h2, h3, h4⟩ := blockMatrixTwoByTwoFin_injective h
  rw [cj_fromBlocks, fromBlocks_multiply, fromBlocks_multiply, h1, h2, h3, h4]

theorem unit_col (s : R →+* R) (a b c d : Matrix (Fin n) (Fin n) R)
    (h : cj s (fromBlocks a b c d) * fromBlocks 0 1 (-1) 0 * fromBlocks a b c d = fromBlocks 0 1 (-1) 0) :
    cj s a * c = cj s c * a ∧ cj s a * d - cj s c * b = 1 ∧ cj s b * d = cj s d * b := by
  rw [cj_fromBlocks, fromBlocks_multiply, fromBlocks_multiply] at h
  simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg,
    zero_add, add_zero] at h
  obtain ⟨h1, h2, h3, h4⟩ := Matrix.fromBlocks_inj.1 h
  refine ⟨?_, ?_, ?_⟩
  · rw [← sub_eq_zero, ← h1]; noncomm_ring
  · rw [← h2]; noncomm_ring
  · rw [← sub_eq_zero, ← h4]; noncomm_ring

end GlobalTheory

section G

variable {D : D7} {n : ℕ}

abbrev Jm (D : D7) (n : ℕ) : Mx D (n + n) (n + n) := blk4 0 1 (-1) 0

theorem Jst_map : (Jst D n).map (inclR (AF D.host.F)) = Jm D n := by
  rw [Jst, block_matrix_map]
  have e : ((-1 : Matrix (Fin n) (Fin n) D.host.E)).map (inclR (F := D.host.F) (AF D.host.F)) = -1 := by
    ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  simp [e]

theorem mat_unit (g : G D n) : cj (cA D) (mat g) * Jm D n * mat g = Jm D n := by
  rw [← Jst_map]; exact g.2

theorem mat_mul (g h : G D n) : mat (g * h) = mat g * mat h := by
  simp [mat]

theorem mat_one : mat (1 : G D n) = 1 := by
  simp [mat]

theorem mat_inv_mul (g : G D n) : mat g⁻¹ * mat g = 1 := by rw [← mat_mul, inv_mul_cancel, mat_one]

theorem mat_inj {g h : G D n} (e : mat g = mat h) : g = h := by
  apply Subtype.ext; apply Units.ext; exact e

theorem mat_inv_eq {g : G D n} {N : Mx D (n + n) (n + n)} (h : mat g * N = 1) : mat g⁻¹ = N := by
  calc mat g⁻¹ = mat g⁻¹ * (mat g * N) := by rw [h, Matrix.mul_one]
    _ = N := by rw [← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]

theorem Jm_inv : blk4 (0 : Mx D n n) (-1) 1 0 * Jm D n = 1 := by
  rw [submatrix_fromBlocks_mul]; simp [block_matrix_one]

theorem exists_G (M : Mx D (n + n) (n + n)) (hM : cj (cA D) M * Jm D n * M = Jm D n) : ∃ g : G D n, mat g = M := by
  have h1 : (blk4 (0 : Mx D n n) (-1) 1 0 * cj (cA D) M * Jm D n) * M = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cj (cA D) M), hM, Jm_inv]
  have h2 := mul_eq_one_comm.1 h1
  let u : GL (Fin (n + n)) (AE D) := ⟨M, _, h2, h1⟩
  have hu : u ∈ HR (AF D.host.F) D.sp.cm.sig (Jst D n) := by
    change cj (cA D) M * (Jst D n).map (inclR (AF D.host.F)) * M = (Jst D n).map (inclR (AF D.host.F))
    rw [Jst_map]; exact hM
  exact ⟨⟨u, hu⟩, rfl⟩

end G

end PositivityTheory.Rg.Rsw.L.LGenK
end
end

