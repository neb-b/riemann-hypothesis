module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0454
public import Development.AutomorphicSpectrum.Proofs.HermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1175
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0007
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0434
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0453
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0425
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0413
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaOpCommLiB
section
set_option maxSynthPendingDepth 1

open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.HCRep

open AutomorphicForm GlobalTheory.CompanionTheory.ArchSmooth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def smL (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    Sm E a →ₗ[ℂ] AutomorphicForm.archSmooth E a where
  toFun φ := ⟨φ.1, sm_mem_archSmooth E a φ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem smL_injective : Function.Injective (smL E a) := fun _ _ h =>
  Subtype.ext (congrArg (fun ψ : AutomorphicForm.archSmooth E a => ψ.1) h)

def liB (X : (isExpLieAlgebra E a).lieSubalgebra) : Module.End ℂ (Sm E a) :=
  lie E a (mMap E a (X : ArchMatrix E a))

def lapOp {d : ℕ} (b : Fin d → (isExpLieAlgebra E a).lieSubalgebra) : Module.End ℂ (Sm E a) :=
  ∑ i, liB (b i) * liB (b i)

def omegaOp {d : ℕ} (b : Fin d → (isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ) :
    Module.End ℂ (Sm E a) :=
  ∑ i, (ε i : ℂ) • (liB (b i) * liB (b i))

theorem smL_liB (X : (isExpLieAlgebra E a).lieSubalgebra) (ψ : Sm E a) :
    smL E a (liB X ψ) = uAction (UniversalEnvelopingAlgebra.ι ℝ X) (smL E a ψ) := by
  apply Subtype.ext
  funext g
  rw [uAction_ι_apply]
  change lieD (mMap E a (X : ArchMatrix E a)) ψ.1 g = _
  have h1 := (isExpLieAlgebra E a).hasDerivAt_rightDeriv (sm_mem_archSmooth E a ψ g)
    ((isExpLieAlgebra E a).ofLie X) 1
  let L : ArchMatrix E a →L[ℝ] Lie E a := LinearMap.toContinuousLinearMap (mMap E a)
  have hc : HasDerivAt (fun t : ℝ => toL (toGL E a ((isExpLieAlgebra E a).expG
      (t • (isExpLieAlgebra E a).ofLie X))).val) (mMap E a (X : ArchMatrix E a)) 0 := by
    have h3 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • (X : ArchMatrix E a)))
        (NormedSpace.exp ((0 : ℝ) • (X : ArchMatrix E a)) * (X : ArchMatrix E a)) 0 :=
      hasDerivAt_exp_smul_const (X : ArchMatrix E a) (0 : ℝ)
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at h3
    have h4 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h3
    refine h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    exact toL_toGL E a _
  have h0 : toGL E a ((isExpLieAlgebra E a).expG ((0 : ℝ) • (isExpLieAlgebra E a).ofLie X)) = 1 := by
    simp [toGL]
  have h2 := hasDerivAt_curve ψ g (fun t => toGL E a ((isExpLieAlgebra E a).expG
      (t • (isExpLieAlgebra E a).ofLie X))) (mMap E a (X : ArchMatrix E a)) h0 hc
  refine h2.unique (h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_))
  simp only [archSlice_apply, one_mul, infEmb_eq]

theorem smL_lapOp {d : ℕ} (b : Fin d → (isExpLieAlgebra E a).lieSubalgebra) (ψ : Sm E a) :
    smL E a (lapOp b ψ) = ∑ i, uAction (UniversalEnvelopingAlgebra.ι ℝ (b i))
      (uAction (UniversalEnvelopingAlgebra.ι ℝ (b i)) (smL E a ψ)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [lapOp, LinearMap.sum_apply, map_sum, Module.End.mul_apply, smL_liB]

theorem smL_omegaOp {d : ℕ} (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ)
    (ψ : Sm E a) : smL E a (omegaOp b ε ψ) = uAction (casimir b ε) (smL E a ψ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [omegaOp, casimir, LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_smul,
    Module.End.mul_apply, smL_liB, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ext g
  simp [Complex.real_smul]

theorem omegaOp_comm_liB {d : ℕ} (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (horth : ∀ i j, archTraceForm E a (b i) (b j) = if i = j then ε i else 0)
    (X : (isExpLieAlgebra E a).lieSubalgebra) :
    omegaOp b ε * liB X = liB X * omegaOp b ε := by
  have hε2 : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with e | e <;> rw [e] <;> norm_num
  have hz : casimir b ε ∈ (isExpLieAlgebra E a).centerU :=
    casimir_mem_center hε2 horth archTraceForm_symm archTraceForm_lie
  have hc := Subalgebra.mem_center_iff.1 hz (UniversalEnvelopingAlgebra.ι ℝ X)
  refine LinearMap.ext fun ψ => smL_injective ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, smL_omegaOp, smL_liB, smL_liB, smL_omegaOp,
    ← Module.End.mul_apply, ← map_mul, ← hc, map_mul, Module.End.mul_apply]

end GlobalTheory.CompanionTheory.HCRep

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneParameterSubgroupExists
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section
namespace GlobalTheory.CompanionTheory.LieCurve

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable (E : Type) [Field E] [NumberField E] (a : ℕ)

def expUnit (M : Matrix (Fin a) (Fin a) (Cinf E)) (t : ℝ) : GL (Fin a) (Cinf E) where
  val := NormedSpace.exp (t • M)
  inv := NormedSpace.exp (-(t • M))
  val_inv := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl (t • M)).neg_right, add_neg_cancel, NormedSpace.exp_zero]
  inv_val := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl (t • M)).neg_left, neg_add_cancel, NormedSpace.exp_zero]

theorem expUnit_val (M : Matrix (Fin a) (Fin a) (Cinf E)) (t : ℝ) :
    (expUnit E a M t).val = NormedSpace.exp (t • M) := rfl

theorem expUnit_inv_val (M : Matrix (Fin a) (Fin a) (Cinf E)) (t : ℝ) :
    ((expUnit E a M t)⁻¹).val = NormedSpace.exp ((-t) • M) := by
  change NormedSpace.exp (-(t • M)) = _
  rw [neg_smul]

theorem hasDerivAt_exp (M : Matrix (Fin a) (Fin a) (Cinf E)) (t : ℝ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • M)) (NormedSpace.exp (t • M) * M) t := by
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  exact hasDerivAt_exp_smul_const (𝕂 := ℝ) M t

theorem continuous_exp_smul (M : Matrix (Fin a) (Fin a) (Cinf E)) :
    Continuous fun t : ℝ => NormedSpace.exp (t • M) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp E a M t).continuousAt

theorem continuous_expUnit (M : Matrix (Fin a) (Fin a) (Cinf E)) : Continuous (expUnit E a M) := by
  refine Units.continuous_iff.2 ⟨continuous_exp_smul E a M, ?_⟩
  exact ((continuous_exp_smul E a M).comp continuous_neg).congr fun t => (expUnit_inv_val E a M t).symm

theorem expUnit_zero (M : Matrix (Fin a) (Fin a) (Cinf E)) : expUnit E a M 0 = 1 := by
  ext1
  rw [expUnit_val, zero_smul, NormedSpace.exp_zero]
  rfl

theorem expUnit_add (M : Matrix (Fin a) (Fin a) (Cinf E)) (s t : ℝ) :
    expUnit E a M (s + t) = expUnit E a M s * expUnit E a M t := by
  ext1
  rw [Units.val_mul, expUnit_val, expUnit_val, expUnit_val, add_smul,
    Matrix.exp_add_of_commute _ _ (((Commute.refl M).smul_left s).smul_right t)]

theorem expUnit_mem_unitary (M : Matrix (Fin a) (Fin a) (Cinf E)) (h : Mᴴ = -M) (t : ℝ) :
    (expUnit E a M t).val ∈ Matrix.unitaryGroup (Fin a) (Cinf E) := by
  have e : star (NormedSpace.exp (t • M)) = NormedSpace.exp (-(t • M)) := by
    rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, h]
    simp
  rw [Matrix.mem_unitaryGroup_iff, expUnit_val, e]
  exact (expUnit E a M t).val_inv

def toLieL : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := Matrix.of.symm
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem toLieL_apply (M : Matrix (Fin a) (Fin a) (Cinf E)) : toLieL E a M = Matrix.of.symm M := rfl

theorem hasDerivAt_toL (M : Matrix (Fin a) (Fin a) (Cinf E)) :
    HasDerivAt (fun t : ℝ => toL (expUnit E a M t).val) (Matrix.of.symm M) 0 := by
  have h := (toLieL E a).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_exp E a M 0)
  have e : toLieL E a (NormedSpace.exp ((0 : ℝ) • M) * M) = Matrix.of.symm M := by
    rw [zero_smul, NormedSpace.exp_zero, one_mul]; rfl
  exact h.congr_deriv e

end

theorem exists_curve (E : Type) [Field E] [NumberField E] (a : ℕ) (X : GlobalTheory.CuspRep.Lie E a) :
    ∃ c : ℝ → GL (Fin a) (Cinf E), Continuous c ∧ c 0 = 1 ∧ (∀ s t, c (s + t) = c s * c t) ∧
      HasDerivAt (fun t => toL (c t).val) X 0 ∧
      ((Matrix.of X)ᴴ = -(Matrix.of X) → ∀ t, (c t).val ∈ Matrix.unitaryGroup (Fin a) (Cinf E)) :=
  ⟨expUnit E a (Matrix.of X), continuous_expUnit E a _, expUnit_zero E a _, expUnit_add E a _,
    hasDerivAt_toL E a _, fun h t => expUnit_mem_unitary E a _ h t⟩

end GlobalTheory.CompanionTheory.LieCurve
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellUnipotentUniquenessClosed
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier.LowerOpen

theorem inv_conj_apply {k : Type} [Field k] {N : ℕ} (w : Equiv.Perm (Fin N)) (x : GL (Fin N) k)
    (p q : Fin N) :
    (((GroundTheory.Automorphic.permGL k w)⁻¹ * x * GroundTheory.Automorphic.permGL k w : GL (Fin N) k) :
      Matrix (Fin N) (Fin N) k) p q = (x : Matrix (Fin N) (Fin N) k) (w p) (w q) := by
  have h1 : (((GroundTheory.Automorphic.permGL k w)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      w.permMatrix k := by
    rw [← map_inv]
    show ((w⁻¹)⁻¹).permMatrix k = w.permMatrix k
    rw [inv_inv]
  have h2 : ((GroundTheory.Automorphic.permGL k w : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      (w⁻¹).permMatrix k := rfl
  rw [Units.val_mul, Units.val_mul, h1, h2, Equiv.Perm.permMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  simp [Equiv.Perm.inv_def]

theorem lt_of_blk_lt {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {p q : Fin N}
    (hb : blk (stdBlocks d hd) (wOpen d hd q) < blk (stdBlocks d hd) (wOpen d hd p)) : p < q := by
  by_contra hpq
  have h1 := Tuple.monotone_sort (GlobalTheory.CompanionTheory.Rodier.wKey d hd) (not_lt.mp hpq)
  simp only [Function.comp_apply, GlobalTheory.CompanionTheory.Rodier.wKey] at h1
  have hb' : blk (stdBlocks d hd) (Tuple.sort (GlobalTheory.CompanionTheory.Rodier.wKey d hd) q) <
      blk (stdBlocks d hd) (Tuple.sort (GlobalTheory.CompanionTheory.Rodier.wKey d hd) p) := hb
  rw [Prod.Lex.toLex_le_toLex] at h1
  rcases h1 with h | ⟨h, -⟩
  · exact lt_asymm hb' (OrderDual.toDual_lt_toDual.mp h)
  · exact (ne_of_lt hb') (OrderDual.toDual.injective h)

theorem lower_entries {k : Type} [Field k] {h N : ℕ} {d : Fin h → ℕ} {hd : ∑ a, d a = N}
    {x : GL (Fin N) k} (hx : x ∈ unipRadLower k (stdBlocks d hd)) (i j : Fin N) :
    (blk (stdBlocks d hd) i < blk (stdBlocks d hd) j → (x : Matrix (Fin N) (Fin N) k) i j = 0) ∧
      (blk (stdBlocks d hd) i = blk (stdBlocks d hd) j →
        (x : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j) := by
  obtain ⟨hpl, hdiag⟩ := (GlobalTheory.SmGL.mem_unipRadLower k).mp hx
  rw [GlobalTheory.SmGL.mem_parabLower_iff] at hpl
  obtain ⟨⟨a, i'⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, j'⟩, rfl⟩ := (stdBlocks d hd).surjective j
  rw [GlobalTheory.SmGL.blk_apply, GlobalTheory.SmGL.blk_apply]
  refine ⟨fun hab => hpl a b i' j' hab, fun hab => ?_⟩
  subst hab
  rw [hdiag a i' j', Matrix.one_apply, Matrix.one_apply]
  simp [(stdBlocks d hd).apply_eq_iff_eq]

theorem parab_inf_lower {k : Type} [Field k] {h N : ℕ} {d : Fin h → ℕ} {hd : ∑ a, d a = N}
    {x : GL (Fin N) k} (hp : x ∈ parab k (stdBlocks d hd))
    (hx : x ∈ unipRadLower k (stdBlocks d hd)) : x = 1 := by
  ext i j
  rcases lt_trichotomy (blk (stdBlocks d hd) i) (blk (stdBlocks d hd) j) with hlt | heq | hgt
  · have hij : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hlt
    rw [(lower_entries hx i j).1 hlt]
    simp [Matrix.one_apply, hij]
  · rw [(lower_entries hx i j).2 heq]
    simp
  · have hij : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hgt
    rw [GlobalTheory.SmGL.mem_parab.mp hp i j hgt]
    simp [Matrix.one_apply, hij]

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)


variable {k d hd} in
theorem mem_unipU_iff {u : GL (Fin N) k} :
    u ∈ unipU k d hd ↔ u ∈ unipB k (Fin N) ∧
      pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹ ∈ unipRadLower k (stdBlocks d hd) := by
  rw [GlobalTheory.CompanionTheory.Rodier.unipU, Subgroup.mem_inf, Subgroup.mem_comap]
  rfl

theorem inv_conj_mem_unipU {x : GL (Fin N) k} (hx : x ∈ unipRadLower k (stdBlocks d hd)) :
    (pm k (wOpen d hd))⁻¹ * x * pm k (wOpen d hd) ∈ unipU k d hd := by
  rw [mem_unipU_iff]
  refine ⟨?_, ?_⟩
  · rw [GlobalTheory.SmGL.mem_unipB]
    have hent : ∀ p q, (((pm k (wOpen d hd))⁻¹ * x * pm k (wOpen d hd) : GL (Fin N) k) :
        Matrix (Fin N) (Fin N) k) p q = (x : Matrix (Fin N) (Fin N) k) (wOpen d hd p) (wOpen d hd q) :=
      fun p q => inv_conj_apply (wOpen d hd) x p q
    refine ⟨fun i j hji => ?_, fun i => ?_⟩
    · rw [hent]
      rcases lt_trichotomy (blk (stdBlocks d hd) (wOpen d hd i)) (blk (stdBlocks d hd) (wOpen d hd j))
        with hlt | heq | hgt
      · exact (lower_entries hx _ _).1 hlt
      · rw [(lower_entries hx _ _).2 heq, Matrix.one_apply, if_neg]
        intro h
        exact hji.ne' ((wOpen d hd).injective h)
      · exact absurd (lt_of_blk_lt d hd hgt) (not_lt.mpr hji.le)
    · rw [hent, (lower_entries hx _ _).2 rfl]
      simp
  · have he : pm k (wOpen d hd) * ((pm k (wOpen d hd))⁻¹ * x * pm k (wOpen d hd)) *
        (pm k (wOpen d hd))⁻¹ = x := by group
    rw [he]
    exact hx

theorem eq_of_mul_eq {p u u' : GL (Fin N) k} (hp : p ∈ parab k (stdBlocks d hd))
    (hu : u ∈ unipU k d hd) (hu' : u' ∈ unipU k d hd)
    (e : p * pm k (wOpen d hd) * u = pm k (wOpen d hd) * u') : u = u' := by
  have hv : u' * u⁻¹ ∈ unipU k d hd := (unipU k d hd).mul_mem hu' ((unipU k d hd).inv_mem hu)
  have hlow := (mem_unipU_iff.mp hv).2
  have hpeq : pm k (wOpen d hd) * (u' * u⁻¹) * (pm k (wOpen d hd))⁻¹ = p := by
    calc pm k (wOpen d hd) * (u' * u⁻¹) * (pm k (wOpen d hd))⁻¹
        = (pm k (wOpen d hd) * u') * u⁻¹ * (pm k (wOpen d hd))⁻¹ := by group
      _ = (p * pm k (wOpen d hd) * u) * u⁻¹ * (pm k (wOpen d hd))⁻¹ := by rw [e]
      _ = p := by group
  rw [hpeq] at hlow
  have h1 := parab_inf_lower hp hlow
  rw [h1] at e
  simpa using e

theorem isClosed_unipU : IsClosed (unipU k d hd : Set (GL (Fin N) k)) := by
  have hent : ∀ (i j : Fin N) (c : k),
      IsClosed {g : GL (Fin N) k | (g : Matrix (Fin N) (Fin N) k) i j = c} :=
    fun i j c => isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const
  have hB : IsClosed (unipB k (Fin N) : Set (GL (Fin N) k)) := by
    have hs : (unipB k (Fin N) : Set (GL (Fin N) k)) =
        (⋂ i, ⋂ j, ⋂ (_ : j < i), {g : GL (Fin N) k | (g : Matrix (Fin N) (Fin N) k) i j = 0}) ∩
          ⋂ i, {g : GL (Fin N) k | (g : Matrix (Fin N) (Fin N) k) i i = 1} := by
      ext g
      simp [GlobalTheory.SmGL.mem_unipB]
    rw [hs]
    exact (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => hent i j 0).inter
      (isClosed_iInter fun i => hent i i 1)
  have hL : IsClosed (unipRadLower k (stdBlocks d hd) : Set (GL (Fin N) k)) := by
    have hs : (unipRadLower k (stdBlocks d hd) : Set (GL (Fin N) k)) =
        (⋂ a, ⋂ b, ⋂ i, ⋂ j, ⋂ (_ : a < b), {g : GL (Fin N) k |
          (g : Matrix (Fin N) (Fin N) k) (stdBlocks d hd ⟨a, i⟩) (stdBlocks d hd ⟨b, j⟩) = 0}) ∩
          ⋂ a, ⋂ i, ⋂ j, {g : GL (Fin N) k |
            (g : Matrix (Fin N) (Fin N) k) (stdBlocks d hd ⟨a, i⟩) (stdBlocks d hd ⟨a, j⟩) =
              (1 : Matrix (Fin (d a)) (Fin (d a)) k) i j} := by
      ext g
      simp [GlobalTheory.SmGL.mem_unipRadLower, GlobalTheory.SmGL.mem_parabLower_iff]
    rw [hs]
    exact (isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun i =>
      isClosed_iInter fun j => isClosed_iInter fun _ => hent _ _ _).inter
      (isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun j => hent _ _ _)
  have hc : Continuous fun u : GL (Fin N) k => pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹ :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hs : (unipU k d hd : Set (GL (Fin N) k)) =
      (unipB k (Fin N) : Set (GL (Fin N) k)) ∩
        (fun u : GL (Fin N) k => pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹) ⁻¹'
          (unipRadLower k (stdBlocks d hd) : Set (GL (Fin N) k)) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]
    exact mem_unipU_iff
  rw [hs]
  exact hB.inter (hL.preimage hc)

end GlobalTheory.CompanionTheory.Rodier.LowerOpen

namespace GlobalTheory.CompanionTheory.Rodier

theorem unipU_open_cell : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ x ∈ unipRadLower k (stdBlocks d hd), (pm k (wOpen d hd))⁻¹ * x * pm k (wOpen d hd) ∈ unipU k d hd) ∧ (∀ p ∈ parab k (stdBlocks d hd), ∀ u ∈ unipU k d hd, ∀ u' ∈ unipU k d hd, p * pm k (wOpen d hd) * u = pm k (wOpen d hd) * u' → u = u') ∧ IsClosed (unipU k d hd : Set (GL (Fin N) k)) := by
  intro k _ _ _ _ h N d hd
  exact ⟨fun x hx => LowerOpen.inv_conj_mem_unipU k d hd hx,
    fun p hp u hu u' hu' e => LowerOpen.eq_of_mul_eq k d hd hp hu hu' e,
    LowerOpen.isClosed_unipU k d hd⟩

end GlobalTheory.CompanionTheory.Rodier
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PluckerMinorsDetermineColumnSpace
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

noncomputable section

namespace GlobalTheory.CompanionTheory.GodementH.Cramer

open Matrix

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}

theorem mul_adjugate_submatrix (M : Matrix ι (Fin n) K) (f₀ : Fin n → ι) (i : ι) (j : Fin n) :
    (M * adjugate (M.submatrix f₀ id)) i j = mnr M (Function.update f₀ j i) := by
  have h1 : (M * adjugate (M.submatrix f₀ id)) i j = cramer (M.submatrix f₀ id)ᵀ (M i) j := by
    rw [cramer_eq_adjugate_mulVec, ← adjugate_transpose]
    simp [mulVec, dotProduct, Matrix.mul_apply, transpose_apply, mul_comm]
  rw [h1, cramer_transpose_apply]
  unfold mnr
  congr 1
  ext a b
  by_cases hab : a = j
  · subst hab; simp
  · simp [updateRow_apply, hab, Function.update_apply]

theorem eq_mul_of_minor_ratio (M M' : Matrix ι (Fin n) K) (f₀ f₀' : Fin n → ι)
    (h0 : mnr M f₀ ≠ 0) (h0' : mnr M' f₀' ≠ 0)
    (h : ∀ f, mnr M f / mnr M f₀ = mnr M' f / mnr M' f₀') : ∃ c : GL (Fin n) K, M' = M * c.1 := by
  set c := mnr M' f₀' / mnr M f₀ with hcdef
  have hc : ∀ f, mnr M' f = c * mnr M f := fun f => by
    calc mnr M' f = mnr M' f / mnr M' f₀' * mnr M' f₀' := by rw [div_mul_cancel₀ _ h0']
      _ = mnr M f / mnr M f₀ * mnr M' f₀' := by rw [h f]
      _ = c * mnr M f := by rw [hcdef]; ring
  have hc0 : c ≠ 0 := div_ne_zero h0' h0
  set A := M.submatrix f₀ id with hA
  set A' := M'.submatrix f₀ id with hA'
  have hdA : A.det = mnr M f₀ := rfl
  have hdA' : A'.det = c * A.det := hc f₀
  have hA0 : A.det ≠ 0 := h0
  have hdA'0 : A'.det ≠ 0 := by rw [hdA']; exact mul_ne_zero hc0 h0
  have key : M' * adjugate A' = c • (M * adjugate A) := by
    ext i j
    rw [mul_adjugate_submatrix, Matrix.smul_apply, mul_adjugate_submatrix, hc, smul_eq_mul]
  have e1 : M' * adjugate A' * A' = A'.det • M' := by
    rw [Matrix.mul_assoc, adjugate_mul, Matrix.mul_smul, Matrix.mul_one]
  have hP : (A⁻¹ * A').det ≠ 0 := by
    rw [det_mul, det_nonsing_inv, Ring.inverse_eq_inv']
    exact mul_ne_zero (inv_ne_zero h0) hdA'0
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (A⁻¹ * A') hP, ?_⟩
  show M' = M * (A⁻¹ * A')
  rw [inv_def, Ring.inverse_eq_inv']
  have e2 : M * ((A.det)⁻¹ • adjugate A * A') = ((A.det)⁻¹ * c⁻¹) • (M' * adjugate A' * A') := by
    rw [key, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel_right₀ hc0, Matrix.mul_assoc]
  rw [e2, e1, smul_smul, hdA']
  rw [show A.det⁻¹ * c⁻¹ * (c * A.det) = 1 by field_simp, one_smul]

end GlobalTheory.CompanionTheory.GodementH.Cramer

theorem GlobalTheory.CompanionTheory.GodementH.Cramer.main : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (M M' : Matrix ι (Fin n) K) (f₀ f₀' : Fin n → ι),
    mnr M f₀ ≠ 0 → mnr M' f₀' ≠ 0 → (∀ f, mnr M f / mnr M f₀ = mnr M' f / mnr M' f₀') → ∃ c : GL (Fin n) K, M' = M * c.1 := by
  intro K _ ι _ _ n M M' f₀ f₀' h0 h0' h
  exact GlobalTheory.CompanionTheory.GodementH.Cramer.eq_mul_of_minor_ratio M M' f₀ f₀' h0 h0' h
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearOrbitFiniteStatement
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shear_orbit_box_finite_of_isSmooth : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (T : Representation ℂ (Mir k (n + 1)) V), IsSmooth T → ∀ (v : V) (r : kˣ), valuation k (r : k) < 1 → ((fun b => T (levi k (n + 1) (shearGL n b)) v) '' (box (n + 1) r : Set (Fin (n + 1) → k))).Finite := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.ShearOrbit.shear_orbit_finite | exact GlobalTheory.CompanionTheory.MirPair.ShearOrbit.shear_orbit_finite | (intros; apply GlobalTheory.CompanionTheory.MirPair.ShearOrbit.shear_orbit_finite <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorFixedParabolicNearOne
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

theorem sigX_fix_nhds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ)
    (v : τ.V ⊗[ℂ] σ.V), ∃ O ∈ 𝓝 (1 : Mir k ((i + 1) + t + 1)), ∀ a : HPG k (i + 1) (t + 1),
      (a : Mir k ((i + 1) + (t + 1))) ∈ O → sigX τ σ a v = v :=
  GlobalTheory.CompanionTheory.BZPhiPG.Onto.sigX_fix

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorFixedSmallShearStatement
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_vector_fixed_small_shear : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (T : Representation ℂ (Mir k (n + 1)) V), IsSmooth T → ∀ v : V, ∃ r : kˣ, valuation k (r : k) < 1 ∧ ∀ b ∈ box (n + 1) r, T (levi k (n + 1) (shearGL n b)) v = v := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.shear_fix_vector | exact GlobalTheory.CompanionTheory.MirPair.shear_fix_vector | (intros; apply GlobalTheory.CompanionTheory.MirPair.shear_fix_vector <;> assumption)
end

