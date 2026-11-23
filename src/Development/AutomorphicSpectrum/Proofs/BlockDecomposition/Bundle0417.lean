module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0394
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0396
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0372
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0374
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0399
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0354
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviMatrixOne
section
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.KFin.LeviOne

theorem sum_parts {S : Type} [Ring S] {n r : ℕ} {a b : Matrix (Fin n) (Fin r) S} {c d : Matrix (Fin r) (Fin n) S}
    (ca : c * a = 0) (db : d * b = 0) (cb : c * b = 1) (da : d * a = 1) :
    a * Matrix.diagonal (fun i => (d * (1 : Matrix (Fin n) (Fin n) S) * a) i i) * d +
      b * Matrix.diagonal (fun i => (c * (1 : Matrix (Fin n) (Fin n) S) * b) i i) * c +
      (1 - a * d - b * c) * (1 : Matrix (Fin n) (Fin n) S) * (1 - a * d - b * c) = 1 := by
  have hd : ∀ m : Matrix (Fin r) (Fin r) S, m = 1 → Matrix.diagonal (fun i => m i i) = 1 := by
    intro m hm
    subst hm
    simp
  have hPa : (1 - a * d - b * c) * a = 0 := by
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, da, Matrix.mul_assoc, ca, Matrix.mul_one,
      Matrix.mul_zero]
    simp
  have hPb : (1 - a * d - b * c) * b = 0 := by
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, db, Matrix.mul_assoc, cb, Matrix.mul_one,
      Matrix.mul_zero]
    simp
  have hPP : (1 - a * d - b * c) * (1 - a * d - b * c) = 1 - a * d - b * c := by
    conv_lhs => rw [Matrix.mul_sub (1 - a * d - b * c) (1 - a * d) (b * c), Matrix.mul_sub (1 - a * d - b * c) 1 (a * d)]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPa, hPb, Matrix.zero_mul, Matrix.zero_mul, Matrix.mul_one]
    simp
  rw [Matrix.mul_one, Matrix.mul_one, Matrix.mul_one, hPP, hd _ da, hd _ cb, Matrix.mul_one, Matrix.mul_one]
  abel

theorem leviMat_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (A : Type) [CommRing A] [Algebra F A], leviMat σ J A X Y (1 : Matrix (Fin n) (Fin n) (A ⊗[F] E)) = 1 := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW A _ _
  have hX : cT (σ : E →+* E) (cT (σ : E →+* E) X) = X := by
    ext i j
    simp [cT, cm_conj_conj h]
  have hJJ : cT (σ : E →+* E) J = J := by
    ext i j
    simpa [cT] using hJ.1 i j
  have yx : cT (σ : E →+* E) Y * J * X = 1 := by
    have e := congrArg (cT (σ : E →+* E)) hW.xy
    rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, hX, hJJ, Formalism.UG.cT_one, ← Matrix.mul_assoc] at e
    exact e
  have m0 : ∀ {M : Matrix (Fin r) (Fin n) E} {N : Matrix (Fin n) (Fin r) E}, M * N = 0 →
      M.map (inclR (F := F) A) * N.map (inclR (F := F) A) = 0 := by
    intro M N e
    rw [← Matrix.map_mul, e, Matrix.map_zero _ (map_zero _)]
  have m1 : ∀ {M : Matrix (Fin r) (Fin n) E} {N : Matrix (Fin n) (Fin r) E}, M * N = 1 →
      M.map (inclR (F := F) A) * N.map (inclR (F := F) A) = 1 := by
    intro M N e
    rw [← Matrix.map_mul, e, Matrix.map_one _ (map_zero _) (map_one _)]
  exact sum_parts (m0 hW.xx) (m0 hW.yy) (m1 hW.xy) (m1 yx)

end GlobalTheory.CompanionTheory.KFin.LeviOne

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFormHermitianPerfect
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.KFin.HermForm

section Ring

variable {A : Type} [CommRing A] (c : A →+* A) {n : ℕ} (M : Matrix (Fin n) (Fin n) A)

theorem isHerm_hform (hc : ∀ a, c (c a) = a) (hM : ∀ i j, c (M j i) = M i j) :
    IsHerm c (Formalism.UG.hform c M) := by
  refine ⟨fun x y z => ?_, fun a x y => ?_, fun x y => ?_⟩
  · simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  · simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · set_option synthInstance.maxHeartbeats 100000 in
      simp only [Formalism.UG.hform, map_sum, map_mul, hc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hM]
    ring

theorem hform_eq_dotProduct (x y : Fin n → A) :
    Formalism.UG.hform c M x y = ((fun i => c (x i)) ᵥ* M) ⬝ᵥ y := by
  simp only [Formalism.UG.hform, Matrix.vecMul, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem isPerfect_hform (hc : ∀ a, c (c a) = a) (hM : IsUnit M.det) :
    IsPerfect (Formalism.UG.hform c M) := by
  refine ⟨fun x hx => ?_, fun f => ?_⟩
  · have hv : (fun i => c (x i)) ᵥ* M = 0 := by
      funext j
      have h1 := hx (Pi.single j 1)
      rw [hform_eq_dotProduct] at h1
      simpa using h1
    have h0 : (fun i => c (x i)) = 0 := by
      have h2 := congrArg (fun v => v ᵥ* M⁻¹) hv
      simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hM] using h2
    funext i
    have h3 : c (x i) = 0 := by simpa using congrFun h0 i
    have h4 := hc (x i)
    rw [h3, map_zero] at h4
    simpa using h4.symm
  · refine ⟨fun i => c (((fun k => f (fun j => if k = j then 1 else 0)) ᵥ* M⁻¹) i), fun y => ?_⟩
    rw [hform_eq_dotProduct]
    simp only [hc]
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hM, Matrix.vecMul_one]
    conv_rhs => rw [pi_eq_sum_univ y]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smul, smul_eq_mul, dotProduct]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end Ring

section Tensor

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem sigR_inclR (a : E) : sigR R σ (inclR (F := F) R a) = inclR (F := F) R (σ a) := by
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]

theorem sigR_sigR_of_invol (hσ : ∀ x, σ (σ x) = x) (t : R ⊗[F] E) : sigR R σ (sigR R σ t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, hσ]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem isUnit_det_JR (h : J.det ≠ 0) : IsUnit (JR (F := F) R J).det := by
  have h1 : (JR (F := F) R J).det = inclR (F := F) R J.det := by
    rw [RingHom.map_det]
    rfl
  rw [h1]
  exact (isUnit_iff_ne_zero.mpr h).map _

end Tensor

end GlobalTheory.CompanionTheory.KFin.HermForm

namespace GlobalTheory.CompanionTheory.KFin

theorem isHerm_isPerfect_hR : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}, IsCMExt F E σ → IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), IsHerm (sigR (Fv F v) σ) (hR (Fv F v) σ J) ∧ IsPerfect (hR (Fv F v) σ J) := by
  intro F E _ _ _ _ _ σ n J hCM hJ v
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hinv : ∀ x : E, σ (σ x) = x := by
    intro x
    apply (w.embedding).injective
    rw [hCM.2.2.2, hCM.2.2.2]
    exact star_star _
  have hc : ∀ a, sigR (Fv F v) σ (sigR (Fv F v) σ a) = a :=
    HermForm.sigR_sigR_of_invol (Fv F v) σ hinv
  have hM : ∀ i j, sigR (Fv F v) σ (JR (F := F) (Fv F v) J j i) = JR (F := F) (Fv F v) J i j := by
    intro i j
    simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Matrix.map_apply]
    rw [HermForm.sigR_inclR, hJ.1]
  exact ⟨HermForm.isHerm_hform _ _ hc hM,
    HermForm.isPerfect_hform _ _ hc (HermForm.isUnit_det_JR (F := F) (Fv F v) J hJ.2)⟩

end GlobalTheory.CompanionTheory.KFin

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHermitianRing
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.KFin.RingHyp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)}

theorem sigR_sigR (h : IsCMExt F E σ) (y : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (sigR (Fv F v) σ y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a e =>
    change a ⊗ₜ[F] σ (σ e) = _
    rw [cm_conj_conj h]

theorem finrank_loc (h : IsCMExt F E σ) : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2 := by
  rw [Module.finrank_baseChange, h.2.2.1]

theorem noeth_intLoc : IsNoetherianRing (intLoc F E v) := by
  let _ := (GlobalTheory.Orb.intLocMap E v).toAlgebra
  have : Module.Finite (v.adicCompletionIntegers F) (intLoc F E v) := GlobalTheory.Orb.finite_intLocMap v
  exact IsNoetherianRing.of_finite (v.adicCompletionIntegers F) _

theorem isUnit_intCast {m : ℤ} (hm : m ≠ 0) : IsUnit ((m : ℤ) : Fv F v ⊗[F] E) := by
  have h1 : IsUnit ((m : ℤ) : E) := isUnit_iff_ne_zero.2 (by exact_mod_cast hm)
  simpa using h1.map (inclR (F := F) (Fv F v))

theorem denom_intLoc (a : Fv F v ⊗[F] E) :
    ∃ s ∈ intLoc F E v, IsUnit s ∧ s * a ∈ intLoc F E v := by
  obtain ⟨x, hx⟩ := exists_sub_mem_intLoc v a
  obtain ⟨m, hm, he⟩ := exists_integral_multiples ℤ ℚ ({x} : Finset E)
  have he' : IsIntegral ℤ (m • x) := he x (Finset.mem_singleton_self x)
  have hmem : ((m : ℤ) : Fv F v ⊗[F] E) ∈ intLoc F E v := intCast_mem _ m
  refine ⟨_, hmem, isUnit_intCast hm, ?_⟩
  have h2 := tmul_mem_intLoc (E := E) (one_mem (v.adicCompletionIntegers F)) ⟨m • x, he'⟩
  have e : ((m : ℤ) : Fv F v ⊗[F] E) * a =
      ((m : ℤ) : Fv F v ⊗[F] E) * (a - (1 : Fv F v) ⊗ₜ[F] x) + (1 : Fv F v) ⊗ₜ[F] (m • x) := by
    have e1 : ((m : ℤ) : Fv F v ⊗[F] E) * (1 : Fv F v) ⊗ₜ[F] x = (1 : Fv F v) ⊗ₜ[F] (m • x) := by
      rw [← zsmul_eq_mul, TensorProduct.tmul_smul]
    rw [mul_sub, e1, sub_add_cancel]
  rw [e]
  exact add_mem (mul_mem hmem hx) h2

theorem span_eq_of {R : Type} [CommRing R] {𝔬 : Subring R} {S : Set R} {u : R}
    (hu : u ∈ Submodule.span 𝔬 S) (h : ∀ s ∈ S, ∃ c ∈ 𝔬, s = c * u) :
    Submodule.span 𝔬 S = Submodule.span 𝔬 {u} := by
  refine le_antisymm (Submodule.span_le.2 fun s hs => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 hu)
  obtain ⟨c, hc, rfl⟩ := h s hs
  exact Submodule.mem_span_singleton.2 ⟨⟨c, hc⟩, rfl⟩

theorem finEmb_injective (hf : IsField (Fv F v ⊗[F] E)) (τ : E →ₐ[F] FvBar F v) :
    Function.Injective (finEmb F v τ) :=
  (injective_iff_map_eq_zero _).2 fun y hy => by
    by_contra h0
    obtain ⟨b, hb⟩ := hf.mul_inv_cancel h0
    have := congrArg (finEmb F v τ) hb
    simp [hy] at this

theorem absBar_finEmb_eq (hf : IsField (Fv F v ⊗[F] E)) (τ τ' : E →ₐ[F] FvBar F v) (y : Fv F v ⊗[F] E) :
    absBar F v (finEmb F v τ y) = absBar F v (finEmb F v τ' y) := by
  apply NNReal.eq
  change spectralNorm (Fv F v) (FvBar F v) _ = spectralNorm (Fv F v) (FvBar F v) _
  rw [spectralNorm, spectralNorm, minpoly.algHom_eq _ (finEmb_injective hf τ),
    minpoly.algHom_eq _ (finEmb_injective hf τ')]

theorem principal_field (hf : IsField (Fv F v ⊗[F] E)) (I : Submodule (intLoc F E v) (Fv F v ⊗[F] E))
    (hI : I.FG) (hu : ∃ u ∈ I, IsUnit u) : ∃ u : Fv F v ⊗[F] E, IsUnit u ∧ I = Submodule.span (intLoc F E v) {u} := by
  classical
  obtain ⟨S, rfl⟩ := hI
  obtain ⟨w, hw, hwu⟩ := hu
  have : Nontrivial (Fv F v ⊗[F] E) := ⟨hf.exists_pair_ne⟩
  let τ₀ : E →ₐ[F] FvBar F v := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let N : Fv F v ⊗[F] E → NNReal := fun y => absBar F v (finEmb F v τ₀ y)
  have hN0 : ∀ y, N y = 0 → y = 0 := fun y hy =>
    finEmb_injective hf τ₀ (by rw [map_zero]; exact (absBar_eq_zero F v).1 hy)
  have hS : S.Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    subst hc
    simp only [Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot] at hw
    exact hwu.ne_zero hw
  obtain ⟨u, huS, hmax⟩ := S.exists_max_image N hS
  have hu0 : u ≠ 0 := by
    rintro rfl
    have h0 : (Submodule.span (intLoc F E v) (S : Set (Fv F v ⊗[F] E))) ≤ ⊥ :=
      Submodule.span_le.2 fun s hs => by
        refine hN0 s (le_antisymm ?_ zero_le)
        have := hmax s hs
        rwa [show N 0 = 0 from by simp [N, (absBar_eq_zero F v).2 rfl]] at this
    exact hwu.ne_zero (by simpa using h0 hw)
  obtain ⟨b, hb⟩ := hf.mul_inv_cancel hu0
  have huU : IsUnit u := IsUnit.of_mul_eq_one b hb
  refine ⟨u, huU, span_eq_of (Submodule.subset_span huS) fun s hs => ⟨b * s, ?_, ?_⟩⟩
  · refine mem_intLoc_iff_absFin_le_one.2 ((absFin_le_iff F v).2 fun τ => ?_)
    rw [absBar_finEmb_eq hf τ τ₀, map_mul, absBar_mul]
    have h1 : absBar F v (finEmb F v τ₀ u) * absBar F v (finEmb F v τ₀ b) = 1 := by
      rw [← absBar_mul, ← map_mul, hb, map_one]
      simpa using absBar_algebraMap F v 1
    calc _ ≤ absBar F v (finEmb F v τ₀ b) * absBar F v (finEmb F v τ₀ u) := mul_le_mul' le_rfl (hmax s hs)
      _ = 1 := by rw [mul_comm, h1]
  · rw [mul_right_comm, mul_comm b, hb, one_mul]

theorem exists_dom (ρ : Fv F v ⊗[F] E →ₐ[Fv F v] Fv F v) (S : Finset (Fv F v ⊗[F] E)) {w : Fv F v ⊗[F] E}
    (hw : w ∈ Submodule.span (intLoc F E v) (S : Set (Fv F v ⊗[F] E))) (hwu : IsUnit w) :
    ∃ j ∈ S, ρ j ≠ 0 ∧ ∀ s ∈ S, ‖ρ s‖₊ ≤ ‖ρ j‖₊ := by
  have hex : ∃ j ∈ S, ρ j ≠ 0 := by
    by_contra hc
    push Not at hc
    have h0 : ∀ y ∈ Submodule.span (intLoc F E v) (S : Set (Fv F v ⊗[F] E)), ρ y = 0 := fun y hy => by
      induction hy using Submodule.span_induction with
      | mem x hx => exact hc x hx
      | zero => simp
      | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
      | smul a x _ hx => rw [Subring.smul_def, smul_eq_mul, map_mul, hx, mul_zero]
    exact (hwu.map ρ).ne_zero (h0 w hw)
  obtain ⟨j0, hj0, hj0'⟩ := hex
  obtain ⟨j, hj, hmax⟩ := S.exists_max_image (fun s => ‖ρ s‖₊) ⟨j0, hj0⟩
  refine ⟨j, hj, fun e => hj0' ?_, hmax⟩
  have := hmax j0 hj0
  rw [e, nnnorm_zero] at this
  exact nnnorm_eq_zero.1 (le_antisymm this zero_le)

theorem principal_split (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (I : Submodule (intLoc F E v) (Fv F v ⊗[F] E))
    (hI : I.FG) (hu : ∃ u ∈ I, IsUnit u) : ∃ u : Fv F v ⊗[F] E, IsUnit u ∧ I = Submodule.span (intLoc F E v) {u} := by
  classical
  obtain ⟨S, rfl⟩ := hI
  obtain ⟨w, hw, hwu⟩ := hu
  obtain ⟨j1, hj1, h1, hm1⟩ := exists_dom (splitProj τ) S hw hwu
  obtain ⟨j2, hj2, h2, hm2⟩ := exists_dom (splitProj (τ.comp σ)) S hw hwu
  set e := splitIdem h τ with he
  have heI : e ∈ intLoc F E v := splitIdem_mem h τ
  set u : Fv F v ⊗[F] E := e * j1 + (1 - e) * j2 with hu
  have hup : splitProj τ u = splitProj τ j1 := by simp [hu, he]
  have huq : splitProj (τ.comp σ) u = splitProj (τ.comp σ) j2 := by simp [hu, he]
  have hmem : u ∈ Submodule.span (intLoc F E v) (S : Set (Fv F v ⊗[F] E)) :=
    add_mem (Submodule.smul_mem _ (⟨e, heI⟩ : intLoc F E v) (Submodule.subset_span hj1))
      (Submodule.smul_mem _ (⟨1 - e, sub_mem (one_mem _) heI⟩ : intLoc F E v) (Submodule.subset_span hj2))
  have hunit : IsUnit u := by
    refine IsUnit.of_mul_eq_one ((splitAlgEquiv h τ).symm ((splitProj τ j1)⁻¹, (splitProj (τ.comp σ) j2)⁻¹)) ?_
    refine split_ext h τ ?_ ?_
    · simp [hup, h1]
    · simp [huq, h2]
  refine ⟨u, hunit, span_eq_of hmem fun s hs => ?_⟩
  refine ⟨(splitAlgEquiv h τ).symm (splitProj τ s / splitProj τ j1, splitProj (τ.comp σ) s / splitProj (τ.comp σ) j2),
    (mem_intLoc_iff_split h τ).2 ⟨?_, ?_⟩, split_ext h τ ?_ ?_⟩
  · rw [splitProj_symm, ← nnnorm_le_one_iff_mem, nnnorm_div]
    exact div_le_one_of_le₀ (hm1 s hs) zero_le
  · rw [splitProj_comp_symm, ← nnnorm_le_one_iff_mem, nnnorm_div]
    exact div_le_one_of_le₀ (hm2 s hs) zero_le
  · simp [hup, h1]
  · simp [huq, h2]

theorem isHermRing_intLoc : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)),
      IsHermRing (sigR (Fv F v) σ) (intLoc F E v) := by
  intro F E _ _ _ _ _ σ h v
  have h2 : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2 := finrank_loc h
  have hfin : Module.Finite (Fv F v) (Fv F v ⊗[F] E) := Module.finite_of_finrank_pos (by omega)
  refine
    { invol := sigR_sigR h
      conj_mem := fun a ha => sigR_mem_intLoc σ ha
      nontrivial := Module.nontrivial_of_finrank_pos (R := Fv F v) (by omega)
      artinian := IsArtinianRing.of_finite (Fv F v) _
      noeth := noeth_intLoc
      two := ?_
      denom := denom_intLoc
      principal := fun I hI hu => ?_ }
  · have h1 : IsUnit (2 : E) := isUnit_iff_ne_zero.2 two_ne_zero
    have h3 := h1.map (inclR (F := F) (Fv F v))
    rwa [map_ofNat] at h3
  · by_cases hf : IsField (Fv F v ⊗[F] E)
    · exact principal_field hf I hI hu
    · obtain ⟨φ⟩ := nonempty_algHom_of_not_isField (K := Fv F v) h2 hf
      exact principal_split h ((φ.restrictScalars F).comp Algebra.TensorProduct.includeRight) I hI hu

end GlobalTheory.CompanionTheory.KFin.RingHyp

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantFiniteBallSum
section
open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.MirLevi

namespace GlobalTheory.CompanionTheory.MirFourier

theorem exists_finset_eq_sum_polyBall_translates :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (E : Type) [AddCommGroup E] [Module ℂ E] (φ : (Fin n → k) → E) (s S : kˣ), (∀ v a : Fin n → k, Multiplicative.ofAdd a ∈ polyBall (k := k) n s → φ (v + a) = φ v) → (∀ v : Fin n → k, φ v ≠ 0 → Multiplicative.ofAdd v ∈ polyBall (k := k) n S) → ∃ R : Finset (Fin n → k), ∀ v : Fin n → k, φ v = ∑ x ∈ R, @ite _ (Multiplicative.ofAdd (v - x) ∈ polyBall (k := k) n s) (Classical.propDecidable _) (φ x) 0 := by
  intro k _ _ _ _ n E _ _ φ s S hinv hsupp
  classical
  set L := polyBall (k := k) n s with hL
  let q : Multiplicative (Fin n → k) → Multiplicative (Fin n → k) ⧸ L := QuotientGroup.mk
  have hopen : IsOpen (L : Set (Multiplicative (Fin n → k))) := isOpen_polyBall n s
  have hcov : ∃ T : Finset (Multiplicative (Fin n → k)),
      ((polyBall (k := k) n S : Subgroup _) : Set (Multiplicative (Fin n → k))) ⊆
        ⋃ x ∈ T, (fun y => x * y) '' (L : Set (Multiplicative (Fin n → k))) := by
    refine (isCompact_polyBall n S).elim_finite_subcover
      (fun x : Multiplicative (Fin n → k) => (fun y => x * y) '' (L : Set (Multiplicative (Fin n → k))))
      (fun x => (Homeomorph.mulLeft x).isOpenMap _ hopen) ?_ |>.imp fun T hT => ?_
    · intro x _
      exact Set.mem_iUnion.2 ⟨x, 1, L.one_mem, by simp⟩
    · simpa using hT
  obtain ⟨T, hT⟩ := hcov
  let f : Multiplicative (Fin n → k) ⧸ L → (Fin n → k) := fun c => (Quotient.out c).toAdd
  have hf : Function.Injective f := fun a b hab =>
    Quotient.out_injective (Multiplicative.toAdd.injective hab)
  have hmem : ∀ (v : Fin n → k) (c : Multiplicative (Fin n → k) ⧸ L),
      Multiplicative.ofAdd (v - f c) ∈ L ↔ q (Multiplicative.ofAdd v) = c := by
    intro v c
    have hc : q (Quotient.out c) = c := QuotientGroup.out_eq' c
    have hinvEq : Multiplicative.ofAdd (v - f c) =
        ((Multiplicative.ofAdd v)⁻¹ * Quotient.out c)⁻¹ := by
      apply Multiplicative.toAdd.injective
      simp [f, sub_eq_add_neg, add_comm]
    rw [hinvEq, L.inv_mem_iff, ← QuotientGroup.eq]
    exact (by rw [hc] : q (Multiplicative.ofAdd v) = q (Quotient.out c) ↔ _)
  have hval : ∀ v : Fin n → k, φ (f (q (Multiplicative.ofAdd v))) = φ v := by
    intro v
    have h := hinv (f (q (Multiplicative.ofAdd v))) (v - f (q (Multiplicative.ofAdd v)))
      ((hmem v _).2 rfl)
    rw [add_sub_cancel] at h
    exact h.symm
  refine ⟨(T.image q).image f, fun v => ?_⟩
  rw [Finset.sum_image (fun a _ b _ h => hf h)]
  by_cases hv : q (Multiplicative.ofAdd v) ∈ T.image q
  · rw [Finset.sum_eq_single_of_mem _ hv
      (fun b _ hb => if_neg (fun h => hb ((hmem v b).1 h).symm)),
      if_pos ((hmem v _).2 rfl), hval]
  · have h0 : φ v = 0 := by
      by_contra hne
      obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hT (hsupp v hne))
      refine hv (Finset.mem_image.2 ⟨x, hx, ?_⟩)
      have hxv : x⁻¹ * Multiplicative.ofAdd v ∈ L := by
        rw [← hxy]
        simpa using hy
      exact QuotientGroup.eq.2 hxv
    rw [h0]
    refine (Finset.sum_eq_zero fun b hb => if_neg fun h => hv ?_).symm
    rw [(hmem v b).1 h]
    exact hb

end GlobalTheory.CompanionTheory.MirFourier
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalParabolicArchimedeanStabilizes
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.CFin

theorem stabUpTo_archMat_of_mem_minParOne : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n r : ℕ) (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin r) E) (p : GAd σ J), p ∈ minParOne σ J X → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (j : Fin r), StabUpTo (X.map τ.1) (archMat σ J τ (projArch σ J w p)) j := by
  intro F E _ _ _ _ _ σ h n r J X p hp w τ j
  have := h.1
  obtain ⟨B, hB, hE, -⟩ := hp
  let φ := (infEmb τ).comp (compInf F E w)
  have h0 : ∀ x : E, φ (inclR (F := F) (AF F) x) = τ.1 x := fun x => by
    change infEmb τ (evInf F w 1 ⊗ₜ[F] x) = _
    simp
  have h2 : (adMat F X).map φ = X.map τ.1 := Matrix.ext fun i j => h0 _
  have h3 : archMat σ J τ (projArch σ J w p) = (matHom _ σ J p).1.map φ := rfl
  have key : archMat σ J τ (projArch σ J w p) * X.map τ.1 = X.map τ.1 * B.map φ := by
    rw [h3, ← h2, ← Matrix.map_mul, hE, Matrix.map_mul]
  intro l hl
  refine ⟨fun m => φ (B m l), ?_, fun m hm => ?_⟩
  · funext a
    simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply] using congrFun (congrFun key a) l
  · have e : B m l = 0 := hB (show id l < id m from lt_of_le_of_lt hl hm)
    change φ (B m l) = 0
    rw [e, map_zero]

end GlobalTheory.CompanionTheory.CFin

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealCompressionStatement
section
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_compression : PositivityTheory.RgBcC.RealD.Compress := by
  first | exact @GlobalTheory.CompanionTheory.LevelCompress.exists_compress | exact GlobalTheory.CompanionTheory.LevelCompress.exists_compress | (intros; apply GlobalTheory.CompanionTheory.LevelCompress.exists_compress <;> assumption)
end

