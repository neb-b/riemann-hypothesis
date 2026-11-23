module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0215
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0214
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodLinearRelationDensityOfUnfoldingSteps
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.DenseRel

variable {D : D7}

theorem sobCont_zero {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Lie : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Sobolev₂ Lie σ 0 :=
  ⟨[], 0, by simp, by simp⟩

theorem sobCont_smul {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Lie : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {ℓ : H →ₗ[ℂ] ℂ} (c : ℂ)
    (h : Sobolev₂ Lie σ ℓ) : Sobolev₂ Lie σ (c • ℓ) := by
  obtain ⟨S, C, h1, h2⟩ := h
  refine ⟨S, ‖c‖ * C, h1, fun w hw => ?_⟩
  rw [LinearMap.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h2 w hw) (norm_nonneg c)

theorem sobCont_add {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Lie : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {ℓ ℓ' : H →ₗ[ℂ] ℂ}
    (h : Sobolev₂ Lie σ ℓ) (h' : Sobolev₂ Lie σ ℓ') : Sobolev₂ Lie σ (ℓ + ℓ') := by
  obtain ⟨S, C, h1, h2⟩ := h
  obtain ⟨S', C', h1', h2'⟩ := h'
  refine ⟨S ++ S', max C C', fun l hl => (List.mem_append.1 hl).elim (h1 l) (h1' l), fun w hw => ?_⟩
  have p : ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), 0 ≤ (S.map fun l => ‖l.foldr (dRep σ) w‖).sum := by
    intro S
    refine List.sum_nonneg fun x hx => ?_
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
    exact norm_nonneg _
  rw [LinearMap.add_apply, List.map_append, List.sum_append, mul_add]
  refine (norm_add_le _ _).trans (add_le_add ((h2 w hw).trans ?_) ((h2' w hw).trans ?_))
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (p S)
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (p S')

section Sep

variable {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)

theorem sepCont_zero : GlobalTheory.Core.Mi.SepCont M 0 := fun τ _ => ⟨0, sobCont_zero _ _, fun _ => by simp⟩

theorem sepCont_add {Λ Λ' : SmT M →ₗ[ℂ] ℂ} (h : GlobalTheory.Core.Mi.SepCont M Λ) (h' : GlobalTheory.Core.Mi.SepCont M Λ') :
    GlobalTheory.Core.Mi.SepCont M (Λ + Λ') := fun τ v => by
  obtain ⟨ℓ, hℓ, e⟩ := h τ v
  obtain ⟨ℓ', hℓ', e'⟩ := h' τ v
  exact ⟨ℓ + ℓ', sobCont_add hℓ hℓ', fun w => by simp [e, e']⟩

theorem sepCont_smul (a : ℂ) {Λ : SmT M →ₗ[ℂ] ℂ} (h : GlobalTheory.Core.Mi.SepCont M Λ) : GlobalTheory.Core.Mi.SepCont M (a • Λ) :=
  fun τ v => by
    obtain ⟨ℓ, hℓ, e⟩ := h τ v
    exact ⟨a • ℓ, sobCont_smul a hℓ, fun w => by simp [e]⟩

theorem sepCont_sum {ι : Type} (s : Finset ι) (Λ : ι → SmT M →ₗ[ℂ] ℂ) (h : ∀ i ∈ s, GlobalTheory.Core.Mi.SepCont M (Λ i)) :
    GlobalTheory.Core.Mi.SepCont M (∑ i ∈ s, Λ i) :=
  Finset.sum_induction Λ (GlobalTheory.Core.Mi.SepCont M) (fun _ _ => sepCont_add M) (sepCont_zero M) h

theorem kill_of_itSpans {W : HSp D} {S' : D.what₂.Tau → SPar} (M' : DSModel W S')
    (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) (hS : GlobalTheory.Core.Mi.ItSpans M M' It) (Λ : SmT M →ₗ[ℂ] ℂ)
    (h : ∀ P (y : M'.Vec), GlobalTheory.Core.Mi.KVecP M' y → Λ (It P (PiTensorProduct.tprod ℂ y)) = 0) :
    ∀ v : M.Vec, GlobalTheory.Core.Mi.KVecP M v → Λ (PiTensorProduct.tprod ℂ v) = 0 := by
  intro v hv
  have hle : Submodule.span ℂ {x | ∃ (P : PolF D W.rank V.rank) (y : M'.Vec), GlobalTheory.Core.Mi.KVecP M' y ∧
      x = It P (PiTensorProduct.tprod ℂ y)} ≤ LinearMap.ker Λ := by
    rw [Submodule.span_le]
    rintro x ⟨P, y, hy, rfl⟩
    exact h P y hy
  exact hle (hS v hv)

end Sep

theorem isContAut_zero (V : HSp D) : IsContAut V (0 : GA D V → ℂ) :=
  ⟨fun _ _ _ => rfl, continuous_const⟩

theorem isContAut_add {V : HSp D} {f g : GA D V → ℂ} (hf : IsContAut V f) (hg : IsContAut V g) :
    IsContAut V (f + g) :=
  ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.1 γ hγ x, hg.1 γ hγ x], hf.2.add hg.2⟩

theorem isContAut_smul {V : HSp D} {f : GA D V → ℂ} (hf : IsContAut V f) (c : ℂ) : IsContAut V (c • f) :=
  ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.1 γ hγ x], hf.2.const_smul c⟩

theorem isContAut_multT {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {G : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hG : G ∈ MultT θ M J χ) (x : SmT M) : IsContAut V (G x) := by
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      exact isContAut_smul ⟨(hT.aut v).left, (hT.aut v).cont⟩ r
    | add x y hx hy => rw [map_add (f := _)]; exact isContAut_add hx hy
  | zero => simpa using isContAut_zero V
  | add T₁ T₂ _ _ h₁ h₂ => rw [map_add (f := _), LinearMap.add_apply]; exact isContAut_add (h₁ x) (h₂ x)
  | smul c T _ h => rw [map_smul, LinearMap.smul_apply]; exact isContAut_smul (h x) c

end GlobalTheory.SeeSaw.DenseRel


open GlobalTheory.SeeSaw.DenseRel in
theorem GlobalTheory.SeeSaw.perF_rel_of_steps : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), c.Is → ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m) (I : Type) [Fintype I] (s : I → 𝒯) (α : I → ℂ) (φ : ∀ i, (t (s i)).Ch j → GA D (c.X j) → ℂ) (G : ∀ i, (t (s i)).CC j), (∀ s, (t s).Is) → (∀ i a, IsContAut (c.X j) (φ i a)) → ∀ (W W' : HSp D) (S' : D.what₂.Tau → SPar) (M' : DSModel W' S') (It' : PolF D W'.rank (c.V (j + 1)).rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT (c.M (j + 1))), GlobalTheory.Core.Mi.ItSpans (c.M (j + 1)) M' It' → (∀ P₁ P₂ v, ∑ i, α i * (t (s i)).perF j ρ h (φ i) ((G i).1 (c.It j P₁ (It' P₂ v))) = 0) → ∀ v, ∑ i, α i * (t (s i)).perF j ρ h (φ i) ((G i).1 v) = 0 := by
  intro hHC D c 𝒯 t hc j ρ h I _ s α φ G ht hφ _W W' S' M' It' hS' hrel
  have hj : j < D.R.m := by omega
  have hj1 : j + 1 < D.R.m := by omega

  have hmult : ∀ i, ∃ J χ, (G i).1 ∈ MultT c.θ (c.M j) J χ := fun i => by
    obtain ⟨J, χ, hle⟩ := (ht (s i)).CC j hj
    exact ⟨J, χ, hle (G i).2⟩
  choose J χ hG using hmult
  have hcont : ∀ i x, IsContAut (c.V j) ((G i).1 x) := fun i x => isContAut_multT (hG i) x

  have hL : ∀ (i : I) (a : (t (s i)).Ch j) (g : GA D (c.V j)), ∃ Λ : SmT (c.M j) →ₗ[ℂ] ℂ, GlobalTheory.Core.Mi.SepCont (c.M j) Λ ∧
      ∀ x, Λ x = (c.B j ρ h).per c.ψ (φ i a) (rTrans g ((G i).1 x)) := fun i a g =>
    _root_.GlobalTheory.Core.Mi.sepCont_per_rTrans D c.θ c.ψ ρ (c.B j ρ h) (c.par j) (c.M j) (J i) (χ i) g (φ i a) hc.inf hc.std (hφ i a) (G i).1 (hG i)
  choose L hLs hLe using hL
  let Λ : SmT (c.M j) →ₗ[ℂ] ℂ :=
    ∑ i, α i • ∑ a, ∑ g ∈ ((t (s i)).e j a).support, ((t (s i)).e j a g) • L i a g
  have hΛ : ∀ x, Λ x = ∑ i, α i * (t (s i)).perF j ρ h (φ i) ((G i).1 x) := by
    intro x
    simp only [Λ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hLe]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    unfold Tup.perF
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [((_root_.GlobalTheory.SeeSaw.per_linear_trc D c.ψ hc.std ρ (c.B j ρ h) (φ i a) (hφ i a)).2 _ _ (hcont i x)).2]
  have hΛs : GlobalTheory.Core.Mi.SepCont (c.M j) Λ :=
    sepCont_sum _ _ _ fun i _ => sepCont_smul _ _ (sepCont_sum _ _ _ fun a _ =>
      sepCont_sum _ _ _ fun g _ => sepCont_smul _ _ (hLs i a g))
  have hK : ∀ v : (c.M j).Vec, GlobalTheory.Core.Mi.KVecP (c.M j) v → Λ (PiTensorProduct.tprod ℂ v) = 0 := by
    refine kill_of_itSpans (c.M j) (c.M (j + 1)) (c.It j) (hc.span j hj1) Λ fun P y hy => ?_
    exact kill_of_itSpans (c.M (j + 1)) M' It' hS' (Λ ∘ₗ c.It j P)
      (fun P₂ z _ => by simp only [LinearMap.comp_apply, hΛ]; exact hrel P P₂ _) y hy
  have h0 := GlobalTheory.Core.Mi.eq_zero_of_sepCont hHC D (c.V j) (c.par j) (c.M j) Λ hΛs hK
  intro v
  rw [← hΛ v, h0, LinearMap.zero_apply]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiTContinuous
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.KUni

variable {D : D7} {V : HSp D}

theorem inv_eq {G B : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1) : B⁻¹ = Bᴴ * G :=
  Matrix.inv_eq_left_inv hB

theorem mul_inv' {G B : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1) : B * B⁻¹ = 1 := by
  rw [inv_eq hB]; exact mul_eq_one_comm.mp hB

theorem inv_mul' {G B : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1) : B⁻¹ * B = 1 := by
  rw [inv_eq hB]; exact hB

theorem gB {G B : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1) : Gᴴ * B * Bᴴ = 1 := by
  have h := congrArg Matrix.conjTranspose hB
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one] at h
  exact mul_eq_one_comm.mp h

theorem conj_unitary {G B g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1) (hg : gᴴ * G * g = G) :
    B⁻¹ * g * B ∈ Matrix.unitaryGroup (Fin V.rank) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, inv_eq hB]
  have e : (Bᴴ * G * g * B)ᴴ * (Bᴴ * G * g * B) = Bᴴ * gᴴ * (Gᴴ * B * Bᴴ) * G * g * B := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [e, gB hB, Matrix.mul_one]
  calc Bᴴ * gᴴ * G * g * B = Bᴴ * (gᴴ * G * g) * B := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg, hB]

theorem back_unitary {G B u : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1)
    (hu : u ∈ Matrix.unitaryGroup (Fin V.rank) ℂ) : (B * u * B⁻¹)ᴴ * G * (B * u * B⁻¹) = G := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hu
  rw [inv_eq hB]
  have e : (B * u * (Bᴴ * G))ᴴ * G * (B * u * (Bᴴ * G)) = Gᴴ * B * uᴴ * (Bᴴ * G * B) * u * Bᴴ * G := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [e, hB, Matrix.mul_one]
  calc Gᴴ * B * uᴴ * u * Bᴴ * G = Gᴴ * B * (uᴴ * u) * Bᴴ * G := by simp only [Matrix.mul_assoc]
    _ = (Gᴴ * B * Bᴴ) * G := by rw [hu, Matrix.mul_one]
    _ = G := by rw [gB hB, Matrix.one_mul]


open Formalism.IndefR.Eqv in
theorem psiT_continuous (τ : D.what₂.Tau) : Continuous (psiT D τ) := by
  have hsum : ∀ x : AE D, psiT D τ x = ∑ c, psiT D τ (algebraMap (AF D.host.F) (AE D) ((basAF D).repr x c)) *
      psiT D τ (basAF D c) := by
    intro x
    conv_lhs => rw [← (basAF D).sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Algebra.smul_def, map_mul]
  have hc : ∀ c, Continuous fun x : AE D => (basAF D).repr x c := fun c =>
    (continuous_apply c).comp (G5.tensCoordH (basE D) (AF D.host.F)).continuous
  have halg : Continuous fun a : AF D.host.F => psiT D τ (algebraMap (AF D.host.F) (AE D) a) := by
    have e : (fun a : AF D.host.F => psiT D τ (algebraMap (AF D.host.F) (AE D) a)) =
        fun a => thetaC D τ ((fstA D.host.F a) ⊗ₜ[D.host.F] (1 : D.host.E)) := by
      funext a
      simp only [psiT, RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply, infPart,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, map_one]
      rfl
    rw [e]
    exact ((isInfFam_thetaC D) τ).2.comp continuous_fst
  have hfun : (⇑(psiT D τ) : AE D → ℂ) = fun x => ∑ c, psiT D τ (algebraMap (AF D.host.F) (AE D)
      ((basAF D).repr x c)) * psiT D τ (basAF D c) := funext hsum
  rw [hfun]
  exact continuous_finsetSum _ fun c _ => (halg.comp (hc c)).mul continuous_const

open Formalism.IndefR.Eqv in
theorem inB_eq (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (g : GA D V) (τ : D.what₂.Tau) :
    inB (thetaC D) V B g τ = (B τ)⁻¹ * infMat D.sp.cm.sig V.gram (thetaC D τ) g * B τ := by
  rw [infMat_thetaC]; rfl

end GlobalTheory.SeeSaw.KUni


open GlobalTheory.SeeSaw.KUni Formalism.IndefR.Eqv in
theorem GlobalTheory.SeeSaw.ontoUni_inB : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ),
    IsInfFam θ → (∀ τ, (B τ)ᴴ * gramAt D V τ * B τ = 1) → OntoUni fun k : GinfC V => inB θ V B k.1 := by
  intro D θ V B hθ hB
  obtain rfl := eq_thetaC D hθ
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine continuous_pi fun τ => ?_
    have hm : Continuous fun g : GA D V => mt V g := Units.continuous_val.comp continuous_subtype_val
    have h1 : Continuous fun k : GinfC V => (mt V k.1).map (psiT D τ) :=
      (hm.comp continuous_subtype_val).matrix_map (psiT_continuous τ)
    exact (continuous_const.matrix_mul h1).matrix_mul continuous_const
  · intro k k' τ
    rw [inB_eq, inB_eq, inB_eq]
    simp only [Subgroup.coe_mul, infMat_thetaC, matA_mul, Matrix.map_mul]
    calc (B τ)⁻¹ * ((matA D V k).map (psiT D τ) * (matA D V k').map (psiT D τ)) * B τ
        = (B τ)⁻¹ * (matA D V k).map (psiT D τ) * (B τ * (B τ)⁻¹) * (matA D V k').map (psiT D τ) * B τ := by
          rw [mul_inv' (hB τ)]; simp only [Matrix.mul_assoc, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]
  · intro k τ
    rw [inB_eq]
    exact conj_unitary (hB τ) (infMat_unitary' D V k.1 τ)
  · intro u hu
    have hgs : IsUnitFam D V fun τ => B τ * u τ * (B τ)⁻¹ := fun τ => back_unitary (hB τ) (hu τ)
    refine ⟨⟨famH D V _ hgs, famH_mem_GinfC D V _ hgs⟩, ?_⟩
    funext τ
    rw [inB_eq, infMat_famH]
    calc (B τ)⁻¹ * (B τ * u τ * (B τ)⁻¹) * B τ = ((B τ)⁻¹ * B τ) * u τ * ((B τ)⁻¹ * B τ) := by
          simp only [Matrix.mul_assoc]
      _ = u τ := by rw [inv_mul' (hB τ), Matrix.one_mul, Matrix.mul_one]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuotientIntegralVanishOfIteratedFiniteIntegrals
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VanCore

theorem quotient_integral_weighted_sum {G : Type} [Group G] [MeasurableSpace G] {R : Subgroup G} {μR : Measure R} {μG : Measure G}
    {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → G → ℂ) (z : ι → ℂ) (h : ∀ i ∈ s, IsQuotIntL1 μR μG (f i) (z i)) :
    IsQuotIntL1 μR μG (fun x => ∑ i ∈ s, c i * f i x) (∑ i ∈ s, c i * z i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    convert (IsQuotIntL1.zero : IsQuotIntL1 μR μG 0 0) using 1
    · funext x; simp
    · simp
  | insert i s hi ih =>
    have h1 := (h i (Finset.mem_insert_self i s)).smul (c i)
    have h2 := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    convert h1.add h2 using 1
    · funext x; simp [Finset.sum_insert hi]
    · simp [Finset.sum_insert hi]

theorem vanish : ∀ (G₁ G₂ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [SecondCountableTopology G₁] [LocallyCompactSpace G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [SecondCountableTopology G₂] [LocallyCompactSpace G₂] [T2Space G₂] [MeasurableSpace G₂] [BorelSpace G₂] (A₁ B₁ R₁ : Subgroup G₁) (A₂ B₂ R₂ : Subgroup G₂), IsClosed (A₁ : Set G₁) → IsClosed (B₁ : Set G₁) → IsClosed (R₁ : Set G₁) → (∀ a ∈ A₁, ∀ b ∈ B₁, a * b = b * a) → (∃ e : (A₁ × B₁) ≃ₜ G₁, ∀ p, e p = p.1 * p.2) → (∀ a ∈ A₁, ∀ b ∈ B₁, a * b ∈ R₁ → a ∈ R₁ ∧ b ∈ R₁) → IsClosed (A₂ : Set G₂) → IsClosed (B₂ : Set G₂) → IsClosed (R₂ : Set G₂) → (∀ a ∈ A₂, ∀ b ∈ B₂, a * b = b * a) → (∃ e : (A₂ × B₂) ≃ₜ G₂, ∀ p, e p = p.1 * p.2) → (∀ a ∈ A₂, ∀ b ∈ B₂, a * b ∈ R₂ → a ∈ R₂ ∧ b ∈ R₂) → ∀ (μR₁ : Measure R₁) (μG₁ : Measure G₁) (ρ₁ : Measure (R₁.subgroupOf B₁)) (μ₁ : Measure B₁) (μR₂ : Measure R₂) (μG₂ : Measure G₂) (ρ₂ : Measure (R₂.subgroupOf B₂)) (μ₂ : Measure B₂), μR₁.IsHaarMeasure → μR₁.IsInvInvariant → μG₁.IsHaarMeasure → ρ₁.IsHaarMeasure → ρ₁.IsInvInvariant → μ₁.IsHaarMeasure → μ₁.IsMulRightInvariant → μR₂.IsHaarMeasure → μR₂.IsInvInvariant → μG₂.IsHaarMeasure → ρ₂.IsHaarMeasure → ρ₂.IsInvInvariant → μ₂.IsHaarMeasure → ∀ (K : Subgroup G₁) (C : Set G₁) (T : Finset G₁), K ≤ B₁ → IsCompact (K : Set G₁) → IsOpen ((K.subgroupOf B₁ : Subgroup B₁) : Set B₁) → IsCompact C → C ⊆ (B₁ : Set G₁) → (∀ q ∈ T, q ∈ B₁) → ∀ (F₁ : G₁ → ℂ) (F₂ : G₁ → G₂ → ℂ) (z : ℂ), IsQuotIntL1 μR₁ μG₁ F₁ z → (∀ h₁, IsQuotIntL1 μR₂ μG₂ (F₂ h₁) (F₁ h₁)) → (∀ h₁, ∀ k ∈ K, F₂ (h₁ * k) = F₂ h₁) → (∀ h₁, F₂ h₁ ≠ 0 → ∃ q ∈ T, ∃ r ∈ R₁, ∃ a ∈ A₁, ∃ k ∈ C, h₁ = r * a * q * k) → (∀ a ∈ A₁, ∀ a' ∈ A₂, Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun (q₁ : B₁) (q₂ : B₂) => F₂ (a * q₁.1) (a' * q₂.1)) 0) → z = 0 := by
  intro G₁ G₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A₁ B₁ R₁ A₂ B₂ R₂ hA₁ hB₁ hR₁ hc₁ he₁ hs₁ hA₂ hB₂ hR₂ hc₂ he₂ hs₂
    μR₁ μG₁ ρ₁ μ₁ μR₂ μG₂ ρ₂ μ₂ i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 K C T hKB hKc hKo hCc hCB hTB
    F₁ F₂ z hF₁ hF₂ hFK hsupp hIter
  classical
  haveI : LocallyCompactSpace B₁ := hB₁.locallyCompactSpace
  haveI : LocallyCompactSpace B₂ := hB₂.locallyCompactSpace
  have hR₁B : IsClosed ((R₁.subgroupOf B₁ : Subgroup B₁) : Set B₁) := by
    rw [Subgroup.coe_subgroupOf]; exact hR₁.preimage continuous_subtype_val
  have hR₂B : IsClosed ((R₂.subgroupOf B₂ : Subgroup B₂) : Set B₂) := by
    rw [Subgroup.coe_subgroupOf]; exact hR₂.preimage continuous_subtype_val

  have FK : ∀ h, ∀ k ∈ K, F₁ (h * k) = F₁ h := fun h k hk => by
    have h1 := hF₂ (h * k)
    rw [hFK h k hk] at h1
    exact (IsQuotIntL1.unique hR₂ (hF₂ h) h1).symm
  have FZ : ∀ h, F₂ h = 0 → F₁ h = 0 := fun h h0 => by
    have h1 := hF₂ h
    rw [h0] at h1
    exact (GlobalTheory.QuotZero.left_and_zero hR₂ μR₂ μG₂ h1).2 rfl
  have FL := (GlobalTheory.QuotZero.left_and_zero hR₁ μR₁ μG₁ hF₁).1

  have hCb : IsCompact (Subtype.val ⁻¹' C : Set B₁) := by
    rw [Subtype.isCompact_iff, Set.image_preimage_eq_of_subset]
    · exact hCc
    · intro x hx; exact ⟨⟨x, hCB hx⟩, rfl⟩
  have hKbc : IsCompact ((K.subgroupOf B₁ : Subgroup B₁) : Set B₁) := by
    rw [Subgroup.coe_subgroupOf, Subgroup.coe_subtype, Subtype.isCompact_iff, Set.image_preimage_eq_of_subset]
    · exact hKc
    · intro x hx; exact ⟨⟨x, hKB hx⟩, rfl⟩
  have hKint : (interior ((K.subgroupOf B₁ : Subgroup B₁) : Set B₁)).Nonempty := by
    rw [hKo.interior_eq]; exact ⟨1, (K.subgroupOf B₁).one_mem⟩
  obtain ⟨S, hS⟩ := compact_covered_by_mul_left_translates hCb hKint
  let T'' : Finset B₁ := ((T.subtype (· ∈ B₁)) ×ˢ S).image (fun p => p.1 * p.2⁻¹)

  have cell : ∀ a ∈ A₁, ∀ q : B₁, F₂ (a * q) ≠ 0 →
      ∃ q' ∈ T'', ∃ r ∈ R₁.subgroupOf B₁, ∃ k ∈ K.subgroupOf B₁, q = r * q' * k := by
    intro a ha q hq
    obtain ⟨q₀, hq₀, r, hr, a'', ha'', k, hk, hdec⟩ := hsupp _ hq
    obtain ⟨e, he⟩ := he₁
    obtain ⟨⟨pa, pb⟩, hp⟩ : ∃ p, e.symm r = p := ⟨_, rfl⟩
    have hrp : r = (pa : G₁) * pb := by rw [← he (pa, pb), ← hp, e.apply_symm_apply]
    subst hrp
    have hpR := hs₁ _ pa.2 _ pb.2 hr
    have hkB : k ∈ B₁ := hCB hk
    have hq₀B : q₀ ∈ B₁ := hTB q₀ hq₀
    have key : e (⟨a, ha⟩, q) = e (pa * ⟨a'', ha''⟩, pb * ⟨q₀, hq₀B⟩ * ⟨k, hkB⟩) := by
      rw [he, he]
      show a * (q : G₁) = ((pa : G₁) * a'') * ((pb : G₁) * q₀ * k)
      rw [hdec, mul_assoc (pa : G₁) pb a'', ← hc₁ a'' ha'' pb pb.2]
      simp only [mul_assoc]
    have hq' : q = pb * ⟨q₀, hq₀B⟩ * ⟨k, hkB⟩ := congrArg Prod.snd (e.injective key)
    obtain ⟨g, hgS, hg⟩ := Set.mem_iUnion₂.1 (hS (show (⟨k, hkB⟩ : B₁) ∈ (Subtype.val ⁻¹' C : Set B₁) from hk))
    refine ⟨⟨q₀, hq₀B⟩ * g⁻¹, ?_, pb, ?_, g * ⟨k, hkB⟩, hg, ?_⟩
    · exact Finset.mem_image.2 ⟨(⟨q₀, hq₀B⟩, g), Finset.mem_product.2 ⟨Finset.mem_subtype.2 hq₀, hgS⟩, rfl⟩
    · exact Subgroup.mem_subgroupOf.2 hpR.2
    · rw [hq']; group
  obtain ⟨T', w, -, hW⟩ := GlobalTheory.CellInt.quotInt_finiteCells B₁ (R₁.subgroupOf B₁) (K.subgroupOf B₁) hR₁B hKbc hKo
    ρ₁ μ₁ inferInstance inferInstance inferInstance inferInstance T''
  refine _root_.GlobalTheory.CommProd.quot_vanish_of_prod G₁ A₁ B₁ R₁ hA₁ hB₁ hR₁ hc₁ he₁ hs₁ μR₁ μG₁ ρ₁ μ₁ inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance F₁ z hF₁ ?_
  intro a ha
  have h1 := hW (fun b => F₁ (a * b.1))
    (fun r hr g => by
      show F₁ (a * ((r : G₁) * g)) = F₁ (a * g)
      rw [← mul_assoc, hc₁ a ha r r.2, mul_assoc]
      exact FL _ (Subgroup.mem_subgroupOf.1 hr) _)
    (fun k hk g => by
      show F₁ (a * ((g : G₁) * k)) = F₁ (a * g)
      rw [← mul_assoc]
      exact FK _ _ (Subgroup.mem_subgroupOf.1 hk))
    (fun g hg => cell a ha g (fun h0 => hg (FZ _ h0)))
  suffices hsum : ∑ q ∈ T', w q * F₁ (a * q.1) = 0 by
    convert h1 using 1; exact hsum.symm
  refine _root_.GlobalTheory.CommProd.quot_vanish_of_prod G₂ A₂ B₂ R₂ hA₂ hB₂ hR₂ hc₂ he₂ hs₂ μR₂ μG₂ ρ₂ μ₂ inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance (fun h₂ => ∑ q ∈ T', w q * F₂ (a * q.1) h₂) _
    (quotient_integral_weighted_sum T' w (fun q => F₂ (a * q.1)) (fun q => F₁ (a * q.1)) (fun q _ => hF₂ _)) ?_
  intro a' ha'
  obtain ⟨f₁, hf₁0, hf₁q⟩ := hIter a ha a' ha'
  have hs := quotient_integral_weighted_sum T' w (fun q (b : B₂) => F₂ (a * q.1) (a' * b.1)) f₁ (fun q _ => hf₁q q)
  have hf₁ : IsQuotIntL1 ρ₁ μ₁ f₁ (∑ q ∈ T', w q * f₁ q) := hW f₁
    (GlobalTheory.QuotZero.left_and_zero hR₁B ρ₁ μ₁ hf₁0).1
    (fun k hk g => by
      have h2 : IsQuotIntL1 ρ₂ μ₂ (fun q₂ : B₂ => F₂ (a * g.1) (a' * q₂.1)) (f₁ (g * k)) := by
        have h3 := hf₁q (g * k)
        have e3 : (fun q₂ : B₂ => F₂ (a * (g * k).1) (a' * q₂.1)) = fun q₂ : B₂ => F₂ (a * g.1) (a' * q₂.1) := by
          funext q₂
          rw [Subgroup.coe_mul, ← mul_assoc, hFK _ _ (Subgroup.mem_subgroupOf.1 hk)]
        exact e3 ▸ h3
      exact IsQuotIntL1.unique hR₂B h2 (hf₁q g))
    (fun g hg => cell a ha g (fun h0 => hg ((GlobalTheory.QuotZero.left_and_zero hR₂B ρ₂ μ₂ (hf₁q g)).2
      (by funext q₂; simp [h0]))))
  have hz := IsQuotIntL1.unique hR₁B hf₁ hf₁0
  rw [hz] at hs
  exact hs

end GlobalTheory.VanCore
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchroedingerIntertwinerSliceRestrictionPlaceMode
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

theorem restrModel_isPlaceModel : ∀ (D : D7) {m n m' n' m'' n'' : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (BS : Mx D m n → Mx D m n → AF D.host.F) (hsS : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)) (BA : Mx D m' n' → Mx D m' n' → AF D.host.F) (hsA : Mx D m' n' → (Mx D m' n' → ℂ) → (Mx D m' n' → ℂ)) (r : Mx D m n ≃+ Mx D m' n' × Mx D m'' n'') (e : AE D) (ΛS : AddSubgroup (Mx D m n)) (ΛA : AddSubgroup (Mx D m' n')) (h : Mx D m'' n'' → ℂ) (f₀ : Mx D m n → ℂ) (T' : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ)), IsPlaceModel ψ BS hsS e ΛS 1 f₀ T' → (∀ a F w y, hsS (r.symm (a, 0)) F (r.symm (w, y)) = hsA a (fun w' => F (r.symm (w', y))) w) → (∀ t a, BS t (r.symm (a, 0)) = BA (r t).1 a) → (∀ a, IsHalf e a → IsHalf e (r.symm (a, 0))) → (∀ a, IsHalf (cA D e) a → IsHalf (cA D e) (r.symm (a, 0))) → (∀ Φ, IsSBHalf e ΛA Φ → IsSBHalf e ΛS (fun t => Φ (r t).1 * h (r t).2)) → halfInd e ΛS = (fun t => halfInd e ΛA (r t).1 * h (r t).2) → ∀ y, IsPlaceModel ψ BA hsA e ΛA 1 (fun w => f₀ (r.symm (w, y))) (GlobalTheory.FinPl.ExtZero.restrModel r h T' y) := by
  intro D m n m' n' m'' n'' ψ BS hsS BA hsA r e ΛS ΛA h f₀ T' hT hcomp hB hhalf hhalfc hSB hInd y
  refine ⟨?_, ?_, ?_⟩
  · intro Φ hΦ x hx
    funext w
    rw [restrModel_apply]
    have hfun : (fun t => (fun t => Φ (t + x)) (r t).1 * h (r t).2) =
        fun t => (fun t => Φ (r t).1 * h (r t).2) (t + r.symm (x, 0)) := by
      funext t
      simp only [map_add (f := _), AddEquiv.apply_symm_apply, Prod.fst_add, Prod.snd_add, add_zero]
    rw [hfun, hT.trans _ (hSB Φ hΦ) _ (hhalf x hx), hcomp]
    rfl
  · intro Φ hΦ y' hy'
    funext w
    rw [restrModel_apply]
    have hfun : (fun t => (fun t => ψ (BA t y') * Φ t) (r t).1 * h (r t).2) =
        fun t => ψ (BS t (r.symm (y', 0))) * (fun t => Φ (r t).1 * h (r t).2) t := by
      funext t
      simp only [hB, mul_assoc]
    rw [hfun, hT.modul _ (hSB Φ hΦ) _ (hhalfc y' hy'), hcomp]
    rfl
  · funext w
    rw [restrModel_apply]
    have hfun : (fun t => ((1 : ℂ) • halfInd e ΛA) (r t).1 * h (r t).2) = (1 : ℂ) • halfInd e ΛS := by
      rw [hInd]; funext t; simp
    rw [hfun, hT.vac]

end GlobalTheory.FinPl.ExtZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaContractionQuasiPeriodicRational
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ContrComb

theorem contr_quasi : ∀ (D : D7) (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (ψ : AddChar (AF D.host.F) ℂ) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ S f₁ → IsThetaFunO ψ S B'.V₀ f₂ → (∀ γ u v, contr l S vL f₁ f₂ (ratW S B.A γ + u) v = ψ (-(symplOH B.A S (ratW S B.A γ) u)) * contr l S vL f₁ f₂ u v) ∧ ∀ γ u v, contr l S vL f₁ f₂ u (ratW B'.A S γ + v) = ψ (-(symplOH S B'.A (ratW B'.A S γ) v)) * contr l S vL f₁ f₂ u v := by
  intro D ρ σ B B' l S vL ψ f₁ f₂ h₁ h₂
  constructor
  · intro γ u v
    have e0 : (B.o.resS S).symm (ratW S B.A γ, 0) = ratW S B.V₀ (γ * B.o.qA) := by
      rw [OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero, ratW_eq, ratW_eq, rat_mul]; rfl
    simp only [contr]
    rw [← integral_const_mul]
    congr 1
    funext w
    have e : ((ratW S B.A γ + u, l.κ S w) : WO B.A S × WO B.L S) = (ratW S B.A γ, (0 : WO B.L S)) + (u, l.κ S w) := by simp
    rw [e, map_add (f := _), e0, h₁.quasi, ← e0, B.o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      symplOH_zero_left, add_zero]
    ring
  · intro γ u v
    have e0 : (B'.o.resT S).symm (ratW B'.A S γ, 0) = ratW B'.V₀ S (B'.o.iA * γ) := by
      rw [OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero, ratW_eq, ratW_eq, rat_mul]; rfl
    simp only [contr]
    rw [← integral_const_mul]
    congr 1
    funext w
    have e : ((ratW B'.A S γ + v, w) : WO S B'.A × WO S B'.L) = (ratW B'.A S γ, (0 : WO S B'.L)) + (v, w) := by simp
    rw [e, map_add (f := _), e0, h₂.quasi, ← e0, B'.o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      symplOH_zero_left, add_zero]
    ring

end GlobalTheory.ContrComb
end

